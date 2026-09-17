#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
M — универсальный инструмент «всё в одном» для Termux (mobile-first).
Версия 6.1 — разрыв undo-группы на движении курсора.

Изменения относительно 6.0:
  • Стрелки/Home/End теперь сбрасывают группу undo: движение курсора
    разрывает непрерывную печать. Ctrl+Z после «abc ← d» откатывает
    сначала 'd', потом 'abc' — как в VS Code / vim.
  • _push_undo() (для явных операций) сбрасывает группу undo сам —
    защита от будущих footgun-вызовов.
  • Убрано дублирование _reset_undo_group() в editor_replace.
  • Уточнён docstring: группируется «непрерывная печать», а не
    «вставка большого текста» (паста через get_wch идёт посимвольно,
    и группировка зависит от таймингов).
"""

import curses
import os
import sys
import shutil
import importlib.util
import json
import zipfile
import tarfile
import subprocess
import time
import unicodedata
from pathlib import Path
from collections import deque


# ============================ ПУТИ ============================
HOME = Path.home()
CONFIG_DIR = HOME / ".m"
HOOKS_DIR = CONFIG_DIR / "hooks"
LOGS_DIR = CONFIG_DIR / "logs"
BACKUP_DIR = CONFIG_DIR / "backups"
CONFIG_FILE = CONFIG_DIR / "config.json"
BOOKMARKS_FILE = CONFIG_DIR / "bookmarks.json"
TRASH_DIR = CONFIG_DIR / "trash"
TRASH_META = TRASH_DIR / ".meta.json"

ARCHIVE_EXTS = (".zip", ".tar", ".tar.gz", ".tgz", ".tar.bz2", ".tbz2", ".tar.xz")

ARCHIVE_EXTS_SET = (".gz", ".bz2", ".xz", ".zst", ".lz", ".lzma",
                    ".7z", ".rar", ".z")

CODE_EXTS = (".py", ".js", ".ts", ".tsx", ".jsx", ".rs", ".go", ".c", ".cpp",
             ".h", ".hpp", ".java", ".rb", ".php", ".lua")
SCRIPT_EXTS = (".sh", ".bash", ".zsh", ".fish", ".ps1")
IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".svg", ".webp", ".ico")

TABSTOP = 8


# ============================ АВТОСОЗДАНИЕ СТРУКТУРЫ ============================
def ensure_directories():
    for d in (CONFIG_DIR, HOOKS_DIR, LOGS_DIR, BACKUP_DIR, TRASH_DIR):
        try:
            d.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass


# ============================ ХУКИ ============================
class HookManager:
    def __init__(self):
        self.hooks = {}
        self.loaded = []
        self.errors = []
        self.reload()

    def reload(self):
        ensure_directories()
        self.hooks = {}
        self.loaded = []
        self.errors = []
        for f in sorted(HOOKS_DIR.glob("*.py")):
            try:
                spec = importlib.util.spec_from_file_location(f.stem, f)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                events = getattr(mod, "EVENTS", {})
                if not isinstance(events, dict):
                    continue
                for evt, fn in events.items():
                    if callable(fn):
                        self.hooks.setdefault(evt, []).append((f.stem, fn))
                self.loaded.append(f.stem)
            except Exception as e:
                self.errors.append(f"{f.name}: {type(e).__name__}: {e}")

    def fire(self, event, **kwargs):
        for name, fn in self.hooks.get(event, []):
            try:
                fn(**kwargs)
            except Exception:
                pass

    def fire_collect(self, event, **kwargs):
        results = []
        for name, fn in self.hooks.get(event, []):
            try:
                r = fn(**kwargs)
                if r is not None:
                    results.append(r)
            except Exception:
                pass
        return results


# ============================ UNDO ============================
class UndoManager:
    def __init__(self, max_size=100):
        self.undo_stack = deque(maxlen=max_size)
        self.redo_stack = deque(maxlen=max_size)

    def push(self, description, undo_fn, redo_fn):
        self.undo_stack.append((description, undo_fn, redo_fn))
        self.redo_stack.clear()

    def undo(self):
        if not self.undo_stack:
            return None
        desc, undo_fn, redo_fn = self.undo_stack.pop()
        try:
            undo_fn()
            self.redo_stack.append((desc, undo_fn, redo_fn))
            return f"Отменено: {desc}"
        except Exception as e:
            return f"Ошибка отмены: {e}"

    def redo(self):
        if not self.redo_stack:
            return None
        desc, undo_fn, redo_fn = self.redo_stack.pop()
        try:
            redo_fn()
            self.undo_stack.append((desc, undo_fn, redo_fn))
            return f"Повторено: {desc}"
        except Exception as e:
            return f"Ошибка повтора: {e}"


# ============================ ОСНОВНОЙ КЛАСС ============================
class M:
    MODE_FILES = "files"
    MODE_EDITOR = "editor"
    MODE_HELP = "help"
    MODE_HELP_EDITOR = "help_editor"
    MODE_HOOKS = "hooks"
    MODE_DASHBOARD = "dashboard"
    MODE_BOOKMARKS = "bookmarks"
    MODE_TRASH = "trash"
    MODE_ARCHIVE = "archive"

    # ── Группировка undo в редакторе ──────────────────────────────
    # Непрерывная печать/backspace одного типа в этом окне = одна
    # группа. Любая смена типа правки, движение курсора, Enter/Tab,
    # undo/redo, save, open или replace разрывают группу.
    UNDO_GROUP_WINDOW = 0.3

    def __init__(self, stdscr):
        self.stdscr = stdscr
        self.hooks = HookManager()
        self.undo = UndoManager()
        self.running = True
        self.message = ""
        self.mode = self.MODE_FILES
        self.return_mode = self.MODE_FILES

        cwd = Path.cwd()
        self.panes = [cwd, cwd]
        self.active = 0
        self.selected = [0, 0]
        self.items = [[], []]
        self.marked = [set(), set()]
        self.show_hidden = False
        self.fm_hits = []
        self.fm_hit_idx = -1

        self.tabs = [{
            "panes": [cwd, cwd],
            "selected": [0, 0],
            "active": 0,
        }]
        self.active_tab = 0

        self.bookmarks = []
        self.bm_idx = 0

        self.ed_filename = ""
        self.ed_buffer = [""]
        self.ed_cursor = [0, 0]
        self.ed_modified = False
        self.ed_undo_stack = deque(maxlen=200)
        self.ed_redo_stack = deque(maxlen=200)
        self.ed_search_hits = []
        self.ed_search_idx = -1

        # Состояние группировки undo в редакторе
        self._last_edit_time = 0.0
        self._last_edit_kind = None   # None | "insert" | "delete" | "other"

        self.prompt_active = False
        self.prompt_text = ""
        self.prompt_input = ""
        self.prompt_callback = None

        self.archive_path = None
        self.archive_items = []
        self.archive_kind = None

        self.load_config()
        self.load_bookmarks()
        self.init_colors()
        self.refresh_pane(0)
        self.refresh_pane(1)

    # ==================== КОНФИГ / ЗАКЛАДКИ ====================
    def load_config(self):
        try:
            if CONFIG_FILE.exists():
                data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
                self.show_hidden = bool(data.get("show_hidden", False))
        except Exception:
            pass

    def save_config(self):
        try:
            ensure_directories()
            CONFIG_FILE.write_text(json.dumps({
                "show_hidden": self.show_hidden,
            }, indent=2), encoding="utf-8")
        except Exception:
            pass

    def load_bookmarks(self):
        try:
            if BOOKMARKS_FILE.exists():
                data = json.loads(BOOKMARKS_FILE.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    self.bookmarks = [str(b) for b in data if isinstance(b, str)]
        except Exception:
            self.bookmarks = []

    def save_bookmarks(self):
        try:
            ensure_directories()
            BOOKMARKS_FILE.write_text(json.dumps(self.bookmarks, indent=2),
                                      encoding="utf-8")
        except Exception:
            pass

    # ==================== ЦВЕТА ====================
    def init_colors(self):
        try:
            if not curses.has_colors():
                return
            curses.start_color()
            try:
                curses.use_default_colors()
            except Exception:
                pass
            bg = -1
            curses.init_pair(1, curses.COLOR_CYAN, bg)
            curses.init_pair(2, curses.COLOR_GREEN, bg)
            curses.init_pair(3, curses.COLOR_YELLOW, bg)
            curses.init_pair(4, curses.COLOR_RED, bg)
            curses.init_pair(5, curses.COLOR_BLACK, curses.COLOR_CYAN)
            curses.init_pair(6, curses.COLOR_MAGENTA, bg)
            curses.init_pair(7, curses.COLOR_BLUE, bg)
            if curses.COLORS >= 256:
                try:
                    curses.init_pair(8, 16, 250)
                    curses.init_pair(9, 16, 240)
                    curses.init_pair(10, 16, 254)
                except Exception:
                    curses.init_pair(8, curses.COLOR_BLACK, curses.COLOR_WHITE)
                    curses.init_pair(9, curses.COLOR_BLACK, curses.COLOR_WHITE)
                    curses.init_pair(10, curses.COLOR_BLACK, curses.COLOR_WHITE)
            else:
                curses.init_pair(8, curses.COLOR_BLACK, curses.COLOR_WHITE)
                curses.init_pair(9, curses.COLOR_BLACK, curses.COLOR_WHITE)
                curses.init_pair(10, curses.COLOR_BLACK, curses.COLOR_WHITE)
        except Exception:
            pass

    def cp(self, n, extra=0):
        try:
            if not curses.has_colors():
                return extra
            return curses.color_pair(n) | extra
        except Exception:
            return extra

    # ==================== ВВОД ====================
    def _get_key(self):
        """Универсальное чтение клавиши с поддержкой Unicode."""
        ch = None
        try:
            ch = self.stdscr.get_wch()
        except AttributeError:
            try:
                ch = self.stdscr.getch()
            except curses.error:
                return -1
            except KeyboardInterrupt:
                raise
        except curses.error:
            return -1
        except KeyboardInterrupt:
            raise

        if isinstance(ch, str):
            if len(ch) == 0:
                # get_wch() иногда возвращает пустую строку —
                # трактуем как отсутствие события
                return -1
            if len(ch) == 1 and ord(ch) < 128:
                return ord(ch)
            return ch
        return ch

    def _set_cursor_visible(self, visible):
        try:
            curses.curs_set(1 if visible else 0)
        except Exception:
            pass

    @staticmethod
    def _char_width(ch):
        """Визуальная ширина одного символа:
        0 — combining / ZWJ / VS15 / VS16,
        2 — Wide/Fullwidth (CJK, эмодзи),
        1 — всё остальное.
        Табы обрабатываются отдельно."""
        cp = ord(ch)
        if cp in (0x200D, 0xFE0E, 0xFE0F):
            return 0
        if unicodedata.combining(ch):
            return 0
        eaw = unicodedata.east_asian_width(ch)
        if eaw in ('F', 'W'):
            return 2
        return 1

    @staticmethod
    def _visual_col(line, cx, tabstop=TABSTOP):
        """Логическая колонка → визуальная с учётом табов и CJK/emoji."""
        if cx <= 0:
            return 0
        prefix = line[:cx]
        if prefix.isascii() and '\t' not in prefix:
            return cx
        col = 0
        for ch in prefix:
            if ch == '\t':
                col = ((col // tabstop) + 1) * tabstop
            else:
                col += M._char_width(ch)
        return col

    # ==================== ПАНЕЛИ ====================
    def refresh_pane(self, idx):
        try:
            all_items = list(self.panes[idx].iterdir())
            if not self.show_hidden:
                all_items = [p for p in all_items if not p.name.startswith('.')]
            items = sorted(all_items,
                           key=lambda p: (not p.is_dir(), p.name.lower()))
            self.items[idx] = [Path("..")] + items
        except Exception:
            self.items[idx] = [Path("..")]
        if self.selected[idx] >= len(self.items[idx]):
            self.selected[idx] = max(0, len(self.items[idx]) - 1)
        if self.selected[idx] < 0:
            self.selected[idx] = 0

    def current_item(self, idx=None):
        idx = self.active if idx is None else idx
        if 0 <= self.selected[idx] < len(self.items[idx]):
            return self.items[idx][self.selected[idx]]
        return None

    # ==================== ВЫВОД ====================
    def addstr(self, y, x, text, attr=0):
        """Рисует текст, обрезая по ВИЗУАЛЬНОЙ ширине."""
        try:
            h, w = self.stdscr.getmaxyx()
            if y < 0 or y >= h or x < 0 or x >= w:
                return
            s = str(text)
            avail = w - x - 1
            if avail <= 0 or not s:
                return

            if s.isascii() and '\t' not in s:
                if len(s) > avail:
                    s = s[:avail]
                if s:
                    self.stdscr.addstr(y, x, s, attr)
                return

            out = []
            col = x
            max_col = w - 1
            for ch in s:
                if ch == '\t':
                    nxt = ((col // TABSTOP) + 1) * TABSTOP
                else:
                    nxt = col + M._char_width(ch)
                if nxt > max_col:
                    break
                out.append(ch)
                col = nxt
            if out:
                self.stdscr.addstr(y, x, ''.join(out), attr)
        except Exception:
            pass

    def move_cursor(self, y, x):
        try:
            h, w = self.stdscr.getmaxyx()
            if 0 <= y < h and 0 <= x < w:
                self.stdscr.move(y, x)
        except Exception:
            pass

    def set_message(self, msg):
        self.message = msg

    # ==================== ЦВЕТ ФАЙЛА ПО РАСШИРЕНИЮ ====================
    def _is_archive_name(self, name):
        n = name.lower()
        return (any(n.endswith(e) for e in ARCHIVE_EXTS)
                or any(n.endswith(e) for e in ARCHIVE_EXTS_SET))

    def _file_attr(self, item):
        if item.name == ".." or item.is_dir():
            return self.cp(2)
        if self._is_archive_name(item.name):
            return self.cp(3)
        ext = item.suffix.lower()
        if ext in CODE_EXTS:
            return self.cp(6, curses.A_BOLD)
        if ext in SCRIPT_EXTS:
            return self.cp(2)
        if ext in IMAGE_EXTS:
            return self.cp(6)
        return curses.A_NORMAL

    # ==================== ОТРИСОВКА: ФАЙЛЫ ====================
    def draw_files(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        tab_label = ""
        if len(self.tabs) > 1:
            tab_label = " ".join(
                f"[{i+1}]" if i == self.active_tab else f" {i+1} "
                for i in range(len(self.tabs))
            )
        title = f" M v6.1 {tab_label} — Файлы "
        self.addstr(0, 0, title, self.cp(1, curses.A_BOLD))

        half = max(10, w // 2)
        for i in range(2):
            x0 = i * half
            width = half if i == 0 else max(1, w - x0)
            if i == 0:
                for y in range(1, h - 2):
                    try:
                        self.stdscr.addch(y, half - 1, curses.A_VLINE)
                    except Exception:
                        pass
            self._draw_pane(i, x0, width, h)

        status = " Enter:откр m:папка n:файл i:пер c:коп d:удал e:ред ?:справка "

        if self.prompt_active:
            self._set_cursor_visible(True)
            prompt_line = f" {self.prompt_text}{self.prompt_input}"
            if self.message:
                self.addstr(h - 2, 0, prompt_line, self.cp(3))
                self.addstr(h - 1, 0, f" {self.message}",
                            self.cp(4, curses.A_BOLD))
                vcol = self._visual_col(prompt_line, len(prompt_line))
                self.move_cursor(h - 2, min(vcol, w - 2))
            else:
                self.addstr(h - 1, 0, prompt_line, self.cp(3, curses.A_BOLD))
                vcol = self._visual_col(prompt_line, len(prompt_line))
                self.move_cursor(h - 1, min(vcol, w - 2))
        else:
            self._set_cursor_visible(False)
            msg = self.message or status
            attr = self.cp(4) if self.message else curses.A_DIM
            self.addstr(h - 1, 0, msg, attr)

        self.stdscr.refresh()

    def _draw_pane(self, i, x0, width, h):
        header = f" {self.panes[i]} "
        attr = self.cp(1, curses.A_BOLD) if i == self.active else curses.A_DIM
        self.addstr(1, x0, header, attr)

        visible = max(1, h - 4)
        sel = self.selected[i]
        start = 0
        if sel >= visible:
            start = sel - visible + 1

        for row in range(visible):
            j = start + row
            if j >= len(self.items[i]):
                break
            item = self.items[i][j]
            is_dotdot = (item.name == "..")
            is_dir = is_dotdot or item.is_dir()
            name = item.name + ("/" if is_dir else "")
            is_marked = (not is_dotdot) and (
                str(self.panes[i] / item) in self.marked[i]
            )
            mark = "●" if is_marked else " "

            if i == self.active and j == sel:
                attr = self.cp(5, curses.A_BOLD)
            elif is_marked:
                attr = self.cp(6, curses.A_BOLD)
            else:
                attr = self._file_attr(item)

            prefix = ">" if j == sel else " "
            self.addstr(2 + row, x0, f"{prefix}{mark} {name}", attr)

    # ==================== ОТРИСОВКА: РЕДАКТОР ====================
    def draw_editor(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        mod = " *" if self.ed_modified else ""
        fname = Path(self.ed_filename).name if self.ed_filename else "(без имени)"
        title = f" M — {fname}{mod} "
        self.addstr(0, 0, title, self.cp(1, curses.A_BOLD))

        visible_h = max(1, h - 3)

        if self.ed_cursor[0] < 0:
            self.ed_cursor[0] = 0
        if self.ed_cursor[0] >= len(self.ed_buffer):
            self.ed_cursor[0] = max(0, len(self.ed_buffer) - 1)
        start = 0
        if self.ed_cursor[0] >= visible_h:
            start = self.ed_cursor[0] - visible_h + 1

        for screen_row in range(visible_h):
            i = start + screen_row
            if i >= len(self.ed_buffer):
                break
            line = self.ed_buffer[i]

            spans = []
            for res in self.hooks.fire_collect(
                "on_draw_line",
                line=line,
                lineno=i,
                filename=self.ed_filename,
                cursor_line=self.ed_cursor[0],
            ):
                if isinstance(res, list):
                    for s in res:
                        if (isinstance(s, (list, tuple)) and len(s) == 3
                                and all(isinstance(x, int) for x in s)):
                            spans.append(tuple(s))

            self._draw_highlighted_line(screen_row + 1, line, spans, w)

        cy, cx = self.ed_cursor
        screen_y = cy - start + 1
        self._set_cursor_visible(True)
        if 0 < screen_y < h - 1:
            line = self.ed_buffer[cy] if cy < len(self.ed_buffer) else ""
            if 0 <= cx < len(line):
                ch = line[cx]
                if self._char_width(ch) == 0 and cx > 0:
                    base_idx = cx - 1
                    while base_idx > 0 and self._char_width(line[base_idx]) == 0:
                        base_idx -= 1
                    base = line[base_idx]
                    base_vcol = self._visual_col(line, base_idx)
                    try:
                        self.stdscr.addstr(screen_y, base_vcol, base,
                                           curses.A_REVERSE | curses.A_BOLD)
                    except Exception:
                        pass
                    self.move_cursor(screen_y, min(base_vcol, w - 2))
                else:
                    vcol = self._visual_col(line, cx)
                    ch_w = max(1, self._char_width(ch))
                    display_ch = " " if ch == "\t" else ch
                    if vcol + ch_w <= w - 1:
                        try:
                            self.stdscr.addstr(screen_y, vcol, display_ch,
                                               curses.A_REVERSE | curses.A_BOLD)
                        except Exception:
                            pass
                        self.move_cursor(screen_y, min(vcol, w - 2))
                    else:
                        try:
                            self.stdscr.addstr(screen_y, min(vcol, w - 2), " ",
                                               curses.A_REVERSE)
                        except Exception:
                            pass
                        self.move_cursor(screen_y, min(vcol, w - 2))
            else:
                vcol = self._visual_col(line, cx)
                try:
                    self.stdscr.addstr(screen_y, min(vcol, w - 2), " ",
                                       curses.A_REVERSE)
                except Exception:
                    pass
                self.move_cursor(screen_y, min(vcol, w - 2))

        status = " ^S:сохр ^O:откр ^Z:undo ^Y:redo ^F:поиск ^G:next ^W:слово ^R:замена ^X:выход ^P:справка "

        if self.prompt_active:
            line = f" {self.prompt_text}{self.prompt_input}"
            self.addstr(h - 2, 0, line, self.cp(3, curses.A_BOLD))
            vcol = self._visual_col(line, len(line))
            self.move_cursor(h - 2, min(vcol, w - 2))
            if self.message:
                self.addstr(h - 1, 0, self.message, self.cp(4, curses.A_BOLD))
            else:
                self.addstr(h - 1, 0, status, self.cp(3))
        else:
            self.addstr(h - 1, 0, status, self.cp(3))
            if self.message:
                self.addstr(h - 2, 0, self.message, self.cp(4))

        self.stdscr.refresh()

    def _draw_highlighted_line(self, y, line, spans, w):
        if not spans:
            self.addstr(y, 0, line, curses.A_NORMAL)
            return

        pad_cp = None
        normal_spans = []
        for s, e, cp in spans:
            if e == -1:
                pad_cp = cp
            else:
                normal_spans.append((s, e, cp))

        if pad_cp is not None:
            try:
                attr = curses.color_pair(pad_cp)
            except Exception:
                attr = curses.A_NORMAL
            total = max(0, w - 1)
            vis = []
            col = 0
            for ch in line:
                if ch == '\t':
                    nxt = ((col // TABSTOP) + 1) * TABSTOP
                else:
                    nxt = col + M._char_width(ch)
                if nxt > total:
                    break
                vis.append(ch)
                col = nxt
            pad = ' ' * max(0, total - col)
            text = ''.join(vis) + pad
            try:
                self.stdscr.addstr(y, 0, text, attr)
            except Exception:
                pass

        spans = sorted(normal_spans, key=lambda s: (s[0], -s[1]))
        cleaned = []
        last_end = 0
        for s, e, cp in spans:
            if s < 0:
                s = 0
            if e > len(line):
                e = len(line)
            if e <= last_end:
                continue
            if s < last_end:
                s = last_end
            if s >= e:
                continue
            cleaned.append((s, e, cp))
            last_end = e

        plain = line.isascii() and '\t' not in line

        def col(idx):
            return idx if plain else self._visual_col(line, idx)

        pos = 0
        for s, e, cp in cleaned:
            if s > pos and pad_cp is None:
                self.addstr(y, col(pos), line[pos:s], curses.A_NORMAL)
            try:
                attr = curses.color_pair(cp)
            except Exception:
                attr = curses.A_NORMAL
            self.addstr(y, col(s), line[s:e], attr)
            pos = e
        if pos < len(line) and pad_cp is None:
            self.addstr(y, col(pos), line[pos:], curses.A_NORMAL)

    # ==================== СПРАВКА ====================
    def draw_help(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        lines = [
            "  M v6.1 — универсальный инструмент Termux  ",
            "",
            "  ФЛАГИ:  M -e [FILE] | -m NAME | -i SRC DST | -c SRC DST | -h | -v",
            "",
            "  ФАЙЛЫ:",
            "    Tab          переключить панель",
            "    j/k/↑/↓      навигация",
            "    Enter        войти / открыть",
            "    m  n         папка / файл (n — next при поиске)",
            "    i  c         переместить / копировать",
            "    r  d         переименовать / в корзину",
            "    Space        отметить файл",
            "    e            редактор",
            "    u  U         undo / redo",
            "    /  n  N      поиск / след. / пред.",
            "    Esc          сбросить поиск",
            "    .            скрытые файлы",
            "    b  B         закладка / список",
            "    R            корзина",
            "    t  T         новая / закрыть вкладку",
            "    1..9         переключить вкладку",
            "    D            дашборд",
            "    x            хуки",
            "    ?            справка",
            "    q            выход",
            "",
            "  РЕДАКТОР: F1 или Ctrl+P внутри редактора",
            "",
            "  ХУКИ:",
            "    ~/.m/hooks/*.py  с EVENTS = {событие: функция}",
            "    События: on_start on_open on_file_change on_save",
            "             on_create on_move on_delete on_draw_line",
            "",
            "  Нажми любую клавишу…",
        ]
        for i, line in enumerate(lines):
            if i >= h:
                break
            attr = curses.A_BOLD if line and not line.startswith("    ") and line.strip() else curses.A_NORMAL
            self.addstr(i, 0, line, attr)
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            self._get_key()
        except Exception:
            pass
        self.mode = self.return_mode

    def draw_help_editor(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        lines = [
            "  M — Справка редактора  ",
            "",
            "  ВЫХОД И ФАЙЛЫ:",
            "    Ctrl+S       сохранить (создаёт файл, если его нет)",
            "    Ctrl+O       открыть другой файл (спросит про несохранённое)",
            "    Ctrl+X       выйти (спросит про несохранённое)",
            "    F1 или ^P    эта справка",
            "",
            "  РЕДАКТИРОВАНИЕ:",
            "    Стрелки, Home/End, Enter, Backspace, Delete",
            "    Tab          вставка отступа (4 пробела или \\t для .go/.c)",
            "    Ctrl+Z       undo (группирует непрерывный ввод)",
            "    Ctrl+Y       redo",
            "    Ctrl+F       поиск",
            "    Ctrl+G       следующее совпадение (после Ctrl+F)",
            "    Ctrl+W       поиск слова под курсором",
            "    Ctrl+R       замена (формат: старый|новый)",
            "",
            "  Нажми любую клавишу…",
        ]
        for i, line in enumerate(lines):
            if i >= h:
                break
            attr = curses.A_BOLD if line and not line.startswith("    ") and line.strip() else curses.A_NORMAL
            self.addstr(i, 0, line, attr)
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            self._get_key()
        except Exception:
            pass
        self.mode = self.MODE_EDITOR

    # ==================== ХУКИ ====================
    def draw_hooks(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        self.addstr(0, 0, " M — Менеджер хуков ", self.cp(1, curses.A_BOLD))
        y = 2
        self.addstr(y, 0, f" Директория: {HOOKS_DIR}")
        y += 2
        if self.hooks.loaded:
            self.addstr(y, 0, " Загружены:", curses.A_BOLD)
            y += 1
            for name in self.hooks.loaded:
                if y >= h - 4:
                    break
                self.addstr(y, 0, f"   • {name}", self.cp(2))
                y += 1
        else:
            self.addstr(y, 0, " Хуков нет.", curses.A_DIM)
            y += 2
        if self.hooks.errors:
            self.addstr(y, 0, " Ошибки:", curses.A_BOLD)
            y += 1
            for err in self.hooks.errors[:8]:
                if y >= h - 3:
                    break
                self.addstr(y, 0, f"   ! {err[:w-6]}", self.cp(4))
                y += 1
        self.addstr(h - 2, 0, " R:перезагрузить  любая:назад ", self.cp(3))
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k in (ord('r'), ord('R')):
            self.hooks.reload()
            self.set_message("Хуки перезагружены.")
        self.mode = self.MODE_FILES

    # ==================== ДАШБОРД ====================
    def draw_dashboard(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        self.addstr(0, 0, " M — Дашборд ", self.cp(1, curses.A_BOLD))

        lines = []
        try:
            base = Path("/sys/class/power_supply")
            if base.exists():
                for d in sorted(base.iterdir()):
                    cap = d / "capacity"
                    status = d / "status"
                    if cap.exists():
                        s = status.read_text().strip() if status.exists() else "?"
                        lines.append(f"  Батарея {d.name}: {cap.read_text().strip()}% ({s})")
        except Exception:
            pass
        try:
            mem = {}
            with open("/proc/meminfo") as f:
                for line in f:
                    k, _, v = line.partition(":")
                    mem[k.strip()] = int(v.split()[0])
            total = mem.get("MemTotal", 0) // 1024
            avail = mem.get("MemAvailable", 0) // 1024
            if total:
                lines.append(f"  Память: {total - avail} / {total} MB")
        except Exception:
            pass
        try:
            st = os.statvfs(str(HOME))
            total = st.f_blocks * st.f_frsize // (1024 * 1024)
            free = st.f_bavail * st.f_frsize // (1024 * 1024)
            lines.append(f"  Диск: {total - free} / {total} MB")
        except Exception:
            pass
        try:
            for p in sorted(Path("/sys/class/thermal").glob("thermal_zone*")):
                tfile = p / "temp"
                if tfile.exists():
                    try:
                        t = int(tfile.read_text().strip()) / 1000.0
                        if 0 < t < 200:
                            lines.append(f"  {p.name}: {t:.1f}°C")
                    except Exception:
                        pass
                if len(lines) > 15:
                    break
        except Exception:
            pass
        try:
            if shutil.which("termux-wifi-connectioninfo"):
                result = subprocess.run(
                    ["termux-wifi-connectioninfo"],
                    capture_output=True, text=True, timeout=3
                )
                if result.returncode == 0:
                    data = json.loads(result.stdout)
                    ip = data.get("ip", "?")
                    if ip and ip != "0.0.0.0":
                        lines.append(f"  Wi-Fi IP: {ip}")
        except Exception:
            pass

        if not lines:
            lines = ["  Системная информация недоступна."]
        for i, line in enumerate(lines):
            if 2 + i >= h - 2:
                break
            self.addstr(2 + i, 0, line)

        self.addstr(h - 1, 0, " Любая клавиша — назад ", self.cp(3))
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            self._get_key()
        except Exception:
            pass
        self.mode = self.MODE_FILES

    # ==================== ЗАКЛАДКИ ====================
    def draw_bookmarks(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        self.addstr(0, 0, " M — Закладки ", self.cp(1, curses.A_BOLD))

        if self.bookmarks:
            self.bm_idx = max(0, min(self.bm_idx, len(self.bookmarks) - 1))
        else:
            self.bm_idx = 0

        if not self.bookmarks:
            self.addstr(2, 0, " Закладок нет. Нажми 'b' в файловом менеджере.",
                        curses.A_DIM)
        else:
            for i, bm in enumerate(self.bookmarks):
                if 2 + i >= h - 2:
                    break
                attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
                self.addstr(2 + i, 0, f"  {i+1}. {bm}", attr)
        self.addstr(h - 2, 0, " ↑/↓:выбор  Enter:перейти  d:удалить  Esc:назад ",
                    self.cp(3))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == 27:
            self.mode = self.MODE_FILES
        elif k == curses.KEY_DOWN and self.bookmarks:
            self.bm_idx = min(len(self.bookmarks) - 1, self.bm_idx + 1)
        elif k == curses.KEY_UP:
            self.bm_idx = max(0, self.bm_idx - 1)
        elif k in (10, 13) and self.bookmarks:
            target = Path(self.bookmarks[self.bm_idx])
            if target.exists():
                self.panes[self.active] = target
                self.selected[self.active] = 0
                self.refresh_pane(self.active)
                self.set_message(f"Переход: {target}")
            else:
                self.set_message("Путь больше не существует.")
            self.mode = self.MODE_FILES
        elif k == ord('d') and self.bookmarks:
            self.bookmarks.pop(self.bm_idx)
            self.save_bookmarks()
            if self.bm_idx >= len(self.bookmarks):
                self.bm_idx = max(0, len(self.bookmarks) - 1)

    # ==================== КОРЗИНА ====================
    def draw_trash(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        self.addstr(0, 0, " M — Корзина ", self.cp(1, curses.A_BOLD))

        items = self._list_trash()
        if items:
            self.bm_idx = max(0, min(self.bm_idx, len(items) - 1))
        else:
            self.bm_idx = 0

        if not items:
            self.addstr(2, 0, " Корзина пуста.", curses.A_DIM)
        else:
            for i, (name, _meta) in enumerate(items):
                if 2 + i >= h - 2:
                    break
                attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
                self.addstr(2 + i, 0, f"  {i+1}. {name}", attr)

        self.addstr(h - 2, 0, " ↑/↓:выбор  r:восст.  d:удалить  C:очистить  Esc:назад ",
                    self.cp(3))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == 27:
            self.mode = self.MODE_FILES
        elif k == curses.KEY_DOWN and items:
            self.bm_idx = min(len(items) - 1, self.bm_idx + 1)
        elif k == curses.KEY_UP:
            self.bm_idx = max(0, self.bm_idx - 1)
        elif k == ord('r') and items and 0 <= self.bm_idx < len(items):
            self._trash_restore(items[self.bm_idx])
        elif k == ord('d') and items and 0 <= self.bm_idx < len(items):
            self._trash_delete_permanent(items[self.bm_idx])
        elif k == ord('C'):
            self._trash_clear()

    def _list_trash(self):
        try:
            if not TRASH_DIR.exists():
                return []
            items = []
            for p in sorted(TRASH_DIR.iterdir()):
                if p.name.startswith('.'):
                    continue
                items.append((p.name, p))
            return items
        except Exception:
            return []

    def _load_trash_meta(self):
        try:
            if TRASH_META.exists():
                data = json.loads(TRASH_META.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
        return {}

    def _save_trash_meta(self, data):
        try:
            TRASH_DIR.mkdir(parents=True, exist_ok=True)
            TRASH_META.write_text(json.dumps(data, indent=2, ensure_ascii=False),
                                  encoding="utf-8")
        except Exception:
            pass

    def _trash_restore(self, item):
        name, path = item
        meta = self._load_trash_meta()
        original = meta.get(name)
        if not original:
            self.set_message("Не найдено оригинального пути.")
            return
        try:
            dst = Path(original)
            dst.parent.mkdir(parents=True, exist_ok=True)
            if dst.exists():
                dst = dst.parent / (dst.name + "_restored")
            shutil.move(str(path), str(dst))
            meta.pop(name, None)
            self._save_trash_meta(meta)
            self.set_message(f"Восстановлено: {dst}")
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def _trash_delete_permanent(self, item):
        name, path = item
        try:
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()
            meta = self._load_trash_meta()
            meta.pop(name, None)
            self._save_trash_meta(meta)
            self.set_message(f"Удалено навсегда: {name}")
            if self.bm_idx > 0:
                self.bm_idx -= 1
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def _trash_clear(self):
        try:
            if TRASH_DIR.exists():
                for p in list(TRASH_DIR.iterdir()):
                    if p.name.startswith('.'):
                        continue
                    if p.is_dir():
                        shutil.rmtree(p)
                    else:
                        p.unlink()
                self._save_trash_meta({})
                self.set_message("Корзина очищена.")
                self.bm_idx = 0
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    # ==================== АРХИВ ====================
    def draw_archive(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        fname = Path(self.archive_path).name if self.archive_path else "?"
        self.addstr(0, 0, f" M — Архив: {fname} ", self.cp(1, curses.A_BOLD))

        if self.archive_items:
            self.bm_idx = max(0, min(self.bm_idx, len(self.archive_items) - 1))
        else:
            self.bm_idx = 0

        for i, name in enumerate(self.archive_items):
            if 2 + i >= h - 2:
                break
            attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
            self.addstr(2 + i, 0, f"  {name[:w-6]}", attr)
        self.addstr(h - 2, 0, " ↑/↓:нав.  x:распаковать всё сюда  Esc:назад ",
                    self.cp(3))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == 27:
            self.mode = self.MODE_FILES
        elif k == curses.KEY_DOWN and self.archive_items:
            self.bm_idx = min(len(self.archive_items) - 1, self.bm_idx + 1)
        elif k == curses.KEY_UP:
            self.bm_idx = max(0, self.bm_idx - 1)
        elif k == ord('x'):
            self._extract_archive()

    def _open_archive(self, path):
        self.archive_path = str(path)
        self.archive_items = []
        self.bm_idx = 0
        try:
            lower = str(path).lower()
            if lower.endswith(".zip"):
                self.archive_kind = "zip"
                with zipfile.ZipFile(path, 'r') as z:
                    self.archive_items = z.namelist()
            elif any(lower.endswith(e) for e in (".tar", ".tar.gz", ".tgz",
                                                  ".tar.bz2", ".tbz2", ".tar.xz")):
                self.archive_kind = "tar"
                with tarfile.open(path, 'r:*') as t:
                    self.archive_items = t.getnames()
            else:
                return False
            self.mode = self.MODE_ARCHIVE
            return True
        except Exception as e:
            self.set_message(f"Ошибка чтения архива: {e}")
            return False

    @staticmethod
    def _is_safe_member(base, name):
        if not name:
            return False
        if name.startswith('/') or name.startswith('\\'):
            return False
        parts = name.replace('\\', '/').split('/')
        if any(p == '..' for p in parts):
            return False
        try:
            target = (base / name).resolve()
            base_r = base.resolve()
            target.relative_to(base_r)
            return True
        except Exception:
            return False

    def _extract_archive(self):
        if not self.archive_path:
            return
        target = self.panes[self.active]
        base = Path(target).resolve()
        extracted = 0
        skipped = 0
        try:
            if self.archive_kind == "zip":
                with zipfile.ZipFile(self.archive_path, 'r') as z:
                    for info in z.infolist():
                        name = info.filename
                        if not self._is_safe_member(base, name):
                            skipped += 1
                            continue
                        try:
                            z.extract(info, str(base))
                            extracted += 1
                        except Exception:
                            skipped += 1
            else:
                with tarfile.open(self.archive_path, 'r:*') as t:
                    for m in t:
                        if m.issym() or m.islnk() or m.isdev():
                            skipped += 1
                            continue
                        if not self._is_safe_member(base, m.name):
                            skipped += 1
                            continue
                        try:
                            try:
                                t.extract(m, str(base), filter='data')
                            except TypeError:
                                t.extract(m, str(base))
                            extracted += 1
                        except Exception:
                            skipped += 1
            msg = f"Распаковано: {extracted}"
            if skipped:
                msg += f" (пропущено: {skipped})"
            self.set_message(msg)
        except Exception as e:
            self.set_message(f"Ошибка распаковки: {e}")
        self.refresh_pane(self.active)
        self.mode = self.MODE_FILES

    # ==================== ГЛАВНЫЙ ЦИКЛ ====================
    def run(self):
        ensure_directories()
        self.hooks.fire("on_start", cwd=str(self.panes[self.active]))
        while self.running:
            try:
                if self.mode == self.MODE_FILES:
                    self.draw_files()
                elif self.mode == self.MODE_EDITOR:
                    self.draw_editor()
                elif self.mode == self.MODE_HELP:
                    self.draw_help()
                    continue
                elif self.mode == self.MODE_HELP_EDITOR:
                    self.draw_help_editor()
                    continue
                elif self.mode == self.MODE_HOOKS:
                    self.draw_hooks()
                    continue
                elif self.mode == self.MODE_DASHBOARD:
                    self.draw_dashboard()
                    continue
                elif self.mode == self.MODE_BOOKMARKS:
                    self.draw_bookmarks()
                    continue
                elif self.mode == self.MODE_TRASH:
                    self.draw_trash()
                    continue
                elif self.mode == self.MODE_ARCHIVE:
                    self.draw_archive()
                    continue
            except curses.error:
                pass
            except Exception as e:
                try:
                    self.set_message(f"Ошибка отрисовки: {e}")
                except Exception:
                    pass

            try:
                key = self._get_key()
            except KeyboardInterrupt:
                break
            except Exception:
                continue

            if key == -1:
                time.sleep(0.02)
                continue

            if self.prompt_active:
                self.handle_prompt_key(key)
                continue

            try:
                if self.mode == self.MODE_FILES:
                    self.handle_files_key(key)
                elif self.mode == self.MODE_EDITOR:
                    self.handle_editor_key(key)
            except Exception as e:
                self.set_message(f"Ошибка: {e}")

        self.save_config()

    # ==================== ПРОМПТ ====================
    def ask(self, text, callback):
        self.prompt_active = True
        self.prompt_text = text
        self.prompt_input = ""
        self.prompt_callback = callback
        self.message = ""

    def handle_prompt_key(self, key):
        if key == 27:
            self.prompt_active = False
            self.prompt_callback = None
            self.set_message("Отменено.")
            return
        if key in (10, 13):
            cb = self.prompt_callback
            val = self.prompt_input
            if cb:
                try:
                    keep_open = cb(val)
                except Exception as e:
                    self.set_message(f"Ошибка: {e}")
                    keep_open = False
                if self.prompt_callback is not cb:
                    return
                if keep_open is True:
                    self.prompt_input = ""
                    return
            self.prompt_active = False
            self.prompt_callback = None
            return
        if key in (curses.KEY_BACKSPACE, 127, 8):
            self.prompt_input = self.prompt_input[:-1]
        elif key == 9:  # Tab
            self.set_message("Tab недоступен в поле ввода.")
        elif isinstance(key, str):
            self.prompt_input += key
        elif isinstance(key, int) and 32 <= key <= 126:
            self.prompt_input += chr(key)

    # ==================== ФАЙЛЫ ====================
    def handle_files_key(self, key):
        idx = self.active

        if key == 9:  # Tab
            self.active = 1 - self.active
            self.fm_hits = []
            self.fm_hit_idx = -1
            self.set_message("")
        elif key in (curses.KEY_UP, ord('k')):
            if self.selected[idx] > 0:
                self.selected[idx] -= 1
        elif key in (curses.KEY_DOWN, ord('j')):
            if self.selected[idx] < len(self.items[idx]) - 1:
                self.selected[idx] += 1
        elif key in (10, 13, curses.KEY_ENTER):
            self.open_item()
        elif key == ord('q'):
            self.running = False
        elif key == 27:
            self.fm_hits = []
            self.fm_hit_idx = -1
            self.set_message("")
        elif key == ord('m'):
            self.ask("Имя новой папки: ", self.do_mkdir)
        elif key == ord('n'):
            if self.fm_hits:
                self.search_next(1)
            else:
                self.ask("Имя нового файла: ", self.do_newfile)
        elif key == ord('N'):
            if self.fm_hits:
                self.search_next(-1)
        elif key == ord('i'):
            self.do_move()
        elif key == ord('c'):
            self.do_copy()
        elif key == ord('r'):
            self.ask("Новое имя: ", self.do_rename)
        elif key == ord('d'):
            self.ask("Удалить в корзину? (y/n): ", self.do_delete)
        elif key == ord('e'):
            self.open_in_editor()
        elif key == ord('u'):
            res = self.undo.undo()
            self.set_message(res or "Нечего отменять.")
            self.refresh_pane(0)
            self.refresh_pane(1)
        elif key == ord('U'):
            res = self.undo.redo()
            self.set_message(res or "Нечего повторять.")
            self.refresh_pane(0)
            self.refresh_pane(1)
        elif key == ord(' '):
            self.toggle_mark()
        elif key == ord('/'):
            self.ask("Поиск: ", self.do_search)
        elif key == ord('.'):
            self.show_hidden = not self.show_hidden
            self.save_config()
            self.refresh_pane(0)
            self.refresh_pane(1)
            self.set_message(f"Скрытые: {'вкл' if self.show_hidden else 'выкл'}")
        elif key == ord('b'):
            self.add_bookmark()
        elif key == ord('B'):
            self.bm_idx = 0
            self.mode = self.MODE_BOOKMARKS
        elif key == ord('R'):
            self.bm_idx = 0
            self.mode = self.MODE_TRASH
        elif key == ord('D'):
            self.mode = self.MODE_DASHBOARD
        elif key == ord('x'):
            self.mode = self.MODE_HOOKS
        elif key == ord('t'):
            self.new_tab()
        elif key == ord('T'):
            self.close_tab()
        elif isinstance(key, int) and ord('1') <= key <= ord('9'):
            ti = key - ord('1')
            if ti < len(self.tabs):
                self.switch_tab(ti)
        elif key == ord('?'):
            self.return_mode = self.MODE_FILES
            self.mode = self.MODE_HELP
        elif key == curses.KEY_RESIZE:
            self.refresh_pane(0)
            self.refresh_pane(1)

    def open_item(self):
        item = self.current_item()
        if item is None:
            return
        if item.name == "..":
            self.panes[self.active] = self.panes[self.active].parent
            self.selected[self.active] = 0
            self.fm_hits = []
            self.fm_hit_idx = -1
            self.refresh_pane(self.active)
            self.hooks.fire("on_open", path=str(self.panes[self.active]), kind="dir")
            return
        full = self.panes[self.active] / item
        if full.is_dir():
            self.panes[self.active] = full
            self.selected[self.active] = 0
            self.fm_hits = []
            self.fm_hit_idx = -1
            self.refresh_pane(self.active)
            self.hooks.fire("on_open", path=str(full), kind="dir")
            return

        lower = full.name.lower()
        if any(lower.endswith(e) for e in ARCHIVE_EXTS):
            if self._open_archive(full):
                self.hooks.fire("on_open", path=str(full), kind="archive")
            return
        elif any(lower.endswith(e) for e in ARCHIVE_EXTS_SET):
            self.set_message(
                f"{full.suffix} не поддерживается — нужен внешний распаковщик."
            )
            return

        self.open_in_editor()

    def open_in_editor(self):
        item = self.current_item()
        if item is None or item.name == "..":
            return
        full = self.panes[self.active] / item
        if full.is_dir():
            self.set_message("Это папка.")
            return
        self.editor_open_file(str(full))
        self.mode = self.MODE_EDITOR

    # ==================== ФАЙЛОВЫЕ ОПЕРАЦИИ ====================
    def do_mkdir(self, name):
        name = name.strip()
        if not name:
            self.set_message("Отменено (пустое имя).")
            return
        try:
            p = self.panes[self.active] / name
            p.mkdir(parents=True, exist_ok=True)
            self.set_message(f"Папка '{name}' создана. (u — отменить)")
            self.refresh_pane(self.active)
            self.hooks.fire("on_create", path=str(p), kind="dir")

            def undo():
                if p.exists() and p.is_dir() and not any(p.iterdir()):
                    p.rmdir()
                else:
                    raise OSError("папка не пуста или не существует")

            def redo():
                p.mkdir(parents=True, exist_ok=True)

            self.undo.push(f"создание папки '{name}'", undo, redo)
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def do_newfile(self, name):
        name = name.strip()
        if not name:
            self.set_message("Отменено (пустое имя).")
            return
        try:
            p = self.panes[self.active] / name
            if p.exists():
                self.set_message("Файл уже существует.")
                return
            p.touch()
            self.set_message(f"Файл '{name}' создан. (u — отменить)")
            self.refresh_pane(self.active)
            self.hooks.fire("on_create", path=str(p), kind="file")

            def undo():
                if p.exists() and p.is_file():
                    p.unlink()
                else:
                    raise OSError("файл не найден")

            def redo():
                p.touch(exist_ok=True)

            self.undo.push(f"создание файла '{name}'", undo, redo)
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def do_rename(self, newname):
        newname = newname.strip()
        if not newname:
            self.set_message("Отменено (пустое имя).")
            return
        item = self.current_item()
        if item is None or item.name == "..":
            return
        if newname == item.name:
            self.set_message("Имя не изменилось.")
            return
        src = self.panes[self.active] / item
        dst = self.panes[self.active] / newname
        if dst.exists():
            self.set_message("Цель уже существует.")
            return
        try:
            src.rename(dst)
            self.set_message(f"Переименовано: {item.name} → {newname}")
            self.refresh_pane(self.active)
            self.hooks.fire("on_move", src=str(src), dst=str(dst))

            def undo():
                if dst.exists() and not src.exists():
                    dst.rename(src)
                else:
                    raise OSError("невозможно откатить")

            def redo():
                if src.exists() and not dst.exists():
                    src.rename(dst)
                else:
                    raise OSError("невозможно повторить")

            self.undo.push(f"переименование '{item.name}' → '{newname}'", undo, redo)
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def do_delete(self, answer):
        if answer.strip().lower() not in ("y", "yes", "д", "да"):
            self.set_message("Отменено.")
            return
        item = self.current_item()
        if item is None or item.name == "..":
            return
        src = self.panes[self.active] / item
        try:
            TRASH_DIR.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.set_message(f"Ошибка создания корзины: {e}")
            return
        ts = int(time.time() * 1000)
        trashed = TRASH_DIR / f"{ts}_{item.name}"
        state = {"trashed": trashed}

        try:
            shutil.move(str(src), str(trashed))
        except Exception as e:
            self.set_message(f"Ошибка: {e}")
            return

        meta = self._load_trash_meta()
        meta[trashed.name] = str(src)
        self._save_trash_meta(meta)

        self.set_message(f"Удалено: {item.name} (u — отменить)")
        self.refresh_pane(self.active)
        self.hooks.fire("on_delete", path=str(src))

        def undo():
            t = state["trashed"]
            if not t.exists():
                raise FileNotFoundError("файл уже удалён из корзины")
            if src.exists():
                raise FileExistsError(f"'{src.name}' уже существует")
            shutil.move(str(t), str(src))
            m = self._load_trash_meta()
            m.pop(t.name, None)
            self._save_trash_meta(m)

        def redo():
            if not src.exists():
                raise FileNotFoundError("исходный файл отсутствует")
            new_ts = int(time.time() * 1000)
            new_path = TRASH_DIR / f"{new_ts}_{src.name}"
            shutil.move(str(src), str(new_path))
            m = self._load_trash_meta()
            m[new_path.name] = str(src)
            self._save_trash_meta(m)
            state["trashed"] = new_path

        self.undo.push(f"удаление '{item.name}'", undo, redo)

    def _get_operation_sources(self):
        if self.marked[self.active]:
            return [Path(p) for p in self.marked[self.active]]
        item = self.current_item()
        if item is None or item.name == "..":
            return []
        return [self.panes[self.active] / item]

    def do_move(self):
        sources = self._get_operation_sources()
        if not sources:
            return
        dst_dir = self.panes[1 - self.active]
        failed = []
        success = 0
        last_error = ""

        for src in sources:
            dst = dst_dir / src.name
            if dst.exists():
                last_error = f"Пропущено (существует): {src.name}"
                failed.append(src)
                continue
            try:
                shutil.move(str(src), str(dst))
                self.hooks.fire("on_move", src=str(src), dst=str(dst))
                self._register_move_undo(src, dst)
                success += 1
            except Exception as e:
                last_error = f"Ошибка: {e}"
                failed.append(src)

        if failed:
            self.marked[self.active] = set(str(p) for p in failed)
            self.set_message(last_error or "Некоторые файлы не перемещены.")
        else:
            self.marked[self.active].clear()
            self.set_message(f"Перемещено: {success}. (u — отменить)")
        self.refresh_pane(0)
        self.refresh_pane(1)

    def _register_move_undo(self, src, dst):
        def undo():
            if dst.exists() and not src.exists():
                shutil.move(str(dst), str(src))
            else:
                raise OSError("невозможно откатить")

        def redo():
            if src.exists() and not dst.exists():
                shutil.move(str(src), str(dst))
            else:
                raise OSError("невозможно повторить")

        self.undo.push(f"перемещение '{src.name}'", undo, redo)

    def do_copy(self):
        sources = self._get_operation_sources()
        if not sources:
            return
        dst_dir = self.panes[1 - self.active]
        failed = []
        success = 0
        last_error = ""

        for src in sources:
            dst = dst_dir / src.name
            if dst.exists():
                last_error = f"Пропущено (существует): {src.name}"
                failed.append(src)
                continue
            try:
                if src.is_dir():
                    shutil.copytree(src, dst)
                else:
                    shutil.copy2(src, dst)
                self.hooks.fire("on_create", path=str(dst), kind="copy")
                self._register_copy_undo(src, dst)
                success += 1
            except Exception as e:
                last_error = f"Ошибка: {e}"
                failed.append(src)

        if failed:
            self.marked[self.active] = set(str(p) for p in failed)
            self.set_message(last_error or "Некоторые файлы не скопированы.")
        else:
            self.marked[self.active].clear()
            self.set_message(f"Скопировано: {success}. (u — отменить)")
        self.refresh_pane(0)
        self.refresh_pane(1)

    def _register_copy_undo(self, src, dst):
        def undo():
            if not dst.exists():
                raise FileNotFoundError("копия уже удалена")
            if dst.is_dir():
                shutil.rmtree(dst)
            else:
                dst.unlink()

        def redo():
            if dst.exists():
                raise FileExistsError("цель уже существует")
            if src.is_dir():
                shutil.copytree(src, dst)
            else:
                shutil.copy2(src, dst)

        self.undo.push(f"копирование '{src.name}'", undo, redo)

    def toggle_mark(self):
        item = self.current_item()
        if item is None or item.name == "..":
            return
        full = str(self.panes[self.active] / item)
        if full in self.marked[self.active]:
            self.marked[self.active].discard(full)
        else:
            self.marked[self.active].add(full)
        if self.selected[self.active] < len(self.items[self.active]) - 1:
            self.selected[self.active] += 1

    def do_search(self, query):
        query = query.strip()
        if not query:
            return
        q_lower = query.lower()
        self.fm_hits = []
        for i, item in enumerate(self.items[self.active]):
            if q_lower in item.name.lower():
                self.fm_hits.append(i)
        if self.fm_hits:
            self.fm_hit_idx = 0
            self.selected[self.active] = self.fm_hits[0]
            self.set_message(f"Найдено: {len(self.fm_hits)} (n/N)")
        else:
            self.fm_hit_idx = -1
            self.set_message("Не найдено.")

    def search_next(self, direction):
        if not self.fm_hits:
            return
        if self.fm_hit_idx < 0:
            self.fm_hit_idx = 0
        else:
            self.fm_hit_idx = (self.fm_hit_idx + direction) % len(self.fm_hits)
        self.selected[self.active] = self.fm_hits[self.fm_hit_idx]

    def add_bookmark(self):
        current = str(self.panes[self.active])
        if current in self.bookmarks:
            self.bookmarks.remove(current)
            self.set_message("Закладка удалена.")
        else:
            self.bookmarks.append(current)
            self.set_message(f"Закладка: {current}")
        self.save_bookmarks()

    # ==================== ВКЛАДКИ ====================
    def _save_tab_state(self):
        self.tabs[self.active_tab]["panes"] = list(self.panes)
        self.tabs[self.active_tab]["selected"] = list(self.selected)
        self.tabs[self.active_tab]["active"] = self.active

    def switch_tab(self, idx):
        if idx == self.active_tab or idx < 0 or idx >= len(self.tabs):
            return
        self._save_tab_state()
        self.active_tab = idx
        tab = self.tabs[idx]
        self.panes = list(tab["panes"])
        self.selected = list(tab["selected"])
        self.active = tab["active"]
        self.marked = [set(), set()]
        self.fm_hits = []
        self.fm_hit_idx = -1
        self.refresh_pane(0)
        self.refresh_pane(1)
        self.set_message(f"Вкладка {idx + 1}")

    def new_tab(self):
        self._save_tab_state()
        cwd = Path.cwd()
        self.tabs.append({
            "panes": [cwd, cwd],
            "selected": [0, 0],
            "active": 0,
        })
        self.active_tab = len(self.tabs) - 1
        self.panes = [cwd, cwd]
        self.selected = [0, 0]
        self.active = 0
        self.marked = [set(), set()]
        self.fm_hits = []
        self.fm_hit_idx = -1
        self.refresh_pane(0)
        self.refresh_pane(1)
        self.set_message(f"Вкладка {self.active_tab + 1}")

    def close_tab(self):
        if len(self.tabs) <= 1:
            self.set_message("Нельзя закрыть последнюю вкладку.")
            return
        self.tabs.pop(self.active_tab)
        self.active_tab = min(self.active_tab, len(self.tabs) - 1)
        tab = self.tabs[self.active_tab]
        self.panes = list(tab["panes"])
        self.selected = list(tab["selected"])
        self.active = tab["active"]
        self.marked = [set(), set()]
        self.fm_hits = []
        self.fm_hit_idx = -1
        self.refresh_pane(0)
        self.refresh_pane(1)
        self.set_message("Вкладка закрыта.")

    # ==================== РЕДАКТОР ====================
    def _snapshot(self):
        return (list(self.ed_buffer), list(self.ed_cursor), self.ed_modified)

    def _push_undo(self):
        """Безусловный push + сброс группы. Для явных операций
        (замена, undo, redo и т.п.): после такой операции следующая
        правка всегда начинает новую группу."""
        self.ed_undo_stack.append(self._snapshot())
        self.ed_redo_stack.clear()
        self._reset_undo_group()

    def _push_undo_for_edit(self, kind):
        """Push с группировкой. kind ∈ {"insert", "delete", "other"}.
        Непрерывный ввод одного типа в пределах UNDO_GROUP_WINDOW
        не создаёт новый snapshot."""
        now = time.monotonic()
        continuous = (
            kind in ("insert", "delete")
            and kind == self._last_edit_kind
            and (now - self._last_edit_time) < self.UNDO_GROUP_WINDOW
        )
        if not continuous:
            self.ed_undo_stack.append(self._snapshot())
            self.ed_redo_stack.clear()
        self._last_edit_time = now
        self._last_edit_kind = kind

    def _reset_undo_group(self):
        self._last_edit_time = 0.0
        self._last_edit_kind = None

    def editor_undo(self):
        if self.ed_undo_stack:
            self.ed_redo_stack.append(self._snapshot())
            buf, cur, mod = self.ed_undo_stack.pop()
            self.ed_buffer = list(buf)
            self.ed_cursor = list(cur)
            self.ed_modified = mod
            self._reset_undo_group()   # следующая правка — новая группа
            self.set_message("Отменено.")
        else:
            self.set_message("Нечего отменять.")

    def editor_redo(self):
        if self.ed_redo_stack:
            self.ed_undo_stack.append(self._snapshot())
            buf, cur, mod = self.ed_redo_stack.pop()
            self.ed_buffer = list(buf)
            self.ed_cursor = list(cur)
            self.ed_modified = mod
            self._reset_undo_group()
            self.set_message("Повторено.")
        else:
            self.set_message("Нечего повторять.")

    def save_editor(self):
        if not self.ed_filename:
            self.set_message("Нет имени файла. Используйте Ctrl+O.")
            return False
        try:
            p = Path(self.ed_filename)
            if not p.parent.exists():
                p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("\n".join(self.ed_buffer), encoding='utf-8')
            self.ed_modified = False
            self._reset_undo_group()
            self.set_message(f"Сохранено: {p.name}")
            self.hooks.fire("on_save", path=str(p))
            return True
        except Exception as e:
            self.set_message(f"Ошибка сохранения: {e}")
            return False

    def clamp_cursor(self):
        cy, cx = self.ed_cursor
        if not self.ed_buffer:
            self.ed_buffer = [""]
        cy = max(0, min(cy, len(self.ed_buffer) - 1))
        line_len = len(self.ed_buffer[cy])
        cx = max(0, min(cx, line_len))
        self.ed_cursor = [cy, cx]

    def handle_editor_key(self, key):
        if key == curses.KEY_F1 or key == 16:
            self.mode = self.MODE_HELP_EDITOR
            return
        if key == curses.KEY_RESIZE:
            return

        if key == 24:  # Ctrl+X
            if self.ed_modified:
                self.ask("Сохранить перед выходом? (y — сохранить, n — не сохранять, Esc — отмена): ",
                         self._editor_exit)
                return
            self.mode = self.MODE_FILES
            self.set_message("")
            return

        if key == 19:  # Ctrl+S
            self.save_editor()
            return

        if key == 15:  # Ctrl+O
            if self.ed_modified:
                self.ask("Несохранённые изменения. Сохранить перед открытием? (y/n): ",
                         self._editor_open_confirm)
                return
            self.ask("Открыть файл: ", self.editor_open_file)
            return

        if key == 26:  # Ctrl+Z
            self.editor_undo()
            return

        if key == 25:  # Ctrl+Y
            self.editor_redo()
            return

        if key == 6:  # Ctrl+F
            self.ask("Поиск: ", self.editor_search)
            return

        if key == 7:  # Ctrl+G
            self._editor_search_next(1)
            return

        if key == 23:  # Ctrl+W
            self._editor_search_word_under_cursor()
            return

        if key == 18:  # Ctrl+R
            self.ask("Найти и заменить (формат: старый|новый): ",
                     self.editor_replace)
            return

        # Определяем вид правки для группировки undo
        edit_kind = None
        if isinstance(key, str):
            edit_kind = "insert"
        elif isinstance(key, int) and 32 <= key <= 126:
            edit_kind = "insert"
        elif key in (curses.KEY_BACKSPACE, 127, 8, curses.KEY_DC):
            edit_kind = "delete"
        elif key in (10, 13, 9):   # Enter, Tab
            edit_kind = "other"

        if edit_kind is not None:
            self._push_undo_for_edit(edit_kind)
            self.editor_edit(key, arrows=True)
            self.clamp_cursor()
        else:
            # Стрелки, Home/End и прочее — движение курсора разрывает
            # undo-группу: следующая правка начнёт новый snapshot.
            self._reset_undo_group()
            self.editor_edit(key, arrows=True)
            self.clamp_cursor()

    def _editor_open_confirm(self, ans):
        ans = ans.strip().lower()
        if ans in ("y", "yes", "д", "да"):
            if self.ed_filename:
                if not self.save_editor():
                    return
            self.ask("Открыть файл: ", self.editor_open_file)
            return
        if ans in ("n", "no", "н", "нет"):
            self.ask("Открыть файл: ", self.editor_open_file)
            return
        self.set_message("Введите y (сохранить) или n (не сохранять).")
        return True

    def _editor_exit(self, ans):
        ans = ans.strip().lower()
        if ans in ("y", "yes", "д", "да"):
            if self.ed_filename:
                if not self.save_editor():
                    return
            self.ed_modified = False
            self.mode = self.MODE_FILES
            self.set_message("")
            return
        if ans in ("n", "no", "н", "нет"):
            self.ed_modified = False
            self.mode = self.MODE_FILES
            self.set_message("Выход без сохранения.")
            return
        self.set_message("Введите y (сохранить) или n (не сохранять).")
        return True

    def editor_edit(self, key, arrows=False):
        cy, cx = self.ed_cursor
        cy = max(0, min(cy, len(self.ed_buffer) - 1))
        cx = max(0, min(cx, len(self.ed_buffer[cy])))
        self.ed_cursor = [cy, cx]

        if arrows:
            if key == curses.KEY_UP and cy > 0:
                self.ed_cursor[0] -= 1
                self.clamp_cursor()
                return
            if key == curses.KEY_DOWN and cy < len(self.ed_buffer) - 1:
                self.ed_cursor[0] += 1
                self.clamp_cursor()
                return
            if key == curses.KEY_LEFT and cx > 0:
                self.ed_cursor[1] -= 1
                return
            if key == curses.KEY_RIGHT and cx < len(self.ed_buffer[cy]):
                self.ed_cursor[1] += 1
                return
            if key == curses.KEY_HOME:
                self.ed_cursor[1] = 0
                return
            if key == curses.KEY_END:
                self.ed_cursor[1] = len(self.ed_buffer[cy])
                return

        if key in (10, 13):
            line = self.ed_buffer[cy]
            self.ed_buffer[cy] = line[:cx]
            self.ed_buffer.insert(cy + 1, line[cx:])
            self.ed_cursor = [cy + 1, 0]
            self.ed_modified = True
        elif key == 9:  # Tab
            line = self.ed_buffer[cy]
            ext = Path(self.ed_filename).suffix.lower() if self.ed_filename else ""
            insert = "\t" if ext in (".go", ".c", ".h", ".cpp", ".hpp") else "    "
            self.ed_buffer[cy] = line[:cx] + insert + line[cx:]
            self.ed_cursor[1] += len(insert)
            self.ed_modified = True
        elif key in (curses.KEY_BACKSPACE, 127, 8):
            if cx > 0:
                line = self.ed_buffer[cy]
                self.ed_buffer[cy] = line[:cx - 1] + line[cx:]
                self.ed_cursor[1] -= 1
                self.ed_modified = True
            elif cy > 0:
                prev_len = len(self.ed_buffer[cy - 1])
                self.ed_buffer[cy - 1] += self.ed_buffer[cy]
                del self.ed_buffer[cy]
                self.ed_cursor = [cy - 1, prev_len]
                self.ed_modified = True
        elif key == curses.KEY_DC:
            line = self.ed_buffer[cy]
            if cx < len(line):
                self.ed_buffer[cy] = line[:cx] + line[cx + 1:]
                self.ed_modified = True
            elif cy < len(self.ed_buffer) - 1:
                self.ed_buffer[cy] += self.ed_buffer[cy + 1]
                del self.ed_buffer[cy + 1]
                self.ed_modified = True
        elif isinstance(key, str):
            line = self.ed_buffer[cy]
            self.ed_buffer[cy] = line[:cx] + key + line[cx:]
            self.ed_cursor[1] += len(key)
            self.ed_modified = True
        elif isinstance(key, int) and 32 <= key <= 126:
            line = self.ed_buffer[cy]
            self.ed_buffer[cy] = line[:cx] + chr(key) + line[cx:]
            self.ed_cursor[1] += 1
            self.ed_modified = True

    def editor_search(self, query):
        query = query.strip()
        if not query:
            return
        self.ed_search_hits = []
        for i, line in enumerate(self.ed_buffer):
            if query in line:
                self.ed_search_hits.append(i)
        if self.ed_search_hits:
            self.ed_search_idx = 0
            self.ed_cursor[0] = self.ed_search_hits[0]
            self.clamp_cursor()
            self.set_message(f"Найдено строк: {len(self.ed_search_hits)} (Ctrl+G — след.)")
        else:
            self.ed_search_idx = -1
            self.set_message("Не найдено.")

    def _editor_search_next(self, direction):
        if not self.ed_search_hits:
            self.set_message("Сначала выполните поиск (Ctrl+F).")
            return
        if self.ed_search_idx < 0:
            self.ed_search_idx = 0
        else:
            self.ed_search_idx = (self.ed_search_idx + direction) % len(self.ed_search_hits)
        self.ed_cursor[0] = self.ed_search_hits[self.ed_search_idx]
        self.clamp_cursor()
        self.set_message(f"Совпадение {self.ed_search_idx + 1} из {len(self.ed_search_hits)}")

    def _editor_search_word_under_cursor(self):
        cy, cx = self.ed_cursor
        if cy >= len(self.ed_buffer):
            return
        line = self.ed_buffer[cy]
        if not line:
            self.set_message("Пустая строка.")
            return
        cx = min(cx, len(line) - 1)
        if not (line[cx].isalnum() or line[cx] == '_'):
            self.set_message("Курсор не на слове.")
            return
        start = cx
        while start > 0 and (line[start - 1].isalnum() or line[start - 1] == '_'):
            start -= 1
        end = cx
        while end < len(line) - 1 and (line[end + 1].isalnum() or line[end + 1] == '_'):
            end += 1
        word = line[start:end + 1]
        if word:
            self.editor_search(word)

    def editor_replace(self, query):
        if "|" not in query:
            self.set_message("Формат: старый|новый")
            return
        old, new = query.split("|", 1)
        if not old:
            self.set_message("Пустая строка поиска.")
            return
        found = any(old in line for line in self.ed_buffer)
        if not found:
            self.set_message("Не найдено.")
            return
        # Явная операция — push + reset (уже внутри _push_undo)
        self._push_undo()
        count = 0
        for i, line in enumerate(self.ed_buffer):
            if old in line:
                count += line.count(old)
                self.ed_buffer[i] = line.replace(old, new)
        self.ed_modified = True
        self.set_message(f"Заменено вхождений: {count} (Ctrl+Z — отменить)")

    def editor_open_file(self, path):
        if not path or not path.strip():
            return
        try:
            p = Path(path).expanduser()
            if p.is_dir():
                self.set_message("Это папка, а не файл.")
                return
            if p.exists():
                text = p.read_text(encoding='utf-8', errors='replace')
                self.ed_buffer = text.splitlines() or [""]
                self.set_message(f"Открыт: {p.name}")
            else:
                self.ed_buffer = [""]
                self.set_message(f"Новый файл: {p.name} (Ctrl+S — сохранить)")
                self.hooks.fire("on_create", path=str(p), kind="file-pending")
                if p.exists():
                    try:
                        text = p.read_text(encoding='utf-8', errors='replace')
                        self.ed_buffer = text.splitlines() or [""]
                    except Exception:
                        pass
            self.ed_filename = str(p)
            self.ed_cursor = [0, 0]
            self.ed_modified = False
            self.ed_undo_stack.clear()
            self.ed_redo_stack.clear()
            self.ed_search_hits = []
            self.ed_search_idx = -1
            self._reset_undo_group()
            self.hooks.fire("on_file_change", path=str(p))
            self.hooks.fire("on_open", path=str(p), kind="file")
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    # ==================== ФЛАГИ КОМАНДНОЙ СТРОКИ ====================
    def apply_flags(self, args):
        """Обрабатывает только -e/--edit. Остальные CLI-флаги
        (-h/-m/-i/-c/-v) перехватываются в main() до curses.wrapper."""
        flag = args[0]
        if flag in ("-e", "--edit"):
            if len(args) > 1:
                self.editor_open_file(args[1])
            else:
                cwd = Path.cwd()
                self.editor_open_file(str(cwd / "untitled.txt"))
            self.mode = self.MODE_EDITOR


# ============================ ТОЧКА ВХОДА ============================
def _run_curses(stdscr):
    try:
        curses.curs_set(1)
    except Exception:
        pass
    try:
        curses.set_escdelay(25)
    except Exception:
        pass
    try:
        stdscr.keypad(True)
    except Exception:
        pass

    m = M(stdscr)
    args = sys.argv[1:]
    if args:
        m.apply_flags(args)
    m.run()


def _print_cli_help():
    print("""M — универсальный инструмент Termux.

Использование:
  M                файловый менеджер
  M -e [FILE]      редактор (FILE — необязательно)
  M -m NAME        создать папку
  M -i SRC DST     переместить файл/папку
  M -c SRC DST     скопировать файл/папку
  M -h, --help     эта справка
  M -v, --version  версия

Горячие клавиши внутри M — нажми '?' в файловом менеджере
или F1/Ctrl+P в редакторе.""")


def main():
    args = sys.argv[1:]
    flag = args[0] if args else None

    ensure_directories()

    # ---------------- CLI-режимы (без curses) ----------------
    if flag in ("-h", "--help"):
        _print_cli_help()
        return
    if flag in ("-m", "--mkdir"):
        if len(args) > 1:
            try:
                Path(args[1]).expanduser().mkdir(parents=True, exist_ok=True)
                print(f"Папка '{args[1]}' создана.")
            except Exception as e:
                print(f"Ошибка: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("Использование: M -m NAME", file=sys.stderr)
            sys.exit(1)
        return
    if flag in ("-i", "--move"):
        if len(args) >= 3:
            try:
                shutil.move(args[1], args[2])
                print(f"Перемещено: {args[1]} → {args[2]}")
            except Exception as e:
                print(f"Ошибка: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("Использование: M -i SRC DST", file=sys.stderr)
            sys.exit(1)
        return
    if flag in ("-c", "--copy"):
        if len(args) >= 3:
            try:
                src, dst = Path(args[1]), Path(args[2])
                if src.is_dir():
                    shutil.copytree(src, dst)
                else:
                    shutil.copy2(src, dst)
                print(f"Скопировано: {args[1]} → {args[2]}")
            except Exception as e:
                print(f"Ошибка: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("Использование: M -c SRC DST", file=sys.stderr)
            sys.exit(1)
        return
    if flag in ("-v", "--version"):
        print("M v6.1")
        return

    # Неизвестный флаг — ошибка
    if flag and flag.startswith("-") and flag not in ("-e", "--edit"):
        print(f"Неизвестный флаг: {flag}", file=sys.stderr)
        print(file=sys.stderr)
        _print_cli_help()
        sys.exit(1)

    # ---------------- Интерактивный режим ----------------
    try:
        import locale
        locale.setlocale(locale.LC_ALL, '')
    except Exception:
        pass

    try:
        curses.wrapper(_run_curses)
    except KeyboardInterrupt:
        pass
    except Exception as e:
        print(f"Критическая ошибка: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
