#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
M — универсальный инструмент «всё в одном» для Termux (mobile-first).
Версия 6.6.4.

Изменения относительно 6.6.3:
  • _prompt_delete: сообщение о снятых мёртвых отметках встроено в
    текст промпта. Раньше оно стиралось ask_yesno до того, как его
    успевал увидеть пользователь.
  • _editor_open_confirm: при попытке открыть файл с несохранённым
    безымянным буфером диалог переспрашивает «открыть без сохранения?»
    вместо тихого отказа. Раньше пользователь застревал.
  • _call_timed: устранена гонка между основным потоком и хук-потоком
    в определении «позднего» завершения. LATE-лог теперь пишется
    основным потоком после короткой догонки через t.join(0.05),
    без чтения разделяемого флага из чужого потока.
  • _get_operation_sources: подчищает мёртвые отметки при отсутствии
    живых, чтобы marked не накапливал несуществующие пути.
  • Тексты ошибок в do_mkdir / do_newfile / do_rename синхронизированы
    с _is_valid_basename: теперь упомянуты управляющие символы.
  • _extract_archive: задокументировано поведение по умолчанию —
    существующие файлы перезаписываются.
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
import tempfile
import time
import unicodedata
import threading
import zlib
from pathlib import Path
from collections import deque, namedtuple


__version__ = "6.6.4"


HOME = Path.home()
CONFIG_DIR = HOME / ".m"
HOOKS_DIR = CONFIG_DIR / "hooks"
LOGS_DIR = CONFIG_DIR / "logs"
BACKUP_DIR = CONFIG_DIR / "backups"
CONFIG_FILE = CONFIG_DIR / "config.json"
BOOKMARKS_FILE = CONFIG_DIR / "bookmarks.json"
TRASH_DIR = CONFIG_DIR / "trash"
TRASH_META = TRASH_DIR / ".meta.json"
HOOKS_LOG = LOGS_DIR / "hooks.log"

ARCHIVE_EXTS = (".zip", ".tar", ".tar.gz", ".tgz", ".tar.bz2", ".tbz2", ".tar.xz")
ARCHIVE_EXTS_SET = (".gz", ".bz2", ".xz", ".zst", ".lz", ".lzma",
                    ".7z", ".rar", ".z")
CODE_EXTS = (".py", ".js", ".ts", ".tsx", ".jsx", ".rs", ".go", ".c", ".cpp",
             ".h", ".hpp", ".java", ".rb", ".php", ".lua")
SCRIPT_EXTS = (".sh", ".bash", ".zsh", ".fish", ".ps1")
IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".svg", ".webp", ".ico")

TABSTOP = 8
MAX_EDITOR_FILE = 10 * 1024 * 1024
HOOK_TIMEOUT = 2.0
HOOK_TIMEOUT_BATCH = 0.3
TRASH_SAVE_EVERY = 10
LOG_MAX_SIZE = 1_000_000
TRASH_NAME_LIMIT = 200

_Entry = namedtuple("_Entry", ["path", "name", "is_dir", "is_parent"])

_DANGEROUS_RESTORE_PREFIXES = {
    "/etc", "/bin", "/sbin", "/boot", "/root",
    "/lib", "/lib64", "/usr/bin", "/usr/sbin", "/usr/lib",
    "/proc", "/sys", "/dev", "/var",
    "/system", "/vendor", "/product", "/odm", "/apex",
}


def _sanitize_display(s):
    if not s:
        return s
    out = None
    for i, c in enumerate(s):
        cp = ord(c)
        if c != '\t' and (cp < 0x20 or cp == 0x7f):
            if out is None:
                out = list(s[:i])
            out.append('?')
        elif out is not None:
            out.append(c)
    return ''.join(out) if out is not None else s


def _is_valid_basename(name):
    if not name or name in ('.', '..'):
        return False
    if '/' in name or '\0' in name:
        return False
    for c in name:
        cp = ord(c)
        if cp < 0x20 or cp == 0x7f:
            return False
    return True


def _invalid_name_message():
    return ("Некорректное имя: пустое, '.', '..', содержит '/' или "
            "управляющие символы.")


def atomic_write_text(path, text, encoding="utf-8"):
    path = Path(path)

    if path.is_symlink():
        try:
            resolved = path.resolve(strict=True)
        except (OSError, RuntimeError) as e:
            raise OSError(f"Не удалось разрешить симлинк {path}: {e}")
        path = resolved

    if not path.parent.exists():
        path.parent.mkdir(parents=True, exist_ok=True)

    old_mode = None
    try:
        if path.exists():
            old_mode = path.stat().st_mode & 0o777
    except OSError:
        old_mode = None

    fd, tmp_name = tempfile.mkstemp(
        prefix="." + path.name + ".",
        suffix=".m.tmp",
        dir=str(path.parent),
    )
    try:
        with os.fdopen(fd, "w", encoding=encoding) as fh:
            fh.write(text)
        if old_mode is not None:
            try:
                os.chmod(tmp_name, old_mode)
            except OSError:
                pass
        os.replace(tmp_name, str(path))
    except Exception:
        try:
            os.close(fd)
        except OSError:
            pass
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


def ensure_directories():
    for d in (CONFIG_DIR, HOOKS_DIR, LOGS_DIR, BACKUP_DIR, TRASH_DIR):
        try:
            d.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass


def path_exists_lexists(p):
    try:
        return os.path.lexists(str(p))
    except Exception:
        return False


def _remove_any(path):
    if path.is_symlink():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)
    else:
        path.unlink()


class HookManager:
    TIMEOUT_EVENTS = {
        "on_start", "on_open", "on_save",
        "on_create", "on_move", "on_delete",
        "on_file_change",
    }

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
                msg = f"{f.name}: {type(e).__name__}: {e}"
                self.errors.append(msg)
                self._log(f"LOAD-FAIL {msg}")

    def _log(self, msg):
        try:
            ensure_directories()
            ts = time.strftime("%Y-%m-%d %H:%M:%S")
            try:
                if HOOKS_LOG.exists() and HOOKS_LOG.stat().st_size > LOG_MAX_SIZE:
                    old = HOOKS_LOG.with_suffix(".log.old")
                    try:
                        if old.exists():
                            old.unlink()
                    except OSError:
                        pass
                    os.replace(str(HOOKS_LOG), str(old))
            except OSError:
                pass
            with open(HOOKS_LOG, "a", encoding="utf-8") as fh:
                fh.write(f"[{ts}] {msg}\n")
        except Exception:
            pass

    def _call_sync(self, name, event, fn, kwargs):
        try:
            return fn(**kwargs)
        except Exception as e:
            self._log(f"ERROR event={event} hook={name}: "
                      f"{type(e).__name__}: {e}")
            return None

    def _call_timed(self, name, event, fn, kwargs, timeout):
        # Никаких разделяемых флагов между потоками: основной поток
        # сам решает, был ли таймаут, по результату done.wait(). После
        # таймаута — короткая догонка, чтобы поймать «позднее»
        # завершение и записать LATE-строку одним автором в лог.
        result = [None]
        exc = [None]
        done = threading.Event()

        def _run(fn=fn, kwargs=kwargs, result=result, exc=exc, done=done):
            try:
                result[0] = fn(**kwargs)
            except Exception as e:
                exc[0] = e
            finally:
                done.set()

        t = threading.Thread(target=_run, daemon=True)
        t.start()
        finished = done.wait(timeout)
        if not finished:
            self._log(f"TIMEOUT event={event} hook={name} (> {timeout}s)")
            t.join(0.05)
            if done.is_set():
                if exc[0] is not None:
                    self._log(f"LATE-ERROR event={event} hook={name}: "
                              f"{type(exc[0]).__name__}: {exc[0]}")
                else:
                    self._log(f"LATE event={event} hook={name}: "
                              f"завершился после таймаута")
            return None
        if exc[0] is not None:
            self._log(f"ERROR event={event} hook={name}: "
                      f"{type(exc[0]).__name__}: {exc[0]}")
            return None
        return result[0]

    def fire(self, event, timeout=None, **kwargs):
        timed = event in self.TIMEOUT_EVENTS
        actual_timeout = HOOK_TIMEOUT if timeout is None else timeout
        for name, fn in self.hooks.get(event, []):
            if timed:
                self._call_timed(name, event, fn, kwargs, actual_timeout)
            else:
                self._call_sync(name, event, fn, kwargs)

    def fire_collect(self, event, **kwargs):
        results = []
        for name, fn in self.hooks.get(event, []):
            r = self._call_sync(name, event, fn, kwargs)
            if r is not None:
                results.append(r)
        return results


class NullHookManager:
    def __init__(self):
        self.hooks = {}
        self.loaded = []
        self.errors = []

    def reload(self):
        pass

    def fire(self, event, timeout=None, **kwargs):
        pass

    def fire_collect(self, event, **kwargs):
        return []


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

    UNDO_GROUP_WINDOW = 0.3

    def __init__(self, stdscr, safe=False, no_color=False):
        self.stdscr = stdscr
        self.safe = safe
        self.no_color = no_color
        self.hooks = NullHookManager() if safe else HookManager()
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

        init_marked = [set(), set()]
        self.marked = init_marked
        self.show_hidden = False
        self.fm_hits = []
        self.fm_hit_idx = -1

        self.tabs = [{
            "panes": [cwd, cwd],
            "selected": [0, 0],
            "active": 0,
            "marked": init_marked,
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
        self.ed_scroll = 0

        self._last_edit_time = 0.0
        self._last_edit_kind = None
        self._last_click_time = 0.0
        self._last_click_pos = (-1, -1)

        self.prompt_active = False
        self.prompt_yesno = False
        self.prompt_text = ""
        self.prompt_input = ""
        self.prompt_callback = None

        self.archive_path = None
        self.archive_items = []
        self.archive_kind = None

        self.load_config()
        self.load_bookmarks()
        self.init_colors()
        self._init_mouse()
        self.refresh_pane(0)
        self.refresh_pane(1)

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
            atomic_write_text(
                CONFIG_FILE,
                json.dumps({"show_hidden": self.show_hidden}, indent=2),
            )
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
            atomic_write_text(
                BOOKMARKS_FILE,
                json.dumps(self.bookmarks, indent=2),
            )
        except Exception:
            pass

    def init_colors(self):
        if self.no_color:
            return
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
        if self.no_color:
            return extra
        try:
            if not curses.has_colors():
                return extra
            return curses.color_pair(n) | extra
        except Exception:
            return extra

    def _init_mouse(self):
        try:
            curses.mousemask(curses.ALL_MOUSE_EVENTS)
        except Exception:
            pass

    def _handle_mouse(self):
        try:
            _mid, mx, my, _mz, bstate = curses.getmouse()
        except Exception:
            return

        scroll_up = getattr(curses, "BUTTON4_PRESSED", 0)
        scroll_down = getattr(curses, "BUTTON5_PRESSED", 0)
        if scroll_up and (bstate & scroll_up):
            self._mouse_scroll(-1)
            return
        if scroll_down and (bstate & scroll_down):
            self._mouse_scroll(1)
            return

        is_double = bool(bstate & getattr(curses, "BUTTON1_DOUBLE_CLICKED", 0))
        is_single = bool(bstate & getattr(curses, "BUTTON1_CLICKED", 0))
        if not (is_double or is_single):
            return

        if self.prompt_active:
            return

        if self.mode == self.MODE_EDITOR:
            self._mouse_editor(mx, my)
        elif self.mode == self.MODE_FILES:
            self._mouse_files(mx, my, is_double)

    def _mouse_scroll(self, delta):
        if self.mode == self.MODE_EDITOR:
            key = curses.KEY_UP if delta < 0 else curses.KEY_DOWN
            for _ in range(abs(delta)):
                self.editor_edit(key, arrows=True)
            self.clamp_cursor()
            self._reset_undo_group()
        elif self.mode == self.MODE_FILES:
            idx = self.active
            step = -abs(delta) if delta < 0 else abs(delta)
            new_sel = self.selected[idx] + step
            new_sel = max(0, min(new_sel, len(self.items[idx]) - 1))
            self.selected[idx] = new_sel

    def _mouse_files(self, mx, my, is_double_from_curses):
        h, w = self.stdscr.getmaxyx()
        half = max(10, w // 2)
        pane = 0 if mx < half else 1

        if my == 1:
            self.active = pane
            return

        if not (2 <= my < h - 2):
            return

        visible = max(1, h - 4)
        sel = self.selected[pane]
        start = 0
        if sel >= visible:
            start = sel - visible + 1

        row = my - 2
        idx = start + row
        if idx < 0 or idx >= len(self.items[pane]):
            return

        self.active = pane

        is_double = bool(is_double_from_curses)
        now = time.monotonic()
        if not is_double:
            if (self._last_click_time > 0
                    and (now - self._last_click_time) < 0.4
                    and self._last_click_pos == (mx, my)):
                is_double = True

        self.selected[pane] = idx

        if is_double:
            self._last_click_time = 0.0
            self._last_click_pos = (-1, -1)
            self.open_item()
        else:
            self._last_click_time = now
            self._last_click_pos = (mx, my)

    def _mouse_editor(self, mx, my):
        h, w = self.stdscr.getmaxyx()

        if not (1 <= my < h - 2):
            return

        start = self.ed_scroll
        line_idx = start + (my - 1)
        if line_idx < 0 or line_idx >= len(self.ed_buffer):
            return

        line = self.ed_buffer[line_idx]
        cx = self._col_to_char(line, mx)
        self.ed_cursor = [line_idx, cx]
        self.clamp_cursor()
        self._reset_undo_group()

    def _get_key(self):
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

    @staticmethod
    def _col_to_char(line, target_col, tabstop=TABSTOP):
        if target_col <= 0:
            return 0
        col = 0
        for i, ch in enumerate(line):
            if ch == '\t':
                nxt = ((col // tabstop) + 1) * tabstop
            else:
                nxt = col + M._char_width(ch)
            if nxt > target_col:
                return i
            col = nxt
        return len(line)

    @staticmethod
    def _char_to_col_table(line, tabstop=TABSTOP):
        table = [0] * (len(line) + 1)
        col = 0
        for i, ch in enumerate(line):
            table[i] = col
            if ch == '\t':
                col = ((col // tabstop) + 1) * tabstop
            else:
                col += M._char_width(ch)
        table[len(line)] = col
        return table

    def refresh_pane(self, idx):
        base = self.panes[idx]
        entries = [_Entry(base.parent, "..", True, True)]
        try:
            all_items = list(base.iterdir())
            if not self.show_hidden:
                all_items = [p for p in all_items if not p.name.startswith('.')]
            info = []
            for p in all_items:
                try:
                    is_dir = p.is_dir()
                except OSError:
                    is_dir = False
                info.append((p, is_dir))
            info.sort(key=lambda t: (not t[1], t[0].name.lower()))
            for p, is_dir in info:
                entries.append(_Entry(p, p.name, is_dir, False))
        except FileNotFoundError:
            self.set_message(f"Каталог не найден: {base}")
        except PermissionError:
            self.set_message(f"Нет доступа: {base}")
        except OSError as e:
            self.set_message(f"Ошибка чтения {base}: {e}")
        self.items[idx] = entries

        if self.selected[idx] >= len(self.items[idx]):
            self.selected[idx] = max(0, len(self.items[idx]) - 1)
        if self.selected[idx] < 0:
            self.selected[idx] = 0

    def current_item(self, idx=None):
        idx = self.active if idx is None else idx
        if 0 <= self.selected[idx] < len(self.items[idx]):
            return self.items[idx][self.selected[idx]]
        return None

    def addstr(self, y, x, text, attr=0):
        try:
            h, w = self.stdscr.getmaxyx()
            if y < 0 or y >= h or x < 0 or x >= w:
                return
            s = str(text)
            if not s:
                return
            s = _sanitize_display(s)

            avail = w - x - 1
            if avail <= 0:
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
                    if nxt > max_col:
                        break
                    out.append(' ' * (nxt - col))
                    col = nxt
                else:
                    cw = M._char_width(ch)
                    nxt = col + cw
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
        self.message = _sanitize_display(str(msg)) if msg else ""

    def _is_archive_name(self, name):
        n = name.lower()
        return (any(n.endswith(e) for e in ARCHIVE_EXTS)
                or any(n.endswith(e) for e in ARCHIVE_EXTS_SET))

    def _file_attr(self, entry):
        if entry.is_parent or entry.is_dir:
            return self.cp(2)
        if self._is_archive_name(entry.name):
            return self.cp(3)
        ext = entry.path.suffix.lower()
        if ext in CODE_EXTS:
            return self.cp(6, curses.A_BOLD)
        if ext in SCRIPT_EXTS:
            return self.cp(2)
        if ext in IMAGE_EXTS:
            return self.cp(6)
        return curses.A_NORMAL

    def _draw_prompt(self, h, w):
        if self.prompt_yesno:
            prompt_line = f" {self.prompt_text}"
            self._set_cursor_visible(False)
        else:
            prompt_line = f" {self.prompt_text}{self.prompt_input}"
            self._set_cursor_visible(True)

        prompt_line = _sanitize_display(prompt_line)

        if self.message:
            self.addstr(h - 2, 0, prompt_line, self.cp(3, curses.A_BOLD))
            self.addstr(h - 1, 0, self.message, self.cp(4, curses.A_BOLD))
            if not self.prompt_yesno:
                vcol = self._visual_col(prompt_line, len(prompt_line))
                self.move_cursor(h - 2, min(vcol, w - 2))
        else:
            self.addstr(h - 1, 0, prompt_line, self.cp(3, curses.A_BOLD))
            if not self.prompt_yesno:
                vcol = self._visual_col(prompt_line, len(prompt_line))
                self.move_cursor(h - 1, min(vcol, w - 2))

    def draw_files(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        tab_label = ""
        if len(self.tabs) > 1:
            tab_label = " ".join(
                f"[{i+1}]" if i == self.active_tab else f" {i+1} "
                for i in range(len(self.tabs))
            )
        title = f" M v{__version__} {tab_label} — Файлы "
        self.addstr(0, 0, title, self.cp(1, curses.A_BOLD))

        half = max(10, w // 2)
        for i in range(2):
            x0 = i * half
            width = half if i == 0 else max(1, w - x0)
            if i == 0:
                for y in range(1, h - 2):
                    try:
                        self.stdscr.addch(y, half - 1, curses.ACS_VLINE)
                    except Exception:
                        pass
            self._draw_pane(i, x0, width, h)

        status = (" Enter:откр m:папка n:файл i:пер c:коп d:удал "
                  "r:переим e:ред t:вклад R:корз ?:справка q:выход")

        if self.prompt_active:
            self._draw_prompt(h, w)
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
            entry = self.items[i][j]
            is_dotdot = entry.is_parent
            is_dir = entry.is_dir
            name = entry.name + ("/" if is_dir and not is_dotdot else "")
            is_marked = (not is_dotdot) and (str(entry.path) in self.marked[i])
            mark = "●" if is_marked else " "

            if i == self.active and j == sel:
                attr = self.cp(5, curses.A_BOLD)
            elif is_marked:
                attr = self.cp(6, curses.A_BOLD)
            else:
                attr = self._file_attr(entry)

            prefix = ">" if j == sel else " "
            self.addstr(2 + row, x0, f"{prefix}{mark} {name}", attr)

    def draw_editor(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        mod = " *" if self.ed_modified else ""
        fname = Path(self.ed_filename).name if self.ed_filename else "(без имени)"
        title = f" M — {fname}{mod} "
        self.addstr(0, 0, title, self.cp(1, curses.A_BOLD))

        visible_h = max(1, h - 3)

        if not self.ed_buffer:
            self.ed_buffer = [""]
        if self.ed_cursor[0] < 0:
            self.ed_cursor[0] = 0
        if self.ed_cursor[0] >= len(self.ed_buffer):
            self.ed_cursor[0] = max(0, len(self.ed_buffer) - 1)

        cur = self.ed_cursor[0]
        if cur < self.ed_scroll:
            self.ed_scroll = cur
        elif cur >= self.ed_scroll + visible_h:
            self.ed_scroll = cur - visible_h + 1

        max_scroll = max(0, len(self.ed_buffer) - visible_h)
        if self.ed_scroll > max_scroll:
            self.ed_scroll = max_scroll
        if self.ed_scroll < 0:
            self.ed_scroll = 0

        start = self.ed_scroll

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
                        self.stdscr.addstr(screen_y, base_vcol,
                                           _sanitize_display(base),
                                           curses.A_REVERSE | curses.A_BOLD)
                    except Exception:
                        pass
                    self.move_cursor(screen_y, min(base_vcol, w - 2))
                else:
                    vcol = self._visual_col(line, cx)
                    ch_w = max(1, self._char_width(ch))
                    if ch == "\t":
                        display_ch = " "
                    else:
                        display_ch = _sanitize_display(ch)
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

        status = (" ^S:сохр ^O:откр ^Z:undo ^Y:redo ^F:поиск ^G:next "
                  "^W:слово ^R:замена ^X:выход ^P:справка ")

        if self.prompt_active:
            self._draw_prompt(h, w)
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

        plain = line.isascii() and '\t' not in line
        col_table = None if plain else self._char_to_col_table(line)

        def col(idx):
            if plain:
                return idx
            if idx <= 0:
                return 0
            if idx >= len(col_table):
                return col_table[-1]
            return col_table[idx]

        if pad_cp is not None:
            try:
                attr = curses.color_pair(pad_cp)
            except Exception:
                attr = curses.A_NORMAL
            total = max(0, w - 1)
            parts = []
            c = 0
            for ch in line:
                if ch == '\t':
                    nxt = ((c // TABSTOP) + 1) * TABSTOP
                else:
                    nxt = c + M._char_width(ch)
                if nxt > total:
                    break
                if ch == '\t':
                    parts.append(' ' * (nxt - c))
                else:
                    parts.append(ch)
                c = nxt
            if c < total:
                parts.append(' ' * (total - c))
            text = ''.join(parts)
            try:
                self.stdscr.addstr(y, 0, _sanitize_display(text), attr)
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

    def draw_help(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        lines = [
            f"  M v{__version__} — универсальный инструмент Termux  ",
            "",
            "  ФЛАГИ:  M -e [FILE] | -m NAME | -i SRC DST | -c SRC DST",
            "          -h | -v | --safe | --no-color",
            "",
            "  ФАЙЛЫ:",
            "    Tab          переключить панель",
            "    j/k/↑/↓      навигация",
            "    Enter        войти / открыть",
            "    m            новая папка",
            "    n            новый файл / следующий при поиске",
            "    N            предыдущий при поиске",
            "    i  c         переместить / копировать (с учётом отметок)",
            "    r  d         переименовать / удалить в корзину",
            "    Space        отметить файл",
            "    e            редактор",
            "    u  U         undo / redo",
            "    /            поиск",
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
            "  МЫШЬ:",
            "    клик         выбрать файл / панель",
            "    двойной клик открыть",
            "    колесо       скролл (1 строка за тик)",
            "",
            "  РЕДАКТОР: F1 или Ctrl+P внутри редактора",
            "",
            "  ХУКИ:",
            "    ~/.m/hooks/*.py  с EVENTS = {событие: функция}",
            "    События: on_start on_open on_file_change on_save",
            "             on_create on_move on_delete on_draw_line",
            f"    Логи: {HOOKS_LOG}",
            "",
            "  Нажми любую клавишу…",
        ]
        for i, line in enumerate(lines):
            if i >= h:
                break
            attr = (curses.A_BOLD if line and not line.startswith("    ")
                    and line.strip() else curses.A_NORMAL)
            self.addstr(i, 0, line, attr)
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
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
            "  МЫШЬ:",
            "    клик         перенести курсор в точку клика",
            "    колесо       скролл текста (1 строка за тик)",
            "",
            "  Нажми любую клавишу…",
        ]
        for i, line in enumerate(lines):
            if i >= h:
                break
            attr = (curses.A_BOLD if line and not line.startswith("    ")
                    and line.strip() else curses.A_NORMAL)
            self.addstr(i, 0, line, attr)
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
        self.mode = self.MODE_EDITOR

    def draw_hooks(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        self.addstr(0, 0, " M — Менеджер хуков ", self.cp(1, curses.A_BOLD))
        y = 2
        self.addstr(y, 0, f" Директория: {HOOKS_DIR}")
        y += 1
        self.addstr(y, 0, f" Лог: {HOOKS_LOG}", curses.A_DIM)
        y += 2
        if self.safe:
            self.addstr(y, 0, " Режим --safe: хуки отключены.", self.cp(3))
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
                self.addstr(y, 0, f"   ! {err[:max(1, w-6)]}", self.cp(4))
                y += 1
        self.addstr(h - 2, 0, " R:перезагрузить  любая:назад ", self.cp(3))
        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))
        self._set_cursor_visible(False)
        self.stdscr.refresh()
        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
        if k in (ord('r'), ord('R')):
            self.hooks.reload()
            self.set_message("Хуки перезагружены.")
        self.mode = self.MODE_FILES

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
                        lines.append(f"  Батарея {d.name}: "
                                     f"{cap.read_text().strip()}% ({s})")
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
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
        self.mode = self.MODE_FILES

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
            visible = max(1, h - 4)
            start = 0
            if self.bm_idx >= visible:
                start = self.bm_idx - visible + 1
            end = min(start + visible, len(self.bookmarks))
            for i in range(start, end):
                bm = self.bookmarks[i]
                attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
                self.addstr(2 + (i - start), 0, f"  {i+1}. {bm}", attr)
        self.addstr(h - 2, 0, " ↑/↓:выбор  Enter:перейти  d:удалить  Esc:назад ",
                    self.cp(3))
        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
        if k == 27:
            self.mode = self.MODE_FILES
        elif k == curses.KEY_DOWN and self.bookmarks:
            self.bm_idx = min(len(self.bookmarks) - 1, self.bm_idx + 1)
        elif k == curses.KEY_UP:
            self.bm_idx = max(0, self.bm_idx - 1)
        elif k in (10, 13, curses.KEY_ENTER) and self.bookmarks:
            target = Path(self.bookmarks[self.bm_idx])
            if target.is_dir():
                self.panes[self.active] = target
                self.selected[self.active] = 0
                self.marked[self.active].clear()
                self.fm_hits = []
                self.fm_hit_idx = -1
                self.refresh_pane(self.active)
                self.set_message(f"Переход: {target}")
                self.mode = self.MODE_FILES
            elif target.exists():
                self.set_message("Это файл, а не папка.")
            else:
                self.set_message("Путь больше не существует.")
        elif k == ord('d') and self.bookmarks:
            self.bookmarks.pop(self.bm_idx)
            self.save_bookmarks()
            if self.bm_idx >= len(self.bookmarks):
                self.bm_idx = max(0, len(self.bookmarks) - 1)
            self.set_message("Закладка удалена.")

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
            visible = max(1, h - 4)
            start = 0
            if self.bm_idx >= visible:
                start = self.bm_idx - visible + 1
            end = min(start + visible, len(items))
            for i in range(start, end):
                name, _meta = items[i]
                attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
                self.addstr(2 + (i - start), 0, f"  {i+1}. {name}", attr)

        self.addstr(h - 2, 0,
                    " ↑/↓:выбор  r:восст.  d:удалить  C:очистить  Esc:назад ",
                    self.cp(3))
        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
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
                if p.name == '.meta.json':
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
                    return {
                        k: v for k, v in data.items()
                        if isinstance(k, str) and isinstance(v, str)
                    }
        except Exception:
            pass
        return {}

    def _save_trash_meta(self, data):
        try:
            TRASH_DIR.mkdir(parents=True, exist_ok=True)
            atomic_write_text(
                TRASH_META,
                json.dumps(data, indent=2, ensure_ascii=False),
            )
        except Exception:
            pass

    def _unique_trash_path(self, name):
        base = f"{time.time_ns()}"
        if len(name) > TRASH_NAME_LIMIT:
            suffix = str(zlib.crc32(name.encode("utf-8")) & 0xffffffff)
            name = name[:TRASH_NAME_LIMIT - len(suffix) - 1] + "_" + suffix
        candidate = TRASH_DIR / f"{base}_{name}"
        n = 1
        while path_exists_lexists(candidate):
            if n > 1000:
                raise OSError("Не удалось подобрать уникальное имя в корзине")
            candidate = TRASH_DIR / f"{base}_{n}_{name}"
            n += 1
        return candidate

    @staticmethod
    def _is_safe_restore_path(p):
        try:
            if not p.is_absolute():
                return False
            try:
                resolved = p.resolve()
            except (OSError, RuntimeError):
                return False
            parts = resolved.parts
            if len(parts) < 3:
                return False
            for prefix in _DANGEROUS_RESTORE_PREFIXES:
                try:
                    resolved.relative_to(prefix)
                    return False
                except ValueError:
                    pass
            return True
        except Exception:
            return False

    def _trash_restore(self, item):
        name, path = item
        meta = self._load_trash_meta()
        original = meta.get(name)
        if not original:
            self.set_message("Не найдено оригинального пути.")
            return
        try:
            dst = Path(original)
            if not self._is_safe_restore_path(dst):
                self.set_message("Некорректный путь в метаданных — отказ.")
                return
            dst.parent.mkdir(parents=True, exist_ok=True)
            if path_exists_lexists(dst):
                base_dst = dst
                counter = 1
                while path_exists_lexists(dst) and counter <= 100:
                    dst = base_dst.parent / f"{base_dst.name}_restored{counter}"
                    counter += 1
                if path_exists_lexists(dst):
                    self.set_message(
                        "Слишком много конфликтов имён при восстановлении."
                    )
                    return
            shutil.move(str(path), str(dst))
            meta.pop(name, None)
            self._save_trash_meta(meta)
            self.set_message(f"Восстановлено: {dst}")
            self.refresh_pane(0)
            self.refresh_pane(1)
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def _trash_delete_permanent(self, item):
        name, path = item
        try:
            _remove_any(path)
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
                    if p.name == '.meta.json':
                        continue
                    _remove_any(p)
                self._save_trash_meta({})
                self.set_message("Корзина очищена.")
                self.bm_idx = 0
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def draw_archive(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        fname = Path(self.archive_path).name if self.archive_path else "?"
        self.addstr(0, 0, f" M — Архив: {fname} ", self.cp(1, curses.A_BOLD))

        if self.archive_items:
            self.bm_idx = max(0, min(self.bm_idx, len(self.archive_items) - 1))
        else:
            self.bm_idx = 0

        if self.archive_items:
            visible = max(1, h - 4)
            start = 0
            if self.bm_idx >= visible:
                start = self.bm_idx - visible + 1
            end = min(start + visible, len(self.archive_items))
            for i in range(start, end):
                name = self.archive_items[i]
                attr = self.cp(5) if i == self.bm_idx else curses.A_NORMAL
                self.addstr(2 + (i - start), 0,
                            f"  {name[:max(1, w-6)]}", attr)

        self.addstr(h - 2, 0, " ↑/↓:нав.  x:распаковать всё сюда  Esc:назад ",
                    self.cp(3))
        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))
        self._set_cursor_visible(False)
        self.stdscr.refresh()

        try:
            k = self._get_key()
        except Exception:
            k = -1
        if k == curses.KEY_RESIZE:
            self._init_mouse()
            return
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
        """Распаковывает архив в текущую папку активной панели.

        Существующие файлы ПЕРЕЗАПИСЫВАЮТСЯ (поведение по умолчанию
        zipfile.extract / tarfile.extract). Символические и жёсткие
        ссылки, special-файлы и небезопасные пути пропускаются.
        """
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
                        if (m.issym() or m.islnk() or m.isdev()
                                or m.isfifo() or m.ischr() or m.isblk()):
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

    def run(self):
        ensure_directories()
        try:
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

                if key == curses.KEY_MOUSE:
                    self._handle_mouse()
                    continue

                if key == curses.KEY_RESIZE:
                    self._init_mouse()
                    if self.mode == self.MODE_FILES:
                        self.refresh_pane(0)
                        self.refresh_pane(1)
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
        finally:
            self.save_config()

    def _close_prompt(self):
        self.prompt_active = False
        self.prompt_yesno = False
        self.prompt_callback = None
        self.prompt_text = ""
        self.prompt_input = ""

    def ask(self, text, callback):
        self.prompt_active = True
        self.prompt_yesno = False
        self.prompt_text = text
        self.prompt_input = ""
        self.prompt_callback = callback
        self.message = ""

    def ask_yesno(self, text, callback):
        self.prompt_active = True
        self.prompt_yesno = True
        self.prompt_text = text
        self.prompt_input = ""
        self.prompt_callback = callback
        self.message = ""

    def handle_prompt_key(self, key):
        if self.prompt_yesno:
            if key == 27:
                self._close_prompt()
                self.set_message("Отменено.")
                return
            ch = None
            if isinstance(key, str) and len(key) == 1:
                ch = key.lower()
            elif isinstance(key, int):
                try:
                    ch = chr(key).lower()
                except (ValueError, OverflowError):
                    ch = None
            if ch in ('y', 'д'):
                val = 'y'
            elif ch in ('n', 'н'):
                val = 'n'
            else:
                return
            cb = self.prompt_callback
            self._close_prompt()
            if cb:
                try:
                    cb(val)
                except Exception as e:
                    self.set_message(f"Ошибка: {e}")
            return

        if key == 27:
            self._close_prompt()
            self.set_message("Отменено.")
            return
        if key in (10, 13, curses.KEY_ENTER):
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
            self._close_prompt()
            return
        if key in (curses.KEY_BACKSPACE, 127, 8):
            self.prompt_input = self.prompt_input[:-1]
        elif key == 9:
            self.set_message("Tab недоступен в поле ввода.")
        elif isinstance(key, str):
            self.prompt_input += key
        elif isinstance(key, int) and 32 <= key <= 126:
            self.prompt_input += chr(key)

    def handle_files_key(self, key):
        idx = self.active

        if key == 9:
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
            self._prompt_delete()
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

    def _live_marks(self):
        return [Path(p) for p in self.marked[self.active]
                if path_exists_lexists(p)]

    def _prune_dead_marks(self):
        m = self.marked[self.active]
        dead = [p for p in m if not path_exists_lexists(p)]
        if not dead:
            return False
        for p in dead:
            m.discard(p)
        return True

    def _prompt_delete(self):
        # Мёртвые отметки снимаем до вычисления live. Сообщение об этом
        # встраиваем в текст промпта: ask_yesno сбрасывает self.message,
        # поэтому отдельный set_message был бы потерян.
        pruned = self._prune_dead_marks()
        live = self._live_marks()

        if live:
            n = len(live)
            if pruned:
                text = (f"Удалить в корзину: {n} шт. "
                        f"(часть отметок снята)? [y/д, n/н]: ")
            else:
                text = f"Удалить в корзину: {n} шт.? [y/д, n/н]: "
        else:
            entry = self.current_item()
            if entry is None:
                self.set_message("Нечего удалять (панель пуста).")
                return
            if entry.is_parent:
                self.set_message("Нечего удалять (курсор на '..').")
                return
            text = f"Удалить '{entry.name}' в корзину? [y/д, n/н]: "
        self.ask_yesno(text, self.do_delete)

    def open_item(self):
        entry = self.current_item()
        if entry is None:
            return
        if entry.is_parent:
            self.panes[self.active] = self.panes[self.active].parent
            self.selected[self.active] = 0
            self.marked[self.active].clear()
            self.fm_hits = []
            self.fm_hit_idx = -1
            self.refresh_pane(self.active)
            self.hooks.fire("on_open", path=str(self.panes[self.active]),
                            kind="dir")
            return
        full = entry.path
        if full.is_dir():
            self.panes[self.active] = full
            self.selected[self.active] = 0
            self.marked[self.active].clear()
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
        entry = self.current_item()
        if entry is None:
            return
        if entry.is_parent:
            self.set_message("Нечего редактировать (курсор на '..').")
            return
        full = entry.path
        if full.is_symlink() and not full.exists():
            self.set_message("Битый симлинк — не редактируем.")
            return
        if full.is_dir():
            self.set_message("Это папка.")
            return
        if not self.editor_open_file(str(full)):
            self.mode = self.MODE_EDITOR

    def do_mkdir(self, name):
        name = name.strip()
        if not _is_valid_basename(name):
            self.set_message(_invalid_name_message())
            return
        try:
            p = self.panes[self.active] / name
            if path_exists_lexists(p):
                self.set_message(f"'{name}' уже существует.")
                return
            p.mkdir(parents=True)
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
        if not _is_valid_basename(name):
            self.set_message(_invalid_name_message())
            return
        try:
            p = self.panes[self.active] / name
            if path_exists_lexists(p):
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
        if not _is_valid_basename(newname):
            self.set_message(_invalid_name_message())
            return
        entry = self.current_item()
        if entry is None or entry.is_parent:
            return
        if newname == entry.name:
            self.set_message("Имя не изменилось.")
            return
        src = entry.path
        dst = self.panes[self.active] / newname
        if path_exists_lexists(dst):
            self.set_message("Цель уже существует.")
            return
        try:
            panel = self.active
            marked_set = self.marked[panel]

            src.rename(dst)
            self.set_message(f"Переименовано: {entry.name} → {newname}")
            self.refresh_pane(panel)
            self.hooks.fire("on_move", src=str(src), dst=str(dst))

            old_s, new_s = str(src), str(dst)
            if old_s in marked_set:
                marked_set.discard(old_s)
                marked_set.add(new_s)

            def undo():
                if path_exists_lexists(dst) and not path_exists_lexists(src):
                    dst.rename(src)
                    if new_s in marked_set:
                        marked_set.discard(new_s)
                        marked_set.add(old_s)
                else:
                    raise OSError("невозможно откатить")

            def redo():
                if path_exists_lexists(src) and not path_exists_lexists(dst):
                    src.rename(dst)
                    if old_s in marked_set:
                        marked_set.discard(old_s)
                        marked_set.add(new_s)
                else:
                    raise OSError("невозможно повторить")

            self.undo.push(f"переименование '{entry.name}' → '{newname}'",
                           undo, redo)
        except Exception as e:
            self.set_message(f"Ошибка: {e}")

    def do_delete(self, answer):
        if answer != 'y':
            self.set_message("Отменено.")
            return
        sources = self._get_operation_sources()
        if not sources:
            self.set_message("Нечего удалять.")
            return

        try:
            TRASH_DIR.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self.set_message(f"Ошибка создания корзины: {e}")
            return

        meta = self._load_trash_meta()
        pairs = []
        failed = 0
        last_error = ""
        moved_since_save = 0

        hook_timeout = HOOK_TIMEOUT if len(sources) == 1 else HOOK_TIMEOUT_BATCH

        for src in sources:
            try:
                trashed = self._unique_trash_path(src.name)
                shutil.move(str(src), str(trashed))
                meta[trashed.name] = str(src)
                pairs.append((src, trashed))
                moved_since_save += 1
                if moved_since_save >= TRASH_SAVE_EVERY:
                    self._save_trash_meta(meta)
                    moved_since_save = 0
            except Exception as e:
                failed += 1
                last_error = f"Ошибка: {e}"
                continue
            self.hooks.fire("on_delete",
                            timeout=hook_timeout,
                            path=str(src))

        if pairs:
            self._save_trash_meta(meta)

        if pairs:
            def undo():
                m = self._load_trash_meta()
                try:
                    for s, t in pairs:
                        if not path_exists_lexists(t):
                            raise FileNotFoundError(
                                f"уже нет в корзине: {t.name}")
                        if path_exists_lexists(s):
                            raise FileExistsError(
                                f"'{s.name}' уже существует")
                        shutil.move(str(t), str(s))
                        m.pop(t.name, None)
                finally:
                    self._save_trash_meta(m)

            def redo():
                m = self._load_trash_meta()
                new_pairs = []
                try:
                    for s, _old_t in pairs:
                        if not path_exists_lexists(s):
                            raise FileNotFoundError(
                                f"исходник отсутствует: {s}")
                        nt = self._unique_trash_path(s.name)
                        shutil.move(str(s), str(nt))
                        m[nt.name] = str(s)
                        new_pairs.append((s, nt))
                finally:
                    self._save_trash_meta(m)
                    pairs[:] = new_pairs

            desc = (f"удаление '{pairs[0][0].name}'" if len(pairs) == 1
                    else f"удаление {len(pairs)} файлов")
            self.undo.push(desc, undo, redo)

        if failed and not pairs:
            self.set_message(last_error or "Ничего не удалено.")
        elif failed:
            self.set_message(f"Удалено: {len(pairs)}, ошибок: {failed}.")
        else:
            self.set_message(
                f"Удалено: {len(pairs)}. (u — отменить)"
                if len(pairs) > 1 else
                f"Удалено: {pairs[0][0].name}. (u — отменить)"
            )

        if pairs:
            removed = set(str(s) for s, _ in pairs)
            self.marked[self.active] -= removed

        self.refresh_pane(self.active)

    def _get_operation_sources(self):
        live = self._live_marks()
        if live:
            return live
        # Живых отметок нет — если в marked остались мёртвые, снимаем
        # их и работаем с элементом под курсором. Так marked не
        # накапливает несуществующие пути между операциями.
        if self.marked[self.active]:
            self._prune_dead_marks()
        entry = self.current_item()
        if entry is None or entry.is_parent:
            return []
        return [entry.path]

    def do_move(self):
        had_marks = bool(self._live_marks())
        sources = self._get_operation_sources()
        if not sources:
            self.set_message("Нечего перемещать.")
            return
        dst_dir = self.panes[1 - self.active]
        failed = []
        success = 0
        last_error = ""

        hook_timeout = HOOK_TIMEOUT if len(sources) == 1 else HOOK_TIMEOUT_BATCH

        for src in sources:
            dst = dst_dir / src.name
            if path_exists_lexists(dst):
                last_error = f"Пропущено (существует): {src.name}"
                failed.append(src)
                continue
            try:
                shutil.move(str(src), str(dst))
                self.hooks.fire("on_move",
                                timeout=hook_timeout,
                                src=str(src), dst=str(dst))
                self._register_move_undo(src, dst)
                success += 1
            except Exception as e:
                last_error = f"Ошибка: {e}"
                failed.append(src)

        if had_marks:
            m = self.marked[self.active]
            if failed:
                m.clear()
                m.update(str(p) for p in failed)
            else:
                m.clear()

        if failed:
            self.set_message(last_error or "Некоторые файлы не перемещены.")
        else:
            self.set_message(f"Перемещено: {success}. (u — отменить)")
        self.refresh_pane(0)
        self.refresh_pane(1)

    def _register_move_undo(self, src, dst):
        def undo():
            if path_exists_lexists(dst) and not path_exists_lexists(src):
                shutil.move(str(dst), str(src))
            else:
                raise OSError("невозможно откатить")

        def redo():
            if path_exists_lexists(src) and not path_exists_lexists(dst):
                shutil.move(str(src), str(dst))
            else:
                raise OSError("невозможно повторить")

        self.undo.push(f"перемещение '{src.name}'", undo, redo)

    def _copy_one(self, src, dst):
        if src.is_symlink():
            linkto = os.readlink(str(src))
            os.symlink(linkto, str(dst))
        elif src.is_dir():
            shutil.copytree(str(src), str(dst), symlinks=True)
        else:
            shutil.copy2(str(src), str(dst))

    def do_copy(self):
        had_marks = bool(self._live_marks())
        sources = self._get_operation_sources()
        if not sources:
            self.set_message("Нечего копировать.")
            return
        dst_dir = self.panes[1 - self.active]
        failed = []
        success = 0
        last_error = ""

        hook_timeout = HOOK_TIMEOUT if len(sources) == 1 else HOOK_TIMEOUT_BATCH

        for src in sources:
            dst = dst_dir / src.name
            if path_exists_lexists(dst):
                last_error = f"Пропущено (существует): {src.name}"
                failed.append(src)
                continue
            try:
                self._copy_one(src, dst)
                self.hooks.fire("on_create",
                                timeout=hook_timeout,
                                path=str(dst), kind="copy")
                self._register_copy_undo(src, dst)
                success += 1
            except Exception as e:
                last_error = f"Ошибка: {e}"
                failed.append(src)

        if had_marks:
            m = self.marked[self.active]
            if failed:
                m.clear()
                m.update(str(p) for p in failed)
            else:
                m.clear()

        if failed:
            self.set_message(last_error or "Некоторые файлы не скопированы.")
        else:
            self.set_message(f"Скопировано: {success}. (u — отменить)")
        self.refresh_pane(0)
        self.refresh_pane(1)

    def _register_copy_undo(self, src, dst):
        def undo():
            if not path_exists_lexists(dst):
                raise FileNotFoundError("копия уже удалена")
            _remove_any(dst)

        def redo():
            if path_exists_lexists(dst):
                raise FileExistsError("цель уже существует")
            self._copy_one(src, dst)

        self.undo.push(f"копирование '{src.name}'", undo, redo)

    def toggle_mark(self):
        entry = self.current_item()
        if entry is None or entry.is_parent:
            return
        full = str(entry.path)
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
        for i, entry in enumerate(self.items[self.active]):
            if q_lower in entry.name.lower():
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

    def _save_tab_state(self):
        tab = self.tabs[self.active_tab]
        tab["panes"] = list(self.panes)
        tab["selected"] = list(self.selected)
        tab["active"] = self.active
        tab["marked"] = self.marked

    def _take_tab_marked(self, tab):
        m = tab.get("marked")
        if m is None:
            m = [set(), set()]
            tab["marked"] = m
        return m

    def switch_tab(self, idx):
        if idx == self.active_tab or idx < 0 or idx >= len(self.tabs):
            return
        self._save_tab_state()
        self.active_tab = idx
        tab = self.tabs[idx]
        self.panes = list(tab["panes"])
        self.selected = list(tab["selected"])
        self.active = tab["active"]
        self.marked = self._take_tab_marked(tab)
        self.fm_hits = []
        self.fm_hit_idx = -1
        self.refresh_pane(0)
        self.refresh_pane(1)
        self.set_message(f"Вкладка {idx + 1}")

    def new_tab(self):
        self._save_tab_state()
        cwd = self.panes[self.active]
        new_marked = [set(), set()]
        self.tabs.append({
            "panes": [cwd, cwd],
            "selected": [0, 0],
            "active": 0,
            "marked": new_marked,
        })
        self.active_tab = len(self.tabs) - 1
        self.panes = [cwd, cwd]
        self.selected = [0, 0]
        self.active = 0
        self.marked = new_marked
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
        self.marked = self._take_tab_marked(tab)
        self.fm_hits = []
        self.fm_hit_idx = -1
        self.refresh_pane(0)
        self.refresh_pane(1)
        self.set_message("Вкладка закрыта.")

    def _snapshot(self):
        return (list(self.ed_buffer), list(self.ed_cursor), self.ed_modified)

    def _push_undo(self):
        self.ed_undo_stack.append(self._snapshot())
        self.ed_redo_stack.clear()
        self._reset_undo_group()

    def _push_undo_for_edit(self, kind):
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
            self._reset_undo_group()
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
            self.set_message("Файл без имени — сохранить нельзя.")
            return False
        try:
            p = Path(self.ed_filename)
            if p.is_symlink() and not p.exists():
                self.set_message("Битый симлинк — сохранение отменено.")
                return False
            data = "\n".join(self.ed_buffer)
            atomic_write_text(p, data)
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

        if key == 24:  # Ctrl+X
            if self.ed_modified:
                self.ask_yesno(
                    "Сохранить перед выходом? [y/д, n/н, Esc — отмена]: ",
                    self._editor_exit,
                )
                return
            self.mode = self.MODE_FILES
            self.set_message("")
            return

        if key == 19:  # Ctrl+S
            self.save_editor()
            return

        if key == 15:  # Ctrl+O
            if self.ed_modified:
                self.ask_yesno(
                    "Несохранённые изменения. Сохранить? [y/д, n/н]: ",
                    self._editor_open_confirm,
                )
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

        edit_kind = None
        if isinstance(key, str):
            edit_kind = "insert"
        elif isinstance(key, int) and 32 <= key <= 126:
            edit_kind = "insert"
        elif key in (curses.KEY_BACKSPACE, 127, 8, curses.KEY_DC):
            edit_kind = "delete"
        elif key in (10, 13, 9, curses.KEY_ENTER):
            edit_kind = "other"

        if edit_kind is not None:
            self._push_undo_for_edit(edit_kind)
            self.editor_edit(key, arrows=True)
            self.clamp_cursor()
        else:
            self._reset_undo_group()
            self.editor_edit(key, arrows=True)
            self.clamp_cursor()

    def _editor_open_confirm(self, ans):
        # Если ans='y' и нет имени файла — сохранять некуда. Спрашиваем
        # разрешение открыть файл без сохранения, чтобы пользователь
        # не застревал в тупике «ответьте n», как раньше.
        if ans == 'y':
            if not self.ed_filename:
                self.ask_yesno(
                    "Файл без имени. Открыть без сохранения? [y/д, n/н]: ",
                    self._editor_open_nosave,
                )
                return
            if not self.save_editor():
                return
        self.ask("Открыть файл: ", self.editor_open_file)

    def _editor_open_nosave(self, ans):
        if ans == 'y':
            self.ask("Открыть файл: ", self.editor_open_file)
        else:
            self.set_message("Отменено — остаёмся в редакторе.")

    def _editor_exit(self, ans):
        if ans == 'y':
            if not self.ed_filename:
                self.ask_yesno(
                    "Файл без имени — сохранить нельзя. "
                    "Выйти без сохранения? [y/д, n/н]: ",
                    self._editor_exit_nosave,
                )
                return
            if not self.save_editor():
                return
            self.ed_modified = False
            self.mode = self.MODE_FILES
            self.set_message("Сохранено и закрыто.")
        else:
            self.ed_modified = False
            self.mode = self.MODE_FILES
            self.set_message("Выход без сохранения.")

    def _editor_exit_nosave(self, ans):
        if ans == 'y':
            self.ed_modified = False
            self.mode = self.MODE_FILES
            self.set_message("Выход без сохранения.")
        else:
            self.set_message("Отменено — остаёмся в редакторе.")

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

        if key in (10, 13, curses.KEY_ENTER):
            line = self.ed_buffer[cy]
            self.ed_buffer[cy] = line[:cx]
            self.ed_buffer.insert(cy + 1, line[cx:])
            self.ed_cursor = [cy + 1, 0]
            self.ed_modified = True
        elif key == 9:
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
            if key:
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
            self.set_message(f"Найдено строк: {len(self.ed_search_hits)} "
                             f"(Ctrl+G — след.)")
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
        self.set_message(f"Совпадение {self.ed_search_idx + 1} "
                         f"из {len(self.ed_search_hits)}")

    def _editor_search_word_under_cursor(self):
        cy, cx = self.ed_cursor
        if cy >= len(self.ed_buffer):
            return
        line = self.ed_buffer[cy]
        if not line:
            self.set_message("Пустая строка.")
            return
        if cx >= len(line):
            cx = len(line) - 1
        if cx < 0:
            return
        if not (line[cx].isalnum() or line[cx] == '_'):
            self.set_message("Курсор не на слове.")
            return
        start = cx
        while start > 0 and (line[start - 1].isalnum() or line[start - 1] == '_'):
            start -= 1
        end = cx
        while end + 1 < len(line) and (line[end + 1].isalnum() or line[end + 1] == '_'):
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
        if old == new:
            self.set_message("Строки совпадают.")
            return
        found = any(old in line for line in self.ed_buffer)
        if not found:
            self.set_message("Не найдено.")
            return
        self._push_undo()
        count = 0
        for i, line in enumerate(self.ed_buffer):
            if old in line:
                count += line.count(old)
                self.ed_buffer[i] = line.replace(old, new)
        self.ed_modified = True
        self.set_message(f"Заменено вхождений: {count} (Ctrl+Z — отменить)")

    def editor_open_file(self, path):
        if path is None:
            return True
        path = path.strip()
        if not path:
            self.set_message("Пустой путь — отменено.")
            return True
        try:
            p = Path(path).expanduser()
            if p.is_symlink() and not p.exists():
                self.set_message(f"Битый симлинк: {p.name}")
                return True
            if p.is_dir():
                self.set_message("Это папка, а не файл.")
                return True
            if p.exists():
                try:
                    if not p.is_file():
                        self.set_message("Не обычный файл.")
                        return True
                except OSError as e:
                    self.set_message(f"Ошибка доступа: {e}")
                    return True
                try:
                    size = p.stat().st_size
                except OSError:
                    size = 0
                if size > MAX_EDITOR_FILE:
                    mb = size / (1024 * 1024)
                    self.set_message(
                        f"Файл слишком большой ({mb:.1f} MB > "
                        f"{MAX_EDITOR_FILE // (1024*1024)} MB). Открытие отменено."
                    )
                    return True
                try:
                    text = p.read_text(encoding='utf-8', errors='replace')
                except Exception as e:
                    self.set_message(f"Ошибка чтения: {e}")
                    return True
                text = text.replace('\r\n', '\n').replace('\r', '\n')
                self.ed_buffer = text.split('\n')
                if not self.ed_buffer:
                    self.ed_buffer = [""]
                self.set_message(f"Открыт: {p.name}")
            else:
                self.ed_buffer = [""]
                self.set_message(f"Новый файл: {p.name} (Ctrl+S — сохранить)")
                self.hooks.fire("on_create", path=str(p), kind="file-pending")
                if p.exists() and p.is_file():
                    try:
                        text = p.read_text(encoding='utf-8', errors='replace')
                        text = text.replace('\r\n', '\n').replace('\r', '\n')
                        self.ed_buffer = text.split('\n') or [""]
                    except Exception:
                        pass
            self.ed_filename = str(p)
            self.ed_cursor = [0, 0]
            self.ed_modified = False
            self.ed_scroll = 0
            self.ed_undo_stack.clear()
            self.ed_redo_stack.clear()
            self.ed_search_hits = []
            self.ed_search_idx = -1
            self._reset_undo_group()
            self.hooks.fire("on_open", path=str(p), kind="file")
            self.hooks.fire("on_file_change", path=str(p))
            return False
        except Exception as e:
            self.set_message(f"Ошибка: {e}")
            return True

    def apply_flags(self, args):
        if not args:
            return
        flag = args[0]
        if flag in ("-e", "--edit"):
            if len(args) > 1:
                ok = not self.editor_open_file(args[1])
            else:
                cwd = Path.cwd()
                ok = not self.editor_open_file(str(cwd / "untitled.txt"))
            if ok:
                self.mode = self.MODE_EDITOR
                if len(args) > 2:
                    extra = " ".join(args[2:])
                    self.set_message(
                        f"Проигнорированы лишние аргументы: {extra}"
                    )


def _run_curses(stdscr, safe=False, no_color=False, args=None):
    try:
        curses.curs_set(1)
    except Exception:
        pass
    try:
        curses.set_escdelay(50)
    except Exception:
        pass
    try:
        stdscr.keypad(True)
    except Exception:
        pass

    m = M(stdscr, safe=safe, no_color=no_color)
    if args:
        m.apply_flags(args)
    m.run()


def _print_cli_help():
    print(f"""M v{__version__} — универсальный инструмент Termux.

Использование:
  M                файловый менеджер
  M -e [FILE]      редактор (FILE — необязательно)
  M -m NAME        создать папку
  M -i SRC DST     переместить файл/папку
  M -c SRC DST     скопировать файл/папку
  M -h, --help     эта справка
  M -v, --version  версия

Опции:
  --safe           отключить хуки
  --no-color       монохромный режим

Справка внутри M — '?' в файловом менеджере, F1 в редакторе.""")


def main():
    raw_args = sys.argv[1:]

    safe = False
    no_color = False
    args = []
    for a in raw_args:
        if a == "--safe":
            safe = True
        elif a == "--no-color":
            no_color = True
        else:
            args.append(a)

    flag = args[0] if args else None

    ensure_directories()

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
                src = Path(args[1]).expanduser()
                dst = Path(args[2]).expanduser()
                shutil.move(str(src), str(dst))
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
                src = Path(args[1]).expanduser()
                dst = Path(args[2]).expanduser()
                if src.is_symlink():
                    linkto = os.readlink(str(src))
                    os.symlink(linkto, str(dst))
                elif src.is_dir():
                    shutil.copytree(str(src), str(dst), symlinks=True)
                else:
                    shutil.copy2(str(src), str(dst))
                print(f"Скопировано: {args[1]} → {args[2]}")
            except Exception as e:
                print(f"Ошибка: {e}", file=sys.stderr)
                sys.exit(1)
        else:
            print("Использование: M -c SRC DST", file=sys.stderr)
            sys.exit(1)
        return
    if flag in ("-v", "--version"):
        print(f"M v{__version__}")
        return

    if flag and flag.startswith("-") and flag not in ("-e", "--edit"):
        print(f"Неизвестный флаг: {flag}", file=sys.stderr)
        print(file=sys.stderr)
        _print_cli_help()
        sys.exit(1)

    try:
        import locale
        locale.setlocale(locale.LC_ALL, '')
    except Exception:
        pass

    try:
        curses.wrapper(_run_curses, safe=safe, no_color=no_color, args=args)
    except KeyboardInterrupt:
        pass
    except Exception as e:
        print(f"Критическая ошибка: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
