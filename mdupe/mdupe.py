#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Mdupe — поиск и очистка дубликатов в стиле M.
Версия 1.5.5.

Спутник файлового менеджера M:
  • делит ~/.m/ с M (общая корзина, общий стиль);
  • удаления уходят в ту же корзину и восстанавливаются через M;
  • работает и как TUI, и как CLI (--list / --json / --trash).

Изменения 1.5.5 (относительно 1.5.4):
  • scan_duplicates: явная проверка stat.S_ISREG для не-симлинков
    (FIFO/сокеты/устройства больше не попадают в хеширование —
    открытие FIFO блокировало поток навсегда).
  • scan_duplicates: прогресс обновляется и на стадии полного
    хеширования мелких файлов.
  • _unique_trash_path: корректная работа при TRASH_NAME_LIMIT,
    близком к длине timestamp (инвариант длины имени соблюдён).
  • MdupeApp: кэш _total_waste, инвалидация при смене групп
    (устраняет O(groups) на каждый кадр TUI).
  • _draw_files: ширина тега считается через wcswidth.
  • Убран скрытый алиас --follow-symlinks (вводил в заблуждение:
    он не следует по симлинкам-каталогам).
"""

import argparse
import curses
import errno
import fcntl
import hashlib
import json
import math
import os
import queue
import re
import shutil
import stat as stat_mod
import subprocess
import sys
import tempfile
import threading
import time
import zlib
from collections import defaultdict, namedtuple
from pathlib import Path

try:
    from wcwidth import wcswidth
except ImportError:
    def wcswidth(s):
        return len(s)

__version__ = "1.5.5"

HOME = Path.home()
CONFIG_DIR = HOME / ".m"
TRASH_DIR = CONFIG_DIR / "trash"
TRASH_META = TRASH_DIR / ".meta.json"
TRASH_META_LOCK = TRASH_DIR / ".meta.lock"

MIN_SIZE_DEFAULT = 1
PARTIAL_BYTES = 64 * 1024
HASH_CHUNK = 1 << 20
TRASH_NAME_LIMIT = 200
SCAN_PROGRESS_EVERY = 200
EXTERNAL_TIMEOUT = 30
MAX_MARKED_SIZE_CACHE = 10000
MAX_SEEN_INODES = 500000
MAX_GET_WCH_ERRORS = 10

# Сигнал через progress-канал (не является количеством файлов).
PROGRESS_INODE_LIMIT = -1

# Минимальное время (в секундах), которое осиротевший файл должен
# пролежать в корзине, прежде чем он будет удалён. Защищает от
# удаления файлов, которые сейчас перемещает другой процесс
# (или мы сами, если процесс упал между os.link и записью meta).
ORPHAN_GRACE_SECONDS = 300

DEFAULT_SKIP_DIRS = frozenset({
    ".git", ".hg", ".svn",
    "node_modules", "__pycache__", ".venv", "venv",
    ".cache", ".npm", ".cargo", ".rustup",
    ".m",
})

SKIP_HIDDEN_DEFAULT = True

HASH_ALGOS = {
    "blake2b": lambda: hashlib.blake2b(digest_size=16),
    "sha256": lambda: hashlib.sha256(),
    "md5": lambda: hashlib.md5(),
}

FileInfo = namedtuple("FileInfo", ["path", "size", "mtime"])
DupGroup = namedtuple("DupGroup", ["size", "digest", "files"])

# Набор errno, при которых жёсткую ссылку создать нельзя и нужно
# переходить к копированию: кросс-устройство, отсутствие поддержки
# ссылок (FAT/exFAT/FUSE), достижение лимита ссылок, отсутствие
# системного вызова в ядре.
_LINK_FALLBACK_ERRNOS = {
    errno.EXDEV,
    errno.EPERM,
    errno.EMLINK,
    errno.ENOSYS,
}
for _name in ("ENOTSUP", "EOPNOTSUPP"):
    _val = getattr(errno, _name, None)
    if _val is not None:
        _LINK_FALLBACK_ERRNOS.add(_val)
del _name, _val

# --------------------------------------------------------------------------
#  Утилиты
# --------------------------------------------------------------------------

def _sanitize_display(s):
    if not s:
        return s
    out = None
    for i, c in enumerate(s):
        cp = ord(c)
        if cp < 0x20 or cp == 0x7f or 0x80 <= cp <= 0x9f or cp in (
            0x200b, 0x200e, 0x200f, 0x2028, 0x2029, 0xfeff
        ) or 0xd800 <= cp <= 0xdfff:
            if out is None:
                out = list(s[:i])
            out.append('?')
        elif out is not None:
            out.append(c)
    return ''.join(out) if out is not None else s

def _clip_by_width(s, max_cols):
    """Обрезает строку по количеству колонок (wcwidth).

    Комбинирующие/неизвестные символы (wcswidth(ch) < 0) сохраняются
    с нулевой шириной: их потеря сместила бы базовые символы и
    испортила бы строку.
    """
    if not s:
        return s
    cols = 0
    out = []
    for ch in s:
        w = wcswidth(ch)
        if w < 0:
            w = 0
        if cols + w > max_cols:
            break
        out.append(ch)
        cols += w
    return ''.join(out)

def _truncate_utf8(s, max_bytes):
    """Обрезает строку до max_bytes байт UTF-8, не разрывая символы."""
    if not s or max_bytes <= 0:
        return "" if s else s
    b = s.encode("utf-8", "surrogatepass")
    if len(b) <= max_bytes:
        return s
    b = b[:max_bytes]
    return b.decode("utf-8", "ignore")

def atomic_write_text(path, text, encoding="utf-8", nofollow=False):
    """Атомарная запись с сохранением прав и без разрушения симлинков.

    Если nofollow=True, запись в симлинк запрещена (бросается OSError).
    """
    path = Path(path)

    if path.is_symlink():
        if nofollow:
            raise OSError(f"запись через симлинк запрещена: {path}")
        try:
            resolved = path.resolve(strict=True)
        except (OSError, RuntimeError):
            raise OSError(f"не удалось разрешить симлинк: {path}")
        path = resolved

    if not path.parent.exists():
        path.parent.mkdir(parents=True, exist_ok=True)

    old_mode = None
    try:
        if path.exists():
            old_mode = path.stat().st_mode & 0o777
    except OSError:
        old_mode = None

    fd, tmp = tempfile.mkstemp(
        prefix="." + path.name + ".",
        suffix=".mdupe.tmp",
        dir=str(path.parent),
    )
    try:
        with os.fdopen(fd, "w", encoding=encoding) as fh:
            fh.write(text)
            fh.flush()
            os.fsync(fh.fileno())
        if old_mode is not None:
            try:
                os.chmod(tmp, old_mode)
            except OSError:
                pass
        os.replace(tmp, str(path))
        try:
            dir_fd = os.open(str(path.parent), os.O_DIRECTORY)
            try:
                os.fsync(dir_fd)
            finally:
                os.close(dir_fd)
        except OSError:
            pass
    except Exception:
        try:
            os.close(fd)
        except OSError:
            pass
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise

def human_size(n):
    try:
        n = int(n)
    except Exception:
        return str(n)
    if n < 0:
        return f"-{human_size(-n)}"
    for unit, div in (("TB", 1 << 40), ("GB", 1 << 30),
                      ("MB", 1 << 20), ("KB", 1 << 10)):
        if n >= div:
            return f"{n / div:.1f} {unit}"
    return f"{n} B"

def parse_size(s):
    if s is None:
        raise ValueError("пустая строка")
    s = str(s).strip().lower().replace(" ", "")
    if not s:
        raise ValueError("пустая строка")
    if re.search(r'\d[eE]\d', s):
        raise ValueError("научная нотация не поддерживается")
    mult = 1
    for suffix, m in (("tb", 1 << 40), ("gb", 1 << 30), ("mb", 1 << 20),
                      ("kb", 1 << 10), ("t", 1 << 40), ("g", 1 << 30),
                      ("m", 1 << 20), ("k", 1 << 10), ("b", 1)):
        if s.endswith(suffix):
            s = s[:-len(suffix)]
            mult = m
            break
    if not s:
        raise ValueError("нет числовой части")
    try:
        val = float(s)
    except ValueError:
        raise ValueError(f"не число: {s!r}")
    if not math.isfinite(val):
        raise ValueError("бесконечность недопустима")
    result = int(val * mult + 0.5)
    if result < 1:
        raise ValueError("размер должен быть положительным (> 0)")
    return result

def _short_path(path, max_len):
    """Сокращает путь по ШИРИНЕ в колонках терминала (wcswidth).

    max_len задаётся в колонках — так его трактуют все вызывающие.
    Для CJK/широких символов len() != wcswidth(), поэтому старая
    реализация на len() могла выдать строку шире max_len.
    """
    s = str(path)
    max_len = max(1, int(max_len))
    if not s:
        return s
    width = wcswidth(s)
    if width < 0:
        width = len(s)
    if width <= max_len:
        return s
    if max_len <= 1:
        # Не помещается даже многоточие — отдаём последний символ.
        return s[-1:]
    budget = max_len - 1
    cols = 0
    out = []
    for ch in reversed(s):
        w = wcswidth(ch)
        if w < 0:
            w = 0
        if cols + w > budget:
            break
        out.append(ch)
        cols += w
    if not out:
        return "…"
    return "…" + ''.join(reversed(out))

# --------------------------------------------------------------------------
#  Корзина (совместима с M)
# --------------------------------------------------------------------------

TRASH_META_VERSION = 2

def _cleanup_orphaned_trash(meta):
    """Удаляет файлы, оставшиеся после сбоя (нет в meta).

    Вызывается только под блокировкой meta, с уже загруженным
    словарём meta. Чтобы не удалить файл, который прямо сейчас
    перемещается другим процессом (или нами, если предыдущий запуск
    упал между os.link и записью meta), пропускаются записи, чей
    st_ctime моложе ORPHAN_GRACE_SECONDS.
    """
    if not TRASH_DIR.is_dir():
        return
    now = time.time()
    for entry in TRASH_DIR.iterdir():
        if entry.name.startswith('.'):
            continue
        if entry.name in meta:
            continue
        try:
            st = entry.lstat()
        except OSError:
            continue
        if now - st.st_ctime < ORPHAN_GRACE_SECONDS:
            # Возможно, файл ещё «в полёте» — не трогаем.
            continue
        try:
            entry.unlink()
        except OSError:
            pass

def _acquire_lock(lock_path, timeout=10):
    try:
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o644)
    except OSError:
        return None
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return fd
        except OSError as e:
            if e.errno == errno.EINTR:
                time.sleep(0.01)
                continue
            if e.errno not in (errno.EAGAIN, errno.EACCES):
                os.close(fd)
                return None
            time.sleep(0.05)
    try:
        os.close(fd)
    except OSError:
        pass
    return None

def _release_lock(fd):
    if fd is None:
        return
    try:
        fcntl.flock(fd, fcntl.LOCK_UN)
    except OSError:
        pass
    try:
        os.close(fd)
    except OSError:
        pass

def _load_trash_meta():
    """Возвращает dict {trash_name: original_abs_path}."""
    if not TRASH_META.is_file():
        return {}
    try:
        data = json.loads(TRASH_META.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            items = data.get("items")
            if isinstance(items, dict):
                return {k: v for k, v in items.items()
                        if isinstance(k, str) and isinstance(v, str)}
            # Обратная совместимость: meta без обёртки.
            return {k: v for k, v in data.items()
                    if isinstance(k, str) and isinstance(v, str)
                    and k not in ("version", "items")}
    except Exception:
        try:
            broken = TRASH_META.with_name(
                f"{TRASH_META.name}.broken.{int(time.time())}"
            )
            TRASH_META.rename(broken)
        except OSError:
            pass
        return {}
    return {}

def _save_trash_meta(data, lock_fd=None):
    own_lock = False
    fd = lock_fd
    if fd is None:
        fd = _acquire_lock(TRASH_META_LOCK)
        if fd is None:
            return False
        own_lock = True
    try:
        TRASH_DIR.mkdir(parents=True, exist_ok=True)
        payload = {"version": TRASH_META_VERSION, "items": data}
        atomic_write_text(
            TRASH_META,
            json.dumps(payload, indent=2, ensure_ascii=True),
            nofollow=True,
        )
        return True
    except Exception:
        return False
    finally:
        if own_lock:
            _release_lock(fd)

def _unique_trash_path(name):
    base = f"{time.time_ns()}"
    max_name_len = TRASH_NAME_LIMIT - len(base) - 1
    if max_name_len < 1:
        max_name_len = 1
    if len(name.encode("utf-8", "surrogatepass")) > max_name_len:
        suffix = str(zlib.crc32(name.encode("utf-8", "surrogatepass"))
                     & 0xffffffff)
        keep = max(0, max_name_len - len(suffix) - 1)
        truncated = _truncate_utf8(name, keep)
        if truncated:
            name = truncated + "_" + suffix
        else:
            # Настолько жёсткий лимит, что даже префикс не влезает —
            # жертвуем им в пользу суффикса (он уникализирует).
            name = suffix
    candidate = TRASH_DIR / f"{base}_{name}"
    n = 1
    while os.path.lexists(str(candidate)):
        if n > 1000:
            raise OSError("Не удалось подобрать уникальное имя в корзине")
        candidate = TRASH_DIR / f"{base}_{n}_{name}"
        n += 1
    return candidate

def _copy_to_trash(src, dst):
    """Резервный путь: копирование в корзину с последующим удалением src.

    Симлинк воссоздаётся как симлинк (без разыменования).
    Возвращает (True, None) либо (False, exception).
    """
    try:
        if os.path.islink(str(src)):
            linkto = os.readlink(str(src))
            os.symlink(linkto, str(dst))
            os.unlink(str(src))
        else:
            fd = os.open(str(dst), os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
            try:
                with os.fdopen(fd, 'wb') as out:
                    with open(str(src), 'rb') as inp:
                        shutil.copyfileobj(inp, out, length=HASH_CHUNK)
                shutil.copystat(str(src), str(dst), follow_symlinks=False)
            except Exception:
                try:
                    os.unlink(str(dst))
                except OSError:
                    pass
                raise
            os.unlink(str(src))
        return True, None
    except Exception as e:
        try:
            os.unlink(str(dst))
        except OSError:
            pass
        return False, e

def _move_file_to_trash(src, dst):
    """Перемещает файл в корзину.

    На одном устройстве и при поддержке ФС используется жёсткая ссылка
    (os.link с follow_symlinks=False) + os.unlink. Это атомарно
    исключает перезапись существующего файла в корзине и корректно
    сохраняет симлинки.

    При кросс-устройственном перемещении, на ФС без поддержки жёстких
    ссылок (FAT/exFAT/некоторые FUSE) и при достижении лимита ссылок
    используется копирование.

    Возвращает (True, None) при успехе или (False, exception) при
    невозможности переместить файл.
    """
    linked = False
    try:
        os.link(str(src), str(dst), follow_symlinks=False)
        linked = True
    except NotImplementedError:
        linked = False
    except OSError as e:
        if e.errno not in _LINK_FALLBACK_ERRNOS:
            # Например, EEXIST — пробрасываем наверх, вызывающий
            # повторит попытку с новым именем.
            return False, e
        linked = False

    if linked:
        try:
            os.unlink(str(src))
            return True, None
        except Exception as e:
            # Откат: убираем только что созданную жёсткую ссылку.
            try:
                os.unlink(str(dst))
            except OSError:
                pass
            return False, e

    return _copy_to_trash(src, dst)

def trash_files(paths):
    TRASH_DIR.mkdir(parents=True, exist_ok=True)
    lock_fd = _acquire_lock(TRASH_META_LOCK)
    if lock_fd is None:
        return 0, ["не удалось получить блокировку meta"]
    try:
        meta = _load_trash_meta()
        _cleanup_orphaned_trash(meta)
        ok = 0
        errors = []
        since_save = 0
        save_fail_count = 0
        for p_str in paths:
            if save_fail_count >= 3:
                errors.append(
                    "meta: слишком много ошибок записи, "
                    "перемещение остановлено"
                )
                break
            src = Path(p_str)
            try:
                if not os.path.lexists(str(src)):
                    errors.append(f"{src}: не существует")
                    continue
                if src.is_dir() and not src.is_symlink():
                    errors.append(f"{src}: директория (используйте удаление)")
                    continue
                try:
                    original_abs = os.path.abspath(str(src))
                except (OSError, RuntimeError):
                    original_abs = str(src)
                moved = False
                for _ in range(10):
                    dst = _unique_trash_path(src.name)
                    ok_move, err = _move_file_to_trash(src, dst)
                    if ok_move:
                        moved = True
                        break
                    # Повторяем только на гонку по имени.
                    if isinstance(err, OSError) and err.errno == errno.EEXIST:
                        continue
                    raise err
                if not moved:
                    errors.append(f"{src}: не удалось подобрать имя в корзине")
                    continue
                meta[dst.name] = original_abs
                ok += 1
                since_save += 1
                if since_save >= 10:
                    saved = _save_trash_meta(meta, lock_fd)
                    if saved:
                        since_save = 0
                        save_fail_count = 0
                    else:
                        save_fail_count += 1
                        errors.append("meta: не удалось сохранить")
            except Exception as e:
                errors.append(f"{src}: {e}")
        if since_save > 0 or ok > 0:
            saved = _save_trash_meta(meta, lock_fd)
            if not saved:
                errors.append("meta: не удалось сохранить")
        return ok, errors
    finally:
        _release_lock(lock_fd)

def delete_files(paths):
    """Безвозвратно удаляет файлы и каталоги.

    Возвращает (ok, errors). Каталог засчитывается успешным ТОЛЬКО
    если shutil.rmtree завершился без исключения. Никаких
    «глушителей» ошибок: иначе пользователь получил бы ложное
    «Удалено: N», а часть файлов осталась бы на диске.
    """
    ok = 0
    errors = []
    for p_str in paths:
        p = Path(p_str)
        try:
            if p.is_symlink():
                p.unlink()
            elif p.is_dir():
                shutil.rmtree(p)
            else:
                p.unlink()
            ok += 1
        except Exception as e:
            errors.append(f"{p}: {e}")
    return ok, errors

# --------------------------------------------------------------------------
#  Поиск дубликатов
# --------------------------------------------------------------------------

def _hash_file(path, max_bytes=None, algo="blake2b"):
    if max_bytes is not None and max_bytes <= 0:
        return None
    try:
        h = HASH_ALGOS[algo]()
    except KeyError:
        raise ValueError(f"неизвестный алгоритм хеширования: {algo}")
    try:
        st_before = os.stat(path)
        with open(path, "rb") as fh:
            remaining = max_bytes
            while True:
                if remaining is None:
                    chunk = fh.read(HASH_CHUNK)
                else:
                    if remaining <= 0:
                        break
                    chunk = fh.read(min(HASH_CHUNK, remaining))
                if not chunk:
                    break
                h.update(chunk)
                if remaining is not None:
                    remaining -= len(chunk)
        st_after = os.stat(path)
        if (st_before.st_size != st_after.st_size
                or st_before.st_mtime_ns != st_after.st_mtime_ns):
            return None
    except OSError:
        return None
    return h.digest()

def scan_duplicates(root, min_size=MIN_SIZE_DEFAULT,
                    progress=None, cancel=None,
                    skip_dirs=None, skip_hidden=SKIP_HIDDEN_DEFAULT,
                    include_symlink_files=False,
                    algo="blake2b"):
    root = Path(root)
    if skip_dirs is None:
        skip_dirs = DEFAULT_SKIP_DIRS

    try:
        trash_abs = os.path.realpath(str(TRASH_DIR))
    except (OSError, RuntimeError):
        trash_abs = None

    by_size = defaultdict(list)
    seen = 0
    seen_inodes = set()
    inode_limit_warned = False

    for dirpath, dirnames, filenames in os.walk(str(root), followlinks=False):
        if cancel and cancel():
            return []

        abs_dir = os.path.realpath(dirpath)
        if trash_abs and abs_dir == trash_abs:
            dirnames[:] = []
            continue

        if skip_hidden:
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
        if skip_dirs:
            dirnames[:] = [d for d in dirnames if d not in skip_dirs]

        safe = []
        for d in dirnames:
            full = os.path.join(dirpath, d)
            try:
                if os.path.islink(full):
                    continue
            except OSError:
                continue
            safe.append(d)
        dirnames[:] = safe

        for fn in filenames:
            p = Path(dirpath) / fn
            try:
                is_symlink = p.is_symlink()
                if is_symlink and not include_symlink_files:
                    continue
                lst = p.lstat()

                # Не-симлинки: пропускаем всё, что не является
                # обычным файлом (FIFO, сокеты, устройства). Открытие
                # FIFO на чтение навсегда заблокировало бы поток.
                if not is_symlink and not stat_mod.S_ISREG(lst.st_mode):
                    continue

                inode = (lst.st_dev, lst.st_ino)
                if inode in seen_inodes:
                    continue
                if len(seen_inodes) < MAX_SEEN_INODES:
                    seen_inodes.add(inode)
                elif not inode_limit_warned:
                    inode_limit_warned = True
                    if progress:
                        progress(PROGRESS_INODE_LIMIT)

                if is_symlink:
                    st = p.stat()
                    # Цель симлинка тоже должна быть обычным файлом.
                    if not stat_mod.S_ISREG(st.st_mode):
                        continue
                else:
                    st = lst
            except OSError:
                continue
            if st.st_size < min_size:
                continue
            by_size[st.st_size].append(FileInfo(p, st.st_size, st.st_mtime))
            seen += 1
            if progress and (seen % SCAN_PROGRESS_EVERY == 0 or seen == 1):
                progress(seen)

    candidates = [files for files in by_size.values() if len(files) > 1]
    by_size.clear()

    # done_partial считает только большие файлы, реально прошедшие
    # частичное хеширование. small_files не учитываем здесь — они
    # попадут в done_full на следующей стадии.
    total_partial = sum(len(f) for f in candidates)
    done_partial = 0
    partial = defaultdict(list)
    small_files = []
    for files in candidates:
        for fi in files:
            if cancel and cancel():
                return []
            if fi.size <= PARTIAL_BYTES:
                small_files.append(fi)
                continue
            h = _hash_file(fi.path, PARTIAL_BYTES, algo)
            done_partial += 1
            if progress and total_partial and done_partial % SCAN_PROGRESS_EVERY == 0:
                progress(seen + done_partial)
            if h is None:
                continue
            partial[(fi.size, h)].append(fi)
    candidates = [files for files in partial.values() if len(files) > 1]
    partial.clear()

    total_full = sum(len(f) for f in candidates) + len(small_files)
    done_full = 0
    full = defaultdict(list)
    for fi in small_files:
        if cancel and cancel():
            return []
        h = _hash_file(fi.path, None, algo)
        done_full += 1
        if progress and total_full and done_full % SCAN_PROGRESS_EVERY == 0:
            progress(seen + done_partial + done_full)
        if h is None:
            continue
        full[(fi.size, h)].append(fi)
    for files in candidates:
        for fi in files:
            if cancel and cancel():
                return []
            h = _hash_file(fi.path, None, algo)
            done_full += 1
            if progress and total_full and done_full % SCAN_PROGRESS_EVERY == 0:
                progress(seen + done_partial + done_full)
            if h is None:
                continue
            full[(fi.size, h)].append(fi)

    groups = []
    for (size, digest), files in full.items():
        if len(files) < 2:
            continue
        files.sort(key=lambda f: (f.mtime, str(f.path)))
        groups.append(DupGroup(size=size, digest=digest, files=files))

    groups.sort(key=lambda g: (-(g.size * (len(g.files) - 1)), -g.size))
    return groups

# --------------------------------------------------------------------------
#  Headless-вывод
# --------------------------------------------------------------------------

def _print_groups(groups):
    if not groups:
        print("Дубликатов не найдено.")
        return
    total_waste = 0
    total_files = 0
    for i, g in enumerate(groups, 1):
        waste = g.size * (len(g.files) - 1)
        total_waste += waste
        total_files += len(g.files)
        print(f"#{i}  {human_size(g.size)} × {len(g.files)}  "
              f"(избыточно {human_size(waste)})")
        for f in g.files:
            print(f"    {_sanitize_display(str(f.path))}")
        print()
    print(f"Всего: групп {len(groups)}, файлов {total_files}, "
          f"избыточно {human_size(total_waste)}")

def _write_json(out_path, root, min_size, groups):
    out = Path(out_path).expanduser()
    if out.is_dir():
        raise IsADirectoryError(f"это директория: {out}")
    if out.is_symlink():
        raise OSError(f"нельзя перезаписать симлинк: {out}")
    data = {
        "version": __version__,
        "root": str(root),
        "min_size": min_size,
        "scanned_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "groups": [
            {
                "size": g.size,
                "hash": g.digest.hex(),
                "files": [{"path": str(f.path), "mtime": f.mtime}
                          for f in g.files],
            }
            for g in groups
        ],
    }
    atomic_write_text(out, json.dumps(data, indent=2, ensure_ascii=True))

# --------------------------------------------------------------------------
#  TUI
# --------------------------------------------------------------------------

KEY_ENTER = getattr(curses, "KEY_ENTER", 343)

class MdupeApp:
    def __init__(self, stdscr, root, min_size, no_color=False,
                 skip_dirs=None, skip_hidden=SKIP_HIDDEN_DEFAULT,
                 include_symlink_files=False,
                 algo="blake2b"):
        self.stdscr = stdscr
        try:
            self.root = Path(root).resolve()
        except (OSError, RuntimeError):
            self.root = Path(os.path.abspath(str(root)))
        self.min_size = min_size
        self.no_color = no_color
        self.skip_dirs = skip_dirs if skip_dirs is not None else DEFAULT_SKIP_DIRS
        self.skip_hidden = skip_hidden
        self.include_symlink_files = include_symlink_files
        self.algo = algo

        self.running = True
        self.message = ""

        self.groups = []
        self.group_idx = 0
        self.file_idx = 0
        self.focus = "groups"
        self.marked = set()

        self.scanning = False
        self.scan_status = ""
        self._scan_cancel_event = threading.Event()
        self._scan_queue = queue.Queue()
        self._scan_thread = None
        self._scan_progress_lock = threading.Lock()
        self.last_scan_duration = 0.0

        self._marked_size_cache = {}
        self._total_waste_cache = None
        self._opener_cache = None

        self.prompt_active = False
        self.prompt_text = ""
        self.prompt_callback = None

        self._get_wch_errors = 0

        self._init_colors()

    def _init_colors(self):
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

    def addstr(self, y, x, text, attr=0):
        try:
            h, w = self.stdscr.getmaxyx()
            if y < 0 or y >= h or x < 0 or x >= w:
                return
            s = _sanitize_display(str(text))
            if not s:
                return
            avail = w - x - 1
            if avail <= 0:
                return
            s = _clip_by_width(s, avail)
            if not s:
                return
            self.stdscr.addstr(y, x, s, attr)
        except curses.error:
            pass
        except Exception:
            pass

    def set_message(self, msg):
        self.message = _sanitize_display(str(msg)) if msg else ""

    def _start_scan(self):
        if self._scan_thread is not None and self._scan_thread.is_alive():
            self._scan_cancel_event.set()
            self._scan_thread.join(timeout=3.0)
            if self._scan_thread.is_alive():
                # Даже если поток жив, открепляем его: следующий скан
                # получит свежие очередь и event, а старый результат
                # уже неактуален.
                self._scan_thread = None
                self._scan_queue = queue.Queue()
                self._scan_cancel_event = threading.Event()
                self.scanning = False
                self.set_message(
                    "Предыдущее сканирование не завершилось за 3 с"
                )
                return
            self._scan_thread = None

        self._scan_cancel_event = threading.Event()
        self._scan_queue = queue.Queue()

        self.scanning = True
        self.scan_status = "Сканирование…"
        self.last_scan_duration = 0.0

        cancel_event = self._scan_cancel_event
        out_queue = self._scan_queue

        root = self.root
        min_size = self.min_size
        skip_dirs = self.skip_dirs
        skip_hidden = self.skip_hidden
        include_symlink_files = self.include_symlink_files
        algo = self.algo

        def _progress(n):
            out_queue.put(("progress", n, 0.0))

        def _run():
            try:
                t0 = time.monotonic()
                groups = scan_duplicates(
                    root, min_size,
                    progress=_progress,
                    cancel=cancel_event.is_set,
                    skip_dirs=skip_dirs,
                    skip_hidden=skip_hidden,
                    include_symlink_files=include_symlink_files,
                    algo=algo,
                )
                duration = time.monotonic() - t0
                out_queue.put(("ok", groups, duration))
            except Exception as e:
                out_queue.put(("err", e, 0.0))

        try:
            self._scan_thread = threading.Thread(target=_run, daemon=True)
            self._scan_thread.start()
        except Exception as e:
            self.scanning = False
            self._scan_thread = None
            self.set_message(f"Не удалось запустить сканирование: {e}")

    def _poll_scan(self):
        while True:
            try:
                msg = self._scan_queue.get_nowait()
            except queue.Empty:
                break
            kind = msg[0]
            if kind == "progress":
                if msg[1] == PROGRESS_INODE_LIMIT:
                    self.set_message(
                        "Достигнут лимит inode — возможны ложные дубликаты "
                        "жёстких ссылок"
                    )
                else:
                    with self._scan_progress_lock:
                        self.scan_status = f"Сканирование… файлов: {msg[1]}"
            elif kind == "ok":
                self.scanning = False
                self._scan_thread = None
                self.groups = msg[1]
                self._total_waste_cache = None
                self.last_scan_duration = msg[2]
                self.group_idx = 0
                self.file_idx = 0
                self.marked.clear()
                self._marked_size_cache.clear()
                self.set_message(
                    f"Найдено групп: {len(self.groups)} "
                    f"за {msg[2]:.1f} с"
                )
            elif kind == "err":
                self.scanning = False
                self._scan_thread = None
                self.last_scan_duration = 0.0
                self.set_message(f"Ошибка сканирования: {msg[1]}")

        if (self.scanning and self._scan_thread is not None
                and not self._scan_thread.is_alive()):
            self.scanning = False
            self._scan_thread = None
            self.set_message("Сканирование прервано.")

    def current_group(self):
        if 0 <= self.group_idx < len(self.groups):
            return self.groups[self.group_idx]
        return None

    def _file_size(self, p):
        key = str(p)
        if key in self._marked_size_cache:
            return self._marked_size_cache[key]
        try:
            if os.path.islink(key):
                sz = os.stat(key).st_size
            else:
                sz = os.lstat(key).st_size
        except OSError:
            sz = 0
        if len(self._marked_size_cache) >= MAX_MARKED_SIZE_CACHE:
            self._marked_size_cache.clear()
        self._marked_size_cache[key] = sz
        return sz

    def _total_waste(self):
        if self._total_waste_cache is None:
            self._total_waste_cache = sum(
                g.size * (len(g.files) - 1) for g in self.groups
            )
        return self._total_waste_cache

    def _marked_waste(self):
        return sum(self._file_size(p) for p in self.marked)

    def _find_opener(self):
        if self._opener_cache is not None:
            return self._opener_cache
        for cmd in ("termux-open", "xdg-open", "open"):
            if shutil.which(cmd):
                self._opener_cache = cmd
                return cmd
        self._opener_cache = ""
        return ""

    def _move(self, delta):
        if self.focus == "groups":
            if not self.groups:
                return
            new = max(0, min(len(self.groups) - 1, self.group_idx + delta))
            if new != self.group_idx:
                self.group_idx = new
                self.file_idx = 0
        else:
            grp = self.current_group()
            if grp is None:
                return
            self.file_idx = max(0, min(len(grp.files) - 1,
                                       self.file_idx + delta))

    def _switch_focus(self):
        self.focus = "files" if self.focus == "groups" else "groups"
        if self.focus == "files":
            self.file_idx = 0

    def _toggle_mark(self):
        if self.focus == "groups":
            self._mark_all_but_current()
            return
        grp = self.current_group()
        if grp is None:
            return
        fi = grp.files[self.file_idx]
        p = str(fi.path)
        if p in self.marked:
            self.marked.discard(p)
            self._marked_size_cache.pop(p, None)
        else:
            self.marked.add(p)
        if self.file_idx < len(grp.files) - 1:
            self.file_idx += 1

    def _mark_all_but_current(self):
        grp = self.current_group()
        if grp is None:
            return
        keep_idx = 0
        for i, fi in enumerate(grp.files):
            p = str(fi.path)
            if i == keep_idx:
                self.marked.discard(p)
                self._marked_size_cache.pop(p, None)
            else:
                self.marked.add(p)
        self.set_message(
            f"Оставлен один (старший), помечено {len(grp.files) - 1}"
        )

    def _unmark_group(self):
        grp = self.current_group()
        if grp is None:
            return
        for fi in grp.files:
            p = str(fi.path)
            self.marked.discard(p)
            self._marked_size_cache.pop(p, None)
        self.set_message("Отметки группы сняты.")

    def _do_trash(self):
        if not self.marked:
            self.set_message("Нет помеченных файлов.")
            return
        paths = [p for p in self.marked
                 if os.path.lexists(p) and not os.path.isdir(p)]
        if not paths:
            self.set_message("Помеченные файлы больше не существуют "
                             "или являются директориями.")
            self.marked.clear()
            self._marked_size_cache.clear()
            return
        n = len(paths)
        freed = sum(self._file_size(p) for p in paths)
        # refresh отдельно: сбой отрисовки не должен отменять операцию.
        try:
            self.stdscr.refresh()
        except Exception:
            pass
        try:
            ok, errs = trash_files(paths)
        except Exception as e:
            self.set_message(f"Ошибка корзины: {e}")
            return
        failed = set()
        for p in paths:
            if os.path.lexists(p):
                failed.add(p)
        self.marked = failed
        self._marked_size_cache.clear()
        if errs:
            self.set_message(f"В корзину: {ok} из {n}, ошибок: {len(errs)}. "
                             f"Освобождено ≈ {human_size(freed)}")
        else:
            self.set_message(
                f"В корзину: {ok}, освобождено ≈ {human_size(freed)} "
                f"(восстановить — M → R)"
            )
        self._prune_groups()

    def _do_delete(self):
        if not self.marked:
            self.set_message("Нет помеченных файлов.")
            return
        paths = [p for p in self.marked if os.path.lexists(p)]
        if not paths:
            self.set_message("Помеченные файлы больше не существуют.")
            self.marked.clear()
            self._marked_size_cache.clear()
            return
        n = len(paths)
        freed = sum(self._file_size(p) for p in paths)

        def cb(ans, paths=paths, n=n, freed=freed):
            if ans != 'y':
                self.set_message("Отменено.")
                return
            try:
                ok, errs = delete_files(paths)
            except Exception as e:
                self.set_message(f"Ошибка удаления: {e}")
                return
            self.marked.clear()
            self._marked_size_cache.clear()
            if errs:
                self.set_message(f"Удалено: {ok} из {n}, ошибок: {len(errs)}.")
            else:
                self.set_message(
                    f"Удалено навсегда: {ok} "
                    f"(освобождено ≈ {human_size(freed)})"
                )
            self._prune_groups()

        self.prompt_callback = cb
        self.prompt_text = (
            f"Удалить БЕЗВОЗВРАТНО {n} файлов "
            f"({human_size(freed)})? [y/д, n/н]: "
        )
        self.prompt_active = True

    def _prune_groups(self):
        new_groups = []
        for g in self.groups:
            remaining = [f for f in g.files
                         if os.path.lexists(str(f.path))]
            if len(remaining) > 1:
                new_groups.append(g._replace(files=remaining))
        self.groups = new_groups
        self._total_waste_cache = None
        if not self.groups:
            self.group_idx = 0
            self.file_idx = 0
        else:
            self.group_idx = min(self.group_idx, len(self.groups) - 1)
            grp = self.current_group()
            if grp and self.file_idx >= len(grp.files):
                self.file_idx = max(0, len(grp.files) - 1)

    def _run_external(self, argv):
        def_ok = False
        end_ok = False
        try:
            curses.def_prog_mode()
            def_ok = True
        except Exception:
            pass
        if def_ok:
            try:
                curses.endwin()
                end_ok = True
            except Exception:
                end_ok = False
        try:
            subprocess.run(argv, timeout=EXTERNAL_TIMEOUT)
        except subprocess.TimeoutExpired:
            self.set_message(f"Команда не завершилась за {EXTERNAL_TIMEOUT} с")
        except KeyboardInterrupt:
            self.set_message("Команда прервана.")
        except Exception as e:
            self.set_message(f"Не удалось запустить: {e}")
        finally:
            if def_ok and end_ok:
                try:
                    curses.reset_prog_mode()
                except Exception:
                    pass
            try:
                self.stdscr.refresh()
            except Exception:
                pass

    def _open_file(self):
        if self.focus == "groups":
            self.focus = "files"
            self.file_idx = 0
            return
        grp = self.current_group()
        if grp is None:
            return
        fi = grp.files[self.file_idx]
        cmd = self._find_opener()
        if cmd:
            self._run_external([cmd, str(fi.path)])
        else:
            self.set_message(
                f"Нет opener. Путь: {_short_path(fi.path, 60)}"
            )

    def _handle_prompt(self, key):
        if key == curses.KEY_RESIZE:
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
        elif key == 27 or key in (10, 13, KEY_ENTER):
            val = 'n'
        else:
            return
        cb = self.prompt_callback
        self.prompt_active = False
        self.prompt_text = ""
        self.prompt_callback = None
        if cb:
            try:
                cb(val)
            except Exception as e:
                self.set_message(f"Ошибка: {e}")

    def handle_key(self, key):
        if key in (ord('q'), 27):
            self.running = False
        elif key == ord('?'):
            self._show_help()
        elif key == ord('r'):
            self._start_scan()
        elif key == 9 or key == getattr(curses, 'KEY_BTAB', -1):
            self._switch_focus()
        elif key in (curses.KEY_UP, ord('k')):
            self._move(-1)
        elif key in (curses.KEY_DOWN, ord('j')):
            self._move(1)
        elif key == curses.KEY_PPAGE:
            self._move(-10)
        elif key == curses.KEY_NPAGE:
            self._move(10)
        elif key == ord(' '):
            self._toggle_mark()
        elif key == ord('a'):
            self._mark_all_but_current()
        elif key == ord('A'):
            self._unmark_group()
        elif key == ord('d'):
            self._do_trash()
        elif key == ord('D'):
            self._do_delete()
        elif key in {10, 13, KEY_ENTER}:
            self._open_file()

    def _draw_scan_screen(self, h, w):
        with self._scan_progress_lock:
            status = self.scan_status
        self.addstr(2, 0, f" {status}", self.cp(3))
        self.addstr(4, 0, " Esc/q — отменить сканирование",
                    curses.A_DIM)
        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))

    def draw(self):
        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()

        self.addstr(0, 0, f" Mdupe v{__version__} — Дубликаты ",
                    self.cp(1, curses.A_BOLD))

        if self.scanning:
            self._draw_scan_screen(h, w)
            self.stdscr.refresh()
            return

        if h < 13 or w < 30:
            self.addstr(2, 0, " Терминал слишком мал.", self.cp(4))
            self.stdscr.refresh()
            return

        summary = (f" {_short_path(self.root, max(8, w - 40))}  "
                   f"групп: {len(self.groups)}  "
                   f"избыточно: {human_size(self._total_waste())}  "
                   f"помечено: {len(self.marked)}/"
                   f"{human_size(self._marked_waste())}")
        self.addstr(1, 0, summary, curses.A_DIM)

        header_h = 2
        footer_h = 2
        avail = h - header_h - footer_h
        groups_h = max(3, avail // 2)
        files_h = avail - groups_h - 2
        if files_h < 3:
            files_h = 3
            groups_h = avail - files_h - 2
            if groups_h < 3:
                groups_h = 3
                files_h = avail - groups_h - 2
                if files_h < 1:
                    files_h = 1

        g_attr = (self.cp(5, curses.A_BOLD) if self.focus == "groups"
                  else curses.A_BOLD)
        self.addstr(header_h, 0, " Группы ", g_attr)
        self._draw_groups(header_h + 1, groups_h, w)

        files_header_y = header_h + 1 + groups_h
        grp = self.current_group()
        if grp is not None:
            flabel = (f" Файлы группы "
                      f"({human_size(grp.size)}, {len(grp.files)}) ")
        else:
            flabel = " Файлы группы "
        f_attr = (self.cp(5, curses.A_BOLD) if self.focus == "files"
                  else curses.A_BOLD)
        self.addstr(files_header_y, 0, flabel, f_attr)
        self._draw_files(files_header_y + 1, files_h, w)

        if self.prompt_active:
            self.addstr(h - 2, 0, f" {self.prompt_text}",
                        self.cp(3, curses.A_BOLD))
        else:
            status = (" Space:отм  a:всё-кроме-1  A:снять  d:в корзину  "
                      "D:удалить  Enter:открыть  Tab:смена  r:перескан  "
                      "?:справка  q:выход ")
            self.addstr(h - 2, 0, status, curses.A_DIM)

        if self.message:
            self.addstr(h - 1, 0, self.message, self.cp(4))

        self.stdscr.refresh()

    def _draw_groups(self, y, height, w):
        if height <= 0:
            return
        if not self.groups:
            self.addstr(y, 0, " (дубликатов не найдено)", curses.A_DIM)
            return
        start = 0
        if self.group_idx >= height:
            start = self.group_idx - height + 1
        for i in range(start, min(start + height, len(self.groups))):
            g = self.groups[i]
            waste = g.size * (len(g.files) - 1)
            n_marked = sum(1 for f in g.files
                           if str(f.path) in self.marked)
            marker = "●" if n_marked > 0 else " "
            line = (f" {marker} [{human_size(g.size):>9}] × {len(g.files):<3}"
                    f" избыт. {human_size(waste):>9}")
            if i == self.group_idx and self.focus == "groups":
                attr = self.cp(5, curses.A_BOLD)
            elif i == self.group_idx:
                attr = curses.A_BOLD
            else:
                attr = curses.A_NORMAL
            self.addstr(y + (i - start), 0, line, attr)

    def _draw_files(self, y, height, w):
        if height <= 0:
            return
        grp = self.current_group()
        if grp is None:
            self.addstr(y, 0, " (нет группы)", curses.A_DIM)
            return
        start = 0
        if self.file_idx >= height:
            start = self.file_idx - height + 1
        avail = max(16, w - 8)
        for i in range(start, min(start + height, len(grp.files))):
            fi = grp.files[i]
            p = str(fi.path)
            is_marked = p in self.marked
            mark = "☑" if is_marked else "☐"
            tag = " ★стар." if i == 0 else ""
            tag_w = wcswidth(tag) if tag else 0
            if tag_w < 0:
                tag_w = len(tag)
            body = _short_path(p, max(10, avail - tag_w))
            line = f" {mark} {body}{tag}"
            if i == self.file_idx and self.focus == "files":
                attr = self.cp(5, curses.A_BOLD)
            elif is_marked:
                attr = self.cp(6, curses.A_BOLD)
            else:
                attr = curses.A_NORMAL
            self.addstr(y + (i - start), 0, line, attr)

    def _show_help(self):
        prev_timeout = None
        try:
            prev_timeout = self.stdscr.gettimeout()
        except Exception:
            pass

        self.stdscr.erase()
        h, w = self.stdscr.getmaxyx()
        lines = [
            f" Mdupe v{__version__} — справка ",
            "",
            " НАЗНАЧЕНИЕ:",
            "   Поиск и очистка дубликатов файлов. Использует общую с M",
            "   корзину ~/.m/trash — файлы восстанавливаются из M (R).",
            "",
            " УПРАВЛЕНИЕ:",
            "   ↑/↓ j/k     навигация",
            "   PgUp/PgDn   быстрая прокрутка",
            "   Tab         переключить группы ↔ файлы",
            "   Space       пометить (в группе — все кроме 1-го)",
            "   a  A        пометить всё кроме 1-го / снять отметки",
            "   d           переместить помеченные в корзину M",
            "   D           удалить помеченные БЕЗВОЗВРАТНО (с подтв.)",
            "   Enter       открыть файл (termux-open/xdg-open)",
            "   r           пересканировать",
            "   ?           справка",
            "   q / Esc     выход",
            "",
            " АЛГОРИТМ (3 ступени):",
            "   1) группировка по размеру",
            f"   2) частичный хеш (первые {PARTIAL_BYTES // 1024} KB)",
            "   3) полный хеш для уцелевших кандидатов",
            f"   Алгоритм: {self.algo}",
            "",
            " ПРИМЕЧАНИЕ О СИМЛИНКАХ:",
            "   При --include-symlink-files две ссылки на один файл",
            "   считаются дубликатами (размер/хеш берутся у цели).",
            "   Перемещение в корзину сохраняет симлинк как симлинк.",
            "",
            " CLI:",
            "   Mdupe [PATH] [-s SIZE] [--list] [--json FILE]",
            "         [--trash FILE...] [--exclude DIR]",
            "         [--include-symlink-files] [--hash ALGO]",
            "         [--no-skip-default] [--no-color]",
            "",
            " Нажми любую клавишу…",
        ]
        for i, line in enumerate(lines):
            if i >= h:
                break
            attr = (curses.A_BOLD if line and not line.startswith(" ")
                    and line.strip() else curses.A_NORMAL)
            self.addstr(i, 0, line, attr)
        self.stdscr.refresh()
        try:
            self.stdscr.timeout(-1)
            try:
                self.stdscr.get_wch()
            except AttributeError:
                self.stdscr.getch()
        except Exception:
            pass
        finally:
            if prev_timeout is not None:
                try:
                    self.stdscr.timeout(prev_timeout)
                except Exception:
                    self.stdscr.timeout(100)
            else:
                try:
                    self.stdscr.timeout(100)
                except Exception:
                    pass
            try:
                self.stdscr.keypad(True)
            except Exception:
                pass

    def run(self):
        try:
            curses.curs_set(0)
        except Exception:
            pass
        try:
            curses.set_escdelay(50)
        except Exception:
            pass
        try:
            self.stdscr.keypad(True)
        except Exception:
            pass

        self.stdscr.timeout(100)
        self._start_scan()

        while self.running:
            self._poll_scan()

            try:
                self.draw()
            except curses.error:
                pass
            except Exception as e:
                self.set_message(f"Ошибка отрисовки: {e}")

            try:
                key = self.stdscr.get_wch()
                self._get_wch_errors = 0
            except curses.error:
                continue
            except KeyboardInterrupt:
                break
            except Exception as e:
                self._get_wch_errors += 1
                if self._get_wch_errors >= MAX_GET_WCH_ERRORS:
                    self.set_message(
                        f"Слишком много ошибок ввода: {e}. Выход."
                    )
                    break
                self.set_message(f"Ошибка ввода: {e}")
                time.sleep(0.1)
                continue

            if isinstance(key, str):
                if len(key) == 0:
                    continue
                if len(key) == 1 and ord(key) < 128:
                    key = ord(key)
            elif not isinstance(key, int):
                continue

            if key == -1:
                continue
            if key == curses.KEY_RESIZE:
                continue

            if self.prompt_active:
                self._handle_prompt(key)
                continue

            if self.scanning:
                if key in (27, ord('q')):
                    self._scan_cancel_event.set()
                    self.running = False
                elif key == curses.KEY_RESIZE:
                    continue
                continue

            try:
                self.handle_key(key)
            except Exception as e:
                self.set_message(f"Ошибка: {e}")

# --------------------------------------------------------------------------
#  CLI
# --------------------------------------------------------------------------

def _build_argparser():
    p = argparse.ArgumentParser(
        prog="Mdupe",
        description=(f"Mdupe v{__version__} — поиск и очистка "
                     "дубликатов (спутник M)."),
    )
    p.add_argument("path", nargs="?", default=".",
                   help="Корневая папка (по умолчанию текущая)")
    p.add_argument("-s", "--min-size", default=str(MIN_SIZE_DEFAULT),
                   help="Минимальный размер файла: 4k, 1.5m, 2g …")
    p.add_argument("--list", action="store_true",
                   help="Напечатать группы в stdout и выйти")
    p.add_argument("--json", metavar="FILE",
                   help="Сохранить отчёт в JSON и выйти")
    p.add_argument("--trash", nargs="+", metavar="FILE",
                   help="Отправить файлы в корзину M и выйти")
    p.add_argument("--exclude", action="append", default=[],
                   metavar="DIR",
                   help="Имя директории для пропуска (можно повторять)")
    p.add_argument("--include-symlink-files", action="store_true",
                   dest="include_symlink_files",
                   help="Учитывать симлинки-файлы (не следует по "
                        "симлинкам-каталогам)")
    p.add_argument("--hash", default="blake2b",
                   choices=sorted(HASH_ALGOS.keys()),
                   help="Алгоритм хеширования (по умолчанию blake2b)")
    p.add_argument("--no-skip-default", action="store_true",
                   help="Не пропускать .git, node_modules и т.п.")
    p.add_argument("--no-skip-hidden", action="store_true",
                   help="Не пропускать скрытые каталоги (.git и т.п.)")
    p.add_argument("--no-color", action="store_true",
                   help="Монохромный режим")
    p.add_argument("-v", "--version", action="version",
                   version=f"Mdupe v{__version__}")
    return p

def _resolve_root(path_str):
    try:
        root = Path(path_str).expanduser()
    except RuntimeError as e:
        print(f"Не удалось раскрыть путь: {path_str}: {e}", file=sys.stderr)
        sys.exit(2)
    try:
        exists = root.exists()
    except OSError as e:
        print(f"Ошибка доступа к пути: {root}: {e}", file=sys.stderr)
        sys.exit(2)
    if not exists:
        print(f"Путь не существует: {root}", file=sys.stderr)
        sys.exit(2)
    try:
        is_dir = root.is_dir()
    except OSError as e:
        print(f"Ошибка доступа к пути: {root}: {e}", file=sys.stderr)
        sys.exit(2)
    if not is_dir:
        print(f"Не директория: {root}", file=sys.stderr)
        sys.exit(2)
    return root

def main():
    args = _build_argparser().parse_args()

    if args.trash:
        try:
            paths = [str(Path(p).expanduser()) for p in args.trash]
        except RuntimeError as e:
            print(f"Ошибка раскрытия пути: {e}", file=sys.stderr)
            sys.exit(2)
        try:
            ok, errs = trash_files(paths)
        except KeyboardInterrupt:
            print("\nПрервано.", file=sys.stderr)
            sys.exit(130)
        except Exception as e:
            print(f"Ошибка корзины: {e}", file=sys.stderr)
            sys.exit(1)
        print(f"В корзину: {ok}")
        for e in errs:
            print(f"  ! {e}", file=sys.stderr)
        sys.exit(0 if not errs else 1)

    try:
        min_size = parse_size(args.min_size)
    except ValueError as e:
        print(f"Некорректный размер: {args.min_size} ({e})", file=sys.stderr)
        sys.exit(2)

    root = _resolve_root(args.path)

    skip_dirs = None
    if args.no_skip_default:
        skip_dirs = frozenset()
    if args.exclude:
        extra = set(args.exclude)
        base = set() if skip_dirs is None else set(skip_dirs)
        skip_dirs = frozenset(base | extra)

    skip_hidden = not args.no_skip_hidden

    if args.list or args.json:
        groups = scan_duplicates(
            root, min_size,
            skip_dirs=skip_dirs,
            skip_hidden=skip_hidden,
            include_symlink_files=args.include_symlink_files,
            algo=args.hash,
        )
        if args.list:
            _print_groups(groups)
        if args.json:
            try:
                _write_json(args.json, root, min_size, groups)
            except Exception as e:
                print(f"Ошибка записи: {e}", file=sys.stderr)
                sys.exit(1)
            print(f"Записано: {args.json} ({len(groups)} групп)")
        return

    try:
        import locale
        locale.setlocale(locale.LC_ALL, '')
    except Exception:
        pass

    try:
        curses.wrapper(
            lambda sc: MdupeApp(
                sc, root, min_size,
                no_color=args.no_color,
                skip_dirs=skip_dirs,
                skip_hidden=skip_hidden,
                include_symlink_files=args.include_symlink_files,
                algo=args.hash,
            ).run()
        )
    except KeyboardInterrupt:
        pass
    except Exception as e:
        print(f"Критическая ошибка: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
