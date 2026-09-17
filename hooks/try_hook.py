"""
Пример хука для M — подсветка ключевых слов Python.

Скопируй в ~/.m/hooks/python_highlight.py и перезапусти M
(или нажми 'x' → R для перезагрузки хуков).
"""

import re

KEYWORDS = re.compile(
    r'\b(def|class|if|else|elif|for|while|return|import|from|as|'
    r'try|except|finally|with|lambda|yield|async|await|pass|break|'
    r'continue|raise|global|nonlocal|assert|del|in|is|not|and|or|'
    r'True|False|None)\b'
)

STRING = re.compile(r'(\'[^\']*\'|"[^"]*")')
COMMENT = re.compile(r'#.*$')


def on_draw_line(line, lineno, filename, cursor_line, **_):
    """Возвращает список (start, end, color_pair) для подсветки."""
    if not filename.endswith('.py'):
        return None

    spans = []

    # комментарии — color_pair(8) (серый/тёмный), приоритет выше
    for m in COMMENT.finditer(line):
        spans.append((m.start(), m.end(), 8))

    # строки — color_pair(2) (зелёный)
    for m in STRING.finditer(line):
        spans.append((m.start(), m.end(), 2))

    # ключевые слова — color_pair(6) (magenta)
    for m in KEYWORDS.finditer(line):
        # не подсвечиваем ключевые слова внутри строк
        if not any(s <= m.start() < e for s, e, _ in spans):
            spans.append((m.start(), m.end(), 6))

    return spans


EVENTS = {
    "on_draw_line": on_draw_line,
}
