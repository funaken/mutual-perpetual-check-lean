#!/usr/bin/env python3
"""Small source audit helpers; Lean remains the authority for elaboration.

Recognizes nested comments, strings, character literals and quoted identifiers.
It is used to check comment-only edits and to report physical source lines.
"""
import re


def segments(source):
    """Yield (is_comment, text), preserving the input exactly."""
    i = start = 0
    while i < len(source):
        if source.startswith('--', i) or source.startswith('/-', i):
            if start < i:
                yield False, source[start:i]
            end = i
            if source.startswith('--', i):
                end = source.find('\n', i)
                if end < 0:
                    end = len(source)
            else:
                end, depth = i + 2, 1
                while end < len(source) and depth:
                    if source.startswith('/-', end):
                        depth += 1
                        end += 2
                    elif source.startswith('-/', end):
                        depth -= 1
                        end += 2
                    else:
                        end += 1
                if depth:
                    raise ValueError('Unclosed Lean comment')
            yield True, source[i:end]
            i = start = end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i] == '«':
            end = source.find('»', i + 1)
            if end < 0:
                raise ValueError('Unclosed quoted identifier')
            i = end + 1
        elif source[i] == "'" and (m := re.match(r"'(?:\\.|[^'\n\\])'", source[i:])):
            i += len(m[0])
        else:
            i += 1
    if start < len(source):
        yield False, source[start:]


def without_comments(source):
    return ''.join(''.join('\n' if c == '\n' else ' ' for c in s) if comment else s
                   for comment, s in segments(source))


def tokens(source):
    return re.findall(r'"(?:\\.|[^"\\])*"|«[^»]*»|\w+|[^\w\s]',
                      without_comments(source))


def line_counts(source):
    plain = without_comments(source).splitlines()
    original = source.splitlines()
    code = sum(bool(s.strip()) for s in plain)
    blank = sum(not s.strip() for s in original)
    return dict(total=len(original), code=code,
                comment_only=len(original) - code - blank, blank=blank)
