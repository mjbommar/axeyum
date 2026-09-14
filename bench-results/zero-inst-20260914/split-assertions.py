#!/usr/bin/env python3
"""Split an SMT-LIB2 file into top-level forms, classify each `assert` as
GROUND (no `forall`/`exists` anywhere inside it) vs QUANTIFIED, and emit a
variant of the file.

    split-assertions.py <file> report      -- counts only, no output file
    split-assertions.py <file> ground      -- drop every QUANTIFIED assert
    split-assertions.py <file> quantified  -- drop every GROUND assert

Parsing is a paren counter that respects |quoted symbols|, "strings" and
`;` comments.  It is deliberately syntactic.

KNOWN LIMIT, checked rather than assumed: an `(assert p)` whose `p` is a
symbol `define-fun`'d to a quantified body would be classified GROUND.
`report` prints `define_fun_with_quant`, so the limit is visible per file
instead of being a silent assumption.  On this lane's population that count
is printed beside every row.
"""
import re
import sys


def forms(text):
    """Yield the top-level s-expressions of an SMT-LIB2 file, in order."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isspace():
            i += 1
            continue
        if c != '(':
            j = i
            while j < n and not text[j].isspace():
                j += 1
            i = j
            continue
        depth, j = 0, i
        while j < n:
            ch = text[j]
            if ch == ';':
                k = text.find('\n', j)
                j = n if k < 0 else k + 1
                continue
            if ch == '"':
                j += 1
                while j < n:
                    if text[j] == '"':
                        if j + 1 < n and text[j + 1] == '"':
                            j += 2
                            continue
                        j += 1
                        break
                    j += 1
                continue
            if ch == '|':
                k = text.find('|', j + 1)
                j = n if k < 0 else k + 1
                continue
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        out.append(text[i:j])
        i = j
    return out


QUANT = re.compile(r'(?<![A-Za-z0-9_.\-])(forall|exists)(?![A-Za-z0-9_.\-])')
HEAD = re.compile(r'\(\s*([A-Za-z0-9_.\-!|]+)')


def head(f):
    m = HEAD.match(f)
    return m.group(1) if m else '?'


def main():
    path, mode = sys.argv[1], sys.argv[2]
    text = open(path, encoding='utf-8', errors='replace').read()
    fs = forms(text)
    n_assert = n_q = n_g = defq = 0
    keep = []
    for f in fs:
        h = head(f)
        if h in ('define-fun', 'define-fun-rec', 'define-funs-rec'):
            if QUANT.search(f):
                defq += 1
        if h == 'assert':
            n_assert += 1
            q = bool(QUANT.search(f))
            if q:
                n_q += 1
            else:
                n_g += 1
            if mode == 'ground' and q:
                continue
            if mode == 'quantified' and not q:
                continue
        if h == 'set-info':
            continue
        keep.append(f)
    if mode == 'report':
        print(f"{path}\tforms={len(fs)}\tassert={n_assert}"
              f"\tground_assert={n_g}\tquant_assert={n_q}"
              f"\tdefine_fun_with_quant={defq}")
        return
    sys.stdout.write('\n'.join(keep) + '\n')


main()
