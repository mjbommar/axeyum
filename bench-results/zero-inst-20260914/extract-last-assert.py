#!/usr/bin/env python3
"""ZERO-INST -- write a standalone file containing only assertion #N of a
benchmark (default: the last one), with `set-info` dropped.

    extract-last-assert.py <file> <out.smt2> [index]

`set-info` is dropped because these benchmarks carry `(set-info :status
unsat)`, and cvc5 turns a correct `sat` on a SUBSET into an `(error ...)`
with a nonzero exit -- which reads as a broken probe rather than a verdict.
"""
import re
import sys

HEAD = re.compile(r'\(\s*([A-Za-z0-9_.\-!|]+)')


def forms(text):
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


def head(f):
    m = HEAD.match(f)
    return m.group(1) if m else '?'


def main():
    path, out = sys.argv[1], sys.argv[2]
    idx = int(sys.argv[3]) if len(sys.argv) > 3 else -1
    fs = forms(open(path, encoding='utf-8', errors='replace').read())
    prefix = [f for f in fs
              if head(f) not in ('assert', 'check-sat', 'exit', 'set-info')]
    asserts = [f for f in fs if head(f) == 'assert']
    with open(out, 'w') as fh:
        fh.write('\n'.join(prefix + [asserts[idx]] + ['(check-sat)']) + '\n')
    print(f'{out}\tassert_index={idx if idx >= 0 else len(asserts) + idx}'
          f'\tof={len(asserts)}\tbytes={len(asserts[idx])}')


main()
