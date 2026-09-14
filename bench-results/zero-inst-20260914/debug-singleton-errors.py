#!/usr/bin/env python3
"""ZERO-INST -- why did the singleton scan report `errors=` on exactly the
ground assertions?  Print the RAW solver output for the first few, so the
answer is read off the tool rather than guessed.
"""
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import importlib.util

_spec = importlib.util.spec_from_file_location(
    'sa', os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'split-assertions.py'))

# split-assertions.py runs main() on import; re-implement the two helpers by
# reading its source is overkill -- copy the paren scanner.
import re
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
    path, work = sys.argv[1], sys.argv[2]
    idxs = [int(x) for x in sys.argv[3].split(',')]
    solver = '/nas3/data/axeyum/harness/bin/cvc5'
    fs = forms(open(path, encoding='utf-8', errors='replace').read())
    prefix = [f for f in fs if head(f) not in ('assert', 'check-sat', 'exit')]
    asserts = [f for f in fs if head(f) == 'assert']
    os.makedirs(work, exist_ok=True)
    for i in idxs:
        p = os.path.join(work, f'dbg{i}.smt2')
        with open(p, 'w') as fh:
            fh.write('\n'.join(prefix + [asserts[i]] + ['(check-sat)']) + '\n')
        r = subprocess.run([solver, '--tlimit', '10000', p],
                           capture_output=True, text=True, timeout=60)
        print(f'--- assert[{i}] rc={r.returncode} '
              f'assert_head={asserts[i][:70]!r}')
        print('  STDOUT:', repr(r.stdout[:400]))
        print('  STDERR:', repr(r.stderr[:400]))


main()
