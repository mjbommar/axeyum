#!/usr/bin/env python3
"""For every over-cap `distinct`, report the PATH of enclosing operator heads
from the `(assert ...)` down to it, and the resulting polarity.

The handoff (`bench-results/qbudget-20260913/DISTINCT-ENCODING.md`) claims the
application is the whole body of an `assert`. This measures it.

Polarity: start positive at the assert body; `not` flips; `=>` flips the
antecedent; `ite`/`=`/`xor` over Bool are NEITHER (a `distinct` there is in both
polarities at once). Everything else (`and`, `or`, `let` body) preserves.
"""
import io
import sys
from multiprocessing import Pool

MIN_OVER = 363
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"


def tok(s):
    """Yield (kind, text, pos). kind in {'(', ')', 'atom'}."""
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c == ';':
            j = s.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c in ' \t\r\n':
            i += 1
            continue
        if c == '(':
            yield ('(', '(', i)
            i += 1
            continue
        if c == ')':
            yield (')', ')', i)
            i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if s[j] == '"':
                    if j + 1 < n and s[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            yield ('atom', s[i:j], i)
            i = j
            continue
        if c == '|':
            j = s.find('|', i + 1)
            j = n if j < 0 else j + 1
            yield ('atom', s[i:j], i)
            i = j
            continue
        j = i
        while j < n and s[j] not in ' \t\r\n()|;"':
            j += 1
        yield ('atom', s[i:j], i)
        i = j


FLIP = {'not'}
NEITHER = {'ite', '=', 'xor', 'distinct'}
BINDER = {'forall', 'exists'}


def scan(path):
    try:
        s = io.open(path, encoding='utf-8', errors='replace').read()
    except OSError:
        return []
    out = []
    # stack entries: [head, argindex, is_assert_root]
    stack = []
    in_assert = False
    pending_head = False
    for kind, text, _pos in tok(s):
        if kind == '(':
            stack.append(['', 0, None])
            pending_head = True
        elif kind == 'atom':
            if pending_head:
                stack[-1][0] = text
                pending_head = False
                if len(stack) == 1 and text == 'assert':
                    in_assert = True
            else:
                if stack:
                    stack[-1][1] += 1
        elif kind == ')':
            if not stack:
                continue
            head, argc, _ = stack.pop()
            if stack:
                stack[-1][1] += 1
            if head == 'distinct' and argc >= MIN_OVER and in_assert:
                # `stack` is now the enclosing path
                path_heads = [f[0] for f in stack]
                out.append((argc, path_heads))
            if not stack:
                in_assert = False
        # argument index bookkeeping for `=>` polarity is approximated by
        # recording only the head chain; `=>` is reported as such.
    return [(path, argc, heads) for argc, heads in out]


def polarity(heads):
    """heads[0] == 'assert'. Returns 'positive', 'negative' or 'both'."""
    pol = 1
    for h in heads[1:]:
        if h in FLIP:
            pol = -pol
        elif h in NEITHER:
            return 'both'
        elif h in BINDER:
            return 'binder'
        # `and`, `or`, `let`, `=>`(consequent) preserve; `=>` antecedent flips,
        # which this approximation does NOT distinguish -- reported separately.
        elif h == '=>':
            return 'implies'
    return 'positive' if pol > 0 else 'negative'


def main():
    rels = [l.strip() for l in sys.stdin if l.strip()]
    paths = [CORPUS + r for r in rels]
    with Pool(16) as p:
        for rows in p.imap_unordered(scan, paths, chunksize=4):
            for path, argc, heads in rows:
                rel = path[len(CORPUS):]
                chain = '>'.join(heads)
                print(f"{argc}\t{len(heads)}\t{polarity(heads)}\t{chain}\t{rel}")


if __name__ == '__main__':
    main()
