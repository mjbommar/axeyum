#!/usr/bin/env python3
"""CORE-SELECT -- what the members of a minimal core ARE, not just how many.

    core-shape.py <coredir> <out.tsv> [--corpus DIR]

A size alone cannot distinguish two very different situations, and the lane's
conclusion turns on which one a row is in:

  * a core of ONE `(not (forall ...))` is the whole verification condition.
    There is nothing to select -- the refutation lives inside one assertion,
    and "which assertions to look at" has no work to do on that row.
  * a core of `(not (forall ...))` PLUS three `(forall ...)` axioms, out of 29
    conjuncts, is the shape a relevance filter is FOR.
  * a core of sixteen `<=` / `=` atoms spread across a 288-conjunct file is a
    coupled constraint system; no ordering rule picks it out.

So this records the HEAD of every core member (`not` unwrapped one level, since
`(not (forall ...))` and `(not (=> ...))` are the same negated-goal shape and a
bare `forall` is an axiom), plus whether the negated goal is present and how
many non-goal members there are.
"""
import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import args_of, split_script  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'
GOALISH = ('not.forall', 'not.=>', 'not.and', 'not.or', 'not.=', 'not.ATOM')


def head_of(s):
    s = s.strip()
    if not s.startswith('('):
        return 'ATOM'
    h = args_of(s)[0]
    if h == 'not':
        a = args_of(s)[1]
        if a:
            inner = a[0].strip()
            return 'not.' + (args_of(inner)[0] if inner.startswith('(') else 'ATOM')
    return h


def main():
    coredir, out = sys.argv[1], sys.argv[2]
    corpus = sys.argv[sys.argv.index('--corpus') + 1] if '--corpus' in sys.argv else CORPUS
    rows, bad = 0, 0
    with open(out, 'w') as fh:
        fh.write('file\tdivision\tconjuncts\tminimal\thas_negated_goal\t'
                 'n_axioms\theads\n')
        for p in sorted(glob.glob(os.path.join(coredir, '*.json'))):
            m = json.load(open(p))
            if not m.get('indices'):
                bad += 1
                continue
            try:
                raw = open(os.path.join(corpus, m['file']),
                           encoding='utf-8', errors='replace').read()
                _pre, b, _na, _mo = split_script(raw)
                if len(b) != m['conjuncts']:
                    bad += 1
                    continue
                heads = [head_of(b[i]) for i in m['indices']]
            except Exception:  # noqa: BLE001
                bad += 1
                continue
            goal = sum(1 for h in heads if h in GOALISH)
            fh.write(f'{m["file"]}\t{m["file"].split("/", 1)[0]}\t{m["conjuncts"]}\t'
                     f'{m["minimal"]}\t{1 if goal else 0}\t{len(heads) - goal}\t'
                     f'{",".join(heads[:12])}\n')
            rows += 1
    print(f'rows={rows} unusable={bad} out={out}')
    sys.exit(0 if rows else 14)


main()
