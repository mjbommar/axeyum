#!/usr/bin/env python3
"""CORE-SELECT -- where in the file the core LIVES, and which fixed-k
reference-free rule would therefore contain it.

    positions.py <coredir> <out.tsv>

Every column here is free arithmetic on the core indices already written by
`core.py`; no solver runs.  It answers the cheap half of "could a strategy find
this without the reference":

  suffix_need = n - min(idx)   the smallest k for which `last k conjuncts`
                               CONTAINS the whole core.  Because a superset of
                               an unsat set is unsat, containing it is
                               sufficient -- so this k is an upper bound on the
                               suffix rule's cost, exactly.
  prefix_need = max(idx) + 1   the same for `first k conjuncts` (the control).
  small_need                   the smallest k for which the k SHORTEST
                               conjuncts contain the core.

The expensive half -- whether OUR solver returns `unsat` on that subset within
24 s -- is NOT free and is measured separately.  Containing an unsat core and
deciding it are different claims.

A fixed k is what makes a rule a strategy.  `suffix_need` is per-row and is
chosen knowing the answer, so it is reported as a DISTRIBUTION whose tail at
each fixed k is the rule's coverage -- never as "the strategy needs k".
"""
import glob
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import split_script  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'


def main():
    coredir, out = sys.argv[1], sys.argv[2]
    corpus = sys.argv[sys.argv.index('--corpus') + 1] if '--corpus' in sys.argv else CORPUS
    rows, bad = 0, 0
    with open(out, 'w') as fh:
        fh.write('file\tconjuncts\tminimal\tmin_status\tmin_idx\tmax_idx\t'
                 'suffix_need\tprefix_need\tsmall_need\tcore_z3\tcore_cvc5\n')
        for p in sorted(glob.glob(os.path.join(coredir, '*.json'))):
            m = json.load(open(p))
            idx, n = m['indices'], m['conjuncts']
            if not idx or n <= 0:
                bad += 1
                continue
            try:
                raw = open(os.path.join(corpus, m['file']),
                           encoding='utf-8', errors='replace').read()
                _pre, bodies, _na, _mo = split_script(raw)
                if len(bodies) != n:
                    bad += 1
                    continue
                rank = {i: r for r, i in enumerate(
                    sorted(range(n), key=lambda i: (len(bodies[i]), i)))}
                small_need = max(rank[i] for i in idx) + 1
            except Exception:  # noqa: BLE001 -- an unreadable row is a row, not a zero
                bad += 1
                continue
            fh.write(f'{m["file"]}\t{n}\t{m["minimal"]}\t{m["min_status"]}\t'
                     f'{min(idx)}\t{max(idx)}\t{n - min(idx)}\t{max(idx) + 1}\t'
                     f'{small_need}\t{m["core_z3"]}\t{m["core_cvc5"]}\n')
            rows += 1
    print(f'rows={rows} unusable={bad} out={out}')
    sys.exit(0 if rows else 5)


main()
