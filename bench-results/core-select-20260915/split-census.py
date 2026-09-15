#!/usr/bin/env python3
"""CORE-SELECT -- the HAYSTACK size for every file in a list.

    split-census.py <list> <out.tsv> [corpus]

Pure parsing, no solver: this column is load-insensitive and can run while the
verdict sweeps hold the pinned cores.  It is the denominator every core size is
read against -- a core of 1 in a haystack of 3 is not the same finding as a core
of 1 in a haystack of 633.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import declared_status, split_script  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'


def main():
    lst, out = sys.argv[1], sys.argv[2]
    corpus = sys.argv[3] if len(sys.argv) > 3 else CORPUS
    rows, failed = 0, 0
    with open(out, 'w') as fh:
        fh.write('file\tbytes\tasserts\tconjuncts\tmode\tdeclared\n')
        for line in open(lst):
            f = line.strip()
            if not f:
                continue
            p = os.path.join(corpus, f)
            try:
                raw = open(p, encoding='utf-8', errors='replace').read()
                prefix, bodies, n_assert, mode = split_script(raw)
                fh.write(f'{f}\t{len(raw)}\t{n_assert}\t{len(bodies)}\t{mode}'
                         f'\t{declared_status(raw)}\n')
            except Exception as exc:  # noqa: BLE001 -- the failure IS the row
                failed += 1
                fh.write(f'{f}\t0\t0\t0\tFAILED:{type(exc).__name__}\tABSENT\n')
            rows += 1
    print(f'rows={rows} failed={failed} out={out}')
    # The exit status depends on the finding: a parser that silently produced
    # zero-conjunct rows for a tenth of the population would otherwise read as
    # a census of small haystacks.
    sys.exit(3 if failed else 0)


main()
