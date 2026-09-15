#!/usr/bin/env python3
"""CORE-SELECT -- write the SUBSET files a reference-free strategy would pick.

    subsets.py <file.smt2-rel> <coredir> <outdir> [--corpus DIR] [--ks 1,2,5,10,25,50]

The reference found a core; that answers "would we decide it if we already knew
the answer", which is a CEILING and not a gain.  A strategy claim needs a rule
computable from the query alone.  The rules sized here are:

  suffix(k)  the LAST k conjuncts             -- VC generators emit the negated
                                                 goal last, so this is the
                                                 cheapest plausible rule there is
  prefix(k)  the FIRST k conjuncts            -- the CONTROL.  If prefix(k) works
                                                 as often as suffix(k), position
                                                 carries no information and the
                                                 suffix rule is not a finding
  small(k)   the k SHORTEST conjuncts by text -- [ADR-2050] found four of six
                                                 minimal cores were propositional
                                                 contradictions, which are short

Every one of these is computable from the file with no solver and no reference.
`k` is FIXED across rows: a per-row optimal k is chosen with knowledge of the
answer and is not a strategy.

Whether the core happens to LIE INSIDE a given subset is free arithmetic on the
core indices and is reported by `positions.py`.  This script exists for the part
that is not free: handing the subset to OUR solver and seeing whether it decides
it.  A subset that contains the core is unsat, but "contains an unsat core" and
"we return unsat within 24 s" are different claims and the second is the one
that matters.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import split_script  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'


def flat(rel):
    return rel.replace('/', '_')


def write(path, prefix, bodies):
    with open(path, 'w') as fh:
        fh.write('\n'.join(prefix))
        fh.write('\n')
        for b in bodies:
            fh.write(f'(assert {b})\n')
        fh.write('(check-sat)\n')


def main():
    rel, coredir, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    corpus = sys.argv[sys.argv.index('--corpus') + 1] if '--corpus' in sys.argv else CORPUS
    ks = [int(x) for x in (sys.argv[sys.argv.index('--ks') + 1]
                           if '--ks' in sys.argv else '1,2,5,10,25,50').split(',')]
    os.makedirs(outdir, exist_ok=True)

    meta = json.load(open(os.path.join(coredir, flat(rel) + '.json')))
    raw = open(os.path.join(corpus, rel), encoding='utf-8', errors='replace').read()
    prefix, bodies, _n, _mode = split_script(raw)
    n = len(bodies)
    if n != meta['conjuncts']:
        print(f'{rel}\tSPLIT-DRIFT\t{n}\t{meta["conjuncts"]}')
        sys.exit(4)

    order_small = sorted(range(n), key=lambda i: (len(bodies[i]), i))
    made = []
    for k in ks:
        if k > n:
            continue
        for tag, idx in (('suffix', list(range(n - k, n))),
                         ('prefix', list(range(k))),
                         ('small', sorted(order_small[:k]))):
            p = os.path.join(outdir, f'{flat(rel)}.{tag}{k}.smt2')
            write(p, prefix, [bodies[i] for i in idx])
            made.append(f'{tag}{k}')
    print(f'{rel}\tOK\t{n}\t{",".join(made)}')


main()
