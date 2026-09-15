#!/usr/bin/env python3
"""CORE-SELECT -- a `sat` on a strategy subset is only WRONG if that subset
contains an unsat core.  Check which.

    check-subset-soundness.py <lane-dir>

Dropping conjuncts weakens the formula, so most `sat` verdicts on a strategy
subset are simply correct: the rule threw away the constraints that made the
query unsatisfiable.  But when the subset PROVABLY contains the reference's own
minimal core, the subset is unsat, and a `sat` there is a wrong answer -- the
kind this repository has shipped before and the kind a verdict tally cannot
see.

Containment is decided from committed data, not re-derived:
  suffix(k) contains the core  iff  suffix_need <= k
  prefix(k)                    iff  prefix_need <= k
  small(k)                     iff  small_need  <= k
  rel(d)                       from the core indices and the rule's own output,
                               so it is recomputed here rather than trusted

Exit status depends on the finding.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import split_script  # noqa: E402
from subsets import declared_symbols, relevance  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'


def read_tsv(p):
    with open(p) as fh:
        h = fh.readline().rstrip('\n').split('\t')
        return [dict(zip(h, ln.rstrip('\n').split('\t'))) for ln in fh if ln.strip()]


def main():
    W = sys.argv[1]
    coredir = sys.argv[2] if len(sys.argv) > 2 else \
        '/nas3/data/axeyum/harness/core-select/cores'
    pos = {r['file'].replace('/', '_'): r
           for r in read_tsv(os.path.join(W, 'ref', 'positions.tsv'))}
    sims = read_tsv(os.path.join(W, 'ref', 'sim-subsets.tsv'))

    relcache = {}

    def rel_contains(flat, d):
        key = (flat, d)
        if key in relcache:
            return relcache[key]
        meta = json.load(open(os.path.join(coredir, flat + '.json')))
        raw = open(os.path.join(CORPUS, meta['file']), encoding='utf-8',
                   errors='replace').read()
        prefix, bodies, _n, _m = split_script(raw)
        idx = relevance(bodies, declared_symbols(prefix), d)
        relcache[key] = set(meta['indices']) <= set(idx)
        return relcache[key]

    def contains_core(name):
        """-> True / False / None (not checkable)."""
        stem = name[:-len('.smt2')]
        flat, mid = stem.rsplit('.', 1)
        tag = mid.rstrip('0123456789')
        k = mid[len(tag):]
        if not k:
            return None
        k = int(k)
        if tag == 'rel':
            return rel_contains(flat, k)
        p = pos.get(flat)
        need = {'suffix': 'suffix_need', 'prefix': 'prefix_need',
                'small': 'small_need'}.get(tag)
        if p is None or need is None:
            return None
        return int(p[need]) <= k

    checked = wrong = unchecked = 0
    sat_rows = [r for r in sims if r['verdict'] == 'sat']
    for r in sat_rows:
        c = contains_core(r['subset'])
        if c is None:
            unchecked += 1
            continue
        checked += 1
        if c:
            wrong += 1
            print(f'WRONG-ANSWER  {r["subset"]}  our verdict sat, but this'
                  f' subset contains the reference core')

    # POSITIVE CONTROL. A containment test that answers False for every subset
    # would print exactly the zero above.  So count containment over ALL
    # subsets and over the ones we DID refute: if the first is zero the check
    # is vacuous, and if `unsat` subsets are never found to contain the core
    # the test is not reading the right rows.
    allc = [contains_core(r['subset']) for r in sims]
    yes = sum(1 for c in allc if c is True)
    uns = [r for r in sims if r['verdict'] == 'unsat']
    unsyes = sum(1 for r in uns if contains_core(r['subset']) is True)

    print(f'\nstrategy subsets            {len(sims)}')
    print(f'our verdict `sat` on         {len(sat_rows)}')
    print(f'  containment CHECKED        {checked}')
    print(f'  containment NOT CHECKABLE  {unchecked}')
    print(f'  WRONG ANSWERS              {wrong}')
    print(f'\npositive control')
    print(f'  subsets that DO contain the core   {yes} of {len(sims)}')
    print(f'  of the {len(uns)} we refute, contain it  {unsyes}')
    print('\nA `sat` on a subset that does NOT contain the core is correct:'
          '\ndropping conjuncts weakens the formula. That is why this check'
          '\nexists -- the verdict tally alone cannot tell the two apart.')
    if yes == 0:
        print('\nRED: the containment test never answers True. It cannot have'
              ' found a wrong answer.')
        sys.exit(20)
    sys.exit(18 if wrong else (19 if checked == 0 else 0))


main()
