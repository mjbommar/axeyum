#!/usr/bin/env python3
"""CORE-SELECT -- R1: the re-derived population, against the inherited board.

    rederive-report.py <lane-dir>

[ADR-2035] found 8 of 22 censused "declining" rows were decided anyway and
[ADR-2065] moved AUFLIRA by 14 after the board TSV was written, so an inherited
list is a claim.  This prints the re-derivation beside it in BOTH directions --
rows that were undecided and are now decided, and rows the board called decided
that are undecided here -- because only one of those two directions is the one
people remember to check.

It also spends the free third authority: the benchmark's own declared `:status`,
compared against every verdict we produce, with the comparable denominator
printed beside the count.
"""
import collections
import os
import sys


def read_tsv(p):
    with open(p) as fh:
        h = fh.readline().rstrip('\n').split('\t')
        return [dict(zip(h, ln.rstrip('\n').split('\t'))) for ln in fh if ln.strip()]


def main():
    W = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    rows = read_tsv(os.path.join(W, 'ref', 'rederive-1400.tsv'))
    spl = {r['file']: r['declared'] for r in read_tsv(os.path.join(W, 'ref', 'split-1400.tsv'))}
    inh = {ln.strip() for ln in open(os.path.join(W, 'lists', 'inherited-undecided.list'))
           if ln.strip()}

    by = collections.defaultdict(collections.Counter)
    for r in rows:
        by[r['file'].split('/', 1)[0]][r['verdict']] += 1
    print(f'{"division":<10} {"n":>5} {"unsat":>6} {"sat":>5} {"unknown":>8} '
          f'{"NOVERDICT":>10} {"board und":>10} {"delta":>6}')
    tot, ti = collections.Counter(), 0
    for d in sorted(by, key=lambda d: -by[d]['unknown']):
        c = by[d]
        n = sum(c.values())
        i = sum(1 for f in inh if f.startswith(d + '/'))
        print(f'{d:<10} {n:>5} {c["unsat"]:>6} {c["sat"]:>5} {c["unknown"]:>8} '
              f'{c["NOVERDICT"]:>10} {i:>10} {c["unknown"] - i:>+6}')
        tot += c
        ti += i
    n = sum(tot.values())
    print(f'{"TOTAL":<10} {n:>5} {tot["unsat"]:>6} {tot["sat"]:>5} {tot["unknown"]:>8} '
          f'{tot["NOVERDICT"]:>10} {ti:>10} {tot["unknown"] - ti:>+6}')

    und = {r['file'] for r in rows if r['verdict'] == 'unknown'}
    print(f'\nre-derived undecided {len(und)}   board undecided {len(inh)}')
    print(f'  board-undecided that are NOW DECIDED  : {len(inh - und)}')
    print(f'  NEWLY undecided (board said decided)  : {len(und - inh)}')
    print(f'  agree                                 : {len(und & inh)}')
    for f in sorted(und - inh)[:20]:
        print(f'    newly undecided: {f}')

    cmp_ = [(r['file'], r['verdict'], spl.get(r['file'], 'ABSENT')) for r in rows
            if r['verdict'] in ('sat', 'unsat') and spl.get(r['file']) in ('sat', 'unsat')]
    bad = [x for x in cmp_ if x[1] != x[2]]
    print(f'\nsoundness: {len(cmp_)} comparisons against the declared :status, '
          f'{len(bad)} disagreements')
    for x in bad[:10]:
        print('   ', x)
    sys.exit(15 if bad else 0)


main()
