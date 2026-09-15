#!/usr/bin/env python3
"""CORE-SELECT -- join the re-derivation, the haystack, the core census, the
positions and the simulation into ONE row per file, and classify it.

    join-census.py <lane-dir> <out.tsv>

The classification is the thing the lane is for, so it is written down here
rather than inferred in prose:

  REF-SAT        the reference satisfies the whole query -- there is NO
                 refutable subset and this row is not a selection candidate
  REF-NONE       the reference is undecided too -- unknown, its own bucket
  CORE-FAILED    the reference refutes the query but `:produce-unsat-cores`
                 turns its `unsat` into an `unknown` (core production disables
                 preprocessing).  A measurement gap, NOT a large core.
  SINGLETON      the minimal core is ONE conjunct.  There is nothing to select:
                 the refutation lives inside a single assertion, so "which
                 assertions to look at" has no work to do on this row
  NEEDLE         1 < minimal, and minimal < conjuncts -- the shape a selection
                 strategy is FOR
  WHOLE          minimal == conjuncts: every conjunct is necessary, so no
                 subset is smaller than the query

SINGLETON vs NEEDLE is a POST-HOC split introduced by the data, not one of the
pre-registered rules, and it is labelled as such wherever it is quoted.  It
exists because a minimal core of 1 turned out to argue AGAINST the selection
axis rather than for it, which is the opposite of how a median of 1 reads at
first glance.
"""
import os
import sys


def read_tsv(path):
    if not os.path.exists(path):
        return []
    with open(path) as fh:
        head = fh.readline().rstrip('\n').split('\t')
        return [dict(zip(head, ln.rstrip('\n').split('\t'))) for ln in fh if ln.strip()]


def classify(c):
    if c is None:
        return 'NOT-CENSUSED'
    s = c['split']
    if s == 'sat':
        return 'REF-SAT'
    if s in ('unknown', 'TIMEOUT'):
        return 'REF-NONE'
    if s.startswith('ROW-ABORT'):
        return 'ROW-ABORT'
    if s != 'unsat':
        return 'SPLIT-' + s
    if not c['z3_core'].isdigit():
        return 'CORE-FAILED'
    if not c['minimal'].isdigit():
        return 'MIN-MISSING'
    m, n = int(c['minimal']), int(c['conjuncts'])
    if m == 1:
        return 'SINGLETON'
    if m >= n:
        return 'WHOLE'
    return 'NEEDLE'


def main():
    W, out = sys.argv[1], sys.argv[2]
    R = os.path.join(W, 'ref')
    red = read_tsv(os.path.join(R, 'rederive-1400.tsv'))
    spl = {r['file']: r for r in read_tsv(os.path.join(R, 'split-1400.tsv'))}
    cor = {r['file']: r for r in read_tsv(os.path.join(R, 'core-census.tsv'))}
    pos = {r['file']: r for r in read_tsv(os.path.join(R, 'positions.tsv'))}
    sim = {}
    for r in read_tsv(os.path.join(R, 'sim-cores.tsv')):
        sim[r['subset']] = r
    if not red:
        print('ABORT: ref/rederive-1400.tsv missing', file=sys.stderr)
        sys.exit(6)

    cols = ('file', 'division', 'ours', 'declared', 'conjuncts', 'class',
            'z3_core', 'minimal', 'min_status', 'suffix_need', 'prefix_need',
            'small_need', 'core_ours', 'core_ms')
    n = 0
    with open(out, 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for r in red:
            f = r['file']
            if r['verdict'] != 'unknown':
                continue
            c = cor.get(f)
            p = pos.get(f, {})
            key = f.replace('/', '_') + '.core.smt2'
            s = sim.get(key, {})
            fh.write('\t'.join(str(x) for x in (
                f, f.split('/', 1)[0], r['verdict'],
                spl.get(f, {}).get('declared', 'NA'),
                spl.get(f, {}).get('conjuncts', 'NA'),
                classify(c),
                (c or {}).get('z3_core', 'NA'), (c or {}).get('minimal', 'NA'),
                (c or {}).get('min_status', 'NA'),
                p.get('suffix_need', 'NA'), p.get('prefix_need', 'NA'),
                p.get('small_need', 'NA'),
                s.get('verdict', 'NOT-SIMULATED'), s.get('ms', 'NA'))) + '\n')
            n += 1
    print(f'rows={n} out={out}')
    sys.exit(0 if n else 7)


main()
