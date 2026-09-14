#!/usr/bin/env python3
"""Three independent A/B passes over one division: the noise band, and the fate
of every row that moved in any pass.

The band is measured on BOTH arms rather than only the base, because a lever is
graded against the churn of the arm it is compared to, not against the shipped
arm's churn alone.

Classification of a row that moved in at least one pass:

  STABLE-GAIN   arm decides it in all 3, base in none
  STABLE-LOSS   base decides it in all 3, arm in none
  UNSTABLE      anything else -- INCLUDING a row that disagrees with ITSELF
                across passes of the SAME arm, which is the case a single pass
                reports as a gain or a loss and cannot distinguish from one.
"""

import argparse
import collections
import glob
import os
import sys


def load(outdir, div):
    rows = {}
    for p in sorted(glob.glob(os.path.join(outdir, f'{div}.shard*.tsv'))):
        with open(p, encoding='utf-8') as fh:
            hdr = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                parts = line.rstrip('\n').split('\t')
                if len(parts) == len(hdr):
                    r = dict(zip(hdr, parts))
                    rows[r['file']] = r
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdirs', nargs='+', required=True)
    ap.add_argument('--division', required=True)
    args = ap.parse_args()

    passes = [load(d, args.division) for d in args.outdirs]
    for i, (d, p) in enumerate(zip(args.outdirs, passes), 1):
        if not p:
            print(f'pass {i} ({d}): **did not run** — no rows')
            return 1

    dec = lambda v: v in ('sat', 'unsat')
    files = sorted(set().union(*(set(p) for p in passes)))
    common = [f for f in files if all(f in p for p in passes)]

    print(f'## Three independent A/B passes — `{args.division}`\n')
    print(f'{len(common)} files present in all {len(passes)} passes '
          f'(of {len(files)} seen).\n')
    print('| pass | base decided | arm decided | net |')
    print('|---|---:|---:|---:|')
    btot, atot = [], []
    for i, p in enumerate(passes, 1):
        b = sum(1 for f in common if dec(p[f]['base']))
        a = sum(1 for f in common if dec(p[f]['arm']))
        btot.append(b); atot.append(a)
        print(f'| {i} | {b} | {a} | {a-b:+d} |')
    print(f'\n**Base-arm totals: {" / ".join(map(str, btot))} — '
          f'BAND {max(btot)-min(btot)} files.**')
    print(f'**Arm totals: {" / ".join(map(str, atot))} — '
          f'BAND {max(atot)-min(atot)} files.**')

    # Rows that disagree with THEMSELVES across passes of the same arm.
    churn = {'base': [], 'arm': []}
    for f in common:
        for col in ('base', 'arm'):
            vals = {dec(p[f][col]) for p in passes}
            if len(vals) > 1:
                churn[col].append(f)
    print(f'\n**Files that disagree with themselves across passes: '
          f'base {len(churn["base"])}, arm {len(churn["arm"])}.**')
    print('\nThis is the number a single-pass A/B cannot see, and it is the')
    print('denominator any claimed gain or loss has to clear.\n')

    moved = [f for f in common
             if any(dec(p[f]['base']) != dec(p[f]['arm']) for p in passes)]
    print(f'### Every row that moved in ANY pass ({len(moved)})\n')
    verdicts = collections.Counter()
    for f in moved:
        b = [p[f]['base'] for p in passes]
        a = [p[f]['arm'] for p in passes]
        if all(not dec(x) for x in b) and all(dec(x) for x in a):
            v = 'STABLE-GAIN'
        elif all(dec(x) for x in b) and all(not dec(x) for x in a):
            v = 'STABLE-LOSS'
        else:
            v = 'UNSTABLE'
        verdicts[v] += 1
        print(f'- **{v}** `{f}`')
        print(f'  - base: {", ".join(b)}')
        print(f'  - arm:  {", ".join(a)}')
    print(f'\n**{dict(verdicts) if verdicts else "no row moved in any pass"}**')

    flips = [f for f in common for p in passes
             if dec(p[f]['base']) and dec(p[f]['arm'])
             and p[f]['base'] != p[f]['arm']]
    print(f'\n**sat↔unsat flips across all passes: {len(flips)}.**')
    return 0


if __name__ == '__main__':
    sys.exit(main())
