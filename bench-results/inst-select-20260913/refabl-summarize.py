#!/usr/bin/env python3
"""M1 -- summarise the reference ablation.

The four arms are NOT a partition and this refuses to print them as one: a file
may refute in all four, and the `ematch` arm is the only one whose SUCCESS is
load-bearing.  Its failure is not evidence of anything -- cvc5's e-matching is
one implementation with its own trigger inference.

`NONE` is kept distinct from `unknown` throughout.  A crash, an OOM and a
watchdog kill all produce no verdict-shaped line and none of them is a solver
opinion; folding them into `unknown` would inflate every denominator here.
"""

import argparse
import collections
import glob
import math
import os
import sys

ARMS = ['default', 'ematch', 'noematch', 'neither']


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


def load(outdir, div):
    rows = []
    for p in sorted(glob.glob(os.path.join(outdir, f'{div}.shard*.tsv'))):
        with open(p, encoding='utf-8') as fh:
            hdr = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                parts = line.rstrip('\n').split('\t')
                if len(parts) == len(hdr):
                    rows.append(dict(zip(hdr, parts)))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', required=True)
    ap.add_argument('--divisions', nargs='+', default=['UFNIA', 'UFLIA'])
    args = ap.parse_args()

    allrows = {}
    for div in args.divisions:
        allrows[div] = load(args.outdir, div)

    print('## M1 -- reference ablation (cvc5 1.3.4, 24 s, 8 GiB, pinned core)\n')
    print('Arms are NOT a partition: a file may refute in several.  `NONE` is a')
    print('run with no verdict-shaped line (crash / OOM / watchdog) and is kept')
    print('separate from `unknown` -- it is not a solver opinion.\n')

    print('| division | rows | arm | unsat | sat | unknown | NONE |')
    print('|---|---:|---|---:|---:|---:|---:|')
    for div, rows in allrows.items():
        for arm in ARMS:
            c = collections.Counter(r[arm] for r in rows)
            print(f'| {div} | {len(rows)} | `{arm}` | {c["unsat"]} | {c["sat"]} '
                  f'| {c["unknown"]} | {c["NONE"]} |')

    print('\n### The load-bearing number: of the files cvc5 DECIDES, how many does')
    print('each ablation still decide the same way?\n')
    print('| division | cvc5 decides | `ematch` agrees | share | Wilson 95% | '
          '`noematch` agrees | `neither` agrees |')
    print('|---|---:|---:|---:|---|---:|---:|')
    tot = collections.Counter()
    for div, rows in allrows.items():
        dec = [r for r in rows if r['default'] in ('sat', 'unsat')]
        e = sum(1 for r in dec if r['ematch'] == r['default'])
        n = sum(1 for r in dec if r['noematch'] == r['default'])
        b = sum(1 for r in dec if r['neither'] == r['default'])
        lo, hi = wilson(e, len(dec))
        tot['dec'] += len(dec); tot['e'] += e; tot['n'] += n; tot['b'] += b
        share = f'{100*e/len(dec):.0f}%' if dec else 'n/a'
        print(f'| {div} | {len(dec)} | {e} | **{share}** | '
              f'[{100*lo:.0f}%, {100*hi:.0f}%] | {n} | {b} |')
    lo, hi = wilson(tot['e'], tot['dec'])
    print(f'| **both** | **{tot["dec"]}** | **{tot["e"]}** | '
          f'**{100*tot["e"]/tot["dec"]:.0f}%** | [{100*lo:.0f}%, {100*hi:.0f}%] '
          f'| {tot["n"]} | {tot["b"]} |')

    print('\n### Files cvc5 decides that the `ematch` arm does NOT\n')
    print('These are the only candidates for "out of e-matching\'s reach", and even')
    print('for them the evidence is one-sided.\n')
    any_ = False
    for div, rows in allrows.items():
        for r in rows:
            if r['default'] in ('sat', 'unsat') and r['ematch'] != r['default']:
                any_ = True
                print(f'- `{r["file"]}` — default `{r["default"]}` '
                      f'({r["default_ms"]} ms), ematch `{r["ematch"]}`, '
                      f'noematch `{r["noematch"]}`, neither `{r["neither"]}`')
    if not any_:
        print('*(none)*')

    print('\n### Rows with NO verdict from cvc5 at all\n')
    for div, rows in allrows.items():
        bad = [r for r in rows if r['default'] == 'NONE']
        print(f'- **{div}: {len(bad)} of {len(rows)}**')
        for r in bad:
            print(f'  - `{r["file"]}` (declared `:status {r["status"]}`)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
