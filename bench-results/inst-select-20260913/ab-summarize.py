#!/usr/bin/env python3
"""Summarise the interleaved A/B for the smallest-witness lever.

Polarity, repeated here because reading it off the wrong column inverts every
conclusion: `base` is the SHIPPED arm (variable unset); `arm` is
`AXEYUM_QINST_SMALLEST_WITNESS=1`.

`NONE` (no verdict-shaped line) is never folded into `unknown` -- a crash, an OOM
and a watchdog kill all land there and none is a solver opinion.

Reports sat<->unsat flips separately from gains and losses, because a flip is a
SOUNDNESS event and a gain is a capability one; a table that adds them is unable
to report the thing that matters most.
"""

import argparse
import collections
import glob
import math
import os
import sys


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
    ap.add_argument('--divisions', nargs='+', required=True)
    ap.add_argument('--controls', nargs='*', default=[])
    args = ap.parse_args()

    print('## A/B — `AXEYUM_QINST_SMALLEST_WITNESS` (ships OFF; `base` = shipped)\n')
    print('| division | n | base | arm | net | gain | loss | sat↔unsat flips | NONE base/arm |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---|')
    moved = []
    flips = []
    for div in args.divisions + args.controls:
        rows = load(args.outdir, div)
        if not rows:
            print(f'| {div} | *(did not run)* | | | | | | | |')
            continue
        dec = lambda v: v in ('sat', 'unsat')
        b = sum(1 for r in rows if dec(r['base']))
        a = sum(1 for r in rows if dec(r['arm']))
        g = [r for r in rows if not dec(r['base']) and dec(r['arm'])]
        l = [r for r in rows if dec(r['base']) and not dec(r['arm'])]
        f = [r for r in rows if dec(r['base']) and dec(r['arm'])
             and r['base'] != r['arm']]
        nb = sum(1 for r in rows if r['base'] == 'NONE')
        na = sum(1 for r in rows if r['arm'] == 'NONE')
        tag = ' *(control)*' if div in args.controls else ''
        print(f'| {div}{tag} | {len(rows)} | {b} | {a} | **{a-b:+d}** | {len(g)} '
              f'| {len(l)} | {len(f)} | {nb}/{na} |')
        moved += [(div, r, 'gain') for r in g] + [(div, r, 'loss') for r in l]
        flips += [(div, r) for r in f]

    print('\n### Every moved row\n')
    if not moved:
        print('*(none)*')
    for div, r, kind in moved:
        print(f'- **{kind.upper()}** `{div}` `{r["file"]}` — base `{r["base"]}` '
              f'({r["base_ms"]} ms), arm `{r["arm"]}` ({r["arm_ms"]} ms), '
              f'order `{r["order"]}`, declared `:status {r["status"]}`')

    print('\n### sat↔unsat flips (a SOUNDNESS event, never a gain)\n')
    if not flips:
        print('**0.** No row is decided differently by the two arms.')
    for div, r in flips:
        print(f'- **FLIP** `{div}` `{r["file"]}` base `{r["base"]}` arm `{r["arm"]}` '
              f'declared `:status {r["status"]}`')

    print('\n### Agreement with the declared `:status`, both arms\n')
    print('The comparable denominator is on the same line (ADR-1957): only files')
    print('that carry a declared status AND that the arm decided can be compared.\n')
    print('| division | base agree/comparable | arm agree/comparable | disagreements |')
    print('|---|---|---|---:|')
    tot_dis = 0
    for div in args.divisions + args.controls:
        rows = load(args.outdir, div)
        if not rows:
            continue
        out = []
        dis = 0
        for col in ('base', 'arm'):
            comp = [r for r in rows if r['status'] in ('sat', 'unsat')
                    and r[col] in ('sat', 'unsat')]
            ok = sum(1 for r in comp if r[col] == r['status'])
            dis += len(comp) - ok
            out.append(f'{ok}/{len(comp)}')
        tot_dis += dis
        print(f'| {div} | {out[0]} | {out[1]} | {dis} |')
    print(f'\n**DISAGREEMENTS: {tot_dis}.**')

    print('\n### Wall-clock cost of the arm\n')
    print('The arm scans the witness pool per bound variable per joined')
    print('substitution, so a cost here is expected and is reported whether or')
    print('not it is convenient.\n')
    print('| division | median base ms | median arm ms | total base s | total arm s |')
    print('|---|---:|---:|---:|---:|')
    for div in args.divisions + args.controls:
        rows = load(args.outdir, div)
        if not rows:
            continue
        bs = sorted(int(r['base_ms']) for r in rows)
        as_ = sorted(int(r['arm_ms']) for r in rows)
        print(f'| {div} | {bs[len(bs)//2]} | {as_[len(as_)//2]} '
              f'| {sum(bs)/1000:.1f} | {sum(as_)/1000:.1f} |')

    n = sum(len(load(args.outdir, d)) for d in args.divisions)
    k = sum(1 for d, _r, kind in moved if kind == 'gain' and d in args.divisions)
    if n:
        lo, hi = wilson(k, n)
        print(f'\n**Target-division gain rate: {k}/{n}, Wilson 95% '
              f'[{100*lo:.1f}%, {100*hi:.1f}%].**')
    return 0


if __name__ == '__main__':
    sys.exit(main())
