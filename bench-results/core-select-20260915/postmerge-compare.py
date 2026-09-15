#!/usr/bin/env python3
"""CORE-SELECT -- the ceiling this lane measured is a measurement of THIS
BRANCH.  Re-measure it on the merged tree and print both, row by row.

    postmerge-compare.py <lane-dir>

`main` moved a long way during this lane's measurement window ([ADR-2100],
[ADR-2101] and the ROUTE-OWNERSHIP / TRACE-API merges), and a ceiling read on
the pre-merge binary is not automatically the ceiling a reader will reproduce.
Checked at ROW level, not just in total: equal totals do not imply equal files,
and that is the check that caught a `+22` becoming `+6`.
"""
import os
import sys


def rd(p):
    with open(p) as f:
        h = f.readline().rstrip('\n').split('\t')
        return [dict(zip(h, ln.rstrip('\n').split('\t'))) for ln in f if ln.strip()]


def main():
    W = sys.argv[1]
    pre = {r['subset']: r['verdict'] for r in rd(os.path.join(W, 'ref', 'sim-cores.tsv'))}
    post = {r['subset']: r['verdict'] for r in rd(os.path.join(W, 'ref', 'sim-cores-postmerge.tsv'))}
    both = sorted(set(pre) & set(post))
    print(f'pre-merge rows {len(pre)}  post-merge rows {len(post)}  comparable {len(both)}')
    pu = sum(1 for k in both if pre[k] == 'unsat')
    qu = sum(1 for k in both if post[k] == 'unsat')
    gain = [k for k in both if pre[k] != 'unsat' and post[k] == 'unsat']
    loss = [k for k in both if pre[k] == 'unsat' and post[k] != 'unsat']
    flip = [k for k in both if {pre[k], post[k]} == {'sat', 'unsat'}]
    print(f'\nCEILING pre-merge  {pu} of {len(both)}')
    print(f'CEILING post-merge {qu} of {len(both)}')
    print(f'\nrow level: gains {len(gain)}  losses {len(loss)}  sat<->unsat flips {len(flip)}')
    for k in gain:
        print(f'  GAIN  {k}')
    for k in loss:
        print(f'  LOSS  {k}')
    for k in flip:
        print(f'  FLIP  {k}  {pre[k]} -> {post[k]}')
    bad = sum(1 for k in both if post[k] == 'sat')
    print(f'\nsoundness on the merged tree: a reference core is unsat, so any'
          f' `sat` is WRONG -- {bad} of {len(both)}')
    sys.exit(22 if bad or flip else 0)


main()
