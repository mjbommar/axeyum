#!/usr/bin/env python3
"""CORE-SELECT -- WHY we fail on the reference's own minimal core.

    trace-report.py <lane-dir>

The give-up reason is only informative as a CONTRAST: printed over the failures
alone it is a list of route names, and any of them could equally well appear on
the rows we refute.  So this splits the traced pass by the ceiling outcome and
prints both halves with their denominators.

`giveup_raw` is carried VERBATIM and unbucketed, because sizing a bucket by its
LABEL is how [ADR-2020]'s census reported one cause where the raw details held
four.  `attempts` is printed because a census that ranks blockers without it
can be measuring a ladder that refused at its first rung.
"""
import collections
import os
import sys


def rd(p):
    with open(p) as f:
        h = f.readline().rstrip('\n').split('\t')
        return [dict(zip(h, ln.rstrip('\n').split('\t'))) for ln in f if ln.strip()]


def main():
    W = sys.argv[1]
    tr = {r['subset']: r for r in rd(os.path.join(W, 'ref', 'trace-cores.tsv'))}
    j = rd(os.path.join(W, 'ref', 'joined.tsv'))
    rows = []
    for r in j:
        k = r['file'].replace('/', '_') + '.core.smt2'
        if k in tr:
            rows.append((r, tr[k]))
    print(f'cores traced and joined: {len(rows)} of {len(tr)} traced\n')
    if not rows:
        print('ABORT: the trace and the join share no rows')
        sys.exit(21)

    # The traced pass re-derives the verdict; if it disagrees with the untraced
    # ceiling run, the ceiling is a measurement of a traced build somewhere and
    # the contrast below is not a contrast. Checked, not assumed.
    dis = [(a['file'], a['core_ours'], b['verdict']) for a, b in rows
           if a['core_ours'] in ('unsat', 'unknown') and a['core_ours'] != b['verdict']]
    print(f'traced verdict vs untraced ceiling: {len(dis)} disagreements'
          f' of {len(rows)}')
    for d in dis[:10]:
        print('   ', d)
    print()

    for want, label in (('unsat', 'WE REFUTE THE CORE (ceiling positive)'),
                        ('unknown', 'WE DO NOT (ceiling negative)')):
        sel = [(a, b) for a, b in rows if a['core_ours'] == want]
        print(f'--- {label}: {len(sel)} ---')
        c = collections.Counter((b['bound_by'], b['giveup_kind']) for a, b in sel)
        for (bb, gk), n in c.most_common(8):
            print(f'   {n:>4}  bound_by={bb:<18} kind={gk}')
        at = sorted(int(b['attempts']) for a, b in sel)
        ms = sorted(int(b['total_ms']) for a, b in sel)
        if at:
            print(f'   attempts med={at[len(at) // 2]} max={at[-1]}   '
                  f'total_ms med={ms[len(ms) // 2]} max={ms[-1]}')
        print()

    neg = [b for a, b in rows if a['core_ours'] == 'unknown']
    print('--- give-up DETAIL over the ceiling-negative rows, VERBATIM, top 12 ---')
    c = collections.Counter(b['giveup_raw'][:120] for b in neg)
    for d, n in c.most_common(12):
        print(f'  {n:>4}  {d}')

    # How much of the 24 s did we actually use? A refusal and an exhausted clock
    # are different findings and the same `unknown`.
    fast = sum(1 for b in neg if int(b['total_ms']) < 2000)
    slow = sum(1 for b in neg if int(b['total_ms']) >= 20000)
    print(f'\nof the {len(neg)} ceiling-negative rows:')
    print(f'  gave up in under 2 s of the 24 s budget : {fast}')
    print(f'  ran 20 s or more                        : {slow}')
    sys.exit(0)


main()
