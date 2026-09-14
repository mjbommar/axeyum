#!/usr/bin/env python3
"""ZERO-INST -- summarize an A/B phase's shard TSVs.

    ab-summarize.py <phase.shard*.tsv ...>

Classifies each row and prints the counts with Wilson intervals.  Three things
it does on purpose:

- GAIN and LOSS are counted separately and both are printed, including zeros.
  A net figure alone hides a lever that wins two rows and loses two.
- The MECHANISM column is summarized beside the verdicts.  A row where the
  `on` arm shows `rung=declined` cannot have been moved by this lever, and a
  "gain" on such a row is a measurement artifact, not a win -- so those are
  called out by name rather than folded into the total.
- FLIP (sat<->unsat between arms) is its own category and is a P0, never a
  gain.  A weakening can only ever add `unsat`; a `sat` becoming `unsat` or
  the reverse means something other than this lever moved.
"""
import csv
import math
import sys

DECIDED = ('sat', 'unsat')


def wilson(k, n, z=1.96):
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (100 * max(0.0, c - h), 100 * min(1.0, c + h))


def main():
    rows = []
    for path in sys.argv[1:]:
        with open(path) as fh:
            rows += list(csv.DictReader(fh, delimiter='\t'))
    n = len(rows)
    if n == 0:
        sys.exit('no rows; nothing measured')

    off_dec = sum(1 for r in rows if r['off_verdict'] in DECIDED)
    on_dec = sum(1 for r in rows if r['on_verdict'] in DECIDED)
    gains, losses, flips, unexplained = [], [], [], []
    for r in rows:
        o, a = r['off_verdict'], r['on_verdict']
        if o in DECIDED and a in DECIDED and o != a:
            flips.append(r)
        elif o not in DECIDED and a in DECIDED:
            gains.append(r)
            if r.get('on_rung') != 'decided':
                unexplained.append(r)
        elif o in DECIDED and a not in DECIDED:
            losses.append(r)

    print(f'rows                {n}')
    print(f'off arm decided     {off_dec}')
    print(f'on  arm decided     {on_dec}')
    lo, hi = wilson(len(gains), n)
    print(f'GAIN  unknown->decided  {len(gains):3d}   Wilson [{lo:.1f}%, {hi:.1f}%]')
    lo, hi = wilson(len(losses), n)
    print(f'LOSS  decided->unknown  {len(losses):3d}   Wilson [{lo:.1f}%, {hi:.1f}%]')
    print(f'FLIP  sat<->unsat       {len(flips):3d}   (any nonzero is a P0)')
    print(f'net                     {len(gains) - len(losses):+d}')

    rung = {}
    for r in rows:
        rung[r.get('on_rung', '?')] = rung.get(r.get('on_rung', '?'), 0) + 1
    print(f'on-arm rung outcomes    {rung}')
    if rung.get('absent'):
        print(f'  WARNING: {rung["absent"]} row(s) never showed the rung -- '
              f'a stale binary would look exactly like this')

    if unexplained:
        print(f'  UNEXPLAINED GAINS: {len(unexplained)} row(s) gained without the '
              f'rung firing -- these are NOT this lever\'s')
        for r in unexplained:
            print(f'    {r["file"]}')
    if flips:
        for r in flips:
            print(f'  FLIP {r["file"]} off={r["off_verdict"]} on={r["on_verdict"]}')

    off_ms = sum(int(r['off_ms']) for r in rows)
    on_ms = sum(int(r['on_ms']) for r in rows)
    ratio = on_ms / off_ms if off_ms else float('nan')
    print(f'wall off {off_ms / 1000:.0f}s   on {on_ms / 1000:.0f}s   '
          f'ratio {ratio:.2f}x')

    print('\nGAINED FILES (off -> on):')
    for r in gains:
        print(f'  {r["off_verdict"]:>7s} -> {r["on_verdict"]:<5s} '
              f'rung={r.get("on_rung", "?"):8s} {r["on_ms"]:>6s}ms  {r["file"]}')
    print('\nLOST FILES (off -> on):')
    for r in losses:
        print(f'  {r["off_verdict"]:>7s} -> {r["on_verdict"]:<5s} '
              f'rung={r.get("on_rung", "?"):8s} {r["on_ms"]:>6s}ms  {r["file"]}')


main()
