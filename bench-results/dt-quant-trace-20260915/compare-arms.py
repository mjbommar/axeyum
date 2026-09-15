#!/usr/bin/env python3
"""DT-QUANT-TRACE -- compare two `ax-trace.sh` arms row by row.

    compare-arms.py <base.tsv> <arm.tsv> [--expect-note]

ADR-2114's change is telemetry: a `&mut bool` set at one point and read at one
point to pick a SUFFIX on a give-up sentence.  Nothing branches on
`UnknownReason::detail`, so it cannot move a verdict -- but "cannot" is an
argument and this repository's rule is to measure it.  Equal TOTALS do not
imply equal rows, so the comparison is per file.

`--expect-note` additionally requires the arm to be non-vacuous: the correction
must actually appear on the rows whose MBQI loop did not run and must NOT
appear on the rows whose loop did.  Without that, an arm where the change did
nothing at all would report a perfect zero-diff and look like a pass.
"""

import csv
import sys
from collections import Counter

NOTE = 'ADR-2114'
NEEDLES = ('a datatype field sort with no expansion variable',
           "an uninterpreted function whose RESULT datatype's expansion is not",
           'RESULT sort MENTIONS a datatype',
           'congruence over a datatype argument whose expansion is not exact')


def load(p):
    return {r['file']: r for r in csv.DictReader(open(p), delimiter='\t')}


def main():
    base, arm = load(sys.argv[1]), load(sys.argv[2])
    expect_note = '--expect-note' in sys.argv[3:]
    shared = sorted(set(base) & set(arm))
    print(f'base={len(base)} arm={len(arm)} compared={len(shared)}')
    if len(shared) != len(base) or len(shared) != len(arm):
        print(f'  WARNING: {len(base) - len(shared)} base rows and '
              f'{len(arm) - len(shared)} arm rows did not pair')

    diffs = [f for f in shared if base[f]['verdict'] != arm[f]['verdict']]
    flips = [f for f in diffs
             if {base[f]['verdict'], arm[f]['verdict']} == {'sat', 'unsat'}]
    print(f'\nVERDICT CHANGES: {len(diffs)} of {len(shared)}')
    print(f'sat<->unsat FLIPS: {len(flips)}')
    for f in diffs:
        print(f"  {base[f]['verdict']:>8} -> {arm[f]['verdict']:<8} {f[:80]}")
    print('\nverdict totals')
    for label, t in (('base', base), ('arm', arm)):
        print(f'  {label:<5} {dict(Counter(r["verdict"] for r in t.values()))}')

    rc = 1 if diffs else 0

    if expect_note:
        # NON-VACUITY. A change that did nothing would produce 0 diffs above and
        # read as a pass, so the arm has to be shown to have done its job: the
        # note present exactly where the loop did not run.
        loop = {f: 'refutation-loop' in arm[f]['mbqi_exit'] for f in shared}
        dtrows = [f for f in shared
                  if any(x in arm[f]['giveup_raw'] for x in NEEDLES)]
        noted = [f for f in dtrows if NOTE in arm[f]['giveup_raw']]
        wrong = [f for f in dtrows if (NOTE in arm[f]['giveup_raw']) == loop[f]]
        base_noted = [f for f in dtrows if NOTE in base[f]['giveup_raw']]
        print(f'\nNON-VACUITY, over the {len(dtrows)} datatype-wording rows')
        print(f'  carry the correction, ARM  : {len(noted)}')
        print(f'  carry the correction, BASE : {len(base_noted)}  '
              f'(must be 0 -- the base binary predates it)')
        print(f'  correction on the WRONG side of the loop flag: {len(wrong)}')
        if not dtrows or not noted or base_noted or wrong:
            print('  NON-VACUITY FAILED')
            rc = 1
        else:
            print('  NON-VACUITY OK')

    print('\nRESULT: ' + ('CHANGED' if rc else 'IDENTICAL'))
    return rc


if __name__ == '__main__':
    sys.exit(main())
