#!/usr/bin/env python3
"""DT-QUANT-TRACE -- join the construct classifier against the traced run and
report the decline wording x construct table.

    summarize.py <shape.tsv> <axtrace.tsv> [<shape.tsv> <axtrace.tsv> ...]

Three things this prints that a single bucket count would hide.

1.  The WORDING as observed, never as predicted.  `dtshape.py` says which
    wording the datatype rung WOULD produce; this says which one the binary
    actually printed.  Where they differ the row is shown, because a classifier
    that is only ever compared against itself is the un-failable checker this
    repository keeps deleting.

2.  `mbqi_exit`, from `AXEYUM_QPROBE`.  The message
    `mbqi declined an unsupported fragment: <a datatype sentence>` is produced
    at `auto.rs:2488` by wrapping ANY `Err(Unsupported)` that comes back from
    `prove_unsat_by_mbqi`, and `prove_unsat_by_mbqi_inner` (auto.rs:12862)
    delegates to `prove_unsat_by_ematching` at five shape guards BEFORE its
    refutation loop runs.  So the prefix does not establish that MBQI ran, and
    `mbqi_exit` is the column that does.

3.  `attempts`, so a blocker is never ranked off a ladder that refused at its
    first rung -- CLAUDE.md's "a census can measure the ladder, not the solver".
"""

import csv
import sys
from collections import Counter

WORDINGS = (
    ('W1', 'a datatype field sort with no expansion variable'),
    ('W3', "an uninterpreted function whose RESULT datatype's expansion is not"),
    ('W3M', 'RESULT sort MENTIONS a datatype'),
    ('W2', 'congruence over a datatype argument whose expansion is not exact'),
)


def observed(raw):
    for tag, needle in WORDINGS:
        if needle in raw:
            return tag
    return 'NONE'


def fold(x):
    return 'INEXACT' if x in ('W2', 'W3', 'W3M') else x


def load(shape, trace):
    sh = {r['file']: r for r in csv.DictReader(open(shape), delimiter='\t')}
    tr = {}
    for r in csv.DictReader(open(trace), delimiter='\t'):
        tr[r['file']] = r
    rows = []
    for f, s in sh.items():
        t = tr.get(f)
        if t is None:
            continue
        rows.append((f, s, t))
    return rows, len(sh), len(tr)


def table(title, counter, denom):
    print(f'\n{title} (n={denom})')
    for k, v in sorted(counter.items(), key=lambda x: (-x[1], str(x[0]))):
        key = k if isinstance(k, str) else '  '.join(str(x) for x in k)
        print(f'  {key:<58} {v:>4}  {100.0 * v / denom:5.1f} %')


def exits(raw):
    """The DISTINCT `mbqi_exit` values, in first-seen order.

    `ax-trace.sh` joins every exit the run printed, and the rung is re-entered
    per ladder pass, so one row can carry fifty-four comma-separated copies of
    one guard. Printing the raw join makes the table unreadable and makes two
    rows that took the same exit look like two different findings; taking only
    the first would hide a row that took two different exits. The distinct set
    is what neither does.
    """
    out = []
    for e in raw.split(','):
        e = e.strip()
        if e and e not in out:
            out.append(e)
    return '+'.join(out) if out else 'NONE'


def reached_loop(raw):
    """Did MBQI's refutation loop run at all on this row?

    `refutation-loop` is printed at `auto.rs:12940`, immediately before the loop
    that calls `check_mbqi_ground_seed`. Every other exit returns
    `prove_unsat_by_ematching` instead. So this is the yes/no the census turns
    on, and it is read from the binary rather than from the message.
    """
    return 'refutation-loop' in raw


def main():
    args = sys.argv[1:]
    if len(args) < 2 or len(args) % 2:
        sys.stderr.write(__doc__)
        return 2
    allrows = []
    for i in range(0, len(args), 2):
        rows, nsh, ntr = load(args[i], args[i + 1])
        label = args[i].rsplit('/', 1)[-1]
        # An unmatched row is a JOIN failure, not an absent finding: print the
        # two denominators so a silently dropped population is visible.
        print(f'{label}: shape={nsh} trace={ntr} joined={len(rows)}')
        if len(rows) != nsh:
            print(f'  WARNING: {nsh - len(rows)} shape rows had no trace row')
        allrows += rows
    n = len(allrows)
    if not n:
        sys.stderr.write('NO ROWS JOINED\n')
        return 3

    table('verdict', Counter(t['verdict'] for _, _, t in allrows), n)
    # THE DENOMINATOR THAT DECIDES HOW TO READ EVERYTHING BELOW. If MBQI's loop
    # runs on almost no row, then "MBQI declined because of datatypes" is not a
    # statement about datatypes at all -- the datatype rows would look the same
    # as every other row. So this is printed BEFORE any datatype bucket.
    table('DID MBQI\'s refutation loop run -- WHOLE population',
          Counter('yes' if reached_loop(t['mbqi_exit']) else 'NO'
                  for _, _, t in allrows), n)
    table('mbqi_exit, distinct -- WHOLE population',
          Counter(exits(t['mbqi_exit']) for _, _, t in allrows), n)
    table('OBSERVED decline wording',
          Counter(fold(observed(t['giveup_raw'])) for _, _, t in allrows), n)
    table('PREDICTED wording (dtshape.py) x OBSERVED',
          Counter((fold(s['predicted']), fold(observed(t['giveup_raw'])))
                  for _, s, t in allrows), n)

    dt = [(f, s, t) for f, s, t in allrows
          if fold(observed(t['giveup_raw'])) != 'NONE']
    print(f'\n--- the {len(dt)} rows that DID print a datatype wording ---')
    nd = max(len(dt), 1)
    table('  mbqi_exit, distinct (AXEYUM_QPROBE)',
          Counter(exits(t['mbqi_exit']) for _, _, t in dt), nd)
    table('  DID MBQI\'s refutation loop run at all',
          Counter('yes' if reached_loop(t['mbqi_exit']) else 'NO'
                  for _, _, t in dt), nd)
    table('  message carries the "mbqi declined" prefix',
          Counter('yes' if 'mbqi declined' in t['giveup_raw'] else 'no'
                  for _, _, t in dt), nd)
    table('  bound_by on those rows',
          Counter(t['bound_by'] for _, _, t in dt), nd)
    # The control in the other direction: if the loop almost never runs on
    # datatype rows but almost always runs elsewhere, the finding is about
    # datatypes; if it almost never runs anywhere, it is about the ladder.
    nodt = [r for r in allrows if fold(observed(r[2]['giveup_raw'])) == 'NONE']
    table('  CONTROL -- did the loop run on the rows with NO datatype wording',
          Counter('yes' if reached_loop(t['mbqi_exit']) else 'NO'
                  for _, _, t in nodt), max(len(nodt), 1))

    print('\n--- construct presence, let-RESOLVED, over all joined rows ---')
    for col in sorted(c for c in allrows[0][1] if c.startswith('r_')):
        k = sum(1 for _, s, _ in allrows if s[col] not in ('0', 'NA'))
        print(f'  {col:<28} present on {k:>4} / {n}  {100.0 * k / n:5.1f} %')

    # A census whose classifier and whose binary never disagree has not been
    # tested against anything. Print the disagreements, or say there are none.
    dis = [(f, s['predicted'], observed(t['giveup_raw']))
           for f, s, t in allrows
           if fold(s['predicted']) != fold(observed(t['giveup_raw']))]
    print(f'\n--- classifier/binary disagreements: {len(dis)} of {n} ---')
    for f, p, o in dis[:40]:
        print(f'  pred={p:<5} obs={o:<5} {f[:96]}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
