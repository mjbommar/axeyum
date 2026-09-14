#!/usr/bin/env python3
"""ZERO-INST -- R5. Classify every row that moved, over three passes per arm.

    r5-classify.py <pass1.tsv ...> --  <pass2.tsv ...> -- <pass3.tsv ...>

or simply pass every shard TSV from every pass; rows are grouped by file.

Labels, and only the first counts toward the go/no-go:

  STABLE-GAIN   every pass: off undecided, on decided, SAME verdict each time
  STABLE-LOSS   every pass: off decided, on undecided
  FLIP          some pass disagrees with another on the DECIDED verdict --
                a P0, since a weakening can only ever add `unsat`
  UNSTABLE      anything else: the row moved in some passes and not others

ADR-2005 ran three passes of IDENTICAL code and got +1 / -2 / +0, so a single
pass is not evidence that a row moved.
"""
import collections
import csv
import sys

DECIDED = ('sat', 'unsat')


def main():
    byfile = collections.defaultdict(list)
    for path in sys.argv[1:]:
        if path == '--':
            continue
        with open(path) as fh:
            for r in csv.DictReader(fh, delimiter='\t'):
                byfile[r['file']].append(r)

    counts = collections.Counter()
    print(f'{"label":13s} {"passes":>6s}  {"off verdicts":22s} {"on verdicts":22s} file')
    for f, rs in sorted(byfile.items()):
        offs = [r['off_verdict'] for r in rs]
        ons = [r['on_verdict'] for r in rs]
        on_decided = [v for v in ons if v in DECIDED]
        if len(set(on_decided)) > 1:
            label = 'FLIP'
        elif all(o not in DECIDED for o in offs) and all(a in DECIDED for a in ons):
            label = 'STABLE-GAIN'
        elif all(o in DECIDED for o in offs) and all(a not in DECIDED for a in ons):
            label = 'STABLE-LOSS'
        else:
            label = 'UNSTABLE'
        counts[label] += 1
        print(f'{label:13s} {len(rs):6d}  {",".join(offs):22s} {",".join(ons):22s} '
              f'{f.split("/")[-1]}')
    print()
    for label, n in sorted(counts.items()):
        print(f'{label:13s} {n}')
    print(f'\nrows counting toward the go/no-go (STABLE-GAIN only): '
          f'{counts["STABLE-GAIN"]}')
    if counts['FLIP']:
        print('FLIP present -- P0, the lever does not ship regardless of count')
        sys.exit(1)


main()
