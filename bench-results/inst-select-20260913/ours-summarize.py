#!/usr/bin/env python3
"""M3 -- our baseline on THIS lane's base, classified by ADR-1941's rule.

The winnable list is a snapshot from `c281a4b22`; this base is 28 commits later.
Rows this base now DECIDES are reported and dropped from the denominator, with
the count published, rather than inherited as still-failing.

ADR-1941: a row is UNCLASSIFIED when its budget sits in an unattributed OPEN
SEGMENT -- not merely when `attempts=` is below the division maximum.  The
`route-open` line is the discriminator and `bound_ms`/`total_ms` corroborates it.
Both readings are printed where they differ, as ADR-1941 step 6 requires.
"""

import argparse
import collections
import glob
import os
import sys


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


def family(giveup):
    """Collapse a give-up detail to its family, keeping the three e-matching
    loop exits distinct (ADR-1956) rather than merging them into one string."""
    g = giveup or ''
    if 'detail=' not in g:
        return '(no give-up line)'
    d = g.split('detail=', 1)[1].strip()
    for probe, name in [
        ('instantiation time budget exhausted', 'e-matching instantiation CLOCK'),
        ('quantified solve time budget exhausted', 'ladder CLOCK exhausted'),
        ('fixpoint', 'e-matching FIXPOINT'),
        ('growth', 'e-matching GROWTH-HEADROOM'),
        ('round', 'instantiation ROUND budget'),
    ]:
        if probe in d.lower():
            return name
    return d[:70]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--outdir', required=True)
    ap.add_argument('--divisions', nargs='+', default=['UFNIA', 'UFLIA'])
    args = ap.parse_args()

    print('## M3 -- our baseline, re-derived on this lane\'s base\n')
    print('| division | list rows | we now DECIDE | still undecided | ground dumps |')
    print('|---|---:|---:|---:|---:|')
    allrows = {}
    for div in args.divisions:
        rows = load(args.outdir, div)
        allrows[div] = rows
        dec = [r for r in rows if r['verdict'] in ('sat', 'unsat')]
        und = [r for r in rows if r['verdict'] not in ('sat', 'unsat')]
        gd = sum(1 for r in rows if r.get('dump_rows', '0') not in ('0', ''))
        print(f'| {div} | {len(rows)} | {len(dec)} | {len(und)} | {gd} |')

    print('\n**Rows this base decides that the snapshot list calls winnable:**\n')
    for div, rows in allrows.items():
        for r in rows:
            if r['verdict'] in ('sat', 'unsat'):
                print(f'- `{r["file"]}` — `{r["verdict"]}` in {r["wall_ms"]} ms')

    print('\n### Blocker families, and ADR-1941 classification\n')
    for div, rows in allrows.items():
        und = [r for r in rows if r['verdict'] not in ('sat', 'unsat')]
        fam = collections.Counter(family(r['giveup']) for r in und)
        openseg = [r for r in und if r.get('open_ms', '')]
        print(f'\n**{div}** — {len(und)} undecided')
        print(f'\n- rows carrying a `route-open` segment (ADR-1941 UNCLASSIFIED): '
              f'**{len(openseg)}**')
        # The attempts-only reading, printed alongside, as ADR-1941 step 6 requires.
        att = [int(r['attempts']) for r in und if r.get('attempts', '').isdigit()]
        if att:
            mx = max(att)
            below = sum(1 for a in att if a < mx)
            print(f'- the `attempts=`-only reading, for comparison: max `attempts={mx}`, '
                  f'{below} rows below it')
        print('\n| family | rows |')
        print('|---|---:|')
        for k, v in fam.most_common():
            print(f'| {k} | {v} |')

        by = collections.Counter(r.get('bound_by', '') for r in und)
        print('\n| `bound_by` | rows |')
        print('|---|---:|')
        for k, v in by.most_common():
            print(f'| `{k or "(none)"}` | {v} |')
    return 0


if __name__ == '__main__':
    sys.exit(main())
