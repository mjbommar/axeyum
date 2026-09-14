#!/usr/bin/env python3
"""M2 -- the bucket distribution, reported over the population it can speak for.

Bucket G needs OUR ground set, which exists only for files whose run reached the
e-matching loop's give-up.  Files without one are reported as a SEPARATE
denominator and get a two-way Q / not-Q reading, never a three-way one -- the
brief's instruction when buckets 2 and 3 cannot be separated.
"""

import argparse
import collections
import json
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--json', required=True)
    args = ap.parse_args()
    with open(args.json, encoding='utf-8') as fh:
        blob = json.load(fh)
    rows = blob['rows']

    withg = [r for r in rows if r['our_ground_blocks'] > 0]
    nog = [r for r in rows if r['our_ground_blocks'] == 0]

    print('## M2 -- what cvc5 instantiated with, classified\n')
    print('`Q` in the query, `G` in our ground set but not the query, `N` neither,')
    print('`S` a cvc5-invented Skolem (its own class -- it has no counterpart in')
    print('the query by construction, so calling it `N` would manufacture the')
    print('finding this lane exists to test).\n')
    print(f'Files with a cvc5 refutation dump: **{len(rows)}**.')
    print(f'Of those, files where our run produced a ground set: **{len(withg)}**;')
    print(f'without one: **{len(nog)}** -- reported separately, two-way only.\n')

    def tally(rs, label, keys):
        occ = collections.Counter()
        dis = collections.Counter()
        for r in rs:
            for k in keys:
                occ[k] += r[f'occ_{k}']
                dis[k] += r[f'distinct_{k}']
        to, td = sum(occ.values()), sum(dis.values())
        print(f'\n### {label}\n')
        print('| bucket | distinct terms | share | instantiation slots | share |')
        print('|---|---:|---:|---:|---:|')
        for k in keys:
            print(f'| **{k}** | {dis[k]} | {100*dis[k]/td:.1f}% | {occ[k]} '
                  f'| {100*occ[k]/to:.1f}% |')
        print(f'| *total* | {td} | | {to} | |')
        return dis, occ

    dis, _ = tally(withg, f'Three-way, over the {len(withg)} files with our ground set',
                   ['Q', 'G', 'N', 'S'])

    # Two-way reading over EVERY file, which needs no ground set at all.
    occ2 = collections.Counter(); dis2 = collections.Counter()
    for r in rows:
        dis2['Q'] += r['distinct_Q']
        dis2['S'] += r['distinct_S']
        dis2['not-Q'] += r['distinct_G'] + r['distinct_N']
        occ2['Q'] += r['occ_Q']
        occ2['S'] += r['occ_S']
        occ2['not-Q'] += r['occ_G'] + r['occ_N']
    td, to = sum(dis2.values()), sum(occ2.values())
    print(f'\n### Two-way, over all {len(rows)} files (needs no ground set)\n')
    print('| bucket | distinct terms | share | slots | share |')
    print('|---|---:|---:|---:|---:|')
    for k in ['Q', 'not-Q', 'S']:
        print(f'| **{k}** | {dis2[k]} | {100*dis2[k]/td:.1f}% | {occ2[k]} '
              f'| {100*occ2[k]/to:.1f}% |')

    print('\n### Bucket N is CONTAMINATED, and by how much\n')
    na = sum(r['distinct_N_arith_head'] for r in withg)
    nt = sum(r['distinct_N'] for r in withg)
    qt = sum(r['distinct_Q'] for r in withg)
    gt = sum(r['distinct_G'] for r in withg)
    print('cvc5 prints arithmetic in a sum-of-monomials normal form — `(+ -1 (typeof S))`,')
    print('`(* -1 x)` — where the source writes `(- (typeof S) 1)`. Those are the SAME')
    print('term and compare unequal as strings, so an N with an arithmetic head is')
    print('evidence of a printer disagreement at least as much as of an absence.\n')
    print(f'- bucket N, all heads: **{nt}** distinct terms')
    print(f'- of those, head in `+ - * div mod /`: **{na}** ({100*na/nt:.1f}% of N)')
    print(f'- **N with a non-arithmetic head: {nt-na}** — the defensible residue\n')
    den = qt + gt + (nt - na)
    print('Re-reading the three-way split with the contaminated part set aside')
    print('entirely (Skolems excluded, since they are their own class):\n')
    print('| bucket | distinct | share of Q+G+N(non-arith) |')
    print('|---|---:|---:|')
    print(f'| **Q** (in the query) | {qt} | {100*qt/den:.1f}% |')
    print(f'| **G** (we built it, not in the query) | {gt} | {100*gt/den:.1f}% |')
    print(f'| **N** (non-arithmetic head) | {nt-na} | {100*(nt-na)/den:.1f}% |')
    print(f'\n**Q+G = {100*(qt+gt)/den:.1f}%** of that residue: terms we either read or built.')

    print('\n### Files with ANY bucket-N term\n')
    nfiles = [r for r in withg if r['distinct_N'] > 0]
    print(f'**{len(nfiles)} of {len(withg)}** files with a ground set contribute any')
    print('term we neither read in the query nor ever built.\n')
    for r in sorted(nfiles, key=lambda r: -r['distinct_N'])[:12]:
        print(f'- `{r["file"]}` — {r["distinct_N"]} of {r["distinct_total"]} distinct, '
              f'e.g. {", ".join("`" + e + "`" for e in r["N_examples"][:4])}')

    print('\n### The brief\'s small-numeral hypothesis\n')
    dn = sum(r['distinct_numeral'] for r in rows)
    ds = sum(r['distinct_skolem'] for r in rows)
    dt = sum(r['distinct_term'] for r in rows)
    tot = dn + ds + dt
    print(f'| shape | distinct terms | share |')
    print(f'|---|---:|---:|')
    print(f'| integer numeral | {dn} | {100*dn/tot:.1f}% |')
    print(f'| cvc5 Skolem | {ds} | {100*ds/tot:.1f}% |')
    print(f'| other ground term | {dt} | {100*dt/tot:.1f}% |')

    print('\n### Explicit `:pattern` -- does the 2019-Preiner shape generalise?\n')
    fam = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        key = 'UFNIA/2019-Preiner' if r['file'].startswith('UFNIA/2019-Preiner') \
            else r['file'].split('/')[0] + '/' + r['file'].split('/')[1]
        fam[key][0] += 1
        fam[key][1] += r['quantifiers']
        fam[key][2] += r['quantifiers_with_pattern']
    print('| family | files | quantifiers instantiated | of those, carrying `:pattern` |')
    print('|---|---:|---:|---:|')
    for k, (f, q, p) in sorted(fam.items(), key=lambda kv: -kv[1][0]):
        print(f'| `{k}` | {f} | {q} | {p} |')
    tq = sum(v[1] for v in fam.values())
    tp = sum(v[2] for v in fam.values())
    print(f'| **all** | **{len(rows)}** | **{tq}** | **{tp}** |')
    return 0


if __name__ == '__main__':
    sys.exit(main())
