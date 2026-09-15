#!/usr/bin/env python3
"""DT-QUANT-TRACE -- join the construct classifier, our traced run, and z3's
engine attribution, and answer the question the fix depends on.

    join-reference.py <shape.tsv> <axtrace.tsv> <ref-trace.tsv> [<out.tsv>]

THE QUESTION.  We refuse 17 of 134 AUFDTLIRA files on a datatype construct in
the GROUND theory.  Building a better ground datatype representation is worth
doing only if a better GROUND theory is what decides those files.  z3's
both-engines-off arm answers that directly and without any modelling: if z3
refutes a row with `smt.ematching=false smt.mbqi=false`, the refutation is
ground and a ground capability converts it; if z3 needs a quantifier engine,
then no datatype encoding in a quantifier-free solver reaches that row and the
bucket is not the one to build for.

This is the arm ADR-2090 did not have, and it is the reason `ref-trace.sh`
runs FOUR configurations rather than three.  Without the both-off control every
ground-refutable row reports "decided by either engine" and the census invents
an attribution for rows where no quantifier reasoning happened at all.
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
            return 'INEXACT' if tag in ('W2', 'W3', 'W3M') else tag
    return 'NONE'


def table(title, counter, denom):
    print(f'\n{title} (n={denom})')
    for k, v in sorted(counter.items(), key=lambda x: (-x[1], str(x[0]))):
        key = k if isinstance(k, str) else '  '.join(str(x) for x in k)
        print(f'  {key:<52} {v:>4}  {100.0 * v / denom:5.1f} %')


def main():
    if len(sys.argv) < 4:
        sys.stderr.write(__doc__)
        return 2
    shape = {r['file']: r for r in csv.DictReader(open(sys.argv[1]), delimiter='\t')}
    ax = {r['file']: r for r in csv.DictReader(open(sys.argv[2]), delimiter='\t')}
    ref = {r['file']: r for r in csv.DictReader(open(sys.argv[3]), delimiter='\t')}

    rows = [(f, shape[f], ax[f], ref[f]) for f in shape if f in ax and f in ref]
    n = len(rows)
    print(f'shape={len(shape)} ax={len(ax)} ref={len(ref)} joined={n}')
    if n != len(shape):
        print(f'  WARNING: {len(shape) - n} shape rows did not join')
    if not n:
        sys.stderr.write('NO ROWS JOINED\n')
        return 3

    table('z3 engine attribution -- ALL joined rows',
          Counter(r['attribution'] for _, _, _, r in rows), n)
    table('our verdict x z3 attribution',
          Counter((a['verdict'], r['attribution']) for _, _, a, r in rows), n)

    dt = [t for t in rows if observed(t[2]['giveup_raw']) != 'NONE']
    nd = max(len(dt), 1)
    print(f'\n===== THE {len(dt)} ROWS WE REFUSE ON A DATATYPE CONSTRUCT =====')
    table('  z3 attribution on exactly those rows',
          Counter(r['attribution'] for _, _, _, r in dt), nd)
    table('  wording x z3 attribution',
          Counter((observed(a['giveup_raw']), r['attribution'])
                  for _, _, a, r in dt), nd)

    ground = [t for t in dt if t[3]['attribution'] == 'GROUND']
    print(f'\n  CONVERTIBLE-BY-A-GROUND-CAPABILITY: {len(ground)} of {len(dt)}')
    print('  (z3 refutes these with smt.ematching=false smt.mbqi=false, so no')
    print('   quantifier reasoning is needed and a ground datatype theory reaches them)')
    for f, s, a, r in ground:
        print(f'    {observed(a["giveup_raw"]):<8} z3_ctor_ax={r["dt_ctor_ax"]:<5} '
              f'z3_acc_ax={r["dt_acc_ax"]:<5} qi={r["qi_inst"]:<6} {f[:70]}')

    # z3's own datatype-axiom counters, which are the direct answer to "what
    # does z3 do with the construct we refuse" -- read from z3, not from source.
    def num(x):
        try:
            return int(x)
        except (TypeError, ValueError):
            return 0
    print('\n  z3 datatype-axiom counters on those rows '
          '(theory_datatype.cpp:140 / :167)')
    for label, col in (('constructor-ax', 'dt_ctor_ax'), ('accessor-ax', 'dt_acc_ax'),
                       ('quant-instantiations', 'qi_inst'), ('max-generation', 'max_gen')):
        vals = sorted(num(r[col]) for _, _, _, r in dt)
        if vals:
            print(f'    {label:<22} min={vals[0]:<6} med={vals[len(vals) // 2]:<6} '
                  f'max={vals[-1]:<6} zero_on={sum(1 for v in vals if v == 0)}/{len(vals)}')

    if len(sys.argv) > 4:
        cols = ['file', 'predicted', 'our_verdict', 'wording', 'mbqi_exit',
                'z3_default', 'z3_emat_only', 'z3_mbqi_only', 'z3_neither',
                'z3_attribution', 'z3_qi_inst', 'z3_dt_ctor_ax', 'z3_dt_acc_ax']
        with open(sys.argv[4], 'w') as fh:
            fh.write('\t'.join(cols) + '\n')
            for f, s, a, r in sorted(rows):
                fh.write('\t'.join([
                    f, s['predicted'], a['verdict'], observed(a['giveup_raw']),
                    a['mbqi_exit'].split(',')[0] if a['mbqi_exit'] else 'NONE',
                    r['default'], r['emat_only'], r['mbqi_only'], r['neither'],
                    r['attribution'], r['qi_inst'], r['dt_ctor_ax'], r['dt_acc_ax'],
                ]) + '\n')
        print(f'\nwrote {sys.argv[4]}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
