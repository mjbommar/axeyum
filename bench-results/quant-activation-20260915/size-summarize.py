#!/usr/bin/env python3
"""QUANT-ACTIVATION -- join `qshape.py`'s rows to the Tier 1 ledger verdict and
print the CEILING IN FILES per division, with its denominator.

    size-summarize.py <sizedir> <listsdir>

Three things are printed and none of them is folded into the others:

  * the DENOMINATOR -- undecided Tier 1 rows per division, counted from the
    ledger itself rather than quoted from a brief;
  * the ACTIVATION TARGET -- undecided files holding at least one POSITIVELY
    OCCURRING universal that is not a unit assertion (`pos_forall_split` or
    `forall_under_binder`), which is the shape whose instances are dropped as
    `rej_nocontext` today;
  * the DISCRIMINATION CONTROL -- the same share on the DECIDED rows.  If the
    two shares are equal the classifier is measuring the corpus and not the
    blocker, and the ceiling means nothing.  That comparison is printed for
    every division, including where it is unflattering.

The predicted `mbqi_exit` distribution is printed separately, because it is a
statement about which RUNG ends the run and the activation target is a
statement about the SHAPE; a file can be in one and not the other.
"""

import collections
import os
import sys


def read_tsv(path):
    with open(path) as fh:
        header = fh.readline().rstrip('\n').split('\t')
        for line in fh:
            parts = line.rstrip('\n').split('\t')
            if len(parts) != len(header):
                continue
            yield dict(zip(header, parts))


DIVS = ('AUFDTLIRA', 'AUFLIRA', 'UF', 'UFDTLIRA', 'UFLIA', 'UFNIA')


def main(argv):
    sizedir, listsdir = argv[1], argv[2]
    grand = collections.Counter()
    print('== ACTIVATION CEILING IN FILES, per division ==')
    print('')
    hdr = ('division', 'T1', 'undec', 'u_target', 'u_share',
           'dec', 'd_target', 'd_share', 'u_widen', 'w_share', 'd_widen',
           'dw_share', 'u_split_wl', 'u_underbinder', 'u_multi', 'parse_fail')
    rows = []
    exits = {}
    for d in DIVS:
        verdicts = {}
        with open(os.path.join(listsdir, d + '.verdict-path.tsv')) as fh:
            for line in fh:
                v, p = line.rstrip('\n').split('\t', 1)
                verdicts[p] = v
        undec = dec = u_target = d_target = 0
        u_widen = d_widen = 0
        u_split_wl = u_under = u_multi = 0
        bad = 0
        ex = collections.Counter()
        for r in read_tsv(os.path.join(sizedir, d + '.shape.tsv')):
            v = verdicts.get(r['file'])
            if v is None:
                bad += 1
                continue
            if r['status'] != 'OK':
                bad += 1
                continue
            is_undec = (v == 'unknown')
            tgt = r['activation_target'] == '1'
            wid = r['widen_target'] == '1'
            if is_undec:
                undec += 1
                u_target += tgt
                u_widen += wid
                u_split_wl += 1 if int(r['split_whitelisted']) > 0 else 0
                u_under += 1 if int(r['forall_under_binder']) > 0 else 0
                u_multi += 1 if int(r['multi_binder_unit']) > 0 else 0
                ex[r['mbqi_exit_pred']] += 1
            else:
                dec += 1
                d_target += tgt
                d_widen += wid
        exits[d] = ex
        grand['undec'] += undec
        grand['u_target'] += u_target
        grand['u_widen'] += u_widen
        grand['dec'] += dec
        grand['d_target'] += d_target
        grand['d_widen'] += d_widen
        grand['bad'] += bad
        rows.append((d, undec + dec + bad, undec, u_target,
                     '%.1f%%' % (100.0 * u_target / undec) if undec else 'NA',
                     dec, d_target,
                     '%.1f%%' % (100.0 * d_target / dec) if dec else 'NA',
                     u_widen,
                     '%.1f%%' % (100.0 * u_widen / undec) if undec else 'NA',
                     d_widen,
                     '%.1f%%' % (100.0 * d_widen / dec) if dec else 'NA',
                     u_split_wl, u_under, u_multi, bad))
    widths = [max(len(str(x)) for x in [h] + [r[i] for r in rows])
              for i, h in enumerate(hdr)]
    print('  '.join(h.ljust(w) for h, w in zip(hdr, widths)))
    for r in rows:
        print('  '.join(str(x).ljust(w) for x, w in zip(r, widths)))
    print('')
    print('TOTAL undecided %d, activation target %d (%.1f%%), widen target %d (%.1f%%)'
          % (grand['undec'], grand['u_target'],
             100.0 * grand['u_target'] / grand['undec'] if grand['undec'] else 0.0,
             grand['u_widen'],
             100.0 * grand['u_widen'] / grand['undec'] if grand['undec'] else 0.0))
    print('      decided   %d, activation target %d (%.1f%%), widen target %d (%.1f%%)'
          % (grand['dec'], grand['d_target'],
             100.0 * grand['d_target'] / grand['dec'] if grand['dec'] else 0.0,
             grand['d_widen'],
             100.0 * grand['d_widen'] / grand['dec'] if grand['dec'] else 0.0))
    print('      unjoined / parse-fail %d' % grand['bad'])
    print('')
    print('== PREDICTED mbqi_exit on the UNDECIDED rows ==')
    print('')
    kinds = sorted({k for e in exits.values() for k in e})
    w0 = max(len('division'), *(len(d) for d in DIVS))
    print('division'.ljust(w0) + '  ' + '  '.join(k for k in kinds))
    for d in DIVS:
        cells = []
        for k in kinds:
            cells.append(str(exits[d][k]).ljust(len(k)))
        print(d.ljust(w0) + '  ' + '  '.join(cells))
    tot = collections.Counter()
    for e in exits.values():
        tot.update(e)
    print('TOTAL'.ljust(w0) + '  ' + '  '.join(str(tot[k]).ljust(len(k)) for k in kinds))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
