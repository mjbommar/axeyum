#!/usr/bin/env python3
"""QUANT-ACTIVATION -- the AGREEMENT CONTROL for `qshape.py`'s predicted
`mbqi_exit` against the OBSERVED one, on [ADR-2114]'s 134 traced `AUFDTLIRA`
files.

    exit-agreement.py <axtrace.tsv> <shape.tsv> [<shape.tsv> ...]

A classifier only ever compared against itself is the un-failable checker this
repository keeps deleting, so this joins the prediction to a run that actually
happened and prints BOTH directions of disagreement separately.

WHAT THE OBSERVED COLUMN IS, and why the join is containment rather than
equality.  `axtrace`'s `mbqi_exit` is every `[mbqi-shape]` line the run printed,
comma-joined -- the ladder re-enters the MBQI rung many times per file, over
assertions the preprocessor has already rewritten, so one file commonly shows
two distinct exits.  `qshape.py` predicts the FIRST guard that fires on the
ORIGINAL assertion list, exactly once.  The honest question is therefore
"is the prediction among the exits the run took", and the failure that matters
is a prediction the run NEVER took.

NON-VACUITY.  A containment test against a set that is usually large drifts
toward answering yes for everything.  So the report also prints how many
observed sets have exactly one distinct exit -- the rows where containment is
equality and the test has real discriminating power -- and the agreement rate
restricted to those.
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


def key_of(path):
    """`axtrace` names a core `<DIV>_<dirs>_<base>.smt2.core.smt2` and an
    original by its corpus-relative path.  Reduce both to the basename stem so
    the two populations join on one key."""
    b = os.path.basename(path)
    for suf in ('.smt2.core.smt2', '.core.smt2', '.smt2'):
        if b.endswith(suf):
            b = b[: -len(suf)]
            break
    return b


def main(argv):
    axtrace, shapes = argv[1], argv[2:]
    observed = {}
    for r in read_tsv(axtrace):
        ex = {e for e in r['mbqi_exit'].split(',') if e and e != 'NONE'}
        observed.setdefault(key_of(r['file']), set()).update(ex)
    predicted = {}
    for s in shapes:
        for r in read_tsv(s):
            if r['status'] == 'OK':
                predicted[key_of(r['file'])] = r['mbqi_exit_pred']

    joined = 0
    agree = 0
    single = 0
    single_agree = 0
    miss = collections.Counter()
    unjoined_obs = 0
    for k, ex in observed.items():
        p = predicted.get(k)
        if p is None:
            unjoined_obs += 1
            continue
        if not ex:
            continue        # the rung was never reached; nothing to agree with
        joined += 1
        ok = p in ex
        agree += ok
        if len(ex) == 1:
            single += 1
            single_agree += ok
        if not ok:
            miss[(p, ','.join(sorted(ex)))] += 1

    print('observed rows with at least one exit : %d' % sum(1 for e in observed.values() if e))
    print('observed rows with NO exit (rung never reached): %d'
          % sum(1 for e in observed.values() if not e))
    print('observed rows with no shape row to join to      : %d' % unjoined_obs)
    print('')
    print('JOINED                       : %d' % joined)
    print('prediction among observed    : %d (%.1f%%)'
          % (agree, 100.0 * agree / joined if joined else 0.0))
    print('')
    print('DISCRIMINATING SUBSET -- observed set has exactly ONE distinct exit,')
    print('so containment IS equality and the test can fail:')
    print('  rows                       : %d' % single)
    print('  prediction equals observed : %d (%.1f%%)'
          % (single_agree, 100.0 * single_agree / single if single else 0.0))
    print('')
    if miss:
        print('DISAGREEMENTS (predicted -> observed set), the failing direction:')
        for (p, ex), n in miss.most_common():
            print('  %4d  %-28s  not in {%s}' % (n, p, ex))
    else:
        print('DISAGREEMENTS: none.  A zero here is only meaningful beside the')
        print('discriminating-subset count above; read both.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
