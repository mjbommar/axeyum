#!/usr/bin/env python3
"""DT-FIELD-EXPANSION -- does RECURSIVE NESTED FIELD EXPANSION reach this file?

    expansion-reach.py <list-of-.smt2-paths>        one TSV row per DATATYPE

[ADR-2114] §4 named the representation the `INEXACT` bucket would need:
recursive tag/field expansion of a datatype-typed field to the datatype's own
finite nesting depth.  Terminating it requires the datatype's FIELD-SORT
CLOSURE to be acyclic; making the expansion EXACT additionally requires every
NON-datatype field sort in that whole closure to expand.

Those are two different predicates and today's code checks neither of them:

  * `register_datatype` (`datatype_native.rs:1491`) already WALKS INTO a
    `Sort::Datatype` field -- a datatype-typed field is not what it refuses.
    It refuses the first non-datatype, non-expanding sort anywhere in the
    closure (`:1511-1518`).  `register_refuses` in `dtshape.py` is that
    predicate.
  * `datatype_expansion_is_exact` (`:1576`) is ONE level deep: a datatype-typed
    field makes it false with no look-through at all.

So the lever can only convert a datatype where

    closure is ACYCLIC          (otherwise the unrolling does not terminate)
  AND every non-datatype field sort in the CLOSURE expands
                                (otherwise `register_datatype` still refuses)
  AND some constructor has a datatype-typed field
                                (otherwise the lever changes nothing: the
                                 datatype is already exact today)

This script reports all three per declared datatype, plus the closure depth, so
the intersection can be counted rather than assumed.  A file-level rollup is
printed to stderr.

The three columns to read are `today_exact`, `today_w1`, and `lever_converts`.
`lever_converts=1` is the ONLY row the lever changes.
"""

import os
import sys

sys.path.insert(
    0,
    os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        'dt-quant-trace-20260915',
    ),
)
import dtshape as D  # noqa: E402


def sig_of(path):
    with open(path, errors='replace') as fh:
        forms = list(D.parse(D.tokenize(fh.read())))
    sig = D.Sig()
    for f in forms:
        if isinstance(f, list) and f and not isinstance(f[0], list):
            h = str(f[0])
            if h == 'declare-sort':
                sig.usorts.add(str(f[1]))
            elif h == 'declare-datatypes':
                D.read_datatype_decl(f, sig)
    D.resolve(sig)
    return sig


def closure_depth(sig, dt, seen=()):
    """Datatype-field nesting depth of `dt`; -1 means the closure is CYCLIC."""
    if dt in seen:
        return -1
    best = 0
    for _, fields in sig.dt.get(dt, []):
        for _, fs in fields:
            if fs[0] == 'D':
                d = closure_depth(sig, fs[1], seen + (dt,))
                if d < 0:
                    return -1
                best = max(best, 1 + d)
    return best


def has_dt_field(sig, dt):
    return any(fs[0] == 'D'
               for _, fields in sig.dt.get(dt, [])
               for _, fs in fields)


def main():
    if len(sys.argv) != 2:
        sys.stderr.write(__doc__)
        return 2
    rows = 0
    files = 0
    print('\t'.join((
        'file', 'datatype', 'depth', 'cyclic', 'has_dt_field',
        'today_exact', 'today_w1', 'w1_sort', 'lever_converts',
    )))
    roll = {
        'files': 0, 'files_any_cyclic': 0, 'files_any_convert': 0,
        'dts': 0, 'cyclic': 0, 'exact_today': 0, 'w1_today': 0, 'convert': 0,
    }
    for line in open(sys.argv[1]):
        p = line.strip()
        if not p:
            continue
        files += 1
        roll['files'] += 1
        sig = sig_of(p)
        # The full path, NOT the basename: UFDT has DUPLICATE BASENAMES
        # across families, and keying a file-level rollup on the basename
        # silently merged 150 files into 127 on this lane's first run.
        base = p
        any_cyclic = False
        any_convert = False
        for dt in sig.dt:
            rows += 1
            roll['dts'] += 1
            d = closure_depth(sig, dt)
            cyclic = 1 if d < 0 else 0
            any_cyclic = any_cyclic or bool(cyclic)
            hdf = 1 if has_dt_field(sig, dt) else 0
            ex = 1 if D.exact(sig, dt) else 0
            w1 = D.register_refuses(sig, dt)
            w1f = 1 if w1 else 0
            # The lever converts this datatype iff it is inexact TODAY only
            # because of datatype-typed fields, its closure terminates, and no
            # non-expanding non-datatype sort survives anywhere in the closure.
            conv = 1 if (not ex and hdf and not cyclic and not w1f) else 0
            any_convert = any_convert or bool(conv)
            roll['cyclic'] += cyclic
            roll['exact_today'] += ex
            roll['w1_today'] += w1f
            roll['convert'] += conv
            print('\t'.join((
                base, dt, 'RECURSIVE' if cyclic else str(d), str(cyclic),
                str(hdf), str(ex), str(w1f),
                str(w1[1]) if w1 else 'NONE', str(conv),
            )))
        if any_cyclic:
            roll['files_any_cyclic'] += 1
        if any_convert:
            roll['files_any_convert'] += 1
    if not files:
        sys.stderr.write('NO FILES READ\n')
        return 3
    sys.stderr.write(
        'files=%(files)d  files with a CYCLIC datatype closure=%(files_any_cyclic)d  '
        'files the lever converts at least one datatype in=%(files_any_convert)d\n'
        'datatypes=%(dts)d  cyclic=%(cyclic)d  exact today=%(exact_today)d  '
        'W1-refused today=%(w1_today)d  LEVER CONVERTS=%(convert)d\n' % roll)
    return 0


if __name__ == '__main__':
    sys.exit(main())
