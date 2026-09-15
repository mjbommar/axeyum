#!/usr/bin/env python3
"""DT-QUANT-TRACE -- is the datatype nest RECURSIVE, how deep is it, and what
field sort does `register_datatype` actually refuse?

    nesting-depth.py <list-of-.smt2-paths>

This sizes the only fix the ground datatype theory could take for the
INEXACT bucket.  `datatype_expansion_is_exact` (`datatype_native.rs:1576`) is
false exactly when some field sort does not expand, and a `Sort::Datatype`
field never does -- it gets no expansion variable (`build_sym_vars`,
`:1645-1650`), which is what makes the encoded equality a relaxation.

The obvious repair is to expand a datatype-typed field RECURSIVELY, into its
own tag and fields.  Whether that terminates, and how deep it has to go, is a
property of the corpus and not of the code, so it is measured here rather than
assumed: a recursive datatype (`list = cons(car, cdr) | nil`) has no finite
unrolling and would still need a cut, while a finite record nest unrolls to an
EXACT expansion with no relaxation left at all.

The W1 arm is reported separately because depth unrolling does NOT fix it: an
array-of-datatype field's expansion variable would carry datatype content into
the residual, which `refuse_if_datatype_survives` must then refuse.
"""

import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
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


def depth(sig, dt, seen=()):
    """Nesting depth of datatype-typed fields; -1 means RECURSIVE."""
    if dt in seen:
        return -1
    best = 0
    for _, fields in sig.dt.get(dt, []):
        for _, fs in fields:
            if fs[0] == 'D':
                d = depth(sig, fs[1], seen + (dt,))
                if d < 0:
                    return -1
                best = max(best, 1 + d)
    return best


def main():
    if len(sys.argv) != 2:
        sys.stderr.write(__doc__)
        return 2
    w1sorts = Counter()
    depths = Counter()
    rec_files = 0
    files = 0
    for line in open(sys.argv[1]):
        p = line.strip()
        if not p:
            continue
        files += 1
        sig = sig_of(p)
        ds = [depth(sig, d) for d in sig.dt]
        if any(x < 0 for x in ds):
            rec_files += 1
            depths['RECURSIVE'] += 1
        else:
            depths[max(ds) if ds else 0] += 1
        for d in sig.dt:
            r = D.register_refuses(sig, d)
            if r:
                w1sorts[str(r[1])] += 1
    print('files=%d  files with a RECURSIVE datatype=%d' % (files, rec_files))
    print('max datatype-field NESTING DEPTH per file:')
    for k, v in sorted(depths.items(), key=lambda x: str(x[0])):
        print('   depth %-10s %d' % (k, v))
    print('the field sorts W1 (`register_datatype`) refuses, by sort:')
    for k, v in w1sorts.most_common(12):
        print('   %-70s %d' % (k, v))
    if not files:
        sys.stderr.write('NO FILES READ\n')
        return 3
    return 0


if __name__ == '__main__':
    sys.exit(main())
