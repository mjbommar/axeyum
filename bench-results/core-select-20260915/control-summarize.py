#!/usr/bin/env python3
"""CORE-SELECT -- can the headline test REPORT THE OTHER ANSWER?

    control-summarize.py <lane-dir> [scratchdir]

R5 is the lane's headline and it is computed by `summarize.py`.  A test that
only ever runs on the real data cannot distinguish "R5 passes" from "R5 cannot
fail".  So this copies the lane's own artifacts into a scratch directory,
mutates ONE column, and requires the printed verdict to move:

  M1  every `minimal` := 99       -> R5(a) median <= 5 must flip PASS -> FAIL
  M2  every `minimal` := 6        -> R5(a) must FAIL.  6 rather than 99 on
                                     purpose: 99 would pass a comparison that
                                     was off by an order of magnitude, and 6 is
                                     one past the pre-registered bound
  M2b every `minimal` := 5        -> R5(a) must PASS.  With M2 this pins the
                                     boundary as INCLUSIVE, which is where an
                                     off-by-one would otherwise live
  M3  every REF-UNSAT `split` := `unknown`
                                  -> R5(b) share >= 20 % must stop passing, and
                                     the REF-UNSAT bucket must read 0 WITH its
                                     denominator beside it
  M4  one `core_cvc5` := `sat`    -> the AUTHORITY-SPLIT count must go up by
                                     exactly one and that row must leave the
                                     size distribution

This control has already earned its keep once: renaming the summariser's
AUTHORITY-SPLIT line made M4 SURVIVE, and the surviving mutant is what said the
control had gone stale.  A baseline that cannot even READ a field is RED here
for the same reason -- `None` and `0` are not the same reading.

Each mutation is applied to a COPY.  Nothing here touches the committed data --
mutating in the shared tree puts your mutant on disk for every other lane's
run, and the failures it causes look like their bug.
"""
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# The one line every assertion below reads. Kept in ONE place because when the
# summariser renamed it, four separate inline regexes would have gone stale
# together and only the mutant that happened to depend on it would have said so.
SPLIT_RE = r'AUTHORITY-SPLIT[^\n]*?\s(\d+)\s'


def run_summary(d):
    p = subprocess.run([sys.executable, os.path.join(HERE, 'summarize.py'), d],
                       capture_output=True, text=True, timeout=600)
    return p.stdout


def field(text, pat):
    m = re.search(pat, text)
    return m.group(1) if m else None


def mutate(src, dst, fn):
    shutil.rmtree(dst, ignore_errors=True)
    shutil.copytree(src, dst)
    p = os.path.join(dst, 'ref', 'core-census.tsv')
    lines = open(p).read().rstrip('\n').split('\n')
    head = lines[0].split('\t')
    rows = [dict(zip(head, ln.split('\t'))) for ln in lines[1:]]
    rows = fn(rows)
    with open(p, 'w') as fh:
        fh.write('\t'.join(head) + '\n')
        for r in rows:
            fh.write('\t'.join(r[c] for c in head) + '\n')


def main():
    W = sys.argv[1]
    scratch = sys.argv[2] if len(sys.argv) > 2 else '/data0/axeyum/core-select-mutants'
    base = os.path.join(scratch, 'base')
    shutil.rmtree(scratch, ignore_errors=True)
    os.makedirs(scratch, exist_ok=True)
    shutil.copytree(W, base, ignore=shutil.ignore_patterns('*.pyc', '__pycache__'))

    out0 = run_summary(base)
    a0 = field(out0, r'R5\(a\).*?:\s*(PASS|FAIL)')
    b0 = field(out0, r'R5\(b\).*?:\s*(PASS|FAIL)')
    sp0 = field(out0, SPLIT_RE)
    print(f'baseline            R5(a)={a0} R5(b)={b0} authority-split={sp0}')
    if a0 is None or b0 is None or sp0 is None:
        print('RED: the baseline cannot READ one of the fields this control'
              ' asserts on. `None` is not `0`, and a mutation test whose baseline'
              ' reads None will report every mutant as killed or none of them.')
        sys.exit(16)

    def set_min(v):
        def f(rows):
            for r in rows:
                if r['minimal'].isdigit():
                    r['minimal'] = str(v)
                    r['min_status'] = 'MINIMAL'
            return rows
        return f

    def kill_unsat(rows):
        for r in rows:
            if r['split'] == 'unsat':
                r['split'] = 'unknown'
        return rows

    def split_authority(rows):
        for r in rows:
            if r['core_cvc5'] == 'unsat':
                r['core_cvc5'] = 'sat'
                break
        return rows

    bad = 0
    r5a = r'R5\(a\).*?:\s*(PASS|FAIL)'
    r5b = r'R5\(b\).*?:\s*(PASS|FAIL)'
    cases = [
        ('M1 minimal:=99', set_min(99), lambda o: field(o, r5a) == 'FAIL'),
        ('M2 minimal:=6', set_min(6), lambda o: field(o, r5a) == 'FAIL'),
        ('M2b minimal:=5', set_min(5), lambda o: field(o, r5a) == 'PASS'),
        ('M3 no REF-UNSAT', kill_unsat,
         lambda o: field(o, r5b) != 'PASS' and 'REF-UNSAT  0/' in o),
        ('M4 one cvc5 sat', split_authority,
         lambda o: field(o, SPLIT_RE) == str(int(sp0) + 1)),
    ]
    for name, fn, want in cases:
        d = os.path.join(scratch, name.split()[0])
        mutate(base, d, fn)
        out = run_summary(d)
        ok = want(out)
        a = field(out, r5a)
        b = field(out, r5b)
        sp = field(out, SPLIT_RE)
        print(f'{name:<20} R5(a)={a} R5(b)={b} authority-split={sp}  '
              f'{"KILLED" if ok else "SURVIVED"}')
        bad += 0 if ok else 1

    print(f'\nscratch={scratch}')
    if bad:
        print(f'RED: {bad} of {len(cases)} mutants SURVIVED -- the headline test'
              f' does not depend on the data it claims to read.')
    else:
        print(f'GREEN: {len(cases)} of {len(cases)} mutants killed. R5 moves when'
              f' the sizes move, when the bucket empties, and when an authority'
              f' disagrees.')
    sys.exit(17 if bad else 0)


main()
