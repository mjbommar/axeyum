#!/usr/bin/env python3
"""CORE-SELECT -- can this instrument report a size OTHER than 1?

    control-nonvacuity.py [scratchdir]

A census whose headline is "the median minimal core is ONE conjunct" is
indistinguishable from a minimiser with a bug that always returns 1, and from a
core extractor that always returns the last assert.  Mutation testing would not
find that: it measures the guards you have.  So this control hands `core.py`
queries whose minimal core size is KNOWN BY CONSTRUCTION and requires the
reported number to match.

  chain(k)   `x0 < x1 < ... < x(k-1) < x0` as k separate conjuncts, padded with
             irrelevant satisfiable conjuncts.  Every one of the k is necessary
             -- delete any and the rest are satisfiable -- so the minimal core
             is EXACTLY k and it is also the minimum-cardinality one.
  needle     one self-contradictory conjunct buried among many irrelevant ones.
             Minimal core is 1, and it is NOT the last conjunct, so a tool that
             reports "the last assert" fails here while passing on chain(k).

Exit status depends on the finding: a mismatch on ANY row is a red control and
the numbers this lane publishes are not usable.
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def chain(k, pad):
    lines = ['(set-logic QF_LIA)', '(set-info :status unsat)']
    lines += [f'(declare-fun x{i} () Int)' for i in range(k)]
    lines += [f'(declare-fun p{i} () Int)' for i in range(pad)]
    body = [f'(< x{i} x{(i + 1) % k})' for i in range(k)]
    body += [f'(>= p{i} {i})' for i in range(pad)]
    # ONE assert holding the whole conjunction: the haystack this lane censuses
    # lives inside an `and`, and a control that used k separate `assert` forms
    # would not exercise the splitter at all.
    lines.append('(assert (and ' + ' '.join(body) + '))')
    lines.append('(check-sat)')
    return '\n'.join(lines) + '\n', k


def needle(pad, at):
    lines = ['(set-logic QF_LIA)', '(set-info :status unsat)']
    lines += [f'(declare-fun p{i} () Int)' for i in range(pad)]
    body = [f'(>= p{i} {i})' for i in range(pad)]
    # A SINGLE atom, deliberately: `(and (> p0 5) (< p0 1))` is two conjuncts
    # after splitting, so a control built from it expects 1 and correctly gets
    # 2.  That first draft of this file reported the instrument RED when the
    # instrument was right and the control was wrong -- worth keeping in the
    # record, because a control that cannot be wrong is not a control.
    body.insert(at, '(< p0 p0)')
    lines.append('(assert (and ' + ' '.join(body) + '))')
    lines.append('(check-sat)')
    return '\n'.join(lines) + '\n', 1


def run(tmp, rel, outdir):
    p = subprocess.run(
        [sys.executable, os.path.join(HERE, 'core.py'), rel, outdir,
         '--tlimit', '30', '--min-cap', '64', '--min-tlimit', '10',
         '--corpus', tmp],
        capture_output=True, text=True, timeout=900)
    out = p.stdout.strip().split('\t')
    return out


def main():
    scratch = sys.argv[1] if len(sys.argv) > 1 else tempfile.mkdtemp(prefix='cs-control-')
    corp = os.path.join(scratch, 'corpus')
    outdir = os.path.join(scratch, 'cores')
    os.makedirs(corp, exist_ok=True)
    cases = [('chain3.smt2',) + chain(3, 20),
             ('chain7.smt2',) + chain(7, 40),
             ('chain12.smt2',) + chain(12, 80),
             ('needle_early.smt2',) + needle(60, 0),
             ('needle_mid.smt2',) + needle(60, 30)]
    bad = 0
    print(f'{"case":<20} {"expect":>7} {"conjuncts":>10} {"z3_core":>8} {"minimal":>8}  verdict')
    for name, text, want in cases:
        open(os.path.join(corp, name), 'w').write(text)
        cols = run(corp, name, outdir)
        if len(cols) < 6:
            print(f'{name:<20} {want:>7} {"":>10} {"":>8} {"":>8}  NO-ROW: {cols}')
            bad += 1
            continue
        conj, split, zc, mn = cols[2], cols[3], cols[4], cols[5]
        ok = split == 'unsat' and mn.isdigit() and int(mn) == want
        # the needle cases also check that the core is not merely "the last
        # conjunct": the contradiction sits at index `at`, not at the end
        if ok and name.startswith('needle'):
            meta = json.load(open(os.path.join(outdir, name + '.json')))
            at = 0 if 'early' in name else 30
            ok = meta['indices'] == [at]
        print(f'{name:<20} {want:>7} {conj:>10} {zc:>8} {mn:>8}  '
              f'{"OK" if ok else "MISMATCH"}')
        bad += 0 if ok else 1
    print(f'\nscratch={scratch}')
    if bad:
        print(f'RED: {bad} of {len(cases)} controls disagree with the construction.')
    else:
        print(f'GREEN: {len(cases)} of {len(cases)} -- the instrument reports 1, 3, 7 '
              f'and 12 when the answer IS 1, 3, 7 and 12, and locates the needle '
              f'at its own index rather than at the end.')
    sys.exit(11 if bad else 0)


main()
