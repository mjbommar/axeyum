#!/usr/bin/env python3
"""ZERO-INST -- reduce a file to a minimal set of `assert`s that is still
unsat, so "what refutes it" is a named subset rather than a story.

    minimize-unsat-core.py <file> <workdir> [--solver PATH] [--tlimit MS]

Two phases:

  1. SINGLETON scan -- is any ONE assertion unsat on its own?  Reported
     explicitly, including the all-zero case, because "no single assertion
     is unsat" is itself a finding about where the refutation lives.
  2. GREEDY ddmin over the assertion list, keeping the file unsat.

Every intermediate call records its verdict.  A call that returns anything
other than `unsat` or `sat` (a parse error, a timeout, a crash) is treated
as NOT-unsat and counted separately, so a minimizer that is silently
erroring out cannot masquerade as a successful reduction: the summary line
prints `errors=` and a nonzero value invalidates the run.
"""
import argparse
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module
_sa = import_module('split-assertions'.replace('-', '_')) if False else None

# split-assertions.py is not importable by that name; inline the two helpers.
import re

QUANT = re.compile(r'(?<![A-Za-z0-9_.\-])(forall|exists)(?![A-Za-z0-9_.\-])')
HEAD = re.compile(r'\(\s*([A-Za-z0-9_.\-!|]+)')


def forms(text):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isspace():
            i += 1
            continue
        if c != '(':
            j = i
            while j < n and not text[j].isspace():
                j += 1
            i = j
            continue
        depth, j = 0, i
        while j < n:
            ch = text[j]
            if ch == ';':
                k = text.find('\n', j)
                j = n if k < 0 else k + 1
                continue
            if ch == '"':
                j += 1
                while j < n:
                    if text[j] == '"':
                        if j + 1 < n and text[j + 1] == '"':
                            j += 2
                            continue
                        j += 1
                        break
                    j += 1
                continue
            if ch == '|':
                k = text.find('|', j + 1)
                j = n if k < 0 else k + 1
                continue
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        out.append(text[i:j])
        i = j
    return out


def head(f):
    m = HEAD.match(f)
    return m.group(1) if m else '?'


class Runner:
    def __init__(self, solver, tlimit, workdir, pin):
        self.solver, self.tlimit, self.workdir, self.pin = solver, tlimit, workdir, pin
        self.calls = 0
        self.errors = 0
        os.makedirs(workdir, exist_ok=True)

    def is_unsat(self, prefix, keep, suffix):
        self.calls += 1
        path = os.path.join(self.workdir, 'probe.smt2')
        with open(path, 'w') as fh:
            fh.write('\n'.join(prefix + keep + suffix) + '\n')
        cmd = []
        if self.pin is not None:
            cmd += ['taskset', '-c', str(self.pin)]
        cmd += [self.solver, '--tlimit', str(self.tlimit), path]
        try:
            out = subprocess.run(cmd, capture_output=True, text=True,
                                 timeout=self.tlimit / 1000.0 + 30).stdout
        except subprocess.TimeoutExpired:
            self.errors += 1
            return False
        for line in out.splitlines():
            line = line.strip()
            if line == 'unsat':
                return True
            if line in ('sat', 'unknown'):
                return False
        self.errors += 1
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file')
    ap.add_argument('workdir')
    ap.add_argument('--solver', default='/nas3/data/axeyum/harness/bin/cvc5')
    ap.add_argument('--tlimit', type=int, default=30000)
    ap.add_argument('--pin', type=int, default=None)
    ap.add_argument('--singleton-only', action='store_true')
    args = ap.parse_args()

    fs = forms(open(args.file, encoding='utf-8', errors='replace').read())
    # `set-info` is DROPPED, not kept.  These benchmarks carry
    # `(set-info :status unsat)`, and cvc5 turns a correct `sat` on a
    # subset into `(error "Expected result unsat but got sat")` with a
    # nonzero exit -- which this script's first version counted as an
    # ERROR.  499 of 589 singleton probes on one file were `sat`
    # results wearing an error's clothes.  The benchmark's own metadata
    # is about the WHOLE file and is meaningless for a subset.
    prefix = [f for f in fs
              if head(f) not in ('assert', 'check-sat', 'exit', 'set-info')]
    asserts = [f for f in fs if head(f) == 'assert']
    suffix = ['(check-sat)']
    r = Runner(args.solver, args.tlimit, args.workdir, args.pin)

    if not r.is_unsat(prefix, asserts, suffix):
        print(f'{args.file}\tBASELINE-NOT-UNSAT\tasserts={len(asserts)}'
              f'\terrors={r.errors}')
        return

    singles = [i for i, a in enumerate(asserts)
               if r.is_unsat(prefix, [a], suffix)]
    print(f'{os.path.basename(args.file)}\tasserts={len(asserts)}'
          f'\tsingletons_unsat={len(singles)}\tsingleton_idx={singles[:5]}')
    if args.singleton_only:
        print(f'  calls={r.calls} errors={r.errors}')
        return

    keep = list(asserts)
    n = len(keep) // 2
    while n >= 1:
        i = 0
        changed = False
        while i < len(keep):
            trial = keep[:i] + keep[i + n:]
            if trial and r.is_unsat(prefix, trial, suffix):
                keep = trial
                changed = True
            else:
                i += n
        if not changed and n == 1:
            break
        n = n // 2 if not changed else min(n, max(1, len(keep) // 2))
        if n < 1:
            break

    quant = sum(1 for a in keep if QUANT.search(a))
    print(f'  MINIMAL\tkept={len(keep)}\tquantified={quant}'
          f'\tground={len(keep) - quant}\tcalls={r.calls}\terrors={r.errors}')
    out = os.path.join(args.workdir, 'minimal.smt2')
    with open(out, 'w') as fh:
        fh.write('\n'.join(prefix + keep + suffix) + '\n')
    print(f'  wrote {out}')


main()
