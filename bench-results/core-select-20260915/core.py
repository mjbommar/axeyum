#!/usr/bin/env python3
"""CORE-SELECT -- find a minimal refutable subset of ONE benchmark, with a
reference solver, and record which of three different sizes each number is.

    core.py <file.smt2> <outdir> [--tlimit 60] [--min-cap 64]
            [--min-tlimit 15] [--min-budget 600] [--corpus DIR]

Pipeline, every step's verdict re-checked so a bug that drops the `unsat`
produces a labelled failure rather than a small file with a wrong story:

  1. split every top-level `(assert (and ...))` into conjuncts (an EQUIVALENCE)
     and CHECK the split file is still `unsat`;
  2. name each conjunct and take z3's `(get-unsat-core)` -- this is *a* core,
     NOT the core and NOT minimal, and the column is named `z3_core` for
     exactly that reason;
  3. greedily delete core members while the remainder stays `unsat`; the
     fixpoint is minimal with respect to SINGLE DELETION (1-minimal), which is
     still not minimum cardinality, and that column is named `minimal`;
  4. re-check the final subset under z3 AND cvc5 from its written file by a
     fresh process (R4).

Dropping conjuncts WEAKENS the formula, so `subset unsat => whole unsat`.  The
converse is never claimed.

Writes `<outdir>/<flat>.core.smt2` (the final subset, runnable on its own) and
`<outdir>/<flat>.json` (the conjunct INDICES of the subset within the file's
conjunct list -- what a selection strategy would have had to find).
Prints one TSV row on stdout.
"""
import json
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import split_script  # noqa: E402

Z3 = os.environ.get('CS_Z3', 'z3')
CVC5 = os.environ.get('CS_CVC5', '/nas3/data/axeyum/harness/bin/cvc5')
CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'


def flat(rel):
    return rel.replace('/', '_')


def write(path, prefix, bodies, names=None, want_core=False):
    with open(path, 'w') as fh:
        if want_core:
            fh.write('(set-option :produce-unsat-cores true)\n')
        fh.write('\n'.join(prefix))
        fh.write('\n')
        for k, b in enumerate(bodies):
            if names is None:
                fh.write(f'(assert {b})\n')
            else:
                fh.write(f'(assert (! {b} :named {names[k]}))\n')
        fh.write('(check-sat)\n')
        if want_core:
            fh.write('(get-unsat-core)\n')


def z3_run(path, tlimit, want_core=False):
    try:
        p = subprocess.run([Z3, f'-T:{tlimit}', path], capture_output=True,
                           text=True, timeout=tlimit * 4 + 30)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', []
    txt = p.stdout
    v = 'unknown'
    for line in txt.splitlines():
        s = line.strip()
        if s in ('sat', 'unsat', 'unknown'):
            v = s
            break
    names = []
    if want_core and v == 'unsat':
        i = txt.find('(', txt.find('unsat') + 5)
        if i >= 0:
            j = txt.find(')', i)
            names = txt[i + 1:j if j > i else None].split()
    return v, names


def cvc5_run(path, tlimit_ms):
    if not os.path.exists(CVC5):
        return 'NO-CVC5'
    try:
        p = subprocess.run([CVC5, '--lang', 'smt2', f'--tlimit={tlimit_ms}', path],
                           capture_output=True, text=True,
                           timeout=tlimit_ms / 1000.0 * 4 + 30)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    for line in p.stdout.splitlines():
        s = line.strip()
        if s in ('sat', 'unsat', 'unknown'):
            return s
    return 'NOVERDICT'


def arg(name, default):
    return type(default)(sys.argv[sys.argv.index(name) + 1]) if name in sys.argv else default


def row(**kw):
    cols = ('file', 'mode', 'conjuncts', 'split', 'z3_core', 'minimal',
            'min_status', 'core_z3', 'core_cvc5', 'ms')
    print('\t'.join(str(kw.get(c, 'NA')) for c in cols), flush=True)


def main():
    rel = sys.argv[1]
    outdir = sys.argv[2]
    tl = arg('--tlimit', 60)
    min_cap = arg('--min-cap', 64)
    min_tl = arg('--min-tlimit', 15)
    min_budget = arg('--min-budget', 600)
    corpus = sys.argv[sys.argv.index('--corpus') + 1] if '--corpus' in sys.argv else CORPUS
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()

    src = os.path.join(corpus, rel)
    raw = open(src, encoding='utf-8', errors='replace').read()
    prefix, bodies, _n_assert, mode = split_script(raw)
    n0 = len(bodies)
    base = os.path.join(outdir, flat(rel))
    work = base + '.work.smt2'

    if n0 == 0:
        row(file=rel, mode=mode, conjuncts=0, split='NO-CONJUNCTS',
            ms=int((time.time() - t0) * 1000))
        return

    # 1. the split is an equivalence -- CHECK it before believing anything else
    write(work, prefix, bodies)
    v, _ = z3_run(work, tl)
    if v != 'unsat':
        row(file=rel, mode=mode, conjuncts=n0, split=v,
            ms=int((time.time() - t0) * 1000))
        os.remove(work)
        return

    # 2. *a* core -- not minimal
    names = [f'cs{k}' for k in range(n0)]
    write(work, prefix, bodies, names, want_core=True)
    v, core = z3_run(work, tl, want_core=True)
    if v != 'unsat' or not core:
        row(file=rel, mode=mode, conjuncts=n0, split='unsat',
            z3_core=f'CORE-FAILED:{v}', ms=int((time.time() - t0) * 1000))
        os.remove(work)
        return
    idx = sorted({int(c[2:]) for c in core if c.startswith('cs') and c[2:].isdigit()})
    n1 = len(idx)

    # 3. greedy single deletion -> 1-minimal (NOT minimum cardinality).
    #    Capped two ways, both fixed before any core was seen: by core size and
    #    by a wall-clock budget.  A row that hits either reports the size it
    #    reached, labelled, never a guess.
    status = 'MINIMAL'
    if n1 > min_cap:
        status = f'MIN-CAPPED>{min_cap}'
    else:
        deadline = time.time() + min_budget
        changed = True
        while changed and len(idx) > 1:
            changed = False
            for k in range(len(idx) - 1, -1, -1):
                if time.time() > deadline:
                    status = 'MIN-BUDGET'
                    changed = False
                    break
                cand = idx[:k] + idx[k + 1:]
                write(work, prefix, [bodies[i] for i in cand])
                vv, _ = z3_run(work, min_tl)
                if vv == 'unsat':
                    idx = cand
                    changed = True
            if status == 'MIN-BUDGET':
                break

    # 4. two independent authorities on the final subset, from its own file
    out = base + '.core.smt2'
    write(out, prefix, [bodies[i] for i in idx])
    cz, _ = z3_run(out, tl)
    cc = cvc5_run(out, tl * 1000)
    json.dump({'file': rel, 'conjuncts': n0, 'mode': mode, 'z3_core': n1,
               'minimal': len(idx), 'min_status': status, 'indices': idx,
               'core_z3': cz, 'core_cvc5': cc},
              open(base + '.json', 'w'), indent=1)
    os.remove(work)
    row(file=rel, mode=mode, conjuncts=n0, split='unsat', z3_core=n1,
        minimal=len(idx), min_status=status, core_z3=cz, core_cvc5=cc,
        ms=int((time.time() - t0) * 1000))


main()
