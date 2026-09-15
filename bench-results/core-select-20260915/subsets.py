#!/usr/bin/env python3
"""CORE-SELECT -- write the SUBSET files a reference-free strategy would pick.

    subsets.py <file.smt2-rel> <coredir> <outdir> [--corpus DIR] [--ks 1,2,5,10,25,50]

The reference found a core; that answers "would we decide it if we already knew
the answer", which is a CEILING and not a gain.  A strategy claim needs a rule
computable from the query alone.  The rules sized here are:

  suffix(k)  the LAST k conjuncts             -- VC generators emit the negated
                                                 goal last, so this is the
                                                 cheapest plausible rule there is
  prefix(k)  the FIRST k conjuncts            -- the CONTROL.  If prefix(k) works
                                                 as often as suffix(k), position
                                                 carries no information and the
                                                 suffix rule is not a finding
  small(k)   the k SHORTEST conjuncts by text -- [ADR-2050] found four of six
                                                 minimal cores were propositional
                                                 contradictions, which are short
  rel(d)     SInE-style symbol relevance: seed with the NEGATED-GOAL conjunct
             (the last conjunct whose head is `not`, else the last conjunct),
             then add every conjunct sharing a declared symbol with the current
             set, d times.  This is the rule the AUFDTLIRA data asks for: those
             cores are the negated goal plus one to four `forall` axioms out of
             12 to 54 conjuncts, which is precisely a premise-selection shape.
             `d` is FIXED across rows, so the rule is a strategy; the resulting
             SUBSET SIZE varies per row and is recorded.

Every one of these is computable from the file with no solver and no reference.
`k` is FIXED across rows: a per-row optimal k is chosen with knowledge of the
answer and is not a strategy.

Whether the core happens to LIE INSIDE a given subset is free arithmetic on the
core indices and is reported by `positions.py`.  This script exists for the part
that is not free: handing the subset to OUR solver and seeing whether it decides
it.  A subset that contains the core is unsat, but "contains an unsat core" and
"we return unsat within 24 s" are different claims and the second is the one
that matters.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smtsplit import args_of, split_script  # noqa: E402

CORPUS = '/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental'
TOKEN = re.compile(r'[A-Za-z0-9_~!@$%^&*+=<>.?/\-]+|\|[^|]*\|')


def flat(rel):
    return rel.replace('/', '_')


def declared_symbols(prefix):
    """Names introduced by `declare-fun` / `declare-const` / `define-fun`.

    Matching on DECLARED names rather than on every token is what keeps the
    relevance graph from collapsing: `and`, `=>`, `Int` and the numerals appear
    in every conjunct, so a token-sharing graph over raw text is complete and
    `rel(1)` would return the whole file on every row.
    """
    out = set()
    for f in prefix:
        h, a = args_of(f)
        if h in ('declare-fun', 'declare-const', 'define-fun', 'define-const',
                 'declare-datatype', 'define-fun-rec') and a:
            out.add(a[0])
    return out


def symbols_of(body, declared):
    return {t for t in TOKEN.findall(body) if t in declared}


def goal_seed(bodies):
    """The negated-goal conjunct: the LAST conjunct whose head is `not`.

    Falls back to the last conjunct. Both are computable from the query alone;
    neither consults the reference or the core.
    """
    for i in range(len(bodies) - 1, -1, -1):
        b = bodies[i].strip()
        if b.startswith('(') and args_of(b)[0] == 'not':
            return i
    return len(bodies) - 1


def relevance(bodies, declared, depth):
    seed = goal_seed(bodies)
    syms = [symbols_of(b, declared) for b in bodies]
    chosen = {seed}
    have = set(syms[seed])
    for _ in range(depth):
        grew = False
        for i, s in enumerate(syms):
            if i not in chosen and s & have:
                chosen.add(i)
                grew = True
        if not grew:
            break
        for i in chosen:
            have |= syms[i]
    return sorted(chosen)


def write(path, prefix, bodies):
    with open(path, 'w') as fh:
        fh.write('\n'.join(prefix))
        fh.write('\n')
        for b in bodies:
            fh.write(f'(assert {b})\n')
        fh.write('(check-sat)\n')


def main():
    rel, coredir, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    corpus = sys.argv[sys.argv.index('--corpus') + 1] if '--corpus' in sys.argv else CORPUS
    ks = [int(x) for x in (sys.argv[sys.argv.index('--ks') + 1]
                           if '--ks' in sys.argv else '1,2,5,10,25,50').split(',')]
    os.makedirs(outdir, exist_ok=True)

    meta = json.load(open(os.path.join(coredir, flat(rel) + '.json')))
    raw = open(os.path.join(corpus, rel), encoding='utf-8', errors='replace').read()
    prefix, bodies, _n, _mode = split_script(raw)
    n = len(bodies)
    if n != meta['conjuncts']:
        print(f'{rel}\tSPLIT-DRIFT\t{n}\t{meta["conjuncts"]}')
        sys.exit(4)

    order_small = sorted(range(n), key=lambda i: (len(bodies[i]), i))
    made, sizes = [], []
    for k in ks:
        if k > n:
            continue
        for tag, idx in (('suffix', list(range(n - k, n))),
                         ('prefix', list(range(k))),
                         ('small', sorted(order_small[:k]))):
            p = os.path.join(outdir, f'{flat(rel)}.{tag}{k}.smt2')
            write(p, prefix, [bodies[i] for i in idx])
            made.append(f'{tag}{k}')
    declared = declared_symbols(prefix)
    for d in (0, 1, 2, 3):
        idx = relevance(bodies, declared, d)
        p = os.path.join(outdir, f'{flat(rel)}.rel{d}.smt2')
        write(p, prefix, [bodies[i] for i in idx])
        made.append(f'rel{d}')
        # the subset SIZE the rule needed on this row, and whether it happens to
        # contain the core -- both recorded, neither used to choose `d`
        sizes.append(f'rel{d}={len(idx)}'
                     f'{"+core" if set(meta["indices"]) <= set(idx) else ""}')
    print(f'{rel}\tOK\t{n}\t{",".join(made)}\t{",".join(sizes)}')


main()
