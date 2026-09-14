#!/usr/bin/env python3
"""M2 -- classify every ground term cvc5 instantiated with.

For each file cvc5 refutes, `--dump-instantiations` prints, per quantified
formula, the tuples of ground terms it instantiated with.  This classifies each
such term into:

  Q  present as a GROUND subterm of the original query
  G  present in OUR accumulated ground set at give-up, but not in Q
  N  neither
  S  a cvc5-invented Skolem constant (`@quantifiers_skolemize_*`)

S is its OWN class and is deliberately NOT folded into Q/G/N.  A cvc5 Skolem has
no counterpart in the query by construction, and matching it to one of our
Skolems modulo renaming would be a judgement, not a measurement.  Reporting it
as N would manufacture exactly the finding this lane exists to test.

DESIGN: the instantiating terms are a SMALL set, so this does not build the
subterm closure of the query at all.  It collects the targets first and then
asks, for each subterm position of the query, only whether it IS one of them.
The first version built the closure with full `let` expansion and hung on the
corpus -- these benchmarks nest `let` hundreds deep with shared bindings, so
substitution is exponential.  Nothing here expands a `let`; binding VALUES are
walked in their own right, so a term the body mentions only as `_let_7` is still
found, while the NAME `_let_7` is never mistaken for a constant.

GROUND means ground: a position counts only when no variable bound by an
enclosing binder occurs in it.  Without that, the numeral inside
`(forall ((a Int)) (f a 2))` would be indistinguishable from the non-ground
`(f a 2)`.  The same exclusion is applied to our own dump for our binder
spellings (`!q.*`, `!qu_*`) -- matching those would turn "we still have an open
quantifier here" into a false PRESENT.

CAVEAT, carried into the report rather than left here: --dump-instantiations
prints what cvc5 PRODUCED on the run that ended unsat, not a minimised set the
refutation NEEDS.  This measures a SUPERSET.  A small N is therefore strong
evidence ("everything cvc5 used, we had"); a large N is weak ("cvc5's winning
run used terms we never build" -- some of which it may not have needed).
"""

import argparse
import json
import os
import re
import sys
from collections import Counter

# ---------------------------------------------------------------- s-expressions

TOKEN = re.compile(r'''\s*(?:(;[^\n]*)|(\|[^|]*\|)|("(?:[^"]|"")*")|([()])|([^\s()|";]+))''')

BINDERS = {'forall', 'exists', 'lambda'}
OUR_BINDER = re.compile(r'^(!q\.|!qu_)')
SKOLEM = re.compile(r'@quantifiers_skolemize|^@')
NUMERAL = re.compile(r'^-?\d+$')
# Heads whose printed form differs between cvc5's sum-of-monomials normal form
# and the source's surface syntax.  Used only to QUALIFY bucket N, never to
# move a term out of it.
ARITH_HEADS = {'+', '-', '*', 'div', 'mod', '/'}

# A target term is small; refusing to render anything larger keeps the walk from
# being quadratic on 10 MB benchmarks.  Raised automatically to fit the largest
# actual target, so the bound can never silently exclude one.
MAX_RENDER_TOKENS = 64


def tokenize(text):
    pos, n = 0, len(text)
    while pos < n:
        m = TOKEN.match(text, pos)
        if not m:
            pos += 1
            continue
        pos = m.end()
        comment, bar, string, paren, atom = m.groups()
        if comment is not None:
            continue
        for tok in (bar, string, paren, atom):
            if tok is not None:
                yield tok
                break


def parse_all(text):
    """Every top-level s-expression in `text`. Tolerates a truncated tail."""
    stack, out = [], []
    for tok in tokenize(text):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            if not stack:
                continue
            done = stack.pop()
            (stack[-1] if stack else out).append(done)
        else:
            (stack[-1] if stack else out).append(tok)
    return out


def render(x):
    """Canonical flat rendering, used as the identity of a term. Iterative."""
    if isinstance(x, str):
        return x
    parts, stack = [], [(x, 0)]
    while stack:
        node, i = stack.pop()
        if isinstance(node, str):
            parts.append(node)
            continue
        if i == 0:
            parts.append('(')
        if i < len(node):
            stack.append((node, i + 1))
            child = node[i]
            if i > 0:
                parts.append(' ')
            stack.append((child, 0))
        else:
            parts.append(')')
    return ''.join(parts)


def size(x):
    """Token count, iteratively; used only to skip oversized positions."""
    n, stack = 0, [x]
    while stack:
        node = stack.pop()
        if isinstance(node, str):
            n += 1
        else:
            n += 1
            stack.extend(node)
            if n > 10 * MAX_RENDER_TOKENS:
                return n
    return n


def normalize(x):
    """Fold the spellings two printers disagree on, so a mismatch is a real one.

    `(- 1)` and `-1` are the same integer; cvc5 prints the first and our renderer
    may print either.  Left un-normalised, every negative literal would be a
    false N.  `1.0` folds to `1` only when exact; `1.5` is left alone.
    """
    if isinstance(x, str):
        if re.fullmatch(r'-?\d+\.0+', x):
            return x.split('.')[0]
        return x
    if len(x) == 2 and x[0] == '-' and isinstance(x[1], str) and re.fullmatch(r'\d+', x[1]):
        return '-' + x[1]
    return [normalize(e) for e in x]


# ---------------------------------------------------------------- the walk

def find_targets(forms, targets, found):
    """Mark which of `targets` occur as a GROUND position anywhere in `forms`.

    Iterative pre-order carrying the set of binder-bound names in scope.  A
    position matches only when its rendering is a target AND no bound name
    occurs as one of its tokens.
    """
    stack = [(f, frozenset()) for f in forms]
    while stack:
        node, bnd = stack.pop()

        if isinstance(node, str):
            if node in targets and node not in bnd and not OUR_BINDER.match(node):
                found.add(node)
            continue
        if not node:
            continue

        head = node[0]

        if isinstance(head, str) and head in BINDERS and len(node) >= 3:
            inner = set(bnd)
            if isinstance(node[1], list):
                for d in node[1]:
                    if isinstance(d, list) and d and isinstance(d[0], str):
                        inner.add(d[0])
            fr = frozenset(inner)
            for sub in node[2:]:
                stack.append((sub, fr))
            continue

        if isinstance(head, str) and head == 'let' and len(node) >= 3:
            inner = set(bnd)
            if isinstance(node[1], list):
                for d in node[1]:
                    if isinstance(d, list) and len(d) == 2 and isinstance(d[0], str):
                        inner.add(d[0])                  # the NAME is never ground
                        stack.append((d[1], frozenset(bnd)))   # the VALUE is walked
            fr = frozenset(inner)
            for sub in node[2:]:
                stack.append((sub, fr))
            continue

        # Ordinary position: test it, then descend.
        if size(node) <= MAX_RENDER_TOKENS:
            r = render(node)
            if r in targets:
                toks = set(re.findall(r'[^\s()]+', r))
                if not (toks & bnd) and not any(OUR_BINDER.match(t) for t in toks):
                    found.add(r)
        for sub in node:
            stack.append((sub, bnd))


def query_forms(path):
    with open(path, encoding='utf-8', errors='replace') as fh:
        forms = parse_all(fh.read())
    keep = ('assert', 'define-fun', 'define-fun-rec', 'declare-fun', 'assert-not')
    return [normalize(sub)
            for form in forms
            if isinstance(form, list) and form and form[0] in keep
            for sub in form[1:]]


def dump_forms(path):
    """Our loop's accumulated ground formulas, unioned over every give-up point.

    Returns (forms, n_rows, n_blocks); n_blocks distinguishes "the loop gave up
    N times" from "the dump is empty because it never ran".
    """
    forms, rows, blocks = [], 0, 0
    if not os.path.exists(path):
        return forms, 0, 0
    with open(path, encoding='utf-8', errors='replace') as fh:
        for line in fh:
            if line.startswith('GROUNDDUMP begin'):
                blocks += 1
                continue
            if not line.startswith('GROUND '):
                continue
            rows += 1
            rest = line.split(' ', 3)
            if len(rest) < 4:
                continue
            forms.extend(normalize(f) for f in parse_all(rest[3]))
    return forms, rows, blocks


def parse_dump(path):
    """(quantifier-render, has_pattern, [tuple-of-terms]) per (instantiations ...).

    `has_pattern` records whether the quantified formula carries an explicit
    `:pattern`, which is the brief's "trigger-directed family" question.
    """
    with open(path, encoding='utf-8', errors='replace') as fh:
        text = fh.read()
    blocks = []
    for form in parse_all(text):
        if not (isinstance(form, list) and form and form[0] == 'instantiations'):
            continue
        if len(form) < 2:
            continue
        blocks.append((render(form[1]), ':pattern' in render(form[1]),
                       [normalize(t) for t in form[2:] if isinstance(t, list)]))
    return blocks


# ---------------------------------------------------------------- main

def resolve(corpus, mangled, index):
    """The mangling `/`->`_` is lossy, so invert it by lookup, never by guessing.
    A silently skipped file would make this a measurement of the accepted subset
    rather than of the population."""
    return index.get(mangled)


def build_index(corpus):
    index = {}
    for root, _dirs, files in os.walk(corpus):
        for f in files:
            if f.endswith('.smt2'):
                rel = os.path.relpath(os.path.join(root, f), corpus)
                index.setdefault(rel.replace('/', '_'), rel)
    return index


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dumps', required=True)
    ap.add_argument('--ground', default='')
    ap.add_argument('--corpus', required=True)
    ap.add_argument('--divisions', nargs='+', default=['UFNIA', 'UFLIA'])
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    index = {}
    for div in args.divisions:
        index.update(build_index(os.path.join(args.corpus, div)))
        for k in list(index):
            if not index[k].startswith(div):
                index[k] = os.path.join(div, index[k])
    # rebuild with division prefixes intact
    index = {}
    for div in args.divisions:
        base = os.path.join(args.corpus, div)
        for root, _dirs, files in os.walk(base):
            for f in files:
                if f.endswith('.smt2'):
                    rel = os.path.join(div, os.path.relpath(os.path.join(root, f), base))
                    index.setdefault(rel.replace('/', '_'), rel)

    global MAX_RENDER_TOKENS
    rows, unresolved = [], []
    for name in sorted(os.listdir(args.dumps)):
        if not name.endswith('.inst'):
            continue
        rel = resolve(args.corpus, name[:-len('.inst')], index)
        if rel is None:
            unresolved.append(name)
            continue

        blocks = parse_dump(os.path.join(args.dumps, name))
        terms = {}
        for _q, _p, tuples in blocks:
            for tup in tuples:
                for t in tup:
                    terms.setdefault(render(t), t)
        if terms:
            MAX_RENDER_TOKENS = max(64, max(size(t) for t in terms.values()) + 2)

        want = set(terms)
        qfound = set()
        find_targets(query_forms(os.path.join(args.corpus, rel)), want, qfound)

        gfound = set()
        grows = gblocks = 0
        if args.ground:
            gp = os.path.join(args.ground, rel.replace('/', '_') + '.ground')
            gforms, grows, gblocks = dump_forms(gp)
            find_targets(gforms, want, gfound)

        def bucket(r):
            if SKOLEM.search(r):
                return 'S'
            if r in qfound:
                return 'Q'
            if r in gfound:
                return 'G'
            return 'N'

        distinct = {r: bucket(r) for r in terms}
        occ = Counter()
        for _q, _p, tuples in blocks:
            for tup in tuples:
                for t in tup:
                    occ[distinct[render(t)]] += 1
        dc = Counter(distinct.values())
        kind = Counter('numeral' if NUMERAL.match(r) else
                       ('skolem' if SKOLEM.search(r) else 'term') for r in distinct)

        # Bucket N is CONTAMINATED by arithmetic normal form and this measures by
        # how much.  cvc5 prints a sum-of-monomials (`(+ -1 (typeof S))`,
        # `(* -1 x)`) where the source writes `(- (typeof S) 1)`; the two are the
        # same term and compare unequal as strings.  So an N whose HEAD is an
        # arithmetic operator is evidence of a printer disagreement at least as
        # much as of an absence, and must not be counted as "we never built it".
        # N restricted to non-arithmetic heads is the defensible signal.
        n_arith = 0
        for r, c in distinct.items():
            if c != 'N':
                continue
            head = r[1:].split(' ', 1)[0] if r.startswith('(') else ''
            if head in ARITH_HEADS:
                n_arith += 1
        rows.append({
            'file': rel,
            'quantifiers': len(blocks),
            'quantifiers_with_pattern': sum(1 for _q, p, _t in blocks if p),
            'instances': sum(len(t) for _q, _p, t in blocks),
            'occ_Q': occ['Q'], 'occ_G': occ['G'], 'occ_N': occ['N'], 'occ_S': occ['S'],
            'distinct_total': len(distinct),
            'distinct_Q': dc['Q'], 'distinct_G': dc['G'],
            'distinct_N': dc['N'], 'distinct_S': dc['S'],
            'distinct_N_arith_head': n_arith,
            'distinct_numeral': kind['numeral'], 'distinct_skolem': kind['skolem'],
            'distinct_term': kind['term'],
            'our_ground_rows': grows, 'our_ground_blocks': gblocks,
            'N_examples': sorted(r for r, c in distinct.items() if c == 'N')[:8],
        })

    with open(args.out, 'w', encoding='utf-8') as fh:
        json.dump({'rows': rows, 'unresolved': unresolved}, fh, indent=1, sort_keys=True)
    print(f'wrote {args.out}: {len(rows)} files, {len(unresolved)} unresolved')
    if unresolved:
        print('UNRESOLVED (reported, never silently dropped):')
        for u in unresolved[:10]:
            print('  ', u)
    return 0


def _run():
    # The walkers above are iterative, but `normalize` still recurses on term
    # DEPTH, and these benchmarks nest hundreds deep.  Raising the recursion
    # limit alone segfaults -- the C stack is the real bound -- so the work runs
    # on a thread with an explicitly large stack.
    import threading
    sys.setrecursionlimit(200_000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}
    t = threading.Thread(target=lambda: box.setdefault('rc', main()))
    t.start()
    t.join()
    return box.get('rc', 1)


if __name__ == '__main__':
    sys.exit(_run())
