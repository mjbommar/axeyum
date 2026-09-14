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

GROUND means ground: a subterm is recorded only when no variable bound by an
enclosing binder occurs free in it.  Without that, the numeral inside
`(forall ((a Int)) (f a 2))` would be indistinguishable from the non-ground
`(f a 2)`, and every `Q` verdict would be suspect.  The same exclusion is
applied to our own dump for our binder spellings (`!q.*`, `!qu_*`), which are
binders and not ground terms -- matching them would turn "we still have an open
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
    """Canonical flat rendering, used as the identity of a term."""
    if isinstance(x, str):
        return x
    return '(' + ' '.join(render(e) for e in x) + ')'


def normalize(x):
    """Fold the spellings two printers disagree on, so a mismatch is a real one.

    `(- 1)` and `-1` are the same integer; cvc5 prints the first and our renderer
    may print either.  Left un-normalised, every negative literal would be a
    false N.  Decimals `1.0` are folded to `1` only when exact, which is what a
    printer difference looks like; `1.5` is left alone.
    """
    if isinstance(x, str):
        if re.fullmatch(r'-?\d+\.0+', x):
            return x.split('.')[0]
        return x
    if len(x) == 2 and x[0] == '-' and isinstance(x[1], str) and re.fullmatch(r'\d+', x[1]):
        return '-' + x[1]
    return [normalize(e) for e in x]


# ---------------------------------------------------------------- ground subterms

BINDERS = {'forall', 'exists', 'lambda'}
# Our own binder spellings.  A term containing one of these is not ground.
OUR_BINDER = re.compile(r'^(!q\.|!qu_)')


def collect_ground(term, bound, out):
    """Record every GROUND subterm of `term`; return True if `term` is ground.

    `bound` is the set of variable names bound by an enclosing binder.
    """
    if isinstance(term, str):
        if term in bound or OUR_BINDER.match(term):
            return False
        out.add(term)
        return True

    if not term:
        return True

    head = term[0]

    if isinstance(head, str) and head in BINDERS and len(term) >= 3:
        inner = set(bound)
        decls = term[1]
        if isinstance(decls, list):
            for d in decls:
                if isinstance(d, list) and d and isinstance(d[0], str):
                    inner.add(d[0])
        for sub in term[2:]:
            collect_ground(sub, inner, out)
        return False                       # a quantified formula is not a ground TERM

    if isinstance(head, str) and head == 'let' and len(term) >= 3:
        # Expand: a let-bound name must not be mistaken for a constant, and the
        # body's ground subterms are the ones the expanded term really has.
        env = {}
        decls = term[1]
        if isinstance(decls, list):
            for d in decls:
                if isinstance(d, list) and len(d) == 2 and isinstance(d[0], str):
                    env[d[0]] = substitute(d[1], env)
                    collect_ground(env[d[0]], bound, out)
        for sub in term[2:]:
            collect_ground(substitute(sub, env), bound, out)
        return False

    if isinstance(head, str) and head == '!' and len(term) >= 2:
        # (! body :pattern (...) ...) -- the annotation keywords are not terms,
        # but the pattern TERMS are, so walk every non-keyword position.
        g = collect_ground(term[1], bound, out)
        i = 2
        while i < len(term):
            if isinstance(term[i], str) and term[i].startswith(':'):
                i += 1
                if i < len(term):
                    collect_ground(term[i], bound, out)
            i += 1
        return g

    ground = True
    for sub in term[1:] if isinstance(head, str) else term:
        if not collect_ground(sub, bound, out):
            ground = False
    if isinstance(head, str) and (head in bound or OUR_BINDER.match(head)):
        ground = False
    if ground:
        out.add(render(term))
    return ground


def substitute(term, env):
    if isinstance(term, str):
        return env.get(term, term)
    return [substitute(e, env) for e in term]


def query_ground_terms(path):
    with open(path, encoding='utf-8', errors='replace') as fh:
        forms = parse_all(fh.read())
    out = set()
    for form in forms:
        if isinstance(form, list) and form and form[0] in ('assert', 'define-fun', 'declare-fun',
                                                           'define-fun-rec', 'assert-not'):
            for sub in form[1:]:
                collect_ground(normalize(sub), set(), out)
    return out


def dump_ground_terms(path):
    """Subterm closure of every formula our loop dumped, over every give-up point.

    "Ever enters" is the question, so the union over all blocks is the right
    population.  Returns (terms, n_rows, n_blocks); n_blocks distinguishes "the
    loop gave up N times" from "the dump is empty because it never ran".
    """
    out, rows, blocks = set(), 0, 0
    if not os.path.exists(path):
        return out, 0, 0
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
            forms = parse_all(rest[3])
            for form in forms:
                collect_ground(normalize(form), set(), out)
    return out, rows, blocks


# ---------------------------------------------------------------- cvc5 dump

SKOLEM = re.compile(r'@quantifiers_skolemize|@quantifiers_|^@')
NUMERAL = re.compile(r'^-?\d+$')


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
        quant = form[1]
        tuples = [normalize(t) for t in form[2:] if isinstance(t, list)]
        blocks.append((render(quant), ':pattern' in render(quant), tuples))
    return blocks


def classify(term, qset, gset):
    r = render(term)
    if SKOLEM.search(r):
        return 'S'
    if r in qset:
        return 'Q'
    if r in gset:
        return 'G'
    return 'N'


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dumps', required=True, help='dir of <mangled>.inst cvc5 dumps')
    ap.add_argument('--ground', default='', help='dir of <mangled>.ground dumps (optional)')
    ap.add_argument('--corpus', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()

    rows = []
    for name in sorted(os.listdir(args.dumps)):
        if not name.endswith('.inst'):
            continue
        rel = name[:-len('.inst')].replace('_', '/')
        src = os.path.join(args.corpus, rel)
        if not os.path.exists(src):
            # The mangling is lossy (a literal '_' in a path becomes '/'), so
            # recover the real path by matching the mangled form instead of
            # trusting the inverse.  A silently-skipped file would make this a
            # measurement of the accepted subset, not of the population.
            cand = None
            for root, _dirs, files in os.walk(args.corpus):
                for f in files:
                    p = os.path.join(root, f)
                    if os.path.relpath(p, args.corpus).replace('/', '_') == name[:-len('.inst')]:
                        cand = p
                        break
                if cand:
                    break
            if not cand:
                rows.append({'file': rel, 'error': 'source-not-found'})
                continue
            src = cand
            rel = os.path.relpath(src, args.corpus)

        blocks = parse_dump(os.path.join(args.dumps, name))
        qset = query_ground_terms(src)
        gset, grows, gblocks = (set(), 0, 0)
        if args.ground:
            gpath = os.path.join(args.ground, rel.replace('/', '_') + '.ground')
            gset, grows, gblocks = dump_ground_terms(gpath)

        counts = Counter()
        kinds = Counter()
        distinct = {}
        npat = sum(1 for _q, p, _t in blocks if p)
        for _q, _p, tuples in blocks:
            for tup in tuples:
                for term in tup:
                    c = classify(term, qset, gset)
                    counts[c] += 1
                    r = render(term)
                    distinct[r] = c
                    kinds['numeral' if NUMERAL.match(r) else
                          ('skolem' if SKOLEM.search(r) else 'term')] += 1

        dcounts = Counter(distinct.values())
        dkind = Counter('numeral' if NUMERAL.match(r) else
                        ('skolem' if SKOLEM.search(r) else 'term')
                        for r in distinct)
        rows.append({
            'file': rel,
            'quantifiers': len(blocks),
            'quantifiers_with_pattern': npat,
            'instances': sum(len(t) for _q, _p, t in blocks),
            'terms_total': sum(counts.values()),
            'terms_Q': counts['Q'], 'terms_G': counts['G'],
            'terms_N': counts['N'], 'terms_S': counts['S'],
            'distinct_total': len(distinct),
            'distinct_Q': dcounts['Q'], 'distinct_G': dcounts['G'],
            'distinct_N': dcounts['N'], 'distinct_S': dcounts['S'],
            'distinct_numeral': dkind['numeral'], 'distinct_skolem': dkind['skolem'],
            'distinct_term': dkind['term'],
            'query_ground_terms': len(qset),
            'our_ground_rows': grows, 'our_ground_blocks': gblocks,
            'our_ground_terms': len(gset),
            'N_examples': sorted(r for r, c in distinct.items() if c == 'N')[:8],
        })

    with open(args.out, 'w', encoding='utf-8') as fh:
        json.dump(rows, fh, indent=1, sort_keys=True)
    print(f'wrote {args.out}: {len(rows)} files')
    return 0


if __name__ == '__main__':
    sys.exit(main())
