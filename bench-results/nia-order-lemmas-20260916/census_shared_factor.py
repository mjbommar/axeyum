#!/usr/bin/env python3
"""Sizing census for ADR-2136 (lane NIA-ORDER-LEMMAS).

Question: on the QF_NIA rows we do not decide, how many files does an ORDER
lemma even APPLY to, and how many does a MONOTONICITY lemma apply to?  That is
the ceiling in files, per class -- it is not a prediction that any of them get
decided.

Applicability is defined by the STEP the lemma takes, not by a name:

  order lemma       needs two DISTINCT nonlinear products that share an operand
                    term (`a*c` and `b*c`), because the lemma couples exactly
                    those two abstractions.  A file with no such pair cannot
                    emit one, whatever the model says.

  monotonicity      needs a product at least one of whose factors carries NO
                    two-sided constant bound entailed by the top-level
                    conjuncts -- because for a factor that IS two-sidedly
                    bounded, `mccormick_lemmas` (nia_linearize.rs:724) already
                    couples the magnitude, and the monotonicity lemma adds
                    nothing we do not have.  This is the population ADR-2112
                    Part E1 claim 2 is about.

The product predicate replicates `int_products` (nia_linearize.rs:71): a binary
`IntMul` node whose two operands are both non-constant, over a LEFT-ASSOCIATIVE
fold of n-ary `*` (`fold_args`, parse.rs:21194) with two-constant folding.  The
bound predicate replicates `harvest_const_bounds` (nia_linearize.rs:587): a walk
that descends through `and` only, reading `<= < >= > =` against an integer
literal.

It is a TEXT census and it therefore differs from the real IR in two named
ways:
  * it runs on the query as WRITTEN, before `eliminate_int_divmod` and the
    `pow2` abstraction, which can create or destroy products;
  * it does not run the rewriter's canonicaliser, so two operands that our
    arena would hash-cons to one term can stay distinct here (this UNDERcounts
    shared factors).
Both push the order-lemma number DOWN, so the figure it reports is a floor on
applicability, not a ceiling on it -- said here rather than discovered later.
"""

import sys
import os

sys.setrecursionlimit(100000)


def tokenize(text):
    out = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
            continue
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == "|":
            j = text.find("|", i + 1)
            if j < 0:
                j = n - 1
            out.append(text[i : j + 1])
            i = j + 1
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(text[i : j + 1])
            i = j + 1
            continue
        if c in "()":
            out.append(c)
            i += 1
            continue
        j = i
        while j < n and text[j] not in " \t\r\n()|;\"":
            j += 1
        out.append(text[i:j])
        i = j
    return out


def parse_sexprs(tokens):
    pos = 0
    out = []
    ntok = len(tokens)
    while pos < ntok:
        node, pos = parse_one(tokens, pos)
        if node is None:
            break
        out.append(node)
    return out


def parse_one(tokens, pos):
    if pos >= len(tokens):
        return None, pos
    t = tokens[pos]
    if t == "(":
        pos += 1
        items = []
        while pos < len(tokens) and tokens[pos] != ")":
            node, pos = parse_one(tokens, pos)
            if node is None:
                break
            items.append(node)
        if pos < len(tokens):
            pos += 1  # ')'
        return items, pos
    if t == ")":
        return None, pos + 1
    return t, pos + 1


# ---------------------------------------------------------------- term arena


class Arena:
    """Hash-consed term nodes.  A node is `('c', v)`, `('v', name)` or
    `(op, id, id, ...)`; the id IS the structural identity, so two occurrences
    of the same subterm are one node, exactly as `TermArena` interns."""

    def __init__(self):
        self.nodes = []
        self.index = {}

    def mk(self, key):
        got = self.index.get(key)
        if got is not None:
            return got
        got = len(self.nodes)
        self.nodes.append(key)
        self.index[key] = got
        return got

    def const(self, v):
        return self.mk(("c", v))

    def var(self, name):
        return self.mk(("v", name))

    def is_const(self, nid):
        return self.nodes[nid][0] == "c"

    def const_val(self, nid):
        k = self.nodes[nid]
        return k[1] if k[0] == "c" else None

    def app(self, op, args):
        return self.mk((op,) + tuple(args))

    def int_mul(self, a, b):
        av, bv = self.const_val(a), self.const_val(b)
        if av is not None and bv is not None:
            return self.const(av * bv)
        return self.app("*", (a, b))

    def int_add(self, a, b):
        av, bv = self.const_val(a), self.const_val(b)
        if av is not None and bv is not None:
            return self.const(av + bv)
        return self.app("+", (a, b))

    def int_sub(self, a, b):
        av, bv = self.const_val(a), self.const_val(b)
        if av is not None and bv is not None:
            return self.const(av - bv)
        return self.app("-", (a, b))


NARY_FOLD = {"*": "int_mul", "+": "int_add"}


def build(arena, sexp, env):
    """Builds a hash-consed node from one s-expression, resolving `let`."""
    if isinstance(sexp, str):
        if sexp in env:
            return env[sexp]
        try:
            return arena.const(int(sexp))
        except ValueError:
            pass
        return arena.var(sexp)
    if not sexp:
        return arena.var("()")
    head = sexp[0]
    if head == "let" and len(sexp) == 3:
        binds = sexp[1]
        newenv = dict(env)
        for b in binds:
            if isinstance(b, list) and len(b) == 2 and isinstance(b[0], str):
                newenv[b[0]] = build(arena, b[1], env)
        return build(arena, sexp[2], newenv)
    if isinstance(head, list):
        # (_ ...) indexed ops and the like -- opaque
        return arena.app("opaque", tuple(build(arena, a, env) for a in sexp[1:]))
    args = [build(arena, a, env) for a in sexp[1:]]
    if head == "-" and len(args) == 1:
        v = arena.const_val(args[0])
        if v is not None:
            return arena.const(-v)
        return arena.app("neg", (args[0],))
    if head in NARY_FOLD and len(args) >= 1:
        f = getattr(arena, NARY_FOLD[head])
        acc = args[0]
        for nxt in args[1:]:
            acc = f(acc, nxt)
        return acc
    if head == "-" and len(args) >= 2:
        acc = args[0]
        for nxt in args[1:]:
            acc = arena.int_sub(acc, nxt)
        return acc
    return arena.app(head, tuple(args))


def collect_products(arena, roots):
    """`int_products` (nia_linearize.rs:71): binary `*` with both operands
    non-constant, reachable from the assertions."""
    seen = set()
    prods = set()
    stack = list(roots)
    while stack:
        t = stack.pop()
        if t in seen:
            continue
        seen.add(t)
        key = arena.nodes[t]
        if key[0] in ("c", "v"):
            continue
        args = key[1:]
        if key[0] == "*" and len(args) == 2:
            if not arena.is_const(args[0]) and not arena.is_const(args[1]):
                prods.add(t)
        stack.extend(args)
    return prods


def harvest_bounds(arena, assertions):
    """`harvest_const_bounds` (nia_linearize.rs:587): descends through `and`
    only; records lo/hi from a comparison against an integer literal."""
    lo, hi = {}, {}

    def tlo(t, v):
        lo[t] = max(lo[t], v) if t in lo else v

    def thi(t, v):
        hi[t] = min(hi[t], v) if t in hi else v

    stack = list(assertions)
    seen = set()
    while stack:
        t = stack.pop()
        if t in seen:
            continue
        seen.add(t)
        key = arena.nodes[t]
        if key[0] in ("c", "v"):
            continue
        op = key[0]
        args = key[1:]
        if op == "and":
            stack.extend(args)
            continue
        if len(args) != 2:
            continue
        a, b = args
        ac, bc = arena.const_val(a), arena.const_val(b)
        if op == "<=":
            if bc is not None:
                thi(a, bc)
            if ac is not None:
                tlo(b, ac)
        elif op == "<":
            if bc is not None:
                thi(a, bc - 1)
            if ac is not None:
                tlo(b, ac + 1)
        elif op == ">=":
            if bc is not None:
                tlo(a, bc)
            if ac is not None:
                thi(b, ac)
        elif op == ">":
            if bc is not None:
                tlo(a, bc + 1)
            if ac is not None:
                thi(b, ac - 1)
        elif op == "=":
            if bc is not None:
                tlo(a, bc)
                thi(a, bc)
            if ac is not None:
                tlo(b, ac)
                thi(b, ac)
    return {t for t in lo if t in hi and not arena.is_const(t)}


def census_text(text):
    toks = tokenize(text)
    forms = parse_sexprs(toks)
    arena = Arena()
    assertions = []
    for f in forms:
        if isinstance(f, list) and f and f[0] == "assert" and len(f) >= 2:
            assertions.append(build(arena, f[1], {}))
    prods = collect_products(arena, assertions)
    bounded = harvest_bounds(arena, assertions)

    factor_to_products = {}
    for p in prods:
        a, b = arena.nodes[p][1:]
        for f in (a, b):
            factor_to_products.setdefault(f, set()).add(p)

    shared_factors = {f: ps for f, ps in factor_to_products.items() if len(ps) >= 2}
    shared_pairs = sum(len(ps) * (len(ps) - 1) // 2 for ps in shared_factors.values())

    # a product whose factors are not BOTH two-sidedly bounded: McCormick
    # cannot couple its magnitude, so a model-driven monotonicity lemma is the
    # only magnitude coupling available for it.
    unbounded_products = 0
    for p in prods:
        a, b = arena.nodes[p][1:]
        if a not in bounded or b not in bounded:
            unbounded_products += 1

    return {
        "assertions": len(assertions),
        "products": len(prods),
        "distinct_factors": len(factor_to_products),
        "shared_factors": len(shared_factors),
        "shared_pairs": shared_pairs,
        "order_applicable": 1 if shared_factors else 0,
        "bounded_terms": len(bounded),
        "unbounded_products": unbounded_products,
        "monotone_applicable": 1 if unbounded_products else 0,
        "max_products_on_one_factor": max(
            (len(ps) for ps in factor_to_products.values()), default=0
        ),
    }


def census_file(path):
    with open(path, "r", errors="replace") as fh:
        return census_text(fh.read())


# ------------------------------------------------------------------ controls

CONTROLS = [
    # (name, text, expected order_applicable, monotone_applicable, products)
    (
        "shared-factor-pair",
        "(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)"
        "(assert (> (+ (* a c) (* b c)) 0))",
        1,
        1,
        2,
    ),
    (
        "no-shared-factor",
        "(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)"
        "(declare-fun d () Int)(assert (> (+ (* a b) (* c d)) 0))",
        0,
        1,
        2,
    ),
    (
        "linear-only-negative-control",
        "(declare-fun a () Int)(declare-fun b () Int)(assert (> (+ a (* 3 b)) 0))",
        0,
        0,
        0,
    ),
    (
        # A LONE square is ONE monomial.  The order lemma couples two DISTINCT
        # monomials that share a factor, so `a*a` on its own is not an
        # opportunity -- the lemma it would emit relates `a*a` to itself.
        # Expectation set from the lemma's own step, not from "a appears twice".
        "lone-square-is-not-a-pair",
        "(declare-fun a () Int)(assert (> (* a a) 0))",
        0,
        1,
        1,
    ),
    (
        # ...but a square NEXT TO another product sharing that factor is: the
        # pair (`a*a`, `a*b`) is exactly z3's `ac`/`bc` with `c = a`.  This is
        # the control that distinguishes the row above from a census that
        # simply never reports a shared factor.
        "square-and-product-share-a-factor",
        "(declare-fun a () Int)(declare-fun b () Int)"
        "(assert (> (+ (* a a) (* a b)) 0))",
        1,
        1,
        2,
    ),
    (
        "nary-left-assoc",
        # (* a b c) folds to (* (* a b) c): two products; the inner one is an
        # operand of the outer, and no operand term is shared between the two,
        # so the order lemma does NOT apply.
        "(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)"
        "(assert (> (* a b c) 0))",
        0,
        1,
        2,
    ),
    (
        "bounded-both-sides-no-monotone-need",
        "(declare-fun a () Int)(declare-fun b () Int)"
        "(assert (and (<= 0 a) (<= a 5) (<= 0 b) (<= b 5) (> (* a b) 3)))",
        0,
        0,
        1,
    ),
    (
        "let-bound-shared-factor",
        "(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)"
        "(assert (let ((x (* a c)) (y (* b c))) (> (+ x y) 0)))",
        1,
        1,
        2,
    ),
]


def run_controls():
    bad = 0
    for name, text, exp_order, exp_mono, exp_prod in CONTROLS:
        got = census_text(text)
        ok = (
            got["order_applicable"] == exp_order
            and got["monotone_applicable"] == exp_mono
            and got["products"] == exp_prod
        )
        print(
            f"CONTROL {'PASS' if ok else 'FAIL'} {name}: "
            f"products={got['products']} (want {exp_prod}) "
            f"order={got['order_applicable']} (want {exp_order}) "
            f"monotone={got['monotone_applicable']} (want {exp_mono})"
        )
        if not ok:
            bad += 1
    return bad


COLS = [
    "corpus_path",
    "assertions",
    "products",
    "distinct_factors",
    "shared_factors",
    "shared_pairs",
    "max_products_on_one_factor",
    "order_applicable",
    "bounded_terms",
    "unbounded_products",
    "monotone_applicable",
    "status",
]


def main():
    args = sys.argv[1:]
    if not args or args[0] == "--controls":
        bad = run_controls()
        print(f"controls: {len(CONTROLS) - bad} passed, {bad} failed")
        sys.exit(1 if bad else 0)

    paths_file, out_tsv = args[0], args[1]
    bad = run_controls()
    if bad:
        print("REFUSING to census with a failing control", file=sys.stderr)
        sys.exit(2)

    n = 0
    failed = 0
    with open(out_tsv, "w") as out:
        out.write("\t".join(COLS) + "\n")
        for line in open(paths_file):
            p = line.strip()
            if not p:
                continue
            n += 1
            try:
                r = census_file(p)
                r["status"] = "ok"
            except Exception as e:  # a file the census cannot read is REPORTED
                failed += 1
                r = {c: "" for c in COLS}
                r["status"] = f"ERROR:{type(e).__name__}:{e}".replace("\t", " ")[:200]
            r["corpus_path"] = p
            out.write("\t".join(str(r.get(c, "")) for c in COLS) + "\n")
            print(f"{n} {os.path.basename(p)}", file=sys.stderr)
    print(f"COMPLETE: {n} files, {failed} errored", file=sys.stderr)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
