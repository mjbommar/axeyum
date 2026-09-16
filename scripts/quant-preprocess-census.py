#!/usr/bin/env python3
"""Census of the two z3 preprocessing shapes DT-GROUND-PROBE named (ADR-2127).

    quant-preprocess-census.py --corpus-root DIR --division NAME \
        --list FILE.list [--undecided FILE.list] --out-tsv OUT.tsv

DT-GROUND-PROBE (`bench-results/dt-ground-probe-20260916/README.md`) showed
that ADR-2114's `GROUND` attribution does NOT mean "there is a separable set
of ground assertions sufficient for unsat": literally deleting every
quantified assertion from those 83 files and asking plain z3 gives 83 of 83
`sat`, 0 `unsat`. The refutation therefore comes from z3's PREPROCESSING of
the quantified assertions -- before `smt.ematching` / `smt.mbqi` are ever
consulted -- and the probe named the two mechanisms:

  1. Skolemizing an existential at positive polarity (in this corpus almost
     always the SPARK convention `(assert (not (forall (...) body)))`, a
     negated universal goal), which turns the goal into GROUND content.
  2. Folding a definitional `forall`-equality `∀x̄. f(x̄) = t[x̄]` into a
     ground MACRO and inlining it.

This script COUNTS both shapes over an SMT-LIB corpus, per file, so the
ceiling on any pass that implements them is known BEFORE the pass is written.
It decides nothing and solves nothing; it is a syntactic census.

The criteria are z3's, transcribed:

  * `macro_util::is_macro_head` -- an application whose declaration is
    UNINTERPRETED, whose arity equals the binder's variable count, and whose
    arguments are DISTINCT bound variables covering every binder variable.
  * `macro_util::is_left_simple_macro` -- `is_macro_head(lhs)` plus the
    OCCURS CHECK: the head's own declaration must not occur in the body.
  * `quasi_macros` -- an application of an uninterpreted `f` whose arguments
    are NOT all distinct bound variables, but in which every binder variable
    occurs at least once, with the same occurs check.

Where this census is deliberately CONSERVATIVE (it under-counts rather than
over-counts, so the number is a floor on the shape and a ceiling on nothing
it does not see):

  * Polarity is proven, never assumed. A quantifier reachable only through a
    `let`-bound VALUE has no single polarity without expanding the binding,
    and this corpus nests `let` hundreds deep (CLAUDE.md: a recursive
    `let`-expander reached 63.4 GB and took a host down on these same files).
    Such positions are counted in their own column `sk_under_let` and are NOT
    counted as skolemizable.
  * A quantifier under `=`/`xor`/`distinct` over Bool, or under an `ite`
    condition, has mixed polarity and is not counted as skolemizable.
  * The occurs check is a WHOLE-SUBTREE token scan of the body, so a head
    symbol appearing in a dead `let` binding still refuses the macro.

Everything is ITERATIVE. The tokenizer and s-expression parser are imported
from `scripts/strip-quantified-assertions.py` rather than re-implemented, so
the two tools cannot drift apart on what a `|quoted symbol|` or a comment is.

Exit status depends on the finding: a file that fails to parse, or a run in
which ZERO files were read, is reported on stderr and exits non-zero. A
census that cannot fail is worse than no census (CLAUDE.md).
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import sys
from typing import Dict, List, Optional, Sequence, Set, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))


def _load_strip_module():
    """Import `strip-quantified-assertions.py` by path -- its filename is not
    a legal Python identifier, so a plain `import` cannot reach it."""
    path = os.path.join(_HERE, "strip-quantified-assertions.py")
    spec = importlib.util.spec_from_file_location("_strip_quant", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_STRIP = _load_strip_module()
tokenize_with_pos = _STRIP.tokenize_with_pos
parse_tokens = _STRIP.parse_tokens


# ---------------------------------------------------------------------------
# s-expression helpers
# ---------------------------------------------------------------------------


def head(node) -> Optional[str]:
    """The operator symbol of a list form, or None for an atom / a list whose
    first element is itself a list."""
    if isinstance(node, list) and node and not isinstance(node[0], list):
        return str(node[0])
    return None


def unwrap_annotation(node):
    """`(! body :key val ...)` -> `body`. z3's macro finder works on the
    quantifier BODY; patterns live beside it and are not part of the term
    whose shape decides macro-hood."""
    while head(node) == "!" and len(node) >= 2:
        node = node[1]
    return node


def binder_vars(bindings) -> List[str]:
    """`((x A) (y B))` -> `['x', 'y']`. A malformed binding list yields []."""
    out: List[str] = []
    if not isinstance(bindings, list):
        return out
    for b in bindings:
        if isinstance(b, list) and b and not isinstance(b[0], list):
            out.append(str(b[0]))
    return out


def symbols_in(node) -> Set[str]:
    """Every atom token appearing anywhere in `node`, INCLUDING operator
    positions and including inside `let` binding values. This is the occurs
    check's population: conservative by construction."""
    out: Set[str] = set()
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            stack.extend(n)
        else:
            out.add(str(n))
    return out


# ---------------------------------------------------------------------------
# declarations
# ---------------------------------------------------------------------------


class Decls:
    """Declared symbols of one script.

    `uninterpreted` is what z3 calls a macro-eligible declaration: a symbol
    introduced by `declare-fun` / `declare-const`, i.e. one with NO built-in
    interpretation and no existing definition. A `define-fun` name is
    excluded: it is ALREADY a macro, so an assertion restating it is not a
    new definition.
    """

    def __init__(self) -> None:
        self.arity: Dict[str, int] = {}
        self.defined: Set[str] = set()

    def is_uninterpreted(self, name: str) -> bool:
        return name in self.arity and name not in self.defined


def collect_decls(forms: Sequence[list]) -> Decls:
    d = Decls()
    for f in forms:
        h = head(f)
        if h == "declare-fun" and len(f) >= 4:
            name = str(f[1])
            args = f[2]
            d.arity[name] = len(args) if isinstance(args, list) else 0
        elif h == "declare-const" and len(f) >= 3:
            d.arity[str(f[1])] = 0
        elif h in ("define-fun", "define-fun-rec") and len(f) >= 5:
            name = str(f[1])
            args = f[2]
            d.arity[name] = len(args) if isinstance(args, list) else 0
            d.defined.add(name)
        elif h == "define-funs-rec" and len(f) >= 2 and isinstance(f[1], list):
            for sig in f[1]:
                if isinstance(sig, list) and sig:
                    d.arity[str(sig[0])] = len(sig[1]) if len(sig) > 1 and isinstance(sig[1], list) else 0
                    d.defined.add(str(sig[0]))
        elif h == "declare-datatypes" and len(f) >= 3:
            # Constructors, selectors and testers are INTERPRETED by the
            # datatype theory: never macro heads. Record their arity so a
            # later `is_uninterpreted` says no.
            for name in _datatype_symbols(f):
                d.arity[name] = 0
                d.defined.add(name)
    return d


def _datatype_symbols(form: list) -> Set[str]:
    """Every constructor/selector name introduced by a `declare-datatypes`.
    Shape-tolerant: walks the declaration body and takes the head symbol of
    each list, which over-approximates (it may include sort names) -- and
    over-approximating the INTERPRETED set only makes the macro census more
    conservative."""
    out: Set[str] = set()
    stack = list(form[2:]) if len(form) > 2 else []
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            h = head(n)
            if h is not None:
                out.add(h)
            stack.extend(n)
    return out


# ---------------------------------------------------------------------------
# z3 `macro_util::is_macro_head` and `is_left_simple_macro`
# ---------------------------------------------------------------------------


def is_macro_head(node, bvars: Sequence[str], decls: Decls) -> Optional[str]:
    """z3 `macro_util::is_macro_head`
    (`references/z3/src/ast/macros/macro_util.cpp:139-165`): return the head
    symbol iff `node` is an application of an UNINTERPRETED declaration whose
    arguments are DISTINCT bound variables covering EVERY binder variable.

    z3's four conjuncts, at `macro_util.cpp:140-143`:
      `is_app(n)`                                          -- :140
      `!to_app(n)->get_decl()->is_associative()`            -- :141
      `to_app(n)->get_family_id() == null_family_id`        -- :142 (uninterpreted)
      `to_app(n)->get_num_args() == num_decls`              -- :143 (NOT `>=`;
          `>=` is exactly the quasi-macro relaxation)
    then per argument, `macro_util.cpp:147-153`: each must be a bound variable
    (`:148-149`), its index must be `< num_decls` and not already used
    (`:150-152` -- distinctness/linearity).

    The associativity conjunct is transcribed for fidelity but is inert over
    this population: an SMT-LIB `declare-fun` symbol is never associative;
    only theory symbols (`+`, `and`, ...) are, and those already fail the
    uninterpreted conjunct.

    COVERAGE is DERIVED in z3, not checked: conjuncts 4+6+7+8 make
    `i |-> idx(arg_i)` an injection from `num_decls` positions into
    `{0..num_decls-1}`, hence a bijection (z3 states this outcome in the doc
    comment at `macro_util.cpp:135-137`). The explicit set equality below is
    the same condition by pigeonhole -- stated rather than derived, because a
    census that relies on an unstated pigeonhole argument is a census whose
    reader cannot check it.

    Each conjunct is load-bearing for SOUNDNESS, not just for matching:
      * uninterpreted head  -- a theory symbol has a fixed meaning already;
      * arity == |binder|   -- see above;
      * arguments distinct  -- otherwise `f(x,x) = t` constrains only the
        diagonal and inlining it at `f(a,b)` is UNSOUND;
      * arguments cover the whole binder -- a binder variable not reachable
        from the head is universally quantified over the BODY only, which is
        a constraint on `t`, not a definition of `f`.
    """
    h = head(node)
    if h is None:
        return None
    if not decls.is_uninterpreted(h):
        return None
    args = node[1:]
    if len(args) != len(bvars):
        return None
    seen: Set[str] = set()
    for a in args:
        if isinstance(a, list):
            return None
        s = str(a)
        if s not in bvars or s in seen:
            return None
        seen.add(s)
    if seen != set(bvars):
        return None
    return h


def occurs(name: str, node) -> bool:
    """The OCCURS CHECK. `∀x. f(x) = g(f(x))` is not a definition of `f`; it
    is a recursive constraint, and inlining it does not terminate and does not
    preserve models. z3 `macro_util::is_left_simple_macro` refuses exactly
    this at `macro_util.cpp:182` (`!occurs(to_app(lhs)->get_decl(), rhs)`),
    mirrored for the other orientation at `macro_util.cpp:222`; the traversal
    itself is `occurs.cpp:76-85` with the visitor at `occurs.cpp:44-51`, which
    descends into nested quantifiers and matches on the `func_decl` POINTER.

    Here the match is on the NAME, over every atom of the subtree including
    `let` binding values -- coarser than z3's pointer identity, and coarser in
    the refusing direction only."""
    return name in symbols_in(node)


def classify_definitional_macro(
    body, bvars: Sequence[str], decls: Decls
) -> Optional[Tuple[str, str]]:
    """Return `(head_symbol, kind)` iff the quantifier body is one of z3's
    SIMPLE macro shapes -- `macro_util::is_left_simple_macro`
    (`macro_util.cpp:177-201`) or `is_right_simple_macro`
    (`macro_util.cpp:217-241`), combined by `is_simple_macro`
    (`macro_util.h:99-101`, left tried first).

    kinds:
      `eq`  -- `f(x̄) = t[x̄]`, either orientation. In z3 `iff` IS `eq` at Bool
               sort (`ast.h:2197`), so the Boolean case `f(x̄) ↔ φ[x̄]` needs no
               separate branch -- and SMT-LIB spells it `=` as well.
      `neq` -- `¬(f(x̄) = φ[x̄])` at Bool sort, i.e. `f(x̄) ↔ ¬φ`; z3 has an
               explicit branch for it (`macro_util.cpp:187-193` /
               `:228-234`) producing `def = ¬φ`.

    DELIBERATELY NOT counted here, because z3's `macro_finder` does not
    recognize them either: the unit literals `∀x̄. f(x̄)` and `∀x̄. ¬f(x̄)`.
    Those are handled ONLY on the quasi-macro path
    (`quasi_macros.cpp:176-186`), and they are counted in `macro_unit`.
    """
    body = unwrap_annotation(body)
    h = head(body)

    if h == "not" and len(body) == 2:
        inner = unwrap_annotation(body[1])
        if head(inner) == "=" and len(inner) == 3:
            lhs, rhs = unwrap_annotation(inner[1]), unwrap_annotation(inner[2])
            for a, b in ((lhs, rhs), (rhs, lhs)):
                hs = is_macro_head(a, bvars, decls)
                if hs is not None and not occurs(hs, b):
                    return (hs, "neq")
        return None

    if h == "=" and len(body) == 3:
        lhs, rhs = unwrap_annotation(body[1]), unwrap_annotation(body[2])
        hs = is_macro_head(lhs, bvars, decls)
        if hs is not None and not occurs(hs, rhs):
            return (hs, "eq")
        hs = is_macro_head(rhs, bvars, decls)
        if hs is not None and not occurs(hs, lhs):
            return (hs, "eq")
        return None

    return None


def classify_unit_macro(body, bvars: Sequence[str], decls: Decls) -> Optional[str]:
    """`∀x̄. f(x̄)` (`f` is `true`) or `∀x̄. ¬f(x̄)` (`f` is `false`).

    z3 reaches these ONLY through `quasi_macros::is_quasi_macro`
    (`quasi_macros.cpp:176-181` for the negated form, `:182-186` for the
    positive one), never through `macro_finder`. The two branches there check
    only `is_non_ground_uninterp` and `is_unique` -- no coverage check and no
    occurs check at that point; coverage is enforced downstream by
    `quasi_macro_to_macro`'s `if (num_seen < q->get_num_decls()) return false;`
    (`quasi_macros.cpp:238-239`), and the two are chained by `&&` at
    `quasi_macros.cpp:297-298`. This census applies the full-coverage form
    directly, which is the same net condition."""
    body = unwrap_annotation(body)
    if head(body) == "not" and len(body) == 2:
        return is_macro_head(unwrap_annotation(body[1]), bvars, decls)
    return is_macro_head(body, bvars, decls)


def fully_depends_on(args: Sequence, bvars: Sequence[str]) -> bool:
    """z3 `quasi_macros::fully_depends_on` (`quasi_macros.cpp:99-119`).

    Every binder variable must appear as a BARE, DIRECT argument of the head:

        for (expr* arg : *a)
            if (is_var(arg)) bitset.set(to_var(arg)->get_idx(), true);
        for (unsigned i = 0; i < bitset.size(); ++i)
            if (!bitset.get(i)) return false;          -- :110-116

    A variable buried inside an argument (`g(y)`) does NOT cover it. The
    older, weaker "occurs somewhere deep down" version is still in the file,
    COMMENTED OUT at `quasi_macros.cpp:102-104`, with the note that it was
    replaced. Transcribing the weak version instead would over-count quasi-
    macros -- and each over-counted one is a transformation z3 refuses to
    make, so the difference is not a rounding error but a wrong ceiling."""
    seen: Set[str] = set()
    for a in args:
        if not isinstance(a, list):
            s = str(a)
            if s in bvars:
                seen.add(s)
    return seen == set(bvars)


def classify_quasi_macro(
    body, bvars: Sequence[str], decls: Decls, unique_heads: Set[str]
) -> Optional[str]:
    """z3 `quasi_macros::is_quasi_def` (`quasi_macros.cpp:147-153`), whose
    four conjuncts are, verbatim:

        is_non_ground_uninterp(lhs) &&                   -- :149
        is_unique(to_app(lhs)->get_decl()) &&            -- :150
        !depends_on(rhs, to_app(lhs)->get_decl()) &&     -- :151  (occurs check)
        fully_depends_on(to_app(lhs), q);                -- :152  (coverage)

    `is_unique` (`quasi_macros.cpp:80-82`) is the condition most easily
    missed and the one that shrinks this census most: `f` must have EXACTLY
    ONE non-ground occurrence in the WHOLE problem, counted up front by
    `find_occurrences` (`quasi_macros.cpp:34-74`, counting at `:61-66`). A
    symbol used anywhere else is not a quasi-macro candidate at all, because
    the guarded rewrite would have to hold at every other use site too."""
    body = unwrap_annotation(body)
    if head(body) != "=" or len(body) != 3:
        return None
    for lhs, rhs in ((body[1], body[2]), (body[2], body[1])):
        lhs, rhs = unwrap_annotation(lhs), unwrap_annotation(rhs)
        h = head(lhs)
        if h is None or not decls.is_uninterpreted(h):
            continue
        args = lhs[1:]
        if not args:
            continue
        if is_macro_head(lhs, bvars, decls) is not None:
            continue  # a plain simple macro, counted in `macro_def`
        if h not in unique_heads:
            continue
        if not fully_depends_on(args, bvars):
            continue
        if occurs(h, rhs):
            continue
        return h
    return None


def nonground_uninterp_occurrences(forms: Sequence[list], decls: Decls) -> Dict[str, int]:
    """z3 `quasi_macros::find_occurrences` (`quasi_macros.cpp:34-74`): count,
    over every assertion, the applications of an uninterpreted declaration
    that are NON-GROUND (`:61-66`).

    "Non-ground" here means the application's subtree mentions at least one
    variable bound by an enclosing binder, so the walk carries the set of
    names in scope. `let`-bound names are carried too: a `let` name standing
    for a term that mentions a bound variable makes its uses non-ground, and
    treating them as in-scope errs toward counting MORE occurrences, which
    only makes `is_unique` refuse more often."""
    counts: Dict[str, int] = {}
    for f in forms:
        if head(f) != "assert" or len(f) < 2:
            continue
        stack: List[Tuple[object, frozenset]] = [(f[1], frozenset())]
        while stack:
            node, scope = stack.pop()
            if not isinstance(node, list) or not node:
                continue
            h = head(node)
            if h in ("forall", "exists") and len(node) >= 3:
                scope = scope | frozenset(binder_vars(node[1]))
                stack.append((node[2], scope))
                continue
            if h == "let" and len(node) >= 3 and isinstance(node[1], list):
                names = []
                for b in node[1]:
                    if isinstance(b, list) and len(b) >= 2:
                        stack.append((b[1], scope))
                        if symbols_in(b[1]) & scope:
                            names.append(str(b[0]))
                stack.append((node[2], scope | frozenset(names)))
                continue
            if h is not None and decls.is_uninterpreted(h) and len(node) > 1:
                if symbols_in(node) & scope:
                    counts[h] = counts.get(h, 0) + 1
            for a in node[1:]:
                stack.append((a, scope))
    return counts


# ---------------------------------------------------------------------------
# polarity walk: where an existential can be skolemized
# ---------------------------------------------------------------------------

POS, NEG, MIXED = 1, -1, 0


class SkolemCensus:
    __slots__ = ("top", "conj", "deep", "under_let", "needs_function", "positions")

    def __init__(self) -> None:
        self.top = 0            # the assert body IS the existential position
        self.conj = 0           # under a chain of top-level `and` only
        self.deep = 0           # proven polarity, deeper than a top-level `and`
        self.under_let = 0      # reachable only through a `let` VALUE: not counted
        self.needs_function = 0 # enclosing universals: a Skolem FUNCTION, not a constant
        self.positions = 0      # top + conj + deep


def skolem_positions(assert_body) -> SkolemCensus:
    """Walk the assertion with an explicit polarity and count the positions
    at which an EXISTENTIAL sits -- `(exists ...)` at positive polarity or
    `(forall ...)` at negative polarity. Both are the same thing: a position
    whose witness can be named by a fresh Skolem symbol.

    The walk is iterative. Each stack entry is
    `(node, polarity, conj_only, under_let, n_enclosing_universals)`.
    `conj_only` is True while the path from the assert body has passed through
    nothing but polarity-preserving structure (`not`, `!`, `and`), which is
    exactly the "top level or under a top-level conjunction" population.
    `through_and` splits that population in two: a position reached without
    crossing an `and` is TOP, one reached through at least one `and` is CONJ.

    The distinction is NOT "the assert body is literally the quantifier".
    `(assert (not (forall ...)))` -- the SPARK goal convention, and the single
    most common shape in this corpus -- reaches the quantifier through one
    `not`, which is what makes it an existential in the first place. Counting
    that as anything but top-level would report zero top-level goals on a
    corpus built almost entirely out of them.
    """
    c = SkolemCensus()
    stack: List[Tuple[object, int, bool, bool, bool, int]] = [
        (assert_body, POS, True, False, False, 0)
    ]
    while stack:
        node, pol, conj_only, through_and, in_let, nuniv = stack.pop()
        if not isinstance(node, list) or not node:
            continue
        h = head(node)
        is_existential_here = (h == "exists" and pol == POS) or (
            h == "forall" and pol == NEG
        )
        if is_existential_here:
            if in_let:
                c.under_let += 1
            else:
                c.positions += 1
                if conj_only and not through_and:
                    c.top += 1
                elif conj_only:
                    c.conj += 1
                else:
                    c.deep += 1
                if nuniv > 0:
                    c.needs_function += 1

        if h in ("forall", "exists") and len(node) >= 3:
            # Descending through a binder preserves polarity. A UNIVERSAL in
            # scope (a `forall` at +, or an `exists` at -) is what forces a
            # Skolem FUNCTION rather than a constant for anything below it.
            adds = 1 if not is_existential_here else 0
            stack.append((node[2], pol, False, through_and, in_let, nuniv + adds))
            continue

        if h == "not" and len(node) == 2:
            stack.append((node[1], -pol if pol != MIXED else MIXED, conj_only, through_and, in_let, nuniv))
            continue
        if h == "and":
            for a in node[1:]:
                stack.append((a, pol, conj_only and pol == POS, True, in_let, nuniv))
            continue
        if h == "or":
            for a in node[1:]:
                stack.append((a, pol, False, through_and, in_let, nuniv))
            continue
        if h == "=>":
            for a in node[1:-1]:
                stack.append((a, -pol if pol != MIXED else MIXED, False, through_and, in_let, nuniv))
            if len(node) >= 2:
                stack.append((node[-1], pol, False, through_and, in_let, nuniv))
            continue
        if h == "ite" and len(node) == 4:
            stack.append((node[1], MIXED, False, through_and, in_let, nuniv))
            stack.append((node[2], pol, False, through_and, in_let, nuniv))
            stack.append((node[3], pol, False, through_and, in_let, nuniv))
            continue
        if h == "let" and len(node) >= 3 and isinstance(node[1], list):
            # A let-bound VALUE is walked at POSITIVE polarity with `in_let`
            # set. That is not a claim that the binding is used positively --
            # it is how the SHAPE gets recognised at all, so that a
            # skolemizable-looking position inside a binding lands in
            # `sk_under_let` instead of vanishing. `in_let` then keeps it out
            # of every skolemizable column. Walking the value at MIXED would
            # report zero here and make `sk_under_let` a column that can never
            # be nonzero -- a counter that cannot fire is not a measurement.
            for b in node[1]:
                if isinstance(b, list) and len(b) >= 2:
                    stack.append((b[1], POS, False, through_and, True, nuniv))
            stack.append((node[2], pol, conj_only, through_and, in_let, nuniv))
            continue
        if h == "!" and len(node) >= 2:
            stack.append((node[1], pol, conj_only, through_and, in_let, nuniv))
            continue
        # `=`/`xor`/`distinct` over Bool, and every uninterpreted context:
        # no single polarity is provable, so nothing below is counted.
        for a in node[1:]:
            stack.append((a, MIXED, False, through_and, in_let, nuniv))
    return c


# ---------------------------------------------------------------------------
# per-file census
# ---------------------------------------------------------------------------

COLUMNS = [
    "division",
    "file",
    "n_assert",
    "n_quant_assert",
    "sk_top",
    "sk_conj",
    "sk_deep",
    "sk_under_let",
    "sk_needs_function",
    "macro_def",
    "macro_def_distinct",
    "macro_unit",
    "macro_quasi",
    "macro_reject_occurs",
    "macro_reject_coverage",
]


class FileCensus:
    def __init__(self, division: str, path: str) -> None:
        self.row = {c: 0 for c in COLUMNS}
        self.row["division"] = division
        self.row["file"] = path


def census_text(division: str, relpath: str, text: str) -> FileCensus:
    forms = parse_tokens([t for t, _s, _e in tokenize_with_pos(text)])
    decls = collect_decls(forms)
    fc = FileCensus(division, relpath)
    macro_heads: Set[str] = set()
    occ = nonground_uninterp_occurrences(forms, decls)
    unique_heads = {k for k, v in occ.items() if v == 1}

    for f in forms:
        if head(f) != "assert" or len(f) < 2:
            continue
        body = f[1]
        fc.row["n_assert"] += 1
        if _STRIP.has_quant_binder(body):
            fc.row["n_quant_assert"] += 1

        sk = skolem_positions(body)
        fc.row["sk_top"] += sk.top
        fc.row["sk_conj"] += sk.conj
        fc.row["sk_deep"] += sk.deep
        fc.row["sk_under_let"] += sk.under_let
        fc.row["sk_needs_function"] += sk.needs_function

        b = unwrap_annotation(body)
        if head(b) == "forall" and len(b) >= 3:
            bvars = binder_vars(b[1])
            if bvars:
                inner = unwrap_annotation(b[2])
                # The three classes are counted INDEPENDENTLY, not as an
                # if/elif chain, because they answer different questions and
                # z3 reaches them through different passes. A shape refused
                # as a simple macro can still be accepted as a quasi-macro --
                # `∀x. h(x, c) = t` is exactly that case -- and folding the
                # counters would hide it.
                got = classify_definitional_macro(inner, bvars, decls)
                if got is not None:
                    fc.row["macro_def"] += 1
                    macro_heads.add(got[0])
                else:
                    why = _why_not_macro(inner, bvars, decls)
                    if why == "occurs":
                        fc.row["macro_reject_occurs"] += 1
                    elif why == "coverage":
                        fc.row["macro_reject_coverage"] += 1
                    if classify_unit_macro(inner, bvars, decls) is not None:
                        fc.row["macro_unit"] += 1
                    elif classify_quasi_macro(inner, bvars, decls, unique_heads) is not None:
                        fc.row["macro_quasi"] += 1
    fc.row["macro_def_distinct"] = len(macro_heads)
    return fc


def _why_not_macro(inner, bvars: Sequence[str], decls: Decls) -> Optional[str]:
    """For an equality whose head IS an uninterpreted application, say which
    z3 condition refused it. This is the census's own negative control: a
    corpus in which no assertion is ever refused for either reason has not
    exercised the conditions, and the numbers would not be evidence that the
    conditions matter."""
    inner = unwrap_annotation(inner)
    if head(inner) != "=" or len(inner) != 3:
        return None
    for lhs, rhs in ((inner[1], inner[2]), (inner[2], inner[1])):
        lhs, rhs = unwrap_annotation(lhs), unwrap_annotation(rhs)
        h = head(lhs)
        if h is None or not decls.is_uninterpreted(h):
            continue
        args = lhs[1:]
        all_distinct_vars = (
            len(args) == len(bvars)
            and all(not isinstance(a, list) and str(a) in bvars for a in args)
            and len({str(a) for a in args}) == len(args)
        )
        if all_distinct_vars and occurs(h, rhs):
            return "occurs"
        if not all_distinct_vars:
            return "coverage"
    return None


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def main(argv: Sequence[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus-root", required=True)
    ap.add_argument("--division", required=True)
    ap.add_argument("--list", dest="listfile", required=True)
    ap.add_argument("--undecided", default=None)
    ap.add_argument("--out-tsv", required=True)
    args = ap.parse_args(list(argv))

    with open(args.listfile, encoding="utf-8") as fh:
        rels = [ln.strip() for ln in fh if ln.strip()]
    undecided: Set[str] = set()
    if args.undecided:
        with open(args.undecided, encoding="utf-8") as fh:
            undecided = {ln.strip() for ln in fh if ln.strip()}

    rows: List[FileCensus] = []
    failures: List[str] = []
    for rel in rels:
        full = os.path.join(args.corpus_root, rel)
        try:
            with open(full, encoding="utf-8", errors="replace") as fh:
                text = fh.read()
            rows.append(census_text(args.division, rel, text))
        except Exception as exc:  # noqa: BLE001 -- the failure IS the finding
            failures.append(f"{rel}: {type(exc).__name__}: {exc}")

    if not rows:
        print(
            f"CENSUS FAILED [{args.division}]: 0 files read from {args.listfile}. "
            "An empty census is indistinguishable from a strong negative.",
            file=sys.stderr,
        )
        return 2

    os.makedirs(os.path.dirname(os.path.abspath(args.out_tsv)) or ".", exist_ok=True)
    with open(args.out_tsv, "w", encoding="utf-8") as out:
        out.write("\t".join(COLUMNS + ["undecided"]) + "\n")
        for fc in rows:
            undec = "1" if fc.row["file"] in undecided else "0"
            out.write("\t".join(str(fc.row[c]) for c in COLUMNS) + "\t" + undec + "\n")

    n = len(rows)
    n_und = sum(1 for fc in rows if fc.row["file"] in undecided)

    def files_with(key: str, only_undecided: bool = False) -> int:
        return sum(
            1
            for fc in rows
            if fc.row[key] > 0
            and (not only_undecided or fc.row["file"] in undecided)
        )

    print(f"== {args.division}: {n} files read, {n_und} undecided ==")
    for key in (
        "sk_top",
        "sk_conj",
        "sk_deep",
        "sk_under_let",
        "sk_needs_function",
        "macro_def",
        "macro_unit",
        "macro_quasi",
        "macro_reject_occurs",
        "macro_reject_coverage",
    ):
        total = sum(fc.row[key] for fc in rows)
        print(
            f"  {key:24s} total={total:7d}  files={files_with(key):4d}/{n}"
            f"  undecided_files={files_with(key, True):4d}/{n_und}"
        )
    sk_any = sum(
        1
        for fc in rows
        if fc.row["sk_top"] + fc.row["sk_conj"] + fc.row["sk_deep"] > 0
    )
    sk_any_und = sum(
        1
        for fc in rows
        if fc.row["sk_top"] + fc.row["sk_conj"] + fc.row["sk_deep"] > 0
        and fc.row["file"] in undecided
    )
    print(
        f"  {'ANY skolem position':24s} {'':12s}  files={sk_any:4d}/{n}"
        f"  undecided_files={sk_any_und:4d}/{n_und}"
    )
    any_shape = sum(
        1
        for fc in rows
        if fc.row["sk_top"] + fc.row["sk_conj"] + fc.row["sk_deep"] + fc.row["macro_def"] > 0
    )
    any_shape_und = sum(
        1
        for fc in rows
        if fc.row["sk_top"] + fc.row["sk_conj"] + fc.row["sk_deep"] + fc.row["macro_def"] > 0
        and fc.row["file"] in undecided
    )
    print(
        f"  {'ANY (skolem or macro)':24s} {'':12s}  files={any_shape:4d}/{n}"
        f"  undecided_files={any_shape_und:4d}/{n_und}"
    )

    if failures:
        print(f"CENSUS PARSE FAILURES [{args.division}]: {len(failures)}", file=sys.stderr)
        for f in failures[:20]:
            print(f"  {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
