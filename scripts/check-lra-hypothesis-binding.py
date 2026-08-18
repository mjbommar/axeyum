#!/usr/bin/env python3
"""The rendered Lean hypotheses must be the query's own `(assert …)` lines.

# The gap this closes

`docs/prover-track/research/13-residual-trust-surface.md` ranks what a third
party must believe to accept an Axeyum result. Item 3 is the weakest link, and
it is weaker than the kernel:

> **The transcription from SMT-LIB into the rendered statement.** … we can prove
> the rendered proposition, and we cannot yet mechanically show the rendered
> proposition is what the input file said. A reader who accepts (1) and (2) must
> still take (3) on inspection.

When an UNSAT is reconstructed to a Lean module, the module declares the query's
constraints as its **own axioms**:

    axiom axeyum.reconstruct.lra.int_hyp._19 : Int.le (Int.add v13 Int.zero) Int.zero

and proves `False` from them. Lean checks the proof. Nothing checked that those
axioms say what `(assert (! (= x_alice_4 0) :named leave_alice_night4))` says. A
renderer that dropped a negation, flipped a relation, or renamed a variable would
produce a module that still typechecks, still reports a clean axiom footprint,
and is still worthless.

# What is actually checked

For each instance: obtain the rendered module from
`crates/axeyum-solver/examples/lean_hypothesis_binding_dump.rs`, then

1. **Parse the `.smt2` TEXT here, in Python.** Not through `axeyum-smtlib`, and
   not through anything this repository compiles. Every assertion is decomposed
   into the linear atoms it *entails* (`and` splits, `=` gives both bounds, `not`
   flips the relation, anything else contributes nothing — fail-closed).
2. **Parse the rendered module TEXT here, in Python**, recovering each
   `hyp`/`int_hyp` axiom as a linear atom over the module's opaque carrier
   constants.
3. **Require an injective renaming** φ from the module's carrier constants to the
   query's declared symbols under which *every* rendered hypothesis is one of the
   atoms the query's assertions entail. Injective, because an injective renaming
   preserves unsatisfiability (a *non*-injective one can turn SAT into UNSAT by
   identifying two variables, so it would prove nothing). Sort-respecting: an
   `Int` carrier may only bind an `Int`-declared symbol.
4. **Account for every axiom in the module.** Each is a carrier
   (`x`/`int_var`, opaque, type `Real`/`Int`), a matched hypothesis, or a pinned
   prelude law. An axiom that is none of those fails the run — otherwise
   `axiom smuggled : False` would sail past a checker that only inspects the
   axioms it recognizes.

Both sides are normalized to `Σ cᵢ·vᵢ + k ⋈ 0` over exact rationals, denominators
cleared and divided through by the gcd, because the renderer emits `x > 5` as
`-x + 5 < 0` and no string comparison can see through that. Normalization is
where a transcription bug would hide, so the two normalizers share no code:
one reads s-expressions, the other reads `Real.add`/`Real.neg` spines.

# Why this one can fail

This repository measured 40 of 162 checker runs exiting 0 on completion alone.
So the run does not merely check the committed artifacts — it **corrupts them and
requires the corruption to be caught**, on every run, in the default mode:

    flip-relation   Real.le -> Real.lt          (a strict/non-strict swap)
    drop-negation   remove one `Real.neg`       (a dropped minus sign)
    swap-arguments  swap the relation's sides   (a flipped inequality)
    shift-constant  add one `Real.one`          (an off-by-one bound)
    drop-term       delete one summand          (a lost variable)

applied to **every** hypothesis of every module, one at a time.

Not every corruption *should* be caught, and pretending otherwise would make the
control lie in the other direction. `x ≤ 0` shifted to `x ≤ 1` names a different
genuine row of the same query; swapping the sides of `x − y < 0` is faithful
again under the renaming that swaps `x` and `y` — measured, on
`cvc5__cli__regress0__dump-unsat-core-full.smt2`, while this was being written.
Both are accepts a correct checker must make. So the run reports two numbers and
guards both directions:

- `mutants_caught` — corruptions rejected, with `--min-required-mutations` as a
  floor. A checker that never rejects anything cannot go quietly vacuous.
- `mutants_accepted` — corruptions the checker calls faithful anyway. Each is
  **re-verified from the returned binding** by `verify_binding`, which shares no
  control flow with the search: injectivity, sort-soundness, and every renamed
  hypothesis present in the query's atom pool. An accept the binding does not
  justify fails the run, and so does a *pristine* accept that fails the same
  re-check. The backtracking search is untrusted; the re-check is the small
  trusted part.

That the pristine modules pass is not by itself evidence of anything — a
consistent global renaming of the carriers must also pass (it is semantically
harmless), while collapsing two carriers into one must not. Both directions are
pinned in `scripts/tests/test_check_lra_hypothesis_binding.py`.

# What this does NOT cover

Stated precisely, because a checker's advertised scope is the part people
believe:

- **Only the arithmetic hypothesis routes.** `axeyum.reconstruct.lra.hyp._N`
  (Real) and `.int_hyp._N` (Int). The QF_BV, EUF, datatype, string and quantifier
  reconstructions render hypotheses under other namespaces and are untouched — an
  unrecognized `axeyum.reconstruct.*` axiom fails the run rather than being
  skipped, so the uncovered routes are visible rather than silently blessed.
- **Only the linear fragment the Python parser admits.** `+ - *` by a numeral,
  `and`, `not`, `<= < >= > =`, `let`. An assertion outside it contributes no
  atoms, so a hypothesis claiming to come from it is unmatched and the run fails.
- **It does not check the proof.** That is the kernel's job, and Lean's.
- **It does not check the prelude axioms** (`Real.add_comm`, …) say what their
  names claim — that is item 2 of the trust surface, and a different gate.
- **It checks a SUBSET relation, not equality.** Every rendered hypothesis must
  come from the query; the refutation is free to use fewer assertions than the
  query has, because a refutation of a subset refutes the whole.
"""

from __future__ import annotations

import argparse
import math
import pathlib
import re
import subprocess
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]

DUMPER_SOURCE = ROOT / "crates/axeyum-solver/examples/lean_hypothesis_binding_dump.rs"
DUMPER_BIN = ROOT / "target/release/examples/lean_hypothesis_binding_dump"
DUMPER_BUILD = [
    "cargo",
    "build",
    "--release",
    "-q",
    "-p",
    "axeyum-solver",
    "--features",
    "full",
    "--example",
    "lean_hypothesis_binding_dump",
]

# The instances this gate is pinned to, one path per line, `#` comments. A
# ratchet: adding a line is routine, removing one means a query that used to have
# a verified transcription no longer does.
MANIFEST = ROOT / "scripts/lra-hypothesis-binding-instances.txt"

# Floors. A scanner that goes blind reports a beautiful clean zero. Measured
# 2026-08-17: 105 instances, 248 hypotheses, 869 corruptions caught.
MIN_INSTANCES = 100
MIN_HYPOTHESES = 240
MIN_REQUIRED_MUTATIONS = 800


def manifest_instances() -> list[str]:
    lines = MANIFEST.read_text(encoding="utf-8").splitlines()
    return [line.strip() for line in lines if line.strip() and not line.startswith("#")]

# Axioms a rendered module may carry that are NOT query-derived: the ordered-field
# prelude and Lean's compiler-internal constants. Their *contents* are item 2 of
# the trust surface and are gated by the Lean axiom ledger, not here; this list
# exists so that an axiom appearing outside both it and the query-derived
# namespace fails the run instead of being ignored.
PRELUDE_AXIOMS = {
    "lcErased",
    "lcAny",
    "lcVoid",
    "Real",
    "Real.add",
    "Real.mul",
    "Real.neg",
    "Real.zero",
    "Real.one",
    "Real.le",
    "Real.lt",
    "Real.le_refl",
    "Real.le_trans",
    "Real.le_antisymm",
    "Real.lt_irrefl",
    "Real.lt_trans",
    "Real.le_of_lt",
    "Real.lt_of_le_of_lt",
    "Real.lt_of_lt_of_le",
    "Real.add_comm",
    "Real.add_assoc",
    "Real.add_zero",
    "Real.zero_add",
    "Real.add_neg",
    "Real.neg_add",
    "Real.add_le_add",
    "Real.add_lt_add",
    "Real.add_lt_add_of_le_of_lt",
    "Real.add_lt_add_of_lt_of_le",
    "Real.mul_comm",
    "Real.mul_assoc",
    "Real.mul_one",
    "Real.one_mul",
    "Real.left_distrib",
    "Real.right_distrib",
    "Real.mul_le_mul_of_nonneg_left",
    "Real.mul_lt_mul_of_pos_left",
    "Real.sq_nonneg",
    "Real.zero_lt_one",
    "Real.zero_ne_one",
    "Real.lt_trichotomy",
    "Real.le_total",
    "Real.exists_inv",
    "Real.inv",
    "Real.mul_inv_cancel",
}

# The two arithmetic hypothesis routes this checker covers, and their carriers.
ROUTES = {
    "axeyum.reconstruct.lra.hyp.": ("Real", "axeyum.reconstruct.lra.x."),
    "axeyum.reconstruct.lra.int_hyp.": ("Int", "axeyum.reconstruct.lra.int_var."),
}
CARRIER_PREFIXES = {
    "axeyum.reconstruct.lra.x.": "Real",
    "axeyum.reconstruct.lra.int_var.": "Int",
}
QUERY_NAMESPACE = "axeyum.reconstruct."


class Unsupported(Exception):
    """A shape this checker deliberately does not model. Never silently skipped."""


# ---------------------------------------------------------------------------
# Canonical atoms
# ---------------------------------------------------------------------------
#
# An atom is `Σ cᵢ·vᵢ + k ⋈ 0` with `⋈ ∈ {<=, <, =}`, coefficients cleared to
# integers and divided by their gcd. Scaling by a POSITIVE rational preserves
# `≤ 0` and `< 0`, which is why the normal form is canonical for them; `= 0` is
# additionally sign-normalized, since `E = 0` and `−E = 0` are the same fact.


def canonical(rel: str, coeffs: dict[str, Fraction], const: Fraction) -> tuple:
    """`(rel, ((var, int_coeff), …) sorted, int_const)` — the comparable form."""
    items = {v: c for v, c in coeffs.items() if c != 0}
    values = list(items.values()) + [const]
    denom = 1
    for value in values:
        denom = denom * value.denominator // math.gcd(denom, value.denominator)
    ints = {v: int(c * denom) for v, c in items.items()}
    k = int(const * denom)
    divisor = 0
    for value in list(ints.values()) + [k]:
        divisor = math.gcd(divisor, abs(value))
    if divisor > 1:
        ints = {v: c // divisor for v, c in ints.items()}
        k //= divisor
    if rel == "=":
        # Sign-normalize on the first variable (or the constant) so `E = 0` and
        # `−E = 0` land on one representative.
        ordered = sorted(ints.items())
        lead = ordered[0][1] if ordered else k
        if lead < 0:
            ints = {v: -c for v, c in ints.items()}
            k = -k
    return (rel, tuple(sorted(ints.items())), k)


def signature(atom: tuple) -> tuple:
    """The rename-invariant part: relation, constant, and the coefficient bag."""
    rel, terms, const = atom
    return (rel, const, tuple(sorted(c for _, c in terms)))


# ---------------------------------------------------------------------------
# Side A: the SMT-LIB text
# ---------------------------------------------------------------------------

SMT_TOKEN = re.compile(r"\(|\)|\|[^|]*\||\"(?:[^\"]|\"\")*\"|[^\s()|\"]+")


def sexprs(text: str) -> list:
    """Every top-level s-expression in `text`, as nested lists of strings."""
    stripped = []
    for line in text.splitlines():
        # `;` starts a comment unless it is inside a string or |quoted| symbol.
        out, in_string, in_pipe = [], False, False
        for ch in line:
            if ch == '"' and not in_pipe:
                in_string = not in_string
            elif ch == "|" and not in_string:
                in_pipe = not in_pipe
            elif ch == ";" and not in_string and not in_pipe:
                break
            out.append(ch)
        stripped.append("".join(out))
    tokens = SMT_TOKEN.findall("\n".join(stripped))
    stack: list[list] = [[]]
    for token in tokens:
        if token == "(":
            stack.append([])
        elif token == ")":
            if len(stack) == 1:
                raise Unsupported("unbalanced `)` in the SMT-LIB input")
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise Unsupported("unbalanced `(` in the SMT-LIB input")
    return stack[0]


NUMERAL = re.compile(r"\A\d+\Z")
DECIMAL = re.compile(r"\A\d+\.\d+\Z")


def as_number(token: str) -> Fraction | None:
    if NUMERAL.match(token):
        return Fraction(int(token))
    if DECIMAL.match(token):
        return Fraction(token)
    return None


def linear(term, env: dict[str, tuple]) -> tuple[dict[str, Fraction], Fraction]:
    """`(coeffs, const)` for an arithmetic term, or raise [`Unsupported`]."""
    if isinstance(term, str):
        number = as_number(term)
        if number is not None:
            return ({}, number)
        if term in env:
            return env[term]
        return ({term: Fraction(1)}, Fraction(0))
    if not term:
        raise Unsupported("empty application")
    head = term[0]
    args = term[1:]
    if head == "+":
        coeffs: dict[str, Fraction] = {}
        const = Fraction(0)
        for arg in args:
            c, k = linear(arg, env)
            for v, value in c.items():
                coeffs[v] = coeffs.get(v, Fraction(0)) + value
            const += k
        return (coeffs, const)
    if head == "-":
        if len(args) == 1:
            c, k = linear(args[0], env)
            return ({v: -value for v, value in c.items()}, -k)
        coeffs, const = linear(args[0], env)
        coeffs = dict(coeffs)
        for arg in args[1:]:
            c, k = linear(arg, env)
            for v, value in c.items():
                coeffs[v] = coeffs.get(v, Fraction(0)) - value
            const -= k
        return (coeffs, const)
    if head == "*":
        # At most ONE factor may be non-constant; the rest multiply into a scalar.
        scalar = Fraction(1)
        linear_factor: tuple[dict[str, Fraction], Fraction] | None = None
        for arg in args:
            c, k = linear(arg, env)
            if not c:
                scalar *= k
                continue
            if linear_factor is not None:
                raise Unsupported("nonlinear product")
            linear_factor = (c, k)
        if linear_factor is None:
            return ({}, scalar)
        c, k = linear_factor
        return ({v: value * scalar for v, value in c.items()}, k * scalar)
    if head == "/":
        if len(args) != 2:
            raise Unsupported("`/` with other than two arguments")
        c, k = linear(args[0], env)
        dc, dk = linear(args[1], env)
        if dc or dk == 0:
            raise Unsupported("division by a non-constant or by zero")
        return ({v: value / dk for v, value in c.items()}, k / dk)
    if head == "let":
        return linear(*_let(term, env))
    if head == "to_real":
        if len(args) != 1:
            raise Unsupported("`to_real` arity")
        return linear(args[0], env)
    raise Unsupported(f"arithmetic head `{head}`")


def _let(term, env: dict[str, tuple]):
    """`(let ((v e) …) body)` -> `(body, extended_env)`."""
    if len(term) != 3:
        raise Unsupported("`let` arity")
    extended = dict(env)
    for binding in term[1]:
        if not isinstance(binding, list) or len(binding) != 2:
            raise Unsupported("`let` binding shape")
        extended[binding[0]] = linear(binding[1], env)
    return (term[2], extended)


# `(rel, swap)`: `swap` means the SMT-LIB order is `b REL a`.
COMPARISONS = {"<=": ("<=", False), "<": ("<", False), ">=": ("<=", True), ">": ("<", True)}
NEGATED = {"<=": ("<", True), "<": ("<=", True), ">=": ("<", False), ">": ("<=", False)}


def atoms_of(term, polarity: bool, env: dict[str, tuple]) -> list[tuple]:
    """Canonical atoms ENTAILED by `term` under `polarity`.

    Fail-closed by omission: a shape that is not decomposable contributes no
    atoms, so a hypothesis claiming to descend from it stays unmatched and the
    run fails. Never returns an atom the term does not entail.
    """
    if isinstance(term, str):
        return []
    if not term:
        return []
    head, args = term[0], term[1:]
    if head == "!":
        return atoms_of(args[0], polarity, env) if args else []
    if head == "let":
        body, extended = _let(term, env)
        return atoms_of(body, polarity, extended)
    if head == "not":
        return atoms_of(args[0], not polarity, env) if len(args) == 1 else []
    if (head == "and" and polarity) or (head == "or" and not polarity):
        out = []
        for arg in args:
            out.extend(atoms_of(arg, polarity, env))
        return out
    if head in COMPARISONS and len(args) >= 2:
        table = COMPARISONS if polarity else NEGATED
        rel, swap = table[head]
        out = []
        # SMT-LIB chains: `(< a b c)` is `a<b ∧ b<c`. Chained NEGATION is a
        # disjunction, so only the positive direction may be split.
        pairs = list(zip(args, args[1:]))
        if len(pairs) > 1 and not polarity:
            return []
        for left, right in pairs:
            try:
                lc, lk = linear(left, env)
                rc, rk = linear(right, env)
            except Unsupported:
                continue
            # `a ⋈ b` is `a − b ⋈ 0`; `a ≥ b` / `a > b` is `b − a ⋈ 0`.
            (nc, nk), (pc, pk) = ((rc, rk), (lc, lk)) if swap else ((lc, lk), (rc, rk))
            coeffs = dict(nc)
            for v, value in pc.items():
                coeffs[v] = coeffs.get(v, Fraction(0)) - value
            out.append(canonical(rel, coeffs, nk - pk))
        return out
    if head == "=" and polarity and len(args) >= 2:
        out = []
        for left, right in zip(args, args[1:]):
            try:
                lc, lk = linear(left, env)
                rc, rk = linear(right, env)
            except Unsupported:
                continue
            coeffs = {v: value for v, value in lc.items()}
            for v, value in rc.items():
                coeffs[v] = coeffs.get(v, Fraction(0)) - value
            const = lk - rk
            # `a = b` entails BOTH bounds; the reconstructors use whichever they
            # need, and the equality atom itself for the equality routes.
            out.append(canonical("<=", coeffs, const))
            out.append(canonical("<=", {v: -c for v, c in coeffs.items()}, -const))
            out.append(canonical("=", coeffs, const))
        return out
    return []


def read_query(path: pathlib.Path) -> tuple[dict[str, str], list[list[tuple]]]:
    """`(declared sort by symbol, per-assertion canonical atoms)`."""
    forms = sexprs(path.read_text(encoding="utf-8"))
    sorts: dict[str, str] = {}
    assertions: list[list[tuple]] = []
    for form in forms:
        if not isinstance(form, list) or not form:
            continue
        head = form[0]
        if head == "declare-fun" and len(form) == 4 and form[2] == []:
            sorts[form[1]] = form[3] if isinstance(form[3], str) else "?"
        elif head == "declare-const" and len(form) == 3:
            sorts[form[1]] = form[2] if isinstance(form[2], str) else "?"
        elif head == "assert" and len(form) == 2:
            assertions.append(atoms_of(form[1], True, {}))
    return sorts, assertions


# ---------------------------------------------------------------------------
# Side B: the rendered Lean module
# ---------------------------------------------------------------------------

LEAN_TOKEN = re.compile(r"\(|\)|[^\s()]+")
AXIOM_LINE = re.compile(r"^axiom\s+(\S+)\s*:\s*(.*)$")


def lean_expr(text: str):
    """Parse a rendered Lean type into nested lists (application = a list)."""
    tokens = LEAN_TOKEN.findall(text)
    pos = 0

    def parse_spine(depth: int):
        nonlocal pos
        items = []
        while pos < len(tokens):
            token = tokens[pos]
            if token == ")":
                if depth == 0:
                    raise Unsupported("unbalanced `)` in a rendered type")
                pos += 1
                break
            if token == "(":
                pos += 1
                items.append(parse_spine(depth + 1))
                continue
            pos += 1
            items.append(token)
        if not items:
            raise Unsupported("empty rendered application")
        return items[0] if len(items) == 1 else items

    result = parse_spine(0)
    if pos != len(tokens):
        raise Unsupported("trailing tokens in a rendered type")
    return result


def lean_linear(expr, carrier: str) -> tuple[dict[str, Fraction], Fraction]:
    """`(coeffs, const)` for a rendered carrier expression."""
    if isinstance(expr, str):
        if expr == f"{carrier}.zero":
            return ({}, Fraction(0))
        if expr == f"{carrier}.one":
            return ({}, Fraction(1))
        if expr.startswith(QUERY_NAMESPACE):
            return ({expr: Fraction(1)}, Fraction(0))
        raise Unsupported(f"rendered leaf `{expr}`")
    head, args = expr[0], expr[1:]
    if not isinstance(head, str):
        raise Unsupported("rendered application with a non-constant head")
    if head == f"{carrier}.add" and len(args) == 2:
        lc, lk = lean_linear(args[0], carrier)
        rc, rk = lean_linear(args[1], carrier)
        coeffs = dict(lc)
        for v, value in rc.items():
            coeffs[v] = coeffs.get(v, Fraction(0)) + value
        return (coeffs, lk + rk)
    if head == f"{carrier}.neg" and len(args) == 1:
        c, k = lean_linear(args[0], carrier)
        return ({v: -value for v, value in c.items()}, -k)
    if head == f"{carrier}.mul" and len(args) == 2:
        lc, lk = lean_linear(args[0], carrier)
        rc, rk = lean_linear(args[1], carrier)
        if lc and rc:
            raise Unsupported("rendered nonlinear product")
        if lc:
            return ({v: value * rk for v, value in lc.items()}, lk * rk)
        return ({v: value * lk for v, value in rc.items()}, lk * rk)
    raise Unsupported(f"rendered head `{head}`")


def lean_atom(ty: str, carrier: str) -> tuple:
    """The canonical atom a rendered hypothesis type denotes."""
    expr = lean_expr(ty)
    if isinstance(expr, str) or len(expr) != 3:
        raise Unsupported("a hypothesis type is not a binary relation application")
    head, left, right = expr
    if head == f"{carrier}.le":
        rel = "<="
    elif head == f"{carrier}.lt":
        rel = "<"
    else:
        raise Unsupported(f"hypothesis relation `{head}`")
    lc, lk = lean_linear(left, carrier)
    rc, rk = lean_linear(right, carrier)
    coeffs = dict(lc)
    for v, value in rc.items():
        coeffs[v] = coeffs.get(v, Fraction(0)) - value
    return canonical(rel, coeffs, lk - rk)


def read_module(source: str) -> tuple[dict[str, str], list[tuple[str, str, str]], list[str]]:
    """`(carrier sort by name, [(name, carrier, type_text)], unaccounted axioms)`."""
    carriers: dict[str, str] = {}
    hypotheses: list[tuple[str, str, str]] = []
    unaccounted: list[str] = []
    for line in source.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if not match:
            continue
        name, ty = match.group(1), match.group(2).strip()
        carrier_hit = next(
            (c for prefix, c in CARRIER_PREFIXES.items() if name.startswith(prefix)), None
        )
        if carrier_hit is not None:
            if ty != carrier_hit:
                unaccounted.append(
                    f"{name} declares type `{ty}`, not the opaque carrier `{carrier_hit}`"
                )
            else:
                carriers[name] = carrier_hit
            continue
        route_hit = next(
            (c for prefix, (c, _) in ROUTES.items() if name.startswith(prefix)), None
        )
        if route_hit is not None:
            hypotheses.append((name, route_hit, ty))
            continue
        if name.startswith(QUERY_NAMESPACE):
            unaccounted.append(
                f"{name} is a query-derived axiom under `{QUERY_NAMESPACE}` that this "
                "checker does not model, so its faithfulness is unverified"
            )
        elif name not in PRELUDE_AXIOMS:
            unaccounted.append(
                f"{name} is an axiom that is neither query-derived nor a pinned prelude "
                "law; it could assert anything"
            )
    return carriers, hypotheses, unaccounted


# ---------------------------------------------------------------------------
# The binding search
# ---------------------------------------------------------------------------


def verify_binding(
    phi: dict[str, str],
    hypotheses: list[tuple[str, str, tuple]],
    allowed: set[tuple],
    carriers: dict[str, str],
    sorts: dict[str, str],
) -> list[str]:
    """Re-check a proposed φ from scratch. The search is untrusted; this is not.

    `bind` is a backtracking search with an ordering heuristic, a node budget and
    a permutation generator — exactly the kind of code that returns a wrong answer
    quietly. So nothing downstream trusts what it returns: every accepted binding
    comes back through here, which re-derives the three properties from the
    binding alone. It shares no control flow with the search.

    Returns the list of violations; empty means the binding genuinely justifies
    the module.
    """
    problems: list[str] = []
    seen: dict[str, str] = {}
    for carrier_name, target in sorted(phi.items()):
        if carrier_name not in carriers:
            problems.append(f"φ binds `{carrier_name}`, which the module never declared")
        if not sort_compatible(carriers.get(carrier_name), sorts.get(target)):
            problems.append(
                f"φ sends `{carrier_name}` (carrier "
                f"{carriers.get(carrier_name)}) to `{target}` (declared "
                f"{sorts.get(target)}), which is not a sound substitution"
            )
        if target in seen:
            problems.append(
                f"φ is NOT injective: `{carrier_name}` and `{seen[target]}` both map to "
                f"`{target}`, and identifying two variables can make a satisfiable query "
                "look refuted"
            )
        seen[target] = carrier_name
    for name, _carrier, atom in hypotheses:
        _rel, terms, _const = atom
        unbound = [v for v, _ in terms if v not in phi]
        if unbound:
            problems.append(f"{name} mentions {unbound}, which φ does not bind")
            continue
        if _rename(atom, phi) not in allowed:
            problems.append(
                f"{name} renames to {_rename(atom, phi)!r}, which no assertion of the "
                "query entails"
            )
    return problems


def sort_compatible(carrier: str | None, declared: str | None) -> bool:
    """May a module carrier of sort `carrier` stand for a symbol declared `declared`?

    Directional on purpose. The rendered `Int` is Lean's inductive `Int`, so a
    proof may use integrality; standing it in for a `Real`-declared symbol would
    let the module refute constraints the query never made. The rendered `Real`
    is an axiomatized opaque ordered field with no integrality, so an
    `Int`-declared symbol is admissible (the refutation holds a fortiori) while
    anything non-numeric is not. An UNDECLARED symbol is rejected: it means the
    Python side lost track of the query's vocabulary, and a checker that cannot
    see the vocabulary must not bless a binding into it.
    """
    if carrier is None:
        return False
    if declared is None:
        return False
    if carrier == "Int":
        return declared == "Int"
    if carrier == "Real":
        return declared in ("Real", "Int")
    return False


def bind(
    hypotheses: list[tuple[str, tuple]],
    carriers: dict[str, str],
    source_atoms: dict[tuple, list[tuple[tuple, int]]],
    sorts: dict[str, str],
    budget: int = 2_000_000,
) -> tuple[dict[str, str] | None, list[int], str]:
    """Search an injective, sort-respecting φ making every hypothesis a query atom.

    Returns `(phi, origins, detail)`. `phi is None` means no binding exists (or
    the node budget was exhausted, which is reported as a failure — a search that
    gave up must never read as a pass).
    """
    ordered = sorted(
        hypotheses, key=lambda h: len(source_atoms.get(signature(h[1]), ()))
    )
    for name, atom in ordered:
        if not source_atoms.get(signature(atom)):
            return (
                None,
                [],
                f"{name}: no assertion of the query entails an atom with this relation, "
                f"constant and coefficient bag ({signature(atom)!r})",
            )

    state = {"nodes": 0, "exhausted": False}

    def extend(
        index: int, phi: dict[str, str], used: frozenset[str], origins: tuple[int, ...]
    ) -> tuple[dict[str, str], tuple[int, ...]] | None:
        if index == len(ordered):
            return (phi, origins)
        _name, atom = ordered[index]
        _, terms, _ = atom
        for candidate, origin in source_atoms.get(signature(atom), ()):
            _, cand_terms, _ = candidate
            # EVERY consistent way of matching this hypothesis onto this atom,
            # not just the first. A single-permutation version of this search
            # rejected `x + y = 1 ∧ x = 2 ∧ y = 0` — a faithful module — because
            # it bound `x._0 ↦ x` from the two-variable row and then could not
            # undo it. A binding checker whose search is incomplete reports
            # transcription defects that are not there.
            for next_phi, next_used in _matchings(
                terms, cand_terms, phi, used, carriers, sorts
            ):
                state["nodes"] += 1
                if state["nodes"] > budget:
                    state["exhausted"] = True
                    return None
                found = extend(index + 1, next_phi, next_used, origins + (origin,))
                if found is not None:
                    return found
                if state["exhausted"]:
                    return None
        return None

    found = extend(0, {}, frozenset(), ())
    if found is not None:
        return (found[0], list(found[1]), "")
    if state["exhausted"]:
        return (None, [], f"binding search exhausted its {budget}-node budget")
    return (
        None,
        [],
        "no injective, sort-respecting renaming makes every rendered hypothesis an "
        "atom of the query",
    )


def _matchings(
    terms: tuple[tuple[str, int], ...],
    cand_terms: tuple[tuple[str, int], ...],
    phi: dict[str, str],
    used: frozenset[str],
    carriers: dict[str, str],
    sorts: dict[str, str],
):
    """Yield every extension of `phi` mapping `terms` onto `cand_terms`."""
    if len(terms) != len(cand_terms):
        return
    if not terms:
        yield phi, used
        return
    var, coeff = terms[0]
    for i, (cand_var, cand_coeff) in enumerate(cand_terms):
        if cand_coeff != coeff:
            continue
        bound = phi.get(var)
        if bound is not None:
            if bound != cand_var:
                continue
            next_phi, next_used = phi, used
        else:
            if cand_var in used:
                continue
            if not sort_compatible(carriers.get(var), sorts.get(cand_var)):
                continue
            next_phi = {**phi, var: cand_var}
            next_used = used | {cand_var}
        yield from _matchings(
            terms[1:], cand_terms[:i] + cand_terms[i + 1 :], next_phi, next_used, carriers, sorts
        )


# ---------------------------------------------------------------------------
# Mutations — the proof that this checker can fail
# ---------------------------------------------------------------------------

MUTATIONS = ("flip-relation", "drop-negation", "swap-arguments", "shift-constant", "drop-term")


def mutate(ty: str, carrier: str, kind: str) -> str | None:
    """Corrupt one rendered hypothesis type the way a renderer bug would."""
    if kind == "flip-relation":
        if ty.startswith(f"{carrier}.le "):
            return f"{carrier}.lt " + ty[len(f"{carrier}.le "):]
        if ty.startswith(f"{carrier}.lt "):
            return f"{carrier}.le " + ty[len(f"{carrier}.lt "):]
        return None
    if kind == "drop-negation":
        needle = f"({carrier}.neg "
        at = ty.find(needle)
        if at < 0:
            return None
        # Remove the wrapper, keeping its argument: find the matching `)`.
        depth = 0
        for i in range(at, len(ty)):
            if ty[i] == "(":
                depth += 1
            elif ty[i] == ")":
                depth -= 1
                if depth == 0:
                    return ty[:at] + ty[at + len(needle) : i] + ty[i + 1 :]
        return None
    if kind == "swap-arguments":
        expr = lean_expr(ty)
        if isinstance(expr, str) or len(expr) != 3:
            return None
        return f"{expr[0]} {_render(expr[2])} {_render(expr[1])}"
    if kind == "shift-constant":
        needle = f"{carrier}.zero"
        at = ty.rfind(needle)
        if at < 0:
            return None
        return ty[:at] + f"({carrier}.add {carrier}.one {carrier}.zero)" + ty[at + len(needle) :]
    if kind == "drop-term":
        # `(C.add A B)` -> `B`: one summand of the constraint simply vanishes.
        needle = f"({carrier}.add "
        at = ty.find(needle)
        if at < 0:
            return None
        depth = 0
        for i in range(at, len(ty)):
            if ty[i] == "(":
                depth += 1
            elif ty[i] == ")":
                depth -= 1
                if depth == 0:
                    inner = ty[at + len(needle) : i]
                    parts = _split_spine(inner)
                    if len(parts) != 2:
                        return None
                    return ty[:at] + parts[1] + ty[i + 1 :]
        return None
    raise Unsupported(f"mutation `{kind}`")


def _render(expr) -> str:
    if isinstance(expr, str):
        return expr
    return "(" + " ".join(_render(item) for item in expr) + ")"


def _split_spine(text: str) -> list[str]:
    """Split a rendered application body into its top-level arguments."""
    parts, depth, current = [], 0, []
    for ch in text:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch.isspace() and depth == 0:
            if current:
                parts.append("".join(current))
                current = []
            continue
        current.append(ch)
    if current:
        parts.append("".join(current))
    return parts


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def dumper_binary(build: bool) -> pathlib.Path:
    if DUMPER_BIN.exists() and (
        not DUMPER_SOURCE.exists() or DUMPER_BIN.stat().st_mtime >= DUMPER_SOURCE.stat().st_mtime
    ):
        return DUMPER_BIN
    if not build:
        raise SystemExit(
            f"{DUMPER_BIN} is missing or older than its source and `--no-build` was given.\n"
            f"Build it with: {' '.join(DUMPER_BUILD)}"
        )
    subprocess.run(DUMPER_BUILD, cwd=ROOT, check=True)
    if not DUMPER_BIN.exists():
        raise SystemExit(f"{' '.join(DUMPER_BUILD)} did not produce {DUMPER_BIN}")
    return DUMPER_BIN


def render_module(binary: pathlib.Path, instance: pathlib.Path) -> tuple[str, list[int], str]:
    result = subprocess.run(
        [str(binary), str(instance)], cwd=ROOT, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise SystemExit(f"{instance}: the dumper failed:\n{result.stderr.strip()}")
    indices: list[int] = []
    fragment = "?"
    for line in result.stderr.splitlines():
        if not line.startswith("BINDING_DUMP|"):
            continue
        fields = dict(
            piece.split("=", 1) for piece in line.split("|")[1:] if "=" in piece
        )
        fragment = fields.get("fragment", "?")
        raw = fields.get("indices", "")
        indices = [int(piece) for piece in raw.split(",") if piece]
    return result.stdout, indices, fragment


def check_instance(
    source: str,
    indices: list[int],
    sorts: dict[str, str],
    assertions: list[list[tuple]],
) -> tuple[dict[str, str] | None, list[tuple[str, str, tuple]], set[tuple], str]:
    """`(phi, [(name, carrier, atom)], allowed atom set, failure detail)`."""
    carriers, raw_hypotheses, unaccounted = read_module(source)
    if unaccounted:
        return (None, [], set(), "; ".join(unaccounted))
    hypotheses: list[tuple[str, str, tuple]] = []
    for name, carrier, ty in raw_hypotheses:
        try:
            hypotheses.append((name, carrier, lean_atom(ty, carrier)))
        except Unsupported as error:
            return (None, [], set(), f"{name}: {error}")

    pool: dict[tuple, list[tuple[tuple, int]]] = {}
    allowed: set[tuple] = set()
    for index in indices:
        if index >= len(assertions):
            return (None, [], set(), f"the dumper named assertion {index}, which does not exist")
        for atom in assertions[index]:
            if atom in allowed:
                # The same atom asserted twice adds nothing but search branches.
                continue
            pool.setdefault(signature(atom), []).append((atom, index))
            allowed.add(atom)

    phi, _origins, detail = bind(
        [(name, atom) for name, _, atom in hypotheses], carriers, pool, sorts
    )
    if phi is None:
        return (None, hypotheses, allowed, detail)
    problems = verify_binding(phi, hypotheses, allowed, carriers, sorts)
    if problems:
        # The search claimed a binding its own definition does not support. That
        # is a defect in THIS checker, and it must never read as a pass.
        return (None, hypotheses, allowed, "SEARCH DEFECT: " + "; ".join(problems))
    return (phi, hypotheses, allowed, "")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--instance", action="append", default=None)
    parser.add_argument(
        "--module",
        default=None,
        help="check a module ALREADY on disk against the single --instance given, "
        "instead of rendering one. The offline form the control tests use, and the "
        "way to reproduce a failure from a captured artifact.",
    )
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--no-self-check", action="store_true")
    parser.add_argument("--min-instances", type=int, default=MIN_INSTANCES)
    parser.add_argument("--min-hypotheses", type=int, default=MIN_HYPOTHESES)
    parser.add_argument(
        "--min-required-mutations", type=int, default=MIN_REQUIRED_MUTATIONS
    )
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)

    instances = [pathlib.Path(p) for p in (args.instance or manifest_instances())]
    if args.module is not None and len(instances) != 1:
        raise SystemExit("--module takes exactly one --instance")
    binary = None if args.module else dumper_binary(build=not args.no_build)

    failures: list[str] = []
    total_hypotheses = 0
    caught_mutations = 0
    accepted_mutations = 0
    escaped: list[str] = []

    for instance in instances:
        path = instance if instance.is_absolute() else ROOT / instance
        sorts, assertions = read_query(path)
        if args.module is not None:
            module_path = pathlib.Path(args.module)
            source = (module_path if module_path.is_absolute() else ROOT / module_path).read_text(
                encoding="utf-8"
            )
            indices, fragment = list(range(len(assertions))), "supplied"
        else:
            source, indices, fragment = render_module(binary, path)
        phi, hypotheses, allowed, detail = check_instance(source, indices, sorts, assertions)
        if phi is None:
            failures.append(f"{instance}: {detail}")
            continue
        total_hypotheses += len(hypotheses)
        if args.verbose:
            print(f"  {instance} [{fragment}] {len(hypotheses)} hypotheses bound")
            for name, _carrier, atom in hypotheses:
                renamed = _rename(atom, phi)
                print(f"    {name} -> {renamed}")

        if args.no_self_check:
            continue
        # Corrupt each hypothesis, each way, and see what happens. Two outcomes,
        # both meaningful, neither assumed:
        #
        #   REJECTED — the corruption was caught. `caught` is what makes this
        #     checker something other than a function that returns 0.
        #   ACCEPTED — the checker says the damaged module is ALSO a faithful
        #     rendering. Sometimes it truly is: `x ≤ 0` shifted to `x ≤ 1` names a
        #     different genuine row of the same query, and swapping the sides of
        #     `x − y < 0` is faithful again under the renaming that swaps x and y.
        #     An accept is therefore not automatically a miss — but it IS a claim,
        #     so it is re-verified from the returned binding, and an accept that
        #     the binding does not justify fails the run.
        _, raw_hypotheses, _ = read_module(source)
        for name, carrier, ty in raw_hypotheses:
            for kind in MUTATIONS:
                try:
                    damaged = mutate(ty, carrier, kind)
                except Unsupported:
                    damaged = None
                if damaged is None or damaged == ty:
                    continue
                mutant_source = source.replace(f"axiom {name} : {ty}", f"axiom {name} : {damaged}")
                if mutant_source == source:
                    failures.append(
                        f"{instance}: could not splice the {kind} mutant of {name} into the "
                        "module, so the control did not run"
                    )
                    continue
                mutant_phi, mutant_hyps, mutant_allowed, mutant_detail = check_instance(
                    mutant_source, indices, sorts, assertions
                )
                if mutant_phi is None:
                    if mutant_detail.startswith("SEARCH DEFECT"):
                        failures.append(f"{instance}: {kind} on {name}: {mutant_detail}")
                    else:
                        caught_mutations += 1
                    continue
                accepted_mutations += 1
                mutant_carriers, _, _ = read_module(mutant_source)
                residual = verify_binding(
                    mutant_phi, mutant_hyps, mutant_allowed, mutant_carriers, sorts
                )
                if residual:
                    escaped.append(
                        f"{instance}: {kind} on {name} was ACCEPTED but its binding does not "
                        f"justify it ({'; '.join(residual)}) — the checker passed something "
                        "it cannot defend"
                    )

    print(
        f"LRA_HYP_BINDING|instances={len(instances)}|hypotheses={total_hypotheses}|"
        f"mutants_caught={caught_mutations}|mutants_accepted={accepted_mutations}|"
        f"unjustified={len(escaped)}|failures={len(failures)}"
    )

    failures.extend(escaped)
    if len(instances) < args.min_instances:
        failures.append(
            f"only {len(instances)} instances were checked (floor {args.min_instances})"
        )
    if total_hypotheses < args.min_hypotheses:
        failures.append(
            f"only {total_hypotheses} hypothesis axioms were bound (floor "
            f"{args.min_hypotheses}); a run that binds nothing proves nothing"
        )
    if not args.no_self_check and caught_mutations < args.min_required_mutations:
        failures.append(
            f"only {caught_mutations} deliberate corruptions were CAUGHT (floor "
            f"{args.min_required_mutations}). A checker that never rejects anything is "
            "worse than no checker: it manufactures unfalsifiable claims at full speed"
        )

    for failure in failures:
        print(f"LRA_HYP_BINDING_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


def _rename(atom: tuple, phi: dict[str, str]) -> tuple:
    rel, terms, const = atom
    return (rel, tuple(sorted((phi.get(v, v), c) for v, c in terms)), const)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
