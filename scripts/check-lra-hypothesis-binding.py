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

Both sides are normalized to `Σ c·m + k ⋈ 0` (`m` a monomial of degree ≤ 2, so a
rendered square binds only a query square and a rendered cross term only a query
cross term) over exact rationals, denominators
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

# The denominator, measured

Advertised scope is the part people believe, so it is a measurement here, not an
estimate. Swept 2026-08-18 over all **1404** committed `.smt2` files. **270** of
them render a Lean module at all, and those 270 split into five pinned classes:

    135  BOUND               every rendered hypothesis bound back to an
                             `(assert …)` line
     32  STRUCTURAL          every rendered TERM is a subterm of the query,
                             injectively — and the query does NOT force the
                             disequality (the congruence-conclusion case)
     66  STRUCTURAL-ANCHORED both of the above at once
      7  ANCHORED            the query FORCES the disequality the module assumes,
                             uniquely — and the module is a BARE PAIR the
                             structural binder cannot grip
      9  ATTESTED            the module transcribes NOTHING; verified content-free
     20  DECLINED            none of the above — not pinned, not checked, listed
                             by name

`scripts/lra-hypothesis-binding-instances.txt` pins the 135;
`scripts/hypothesis-binding-structural-instances.txt` pins the 32;
`scripts/hypothesis-binding-structural-anchored-instances.txt` pins the 66;
`scripts/hypothesis-binding-anchored-instances.txt` pins the 7;
`scripts/hypothesis-binding-attestations.txt` pins the 9 and names the 20.

The five are a PARTITION and each pin is TWO-SIDED: an instance must pass its own
class's checks and FAIL its neighbours'. The negative half is the half that does
the work. Without it a class can only be entered deliberately and never left, so
a stronger statement that becomes true stays unrecorded and a class that stops
describing its members stays green — which is how six `QfAbv`/`QfUf` instances
sat pinned "content-free" while they were structural all along, and how 66
instances went on being recorded as merely `structural` when their queries
asserted the disequality outright. Both were found by measurement, not by a
check; both are now checks.

ANCHORED is the newest and the weakest of the three checked verdicts, and it
exists because the structural binder correctly refuses a module whose two equated
sides are both BARE constants — an injective map onto two of the query's symbols
exists for any query with two symbols, so a match there would show nothing. That
refusal left thirteen `ArrayAxiom`/`TermIdentity` instances whose entire module is

    axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
    axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)

pinned as content-free. The second axiom is the interesting one: the module
ASSUMES the query's disequality and nothing in Lean checks that the query says
so. Anchoring checks it, from the `.smt2` text, by propagating a required truth
value down each `(assert …)` — through `not`/`and`/`or`/`=>`, through `distinct`,
and through the one-bit-vector encoding a BTOR-derived file writes Booleans in
(`(= #b1 t)`, `bvand`/`bvor`/`bvnot`, `(ite c #b1 #b0)`) — and collecting the
pairs the assertions FORCE unequal. Propagation stops wherever the value is not
forced: an `or` under a true polarity, an `xor`, an n-ary `=` under a false
polarity and an `ite` without the Boolean branch pair all contribute nothing,
because each entails a disjunction rather than a fact.

The pinned requirement is that the query force EXACTLY ONE such disequality the
module's rendered sides can stand for. That uniqueness is what makes it an anchor
rather than a formality, and it bites on the same thirteen: THREE are refused and
stay attested. `solver__array__ext27.btor.smt2` forces four leaf disequalities
and a bare module does not say which; the two `unsat__replace_all__not-first-only`
files force none at all.

Anchoring is NOT confined to those thirteen, and assuming it was is what made the
class look small. Run over the whole pinned corpus it holds of 73 modules: the 7
bare pairs, plus 66 that ALSO bind structurally because their query asserts the
disequality outright rather than deriving it. Those 66 are now their own class.

What anchoring does NOT show is stated in
`scripts/hypothesis-binding-anchored-instances.txt` and repeated here because it
is the honest half: for the three `TermIdentity` rows the correspondence is
pinned by structure as well (`(ite true x y)` is a four-node term of the file),
but for the seven bare-pair `ArrayAxiom` rows it is pinned ONLY by uniqueness —
those seven modules are byte-identical, so each anchors against any of the
others' queries. It rules out a module assuming a disequality the query does not
entail, and a query that entails none or several. It does not identify which
symbols a bare `atom._0` means.
A 270th instance, `neg-no-self-negating-proposition.smt2`, renders no theory
module at all any more: its was *self-refuting* and its route now declines.
The three bound routes are `lra.hyp._N` (Real Farkas), `lra.int_hyp._N` (Int
Farkas) and `dio.hyp._N` (Int Diophantine).

# What this does NOT cover

- **The 20 declined instances.** 13 are quantified LIA/BV whose hypothesis is a
  pi-type `((x0 : Int) -> … Or/Not/Iff …)`; 7 are ground modules whose hypothesis
  is the OUTPUT of an array or BV abstraction step rather than a transcription of
  any assertion, so there is no assertion for it to bind to. An unrecognized
  `axeyum.reconstruct.*` axiom fails the run rather than being skipped, so these
  stay visible rather than silently blessed.
- **The 9 attestations transcribe nothing, and that is the finding, not a
  gap this closes.** Their correspondence to the query lives in the Rust
  certificate and is checked there. What is checked here is only that each really
  is the content-free skeleton it claims to be. A *self-refuting* module — one
  carrying `Not (Eq.{1} α t t)`, which Lean's own `rfl` refutes, so its `False`
  needs none of its other axioms and nothing at all from the query — is no longer
  counted but FAILS the run (`attested_vacuous=`). Exactly one existed; its route
  now declines instead.
- **Only the degree-≤2 fragment the Python parser admits.** `+ - * /` (division
  by a constant), `and`, `not`, `<= < >= > =`, `let`. Degree 2 is new on
  2026-08-18, for the `Sos` route, whose hypotheses are genuinely quadratic
  (`Real.mul x x`) and whose `.smt2` rows are too (`(< (+ (* x1 x1) 1.0) 0.0)`);
  a product that would exceed it raises, so its assertion contributes no atoms
  and a hypothesis claiming to come from it is unmatched and the run fails. That
  is the same fail-closed policy the old "nonlinear product" rejection had, one
  degree up — nothing became matchable by default.
- **It does not check the proof.** That is the kernel's job, and Lean's.
- **It does not check the prelude axioms** (`Real.add_comm`, …) say what their
  names claim — that is item 2 of the trust surface, and a different gate.
- **It checks a SUBSET relation, not equality.** Every rendered hypothesis must
  come from the query; the refutation is free to use fewer assertions than the
  query has, because a refutation of a subset refutes the whole. Sound, but
  weaker than it sounds — so the shortfall is now *measured* rather than left to
  the reader: `represented_assertions=296` of `spine_assertions=541`. Barely half
  the rows these refutations are handed are rendered at all. The number is
  recomputed from the accepted renaming, never from the search's own bookkeeping,
  and `--min-represented` floors it so a wholesale drop cannot pass quietly.

  Two further measurements, because "296 of 541" is worth nothing until you know
  which side of the check the missing 245 are on. **`undecomposable_spine=0`**:
  every one of the 541 rows was decomposed into atoms, so not one of the 245 is
  unrepresentable because this parser could not read it. The shortfall is a
  property of the REFUTATIONS — they rest on 296 rows and Lean derives `False`
  from those alone — and not of this script, and a nonzero count now fails the
  run rather than arriving as a lower `represented`. And the 296 is a maximum
  bipartite MATCHING, so each represented row has its own hypothesis standing
  for it; an overlap count would credit three rows entailing a common atom to a
  module that rendered it once. Measured, every one of the 298 hypotheses
  matches exactly one row, so the two agree today — which is a fact, not a
  reason to compute the cheaper one.
- **Constant-only atoms are compared up to positive scaling.** `0 = 5` and
  `0 = 1` normalize to the same atom (dividing through by the gcd), because both
  are the false proposition and the relation is preserved. So this checker cannot
  distinguish two different variable-free contradictions from one another.
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

# The instances whose modules carry NO query content at all (see "Opaque-skeleton
# attestations" below). Pinned separately and reported separately: they are the
# denominator's honest other half, not coverage.
ATTESTATION_MANIFEST = ROOT / "scripts/hypothesis-binding-attestations.txt"

# Floors. A scanner that goes blind reports a beautiful clean zero. Measured
# 2026-08-18 over the whole committed corpus, after the `Sos` route began
# reconstructing: 135 bound instances, 298 hypotheses, 1259 corruptions caught,
# 95 structural instances over 2982 matched term nodes, 19 attestations of which
# 0 are self-refuting (one was, and its route now declines), and 296 of 541
# spine assertions represented.
MIN_INSTANCES = 130
MIN_HYPOTHESES = 290
MIN_REQUIRED_MUTATIONS = 1200
# A floor on the attestation class is a floor on HONESTY, not on coverage, so it
# moves DOWN when a route stops attesting and starts reconstructing -- which is
# what happened on 2026-08-18, when the 9 `Sos` rows left this class for the
# bound manifest and took it from 28 to 19, and again the same day when 10 of
# the 13 bare-leaf rows became `anchored` and took it from 19 to 9. Lowering it
# is a reviewable act for the same reason raising it would be: it is the count of
# Lean evidence this repository publishes as transcribing nothing. It moved again
# on 2026-08-18, from 8 to 5, when the `FiniteArrayExtensionality` emitter stopped
# collapsing each `(select a i)` into one opaque constant and its 4 rows became
# structural.
MIN_ATTESTATIONS = 5
# The converse direction, measured rather than assumed: how many of the spine's
# `(assert …)` rows a rendered hypothesis actually stands for. 296 of 541 --
# barely over half. That is not a soundness hole (a refutation of a subset
# refutes the whole) but it IS the precise size of what binding does not show.
MIN_REPRESENTED = 290
# ...and 296 of 541 is a fact about the REFUTATIONS, not about this script. That
# distinction was not available to a reader until it was measured: a row this
# parser cannot decompose is unrepresentable no matter what the module renders,
# so it would arrive as a lower `represented_assertions` and read as the modules
# resting on less of the query. Measured 2026-08-18 across all 135 bound
# instances: ZERO of the 541 rows are in that state. The ceiling holds it there,
# because the alternative is a number that can shrink for two opposite reasons
# and cannot be told which.
MAX_UNDECOMPOSABLE_SPINE = 0


def _manifest(path: pathlib.Path) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    return [line.strip() for line in lines if line.strip() and not line.startswith("#")]


def manifest_instances() -> list[str]:
    return _manifest(MANIFEST)


def attestation_instances() -> list[str]:
    return _manifest(ATTESTATION_MANIFEST)

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
    "Real.mul_zero",
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

# The hypothesis routes this checker BINDS, and their carriers. Every one of
# these renders query constraints as arithmetic over module-local carriers, so a
# renaming back to the query's own symbols is a meaningful thing to demand.
ROUTES = {
    "axeyum.reconstruct.lra.hyp.": ("Real", "axeyum.reconstruct.lra.x."),
    "axeyum.reconstruct.lra.int_hyp.": ("Int", "axeyum.reconstruct.lra.int_var."),
    # The integer Diophantine route. Its hypotheses are `Eq.{1} Int` equalities
    # (and occasionally `Int.le`/`Int.lt` bounds) over `dio.x._N` carriers, with
    # coefficients rendered as repeated `Int.add` rather than multiplication.
    "axeyum.reconstruct.dio.hyp.": ("Int", "axeyum.reconstruct.dio.x."),
}
CARRIER_PREFIXES = {
    "axeyum.reconstruct.lra.x.": "Real",
    "axeyum.reconstruct.lra.int_var.": "Int",
    "axeyum.reconstruct.dio.x.": "Int",
}
QUERY_NAMESPACE = "axeyum.reconstruct."


class Unsupported(Exception):
    """A shape this checker deliberately does not model. Never silently skipped."""


# ---------------------------------------------------------------------------
# Canonical atoms
# ---------------------------------------------------------------------------
#
# An atom is `Σ c_m·m + k ⋈ 0` with `⋈ ∈ {<=, <, =}`, coefficients cleared to
# integers and divided by their gcd. Scaling by a POSITIVE rational preserves
# `≤ 0` and `< 0`, which is why the normal form is canonical for them; `= 0` is
# additionally sign-normalized, since `E = 0` and `−E = 0` are the same fact.
#
# `m` is a MONOMIAL: a sorted tuple of variable names, of total degree at most
# `MAX_DEGREE`. Degree 1 (`("x",)`) is the linear case this check started as;
# degree 2 (`("x", "x")`, `("x", "y")`) is what the SOS route renders, and the
# `.smt2` files it reconstructs contain (`(< (+ (* x1 x1) 1.0) 0.0)`). Nothing
# above degree 2 is admitted: a term that would produce one raises `Unsupported`
# and its assertion contributes no atoms, which is the same fail-closed policy
# every other unmodelled shape gets.
#
# The monomial is the unit φ renames, factor by factor, so a rendered `x·x` can
# only bind a query SQUARE and never a cross term `x·y` — see `_bind_monomial`.

# Total degree the two normalizers model. Raising it is a real extension, not a
# tuning knob: `_bind_monomial` enumerates the factor permutations of a monomial.
MAX_DEGREE = 2


def canonical(rel: str, coeffs: dict[tuple, Fraction], const: Fraction) -> tuple:
    """`(rel, ((monomial, int_coeff), …) sorted, int_const)` — the comparable form."""
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
    # `=` is deliberately NOT sign-normalized. The obvious normalization -- flip
    # the sign so the lexicographically first variable is positive -- reads the
    # VARIABLE NAMES, and the two sides of this check use different names by
    # construction, so it is not rename-invariant: `(= value (+ x_squared 1))`
    # normalizes on `value` while its rendering normalizes on `dio.x._0`, and the
    # faithful module is rejected. Measured on four Diophantine instances while
    # this route was being added. `E = 0` and `−E = 0` are reconciled instead by
    # `atoms_of` putting BOTH orientations of every equality into the pool, which
    # needs no name ordering at all.
    return (rel, tuple(sorted(ints.items())), k)


def signature(atom: tuple) -> tuple:
    """The rename-invariant part: relation, constant, and the coefficient bag.

    Each monomial contributes its DEGREE and its number of DISTINCT factors
    alongside the coefficient. Both survive any injective renaming — φ maps
    variables to variables — so this stays a sound prune, and it keeps a rendered
    square `x·x` from even being offered a cross term `x·y` of the same
    coefficient.
    """
    rel, terms, const = atom
    return (
        rel,
        const,
        tuple(sorted((len(m), len(set(m)), c) for m, c in terms)),
    )


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


def _smt_poly_mul(left: tuple, right: tuple) -> tuple:
    """The product of two `(coeffs, const)` polynomials, capped at `MAX_DEGREE`.

    Deliberately NOT shared with `_lean_poly_mul`, which does the same arithmetic
    on the rendered side. The whole point of this file is that the two
    normalizers agree only because both are right; a single shared multiply would
    make a bug in it invisible to the comparison, and the product is where a
    degree-2 transcription bug would live.
    """
    (lc, lk), (rc, rk) = left, right
    coeffs: dict[tuple, Fraction] = {}

    def add(mono: tuple, value: Fraction) -> None:
        if len(mono) > MAX_DEGREE:
            raise Unsupported(f"product of total degree {len(mono)} > {MAX_DEGREE}")
        coeffs[mono] = coeffs.get(mono, Fraction(0)) + value

    for mono, value in lc.items():
        add(mono, value * rk)
    for mono, value in rc.items():
        add(mono, value * lk)
    for lmono, lvalue in lc.items():
        for rmono, rvalue in rc.items():
            add(tuple(sorted(lmono + rmono)), lvalue * rvalue)
    return (coeffs, lk * rk)


def linear(term, env: dict[str, tuple]) -> tuple[dict[tuple, Fraction], Fraction]:
    """`(coeffs, const)` for an arithmetic term, or raise [`Unsupported`].

    `coeffs` is keyed by MONOMIAL (a sorted tuple of variable names) of total
    degree at most `MAX_DEGREE`, so this reads the degree-2 fragment the SOS route
    reconstructs as well as the linear one. The name is kept: it is still a
    normalizer to `Σ c·m + k`, and every caller treats the result the same way.
    """
    if isinstance(term, str):
        number = as_number(term)
        if number is not None:
            return ({}, number)
        if term in env:
            bound = env[term]
            if bound is OPAQUE:
                raise Unsupported(f"`let`-bound name `{term}` is not arithmetic")
            return bound
        return ({(term,): Fraction(1)}, Fraction(0))
    if not term:
        raise Unsupported("empty application")
    head = term[0]
    args = term[1:]
    if head == "+":
        coeffs: dict[tuple, Fraction] = {}
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
        # A genuine polynomial product, capped at `MAX_DEGREE`. A degree-3 factor
        # raises, so its assertion contributes no atoms and any hypothesis
        # claiming to descend from it stays unmatched — the same fail-closed
        # policy the old "nonlinear product" rejection had, one degree up.
        product: tuple = ({}, Fraction(1))
        for arg in args:
            product = _smt_poly_mul(product, linear(arg, env))
        return product
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


# A `let`-bound name whose definition is not degree-≤2 arithmetic. It must NOT
# degrade to a free variable: `(let ((a (forall …))) …)` would then contribute an
# invented symbol `a` that a rendered hypothesis could match against. Referencing
# it raises instead, so the enclosing assertion contributes no atoms.
OPAQUE = object()


def _let(term, env: dict[str, tuple]):
    """`(let ((v e) …) body)` -> `(body, extended_env)`."""
    if len(term) != 3:
        raise Unsupported("`let` arity")
    extended = dict(env)
    for binding in term[1]:
        if not isinstance(binding, list) or len(binding) != 2:
            raise Unsupported("`let` binding shape")
        try:
            extended[binding[0]] = linear(binding[1], env)
        except Unsupported:
            # A Boolean or quantified `let` body. Binding it opaquely keeps
            # `read_query` from dying on the whole FILE over one non-arithmetic
            # binding, which it did: `006-cbqi-ite.smt2` raised
            # `Unsupported: arithmetic head 'forall'` out of `read_query` and the
            # run ended in a traceback rather than a decline.
            extended[binding[0]] = OPAQUE
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
            # need, and the equality atom itself for the equality routes. BOTH
            # ORIENTATIONS of the equality go in, because `E = 0` and `−E = 0`
            # are the same fact and the renderer is free to emit either.
            flipped = {v: -c for v, c in coeffs.items()}
            out.append(canonical("<=", coeffs, const))
            out.append(canonical("<=", flipped, -const))
            out.append(canonical("=", coeffs, const))
            out.append(canonical("=", flipped, -const))
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
            try:
                assertions.append(atoms_of(form[1], True, {}))
            except Unsupported:
                # Fail-closed by omission, the same policy `atoms_of` states: an
                # assertion this parser cannot decompose contributes NO atoms, so
                # any hypothesis claiming to descend from it stays unmatched and
                # the instance fails. An exception escaping to the driver instead
                # would end the run in a traceback, which is neither a pass nor an
                # honest decline.
                assertions.append([])
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


def _lean_poly_mul(left: tuple, right: tuple) -> tuple:
    """`_smt_poly_mul`'s counterpart on the rendered side, written separately.

    See that function: the two sides of this check must not share the arithmetic
    they are being compared through. This one is reached from `Real.mul` /
    `Int.mul` spines, that one from `(* …)` s-expressions.
    """
    (lc, lk), (rc, rk) = left, right
    coeffs: dict[tuple, Fraction] = {}
    for mono, value in lc.items():
        coeffs[mono] = coeffs.get(mono, Fraction(0)) + value * rk
    for mono, value in rc.items():
        coeffs[mono] = coeffs.get(mono, Fraction(0)) + value * lk
    for lmono, lvalue in lc.items():
        for rmono, rvalue in rc.items():
            product = tuple(sorted(lmono + rmono))
            if len(product) > MAX_DEGREE:
                raise Unsupported(
                    f"rendered product of total degree {len(product)} > {MAX_DEGREE}"
                )
            coeffs[product] = coeffs.get(product, Fraction(0)) + lvalue * rvalue
    return (coeffs, lk * rk)


def lean_linear(expr, carrier: str) -> tuple[dict[tuple, Fraction], Fraction]:
    """`(coeffs, const)` for a rendered carrier expression, keyed by monomial."""
    if isinstance(expr, str):
        if expr == f"{carrier}.zero":
            return ({}, Fraction(0))
        if expr == f"{carrier}.one":
            return ({}, Fraction(1))
        if expr.startswith(QUERY_NAMESPACE):
            return ({(expr,): Fraction(1)}, Fraction(0))
        raise Unsupported(f"rendered leaf `{expr}`")
    head, args = expr[0], expr[1:]
    if not isinstance(head, str):
        raise Unsupported("rendered application with a non-constant head")
    if head == f"{carrier}.add" and len(args) == 2:
        lc, lk = lean_linear(args[0], carrier)
        rc, rk = lean_linear(args[1], carrier)
        coeffs = dict(lc)
        for mono, value in rc.items():
            coeffs[mono] = coeffs.get(mono, Fraction(0)) + value
        return (coeffs, lk + rk)
    if head == f"{carrier}.neg" and len(args) == 1:
        c, k = lean_linear(args[0], carrier)
        return ({mono: -value for mono, value in c.items()}, -k)
    if head == f"{carrier}.mul" and len(args) == 2:
        return _lean_poly_mul(
            lean_linear(args[0], carrier), lean_linear(args[1], carrier)
        )
    raise Unsupported(f"rendered head `{head}`")


# `Eq.{1} Int a b` is a FOUR-token application: the eliminator, the sort, and the
# two sides. Only this exact universe/sort pair is admitted, because `Eq.{1} α …`
# over an opaque attestation carrier says nothing about the query's arithmetic and
# must not be mistaken for an equality between query terms.
EQ_HEADS = ("Eq.{1}", "Eq")


def lean_atom(ty: str, carrier: str) -> tuple:
    """The canonical atom a rendered hypothesis type denotes."""
    expr = lean_expr(ty)
    if isinstance(expr, str):
        raise Unsupported("a hypothesis type is not a relation application")
    if len(expr) == 4 and expr[0] in EQ_HEADS:
        if expr[1] != carrier:
            raise Unsupported(
                f"`{expr[0]}` at sort `{expr[1]}`, not the route's carrier `{carrier}`"
            )
        rel, left, right = "=", expr[2], expr[3]
        lc, lk = lean_linear(left, carrier)
        rc, rk = lean_linear(right, carrier)
        coeffs = dict(lc)
        for mono, value in rc.items():
            coeffs[mono] = coeffs.get(mono, Fraction(0)) - value
        return canonical(rel, coeffs, lk - rk)
    if len(expr) != 3:
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
    for mono, value in rc.items():
        coeffs[mono] = coeffs.get(mono, Fraction(0)) - value
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
# Structural binding: the module's terms ARE the query's terms
# ---------------------------------------------------------------------------
#
# The arithmetic routes above bind a hypothesis to an `(assert …)` LINE, because
# a Farkas hypothesis IS one of the query's constraints in normalized form. The
# array/EUF routes cannot be bound that way and it would be wrong to pretend
# otherwise: their hypothesis is the *conclusion of a congruence derivation*, so
# for 89 of the 105 queries `ArrayAxiom` certifies there is no assertion saying
# `¬(lhs = rhs)` at all. Binding those to an assert line is not a check that is
# hard — it is a check with no true instance.
#
# What IS true of them, and is checked here, is one step weaker and still sharp:
#
#     every term the module equates is a SUBTERM of the `.smt2` file, under one
#     injective correspondence between the module's opaque names and the file's
#     own symbols, literals and operators.
#
# So `axeyum.reconstruct.func._2 atom._0 atom._1` must be some `(select a2 v1)`
# the file actually contains, with `func._2` standing for `select` everywhere it
# occurs and `atom._0` for `a2` everywhere it occurs. Swap two arguments, drop a
# `store`, point an atom at the wrong symbol, or reuse one Lean name for two
# query symbols, and no correspondence exists — the run fails. That is the
# difference between this and the attestation class below, whose vocabulary has
# NO declared relationship to the query and where a match therefore cannot fail.
#
# Two things this does NOT show, stated because the gap is the interesting part:
# the array-axiom instance `lhs = rhs` is still an ASSUMED hypothesis (nothing
# here proves it follows from the array axioms), and the query's entailment of
# `¬(lhs = rhs)` is re-derived in Rust, not here.

STRUCTURAL_MANIFEST = ROOT / "scripts/hypothesis-binding-structural-instances.txt"
# Floor on the structural class and on how much of it is actually matched.
# Measured 2026-08-18: 95 instances, 2982 matched term nodes. The node floor is
# the one that matters: the instance count alone cannot see a renderer that
# degraded to bare constants, because those would still be "structural" and
# would bind vacuously.
MIN_STRUCTURAL = 98
MIN_STRUCTURAL_NODES = 3300
MIN_STRUCTURAL_MUTATIONS = 370

# `let` and the quantifiers need a binder environment; everything else is a
# plain head-and-arguments tree.
_BINDERS = frozenset({"forall", "exists", "let"})


def structural_instances() -> list[str]:
    return _manifest(STRUCTURAL_MANIFEST)


def _smt_term(form, env: dict) -> object:
    """One `.smt2` term as a `str` leaf or a `(head, arg, …)` tuple.

    `let` is expanded. A quantifier is NOT descended into: it is returned as an
    opaque leaf that no rendered term can match, which is fail-closed — a module
    claiming to transcribe a quantified subterm stays unmatched and its instance
    fails, rather than matching a shape this reader guessed at.
    """
    if isinstance(form, str):
        return env.get(form, form)
    if not form:
        raise Unsupported("empty s-expression")
    head = form[0]
    if head == "let" and len(form) == 3:
        extended = dict(env)
        for binding in form[1]:
            if not isinstance(binding, list) or len(binding) != 2:
                raise Unsupported("`let` binding shape")
            extended[binding[0]] = _smt_term(binding[1], env)
        return _smt_term(form[2], extended)
    if isinstance(head, str) and head in _BINDERS:
        return ("!quantified",)
    if head == "_":
        # `(_ bv13 16)` is an indexed IDENTIFIER -- a literal -- not an
        # application of a function `_`. Reading it as a 3-argument application
        # made every module mentioning one unmatchable, a false negative that
        # pushes a transcribing module into the attestation class: exactly the
        # direction that must not fail silently.
        return " ".join(t for t in form if isinstance(t, str))
    if isinstance(head, list):
        # An indexed OPERATOR, `((_ extract 7 0) x)`. Flatten it into one head
        # token: the indices are part of which operator this is.
        head = " ".join(t for t in head if isinstance(t, str))
    if len(form) == 1:
        return head
    return (head, *(_smt_term(arg, env) for arg in form[1:]))


def query_subterms(path: pathlib.Path) -> dict[tuple[int, int], list]:
    """Every subterm of every `(assert …)`, bucketed by `(node count, arity)`.

    Bucketing is a pure search prune: a rendered term can only match a subterm
    with the same tree size and the same top arity.
    """
    forms = sexprs(path.read_text(encoding="utf-8"))
    buckets: dict[tuple[int, int], list] = {}
    seen: set = set()

    def visit(term) -> int:
        if term in seen:
            return _nodes(term)
        seen.add(term)
        if isinstance(term, str):
            count = 1
        else:
            count = 1 + sum(visit(arg) for arg in term[1:])
        buckets.setdefault((count, _arity(term)), []).append(term)
        return count

    for form in forms:
        if isinstance(form, list) and len(form) == 2 and form[0] == "assert":
            try:
                visit(_smt_term(form[1], {}))
            except Unsupported:
                continue
    return buckets


def _nodes(term) -> int:
    if isinstance(term, str):
        return 1
    return 1 + sum(_nodes(arg) for arg in term[1:])


def _arity(term) -> int:
    return 0 if isinstance(term, str) else len(term) - 1


def _lean_nodes(term) -> int:
    if isinstance(term, str):
        return 1
    return 1 + sum(_lean_nodes(arg) for arg in term[1:])


def _lean_arity(term) -> int:
    return 0 if isinstance(term, str) else len(term) - 1


def _bind_name(phi: dict[str, str], lean: str, smt: str) -> dict[str, str] | None:
    """Extend `phi` with `lean -> smt`, keeping it a function and injective."""
    if lean in phi:
        return phi if phi[lean] == smt else None
    if smt in phi.values():
        return None
    out = dict(phi)
    out[lean] = smt
    return out


def _match(lean, smt, phi: dict[str, str]) -> dict[str, str] | None:
    """Extend `phi` so the rendered `lean` term transcribes the query's `smt`."""
    if isinstance(lean, str):
        return _bind_name(phi, lean, smt) if isinstance(smt, str) else None
    if not lean or not isinstance(lean[0], str):
        return None
    if isinstance(smt, str) or len(smt) - 1 != len(lean) - 1:
        return None
    phi = _bind_name(phi, lean[0], smt[0])
    if phi is None:
        return None
    for lean_arg, smt_arg in zip(lean[1:], smt[1:]):
        phi = _match(lean_arg, smt_arg, phi)
        if phi is None:
            return None
    return phi


def _eq_nodes(expr) -> list | None:
    """Every `Eq.{1} α L R` in a type built from `Not`, `And` and `Eq`.

    `None` if the type uses anything else — fail-closed, and deliberately a
    CLOSED grammar: widening it is how the structural verdict would come to
    cover shapes whose rendered terms nobody checked. `Or` and `Iff` are absent
    on purpose. A negated conjunction is not a fact about either conjunct, but
    that does not matter here: this walker is only used to collect the TERMS the
    module names, and every one of them still has to be a subterm of the query.
    What the module *asserts* about them is the anchor's question, not this one.

    The shape that motivated it is `FiniteArrayExtensionality`, whose refutation
    is `¬(r₁ ∧ … ∧ rₙ)` against the reads `r₁ … rₙ` — n equalities under one
    negated conjunction rather than one equality and its negation.
    """
    out: list = []

    def walk(node) -> bool:
        if isinstance(node, str):
            return False
        head = node[0]
        if head == "Not" and len(node) == 2:
            return walk(node[1])
        if head == "And" and len(node) == 3:
            return walk(node[1]) and walk(node[2])
        if head in EQ_HEADS and len(node) == 4:
            out.append(node)
            return True
        return False

    return out if walk(expr) else None


def _equated_terms(ty: str) -> list | None:
    """Every term a rendered hypothesis equates, across the whole `Not`/`And` tree."""
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return None
    nodes = _eq_nodes(expr)
    if not nodes:
        return None
    return [side for node in nodes for side in (node[2], node[3])]


def _equated_sides(ty: str) -> tuple[object, object] | None:
    """The two sides of `Eq.{1} α L R` (optionally under `Not`), as trees.

    Deliberately NOT `_equated_terms`: anchoring covers a module that states one
    equality and its negation, and must keep refusing anything else. A module
    equating several pairs cannot say which disequality a query is supposed to
    force.
    """
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return None
    if isinstance(expr, list) and len(expr) == 2 and expr[0] == "Not":
        expr = expr[1]
    if isinstance(expr, str) or len(expr) != 4 or expr[0] not in EQ_HEADS:
        return None
    return (expr[2], expr[3])


def _lean_leaf_names(term) -> frozenset[str]:
    """Every opaque name a rendered term mentions, head constants included."""
    if isinstance(term, str):
        return frozenset({term})
    out: set[str] = set()
    if isinstance(term[0], str):
        out.add(term[0])
    for arg in term[1:]:
        out |= _lean_leaf_names(arg)
    return frozenset(out)


def bind_structural(
    source: str, path: pathlib.Path, budget: int = 200_000
) -> tuple[bool, str, int]:
    """`(bound, why not, matched term nodes)` for a rendered module.

    Shares no code with the arithmetic binder and none with the attestation
    classifier: this decides that a module DOES transcribe the query, and it
    must not be able to reach that verdict through machinery whose job is to
    decide something else.
    """
    sides: list[object] = []
    declared: set[str] = set()
    for line in source.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if not match:
            continue
        name, ty = match.group(1), match.group(2).strip()
        if ty.count("(") != ty.count(")"):
            return (False, f"{name}: the rendered type is not balanced on one line", 0)
        if not name.startswith(QUERY_NAMESPACE):
            if (name, ty) != ATTESTATION_SORT_AXIOM:
                return (False, f"`{name} : {ty}` is not the opaque sort `α : Sort (1)`", 0)
            continue
        if name.startswith(ATTESTATION_HYP_PREFIXES):
            terms = _equated_terms(ty)
            if terms is None:
                return (
                    False,
                    f"{name} is not built from `Not`, `And` and equalities between "
                    "rendered terms",
                    0,
                )
            sides.extend(terms)
            continue
        declared.add(name)
    if not sides:
        return (False, "the module states no equality between rendered terms", 0)
    if not any(isinstance(side, list) for side in sides):
        # Both sides of every equality are bare opaque constants. An injective
        # map onto two of the query's symbols exists for ANY query with two
        # symbols, so a match here would show nothing: this is the attestation
        # class, not this one.
        return (False, "every rendered term is a bare opaque constant, so it carries no structure", 0)

    buckets = query_subterms(path)
    names = [_lean_leaf_names(side) for side in sides]
    state = {"nodes": 0, "exhausted": False}

    def extend(remaining: frozenset[int], phi: dict[str, str]) -> dict[str, str] | None:
        if not remaining:
            return phi
        # The MOST CONSTRAINED side next, recomputed at every step: the one
        # sharing the most already-bound names, breaking ties on the smaller
        # candidate bucket. A static largest-first order was enough while every
        # module equated one or two terms; `FiniteArrayExtensionality` equates
        # sixteen terms of identical size over a query holding sixteen identical
        # shapes, and the static order let the search bind them in an arbitrary
        # sequence and backtrack over the whole space. This is a search ORDER,
        # not a soundness property -- every side still has to match.
        def constraint(i: int) -> tuple:
            side = sides[i]
            key = (_lean_nodes(side), _lean_arity(side))
            return (-len(names[i] & phi.keys()), len(buckets.get(key, ())))

        index = min(remaining, key=constraint)
        side = sides[index]
        key = (_lean_nodes(side), _lean_arity(side))
        rest = remaining - {index}
        for candidate in buckets.get(key, ()):
            state["nodes"] += 1
            if state["nodes"] > budget:
                state["exhausted"] = True
                return None
            next_phi = _match(side, candidate, phi)
            if next_phi is None:
                continue
            found = extend(rest, next_phi)
            if found is not None:
                return found
            if state["exhausted"]:
                return None
        return None

    phi = extend(frozenset(range(len(sides))), {})
    if state["exhausted"]:
        # A search that gave up must never read as a pass, and must not read as a
        # refutation either: it is this checker failing to decide, so say so.
        return (False, f"structural search exhausted its {budget}-node budget", 0)
    if phi is None:
        return (
            False,
            "no injective correspondence makes the module's rendered terms subterms "
            "of this query -- so the module states something the file does not contain",
            0,
        )
    for name in declared:
        if name not in phi:
            return (
                False,
                f"{name} is declared but no rendered term binds it, so the module "
                "carries a constant with no query counterpart",
                0,
            )
    return (True, "", sum(_lean_nodes(side) for side in sides))


# ---------------------------------------------------------------------------
# Assertion anchoring: the query ENTAILS the disequality the module assumes
# ---------------------------------------------------------------------------
#
# The structural binder above refuses a module whose two equated sides are both
# bare opaque constants, and it is right to: an injective map onto two of the
# query's symbols exists for any query with two symbols, so a match would show
# nothing. That refusal left 13 instances (10 `ArrayAxiom`, 3 `TermIdentity`)
# pinned as content-free attestations, whose modules are all literally
#
#     axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
#     axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)
#
# -- one assumed array-axiom/identity conclusion and one assumed disequality.
# What is NOT checked anywhere in Lean is that the second one is the query's:
# the module simply assumes it.
#
# Anchoring checks exactly that, from the `.smt2` TEXT, and it is a different
# question from the structural one. Not "is this term in the file" but:
#
#     do the query's own assertions FORCE `lhs = rhs` to be false --
#     and is that the ONLY disequality they force which this module's
#     rendered sides could stand for?
#
# `forced_disequalities` answers the first half by propagating a required truth
# value down each `(assert …)`, through the Boolean connectives and through the
# one-bit-vector encoding BTOR-derived files use for them (`(= #b1 t)`,
# `bvand`/`bvor`/`bvnot`, `(ite c #b1 #b0)`). It propagates only where the value
# is forced -- an `or` under a true polarity, an `ite` with a non-Boolean pair of
# branches, an `xor`, an n-ary `=` under a false polarity all contribute nothing.
# Fail-closed: a shape it does not model yields no forced disequality, so a
# module claiming to descend from one stays unanchored and its instance fails.
#
# The UNIQUENESS half is what makes this a check rather than a formality, and it
# is where the honest limit sits. For a module whose sides carry structure (the
# `TermIdentity` route renders `x` against `(ite true x y)`) the correspondence
# is pinned by that structure, and a corrupted module names a term the file does
# not contain. For a module whose sides are BARE constants, the correspondence is
# pinned only by there being exactly one candidate: two different queries that
# each force exactly one leaf disequality accept each other's module, because the
# two modules are byte-identical. What anchoring rules out, and what `attested`
# did not, is a module assuming a disequality the query does NOT entail, and a
# query that entails none, or several.
#
# That the requirement bites is not a claim -- it is measured on the same 13:
# three of them are refused and stay attested. `solver__array__ext27.btor.smt2`
# forces FOUR leaf disequalities (`i0≠i1`, `v5≠v6`, `i0≠i2`, `i1≠i2`) and the
# bare module does not say which; the two `unsat__replace_all__not-first-only`
# files force NONE, because their single assertion is a forced-TRUE equality
# whose sides the arena constant-folded (the rewrite residue, as for `ext10`).

ANCHORED_MANIFEST = ROOT / "scripts/hypothesis-binding-anchored-instances.txt"
# Measured 2026-08-18: 73 instances, 1098 rendered term nodes, 269 corruptions
# caught -- counting the 66 that ALSO bind structurally, because they genuinely
# do anchor and a floor that excluded them would under-report what is checked.
# It was 10/29/26 earlier the same day, before the two manifests were allowed to
# overlap; the jump is a change in what is RECORDED, not in what holds.
# The node floor is what sees a renderer degrading a structured side back to a
# bare constant: those would still anchor (a bare pair is the weakest thing that
# can), and would anchor on uniqueness alone.
MIN_ANCHORED = 70
MIN_ANCHORED_NODES = 1050
MIN_ANCHORED_MUTATIONS = 250

# The Boolean values a one-bit vector stands for in the BTOR-derived encoding,
# and the `Bool` literals. Deliberately narrow: `#b1` is a Boolean only because
# the surrounding `(= #b1 t)` / `(ite c #b1 #b0)` idiom makes it one, and a wider
# literal (`#b1111`) is not admitted at all, so propagation can never leave the
# one-bit fragment where `bvand`/`bvor`/`bvnot` ARE conjunction/disjunction/
# negation.
_BIT_TRUE = frozenset({"#b1", "true"})
_BIT_FALSE = frozenset({"#b0", "false"})

# Heads that are conjunction/disjunction/negation, at whichever of the two sorts.
_NOT_HEADS = frozenset({"not", "bvnot"})
_AND_HEADS = frozenset({"and", "bvand"})
_OR_HEADS = frozenset({"or", "bvor"})


def anchored_instances() -> list[str]:
    return _manifest(ANCHORED_MANIFEST)


# ---------------------------------------------------------------------------
# Both at once: the query contains the module's terms AND forces its disequality
# ---------------------------------------------------------------------------
#
# `structural` and `anchored` answer different questions, and for most of the
# corpus the answer to both is yes. Measured 2026-08-18: 63 of the 95 rows then
# pinned `structural` ALSO anchor, and 3 of the 10 rows then pinned `anchored`
# also bind structurally. Recording only one verdict for those 66 threw away a
# strictly stronger statement that was already true of them.
#
# So the four verdicts are now a PARTITION, and each is falsifiable in BOTH
# directions:
#
#     structural           binds structurally, and does NOT anchor
#     structural-anchored  does BOTH
#     anchored             anchors, and does NOT bind structurally
#     attested             does NEITHER
#
# The negative half of each is the anti-absorption guard, and it is the half
# that does the work. Without it a class can only be entered deliberately and
# never left, so a renderer that degraded a dual instance to a bare pair would
# leave it green in the class it was pinned to while the words describing that
# class quietly stopped being true. That is exactly the failure the `attested`
# guard was added for, one class over: six `QfAbv`/`QfUf` instances sat pinned
# content-free while they were structural all along.
#
# It cuts the other way too. A row pinned `structural` that STARTS anchoring
# fails the run and must be moved here — the gate refuses to keep recording the
# weaker of two true statements once the stronger one holds.
#
# The counters do not partition: an instance here is counted in `structural`
# AND in `anchored`, because it genuinely is both, and the floors on those two
# numbers therefore keep meaning what they meant. `structural_anchored` is
# reported separately so the overlap itself is a measured number.
STRUCTURAL_ANCHORED_MANIFEST = ROOT / "scripts/hypothesis-binding-structural-anchored-instances.txt"
# Measured 2026-08-18: 66 instances, 2168 structurally matched term nodes and
# 1084 anchored ones. The dual class is the LARGEST of the four, which is the
# finding: for two thirds of the array/EUF corpus the query both contains the
# module's terms and forces the disequality it assumes.
MIN_STRUCTURAL_ANCHORED = 60


def structural_anchored_instances() -> list[str]:
    return _manifest(STRUCTURAL_ANCHORED_MANIFEST)


def _bit_value(term) -> bool | None:
    """`True`/`False` if `term` is a Boolean literal in either sort, else `None`."""
    if not isinstance(term, str):
        return None
    if term in _BIT_TRUE:
        return True
    if term in _BIT_FALSE:
        return False
    return None


def forced_disequalities(path: pathlib.Path) -> list[tuple[object, object]]:
    """Every pair `(L, R)` this query's assertions force to be UNEQUAL.

    Shares no code with `bind_structural`'s matcher and none with the arithmetic
    binder: this decides what the FILE entails, and it must not be able to reach
    that verdict through machinery whose job is to read the module.

    Polarity is propagated only where it is forced. `or` under a true polarity,
    `and` under a false one, `xor`, an `ite` whose branches are not the Boolean
    pair, and an n-ary `=` under a false polarity all stop the walk -- each of
    them entails a disjunction, not a fact, and treating one as a fact is exactly
    the transcription bug this file exists to catch.
    """
    forms = sexprs(path.read_text(encoding="utf-8"))
    stack: list[tuple[object, bool]] = []
    for form in forms:
        if isinstance(form, list) and len(form) == 2 and form[0] == "assert":
            try:
                stack.append((_smt_term(form[1], {}), True))
            except Unsupported:
                continue

    found: list[tuple[object, object]] = []
    keys: set = set()
    seen: set = set()

    def record(left, right) -> None:
        key = (left, right) if repr(left) <= repr(right) else (right, left)
        if key in keys:
            return
        keys.add(key)
        found.append((left, right))

    while stack:
        term, value = stack.pop()
        if (term, value) in seen:
            continue
        seen.add((term, value))
        if isinstance(term, str):
            continue
        head, args = term[0], term[1:]
        if head in _NOT_HEADS and len(args) == 1:
            stack.append((args[0], not value))
        elif head in _AND_HEADS and value:
            stack.extend((arg, True) for arg in args)
        elif head in _OR_HEADS and not value:
            stack.extend((arg, False) for arg in args)
        elif head == "=>" and not value and len(args) == 2:
            stack.append((args[0], True))
            stack.append((args[1], False))
        elif head == "ite" and len(args) == 3:
            then_bit, else_bit = _bit_value(args[1]), _bit_value(args[2])
            if then_bit is True and else_bit is False:
                stack.append((args[0], value))
            elif then_bit is False and else_bit is True:
                stack.append((args[0], not value))
        elif head == "distinct" and value:
            # `(distinct a b c)` is PAIRWISE distinct, so every pair is forced.
            for i, left in enumerate(args):
                for right in args[i + 1 :]:
                    record(left, right)
        elif head == "=" and len(args) == 2:
            if not value:
                record(args[0], args[1])
                continue
            # `(= #b1 t)` is how a BTOR-derived file asserts the Boolean `t`.
            # The literal side fixes the other side's value; two literals fix
            # nothing, and neither does a wider constant.
            left_bit, right_bit = _bit_value(args[0]), _bit_value(args[1])
            if left_bit is not None and right_bit is None:
                stack.append((args[1], left_bit))
            elif right_bit is not None and left_bit is None:
                stack.append((args[0], right_bit))
    return found


def _is_negated_equality(ty: str) -> bool:
    """Is the rendered type `Not (Eq.{1} α L R)` rather than the bare equality?"""
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return False
    return isinstance(expr, list) and len(expr) == 2 and expr[0] == "Not"


def bind_anchored(source: str, path: pathlib.Path) -> tuple[bool, str, int]:
    """`(anchored, why not, matched term nodes)` for a rendered module.

    The module must state ONE equality and its negation over the same two
    rendered terms -- the shape both routes emit -- and the query must force
    exactly one disequality those two terms can stand for.
    """
    sides: tuple[object, object] | None = None
    declared: set[str] = set()
    disequality = False
    for line in source.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if not match:
            continue
        name, ty = match.group(1), match.group(2).strip()
        if ty.count("(") != ty.count(")"):
            return (False, f"{name}: the rendered type is not balanced on one line", 0)
        if not name.startswith(QUERY_NAMESPACE):
            if (name, ty) != ATTESTATION_SORT_AXIOM:
                return (
                    False,
                    f"`{name} : {ty}` is not the opaque sort `α : Sort (1)`",
                    0,
                )
            continue
        if name.startswith(ATTESTATION_HYP_PREFIXES):
            pair = _equated_sides(ty)
            if pair is None:
                return (False, f"{name} is not an equality between two rendered terms", 0)
            if sides is None:
                sides = pair
            elif pair != sides:
                return (
                    False,
                    f"{name} equates a different pair of terms than the module's other "
                    "hypotheses; anchoring covers a module that states ONE equality and "
                    "its negation, and cannot say which of several a query entails",
                    0,
                )
            disequality = disequality or _is_negated_equality(ty)
            continue
        declared.add(name)
    if sides is None:
        return (False, "the module states no equality between rendered terms", 0)
    if not disequality:
        return (
            False,
            "the module assumes no DISEQUALITY, so there is nothing here for the "
            "query to have to entail",
            0,
        )

    forced = forced_disequalities(path)
    matches: list[dict[str, str]] = []
    for left, right in forced:
        for candidate in ((left, right), (right, left)):
            phi = _match(sides[0], candidate[0], {})
            if phi is None:
                continue
            phi = _match(sides[1], candidate[1], phi)
            if phi is None:
                continue
            matches.append(phi)
            # One orientation is enough: `=` is symmetric, so the two readings of
            # the SAME query pair are one candidate, not two.
            break
    if not matches:
        return (
            False,
            f"this query's assertions force {len(forced)} disequalities and the "
            "module's rendered sides stand for none of them, so the disequality it "
            "assumes is not one the file entails",
            0,
        )
    if len(matches) > 1:
        return (
            False,
            f"this query forces {len(matches)} different disequalities that the "
            "module's rendered sides could stand for, so WHICH one the module assumes "
            "is not determined by anything -- an anchor that picks one of several is "
            "not an anchor",
            0,
        )
    phi = matches[0]
    for name in declared:
        if name not in phi:
            return (
                False,
                f"{name} is declared but no rendered term binds it, so the module "
                "carries a constant with no query counterpart",
                0,
            )
    return (True, "", _lean_nodes(sides[0]) + _lean_nodes(sides[1]))


# ---------------------------------------------------------------------------
# Opaque-skeleton attestations
# ---------------------------------------------------------------------------
#
# Not every rendered module transcribes anything. Measured 2026-08-18 over the
# 1404 committed `.smt2` files: of the 270 that render a Lean module at all, 124
# render one whose ENTIRE vocabulary is
#
#     α  atom._N  prop._N  func._N  Eq.{1}  Not  And
#
# and nothing else -- no numeral, no `Int.*`/`Real.*` constructor, no carrier of
# any bound route. That is the `ArrayAxiom`, `QfAbv`, `Sos` and friends shape:
#
#     axiom α : Sort (1)
#     axiom axeyum.reconstruct.atom._0 : α
#     axiom axeyum.reconstruct.atom._1 : α
#     axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
#     axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)
#
# Lean checks that `False` follows. It does, and it would follow just as well if
# the query said something else entirely: the module's trusted base is a FRESH
# vocabulary with no declared relationship to any symbol in the `.smt2` file.
# There is no transcription here to bind, so binding these would be a check that
# cannot fail -- worse than an honest decline.
#
# What IS checkable, and is checked, is that the module really is that shape:
# a single smuggled `Int.one`, an undeclared opaque name, a truncated type, or
# any extra axiom takes it out of the class. So the classification cannot quietly
# absorb a content-bearing module, and the run reports `attested` SEPARATELY from
# `bound` -- these instances are counted as unverified transcription, in public.

# The opaque declarations an attestation may make, and the exact type each must
# have. `func._N` is checked structurally instead (a function over `α`).
ATTESTATION_DECL_TYPES = {
    "axeyum.reconstruct.atom.": "α",
    "axeyum.reconstruct.prop.": "Prop",
}
ATTESTATION_FUNC_PREFIX = "axeyum.reconstruct.func."
ATTESTATION_HYP_PREFIXES = ("axeyum.reconstruct.hyp.", "axeyum.reconstruct.em.")
# The logical vocabulary an attestation hypothesis may use. Deliberately tiny and
# deliberately CLOSED: adding to it is how this class would silently grow to
# cover modules that do carry content.
ATTESTATION_CONNECTIVES = frozenset(
    {"Eq.{1}", "Eq", "Not", "And", "Or", "Iff", "α", "Prop"}
)
ATTESTATION_SORT_AXIOM = ("α", "Sort (1)")


def classify_attestation(source: str) -> tuple[bool, str, int]:
    """`(is_attestation, why not, vacuous hypothesis count)` for a rendered module.

    Shares nothing with the binding path on purpose: this decides that a module
    says NOTHING about the query, and it must not be able to reach that verdict
    by reusing the machinery that decides what a module says.
    """
    decls: set[str] = set()
    hypotheses: list[tuple[str, str]] = []
    for line in source.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if not match:
            continue
        name, ty = match.group(1), match.group(2).strip()
        if ty.count("(") != ty.count(")"):
            # A type that spilled onto the next line. `AXIOM_LINE` reads one line,
            # so what we hold is a PREFIX -- and a prefix of a content-bearing type
            # can easily look like a skeleton. Refuse rather than classify.
            return (False, f"{name}: the rendered type is not balanced on one line", 0)
        if not name.startswith(QUERY_NAMESPACE):
            if (name, ty) != ATTESTATION_SORT_AXIOM:
                return (
                    False,
                    f"`{name} : {ty}` is not the opaque sort `α : Sort (1)`, so this "
                    "module carries a trusted base beyond the skeleton",
                    0,
                )
            continue
        declared = next(
            (want for prefix, want in ATTESTATION_DECL_TYPES.items() if name.startswith(prefix)),
            None,
        )
        if declared is not None:
            if ty != declared:
                return (False, f"{name} declares `{ty}`, not the opaque `{declared}`", 0)
            decls.add(name)
            continue
        if name.startswith(ATTESTATION_FUNC_PREFIX):
            if not _is_opaque_function_type(ty):
                return (False, f"{name} is not a function over the opaque sort: `{ty}`", 0)
            decls.add(name)
            continue
        if name.startswith(ATTESTATION_HYP_PREFIXES):
            hypotheses.append((name, ty))
            continue
        return (False, f"{name} is a query-derived axiom outside the skeleton grammar", 0)

    if not hypotheses:
        return (False, "the module declares no hypothesis axiom at all", 0)
    allowed = decls | ATTESTATION_CONNECTIVES
    for name, ty in hypotheses:
        for token in ty.replace("(", " ").replace(")", " ").split():
            if token not in allowed:
                return (
                    False,
                    f"{name} mentions `{token}`, which is neither an opaque constant "
                    "this module declared nor a logical connective -- so the module "
                    "does carry content and must be BOUND, not attested",
                    0,
                )
    return (True, "", sum(1 for _n, ty in hypotheses if _is_self_refuting(ty)))


def _is_opaque_function_type(ty: str) -> bool:
    """`((x0 : α) -> ((x1 : α) -> α))` and its arities: α → … → α, nothing else."""
    tokens = set(ty.replace("(", " ").replace(")", " ").split())
    if not tokens <= {"α", ":", "->"} | {f"x{i}" for i in range(64)}:
        return False
    return "α" in tokens and "->" in tokens


def _is_self_refuting(ty: str) -> bool:
    """`Not (Eq.{1} α t t)` — an axiom Lean's own `rfl` refutes on its own.

    Such a module needs none of its other axioms: `False` follows from this one
    alone, so even the propositional step it appears to take is not taken.
    """
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return False
    if isinstance(expr, str) or len(expr) != 2 or expr[0] != "Not":
        return False
    inner = expr[1]
    if isinstance(inner, str) or len(inner) != 4 or inner[0] not in EQ_HEADS:
        return False
    return inner[2] == inner[3]


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
        unbound = sorted({f for mono, _ in terms for f in mono if f not in phi})
        if unbound:
            problems.append(f"{name} mentions {unbound}, which φ does not bind")
            continue
        if _rename(atom, phi) not in allowed:
            problems.append(
                f"{name} renames to {_rename(atom, phi)!r}, which no assertion of the "
                "query entails"
            )
    return problems


def represented_assertions(
    phi: dict[str, str],
    hypotheses: list[tuple[str, str, tuple]],
    indices: list[int],
    assertions: list[list[tuple]],
) -> tuple[int, int, int]:
    """`(spine rows, rows a DISTINCT hypothesis stands for, rows with no atoms)`.

    The CONVERSE of what `bind` establishes, and the honest measure of its limit.
    Binding shows every rendered hypothesis comes FROM the query; it says nothing
    about the query's rows that were never rendered. That direction is not a
    soundness hole -- a refutation of a subset refutes the whole -- but it does
    mean "the module is a faithful rendering of the query" is a stronger claim
    than the binding supports, so the shortfall is counted and printed instead of
    being left to the reader's imagination.

    Two things make the count mean what it says, and neither is free:

    **It is a maximum MATCHING, not an overlap.** Counting a row as represented
    whenever *some* renamed hypothesis appears in it lets ONE hypothesis stand
    for several rows at once — three assertions entailing a common atom would all
    be credited to a module that rendered that atom once. The measured shortfall
    would then be smaller than the truth, in the direction nobody checks. So each
    represented row must be assigned its OWN hypothesis, and the number reported
    is the largest such assignment. Measured 2026-08-18: every one of the 298
    hypotheses matches exactly one spine row, so matching and overlap coincide at
    296 today. Computing it as a matching is what keeps them from diverging
    silently later.

    **Rows this parser could not decompose are counted separately.** An assertion
    that yields no atoms cannot be represented no matter what the module renders,
    so folding it into the shortfall would blame the refutation for a blind spot
    in the checker. Measured 2026-08-18: ZERO of the 541 spine rows across all
    135 bound instances are in that state — this parser understands every
    assertion these reconstructions were handed, so 296/541 is a property of the
    refutations and not of this script. The driver treats any nonzero count as a
    failure rather than as a quietly lower `represented`.

    Recomputed from `phi` alone. The search's own `origins` are not consulted:
    an untrusted search must not be the source of the number that describes it.
    """
    renamed = [_rename(atom, phi) for _name, _carrier, atom in hypotheses]
    spine = [index for index in indices if index < len(assertions)]
    undecomposable = sum(1 for index in spine if not assertions[index])
    # Bipartite adjacency: which spine rows each hypothesis could stand for.
    adjacency = [
        [index for index in spine if atom in assertions[index]] for atom in renamed
    ]
    owner: dict[int, int] = {}

    def assign(hypothesis: int, seen: set[int]) -> bool:
        for index in adjacency[hypothesis]:
            if index in seen:
                continue
            seen.add(index)
            if index not in owner or assign(owner[index], seen):
                owner[index] = hypothesis
                return True
        return False

    for hypothesis in range(len(renamed)):
        assign(hypothesis, set())
    return (len(indices), len(owner), undecomposable)


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


def _bind_monomial(
    mono: tuple,
    cand: tuple,
    phi: dict[str, str],
    used: frozenset[str],
    carriers: dict[str, str],
    sorts: dict[str, str],
):
    """Yield every extension of `phi` sending the monomial `mono` onto `cand`.

    Factor by factor, over every pairing of the candidate's factors — φ is not
    order-preserving, so `(a, b)` may have to land on `(y, x)`.

    The two properties that make the degree-2 case a real check rather than a
    looser one both fall out of doing it this way, and are asserted by the
    control tests:

    - a rendered SQUARE can only bind a query square. `(a, a)` onto `(x, y)`
      binds `a -> x` and then finds `a` already bound to something other than
      `y`; both pairings fail.
    - a rendered CROSS term can only bind a query cross term. `(a, b)` onto
      `(x, x)` binds `a -> x`, and `b -> x` is refused by injectivity — which is
      the same rule that stops two carriers collapsing onto one symbol anywhere
      else, not a special case bolted on here.
    """
    if len(mono) != len(cand):
        return
    if len(mono) == 1:
        pairings = [(0,)]
    elif len(mono) == 2:
        pairings = [(0, 1), (1, 0)]
    else:
        # `MAX_DEGREE` is 2. A higher degree would need a permutation generator,
        # and silently matching nothing here would read as "no binding exists"
        # rather than "this checker does not model that", so refuse loudly.
        raise Unsupported(f"monomial of degree {len(mono)} > {MAX_DEGREE}")
    for pairing in pairings:
        next_phi, next_used, ok = phi, used, True
        for position, index in enumerate(pairing):
            factor, target = mono[position], cand[index]
            bound = next_phi.get(factor)
            if bound is not None:
                if bound != target:
                    ok = False
                    break
                continue
            if target in next_used:
                ok = False
                break
            if not sort_compatible(carriers.get(factor), sorts.get(target)):
                ok = False
                break
            next_phi = {**next_phi, factor: target}
            next_used = next_used | {target}
        if ok:
            yield next_phi, next_used


def _matchings(
    terms: tuple[tuple[tuple, int], ...],
    cand_terms: tuple[tuple[tuple, int], ...],
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
    mono, coeff = terms[0]
    for i, (cand_mono, cand_coeff) in enumerate(cand_terms):
        if cand_coeff != coeff:
            continue
        for next_phi, next_used in _bind_monomial(
            mono, cand_mono, phi, used, carriers, sorts
        ):
            yield from _matchings(
                terms[1:],
                cand_terms[:i] + cand_terms[i + 1 :],
                next_phi,
                next_used,
                carriers,
                sorts,
            )


# ---------------------------------------------------------------------------
# Mutations — the proof that this checker can fail
# ---------------------------------------------------------------------------

MUTATIONS = (
    "flip-relation",
    "drop-negation",
    "swap-arguments",
    "shift-constant",
    "drop-term",
    "duplicate-term",
)


def mutate(ty: str, carrier: str, kind: str) -> str | None:
    """Corrupt one rendered hypothesis type the way a renderer bug would."""
    if kind == "flip-relation":
        if ty.startswith(f"{carrier}.le "):
            return f"{carrier}.lt " + ty[len(f"{carrier}.le "):]
        if ty.startswith(f"{carrier}.lt "):
            return f"{carrier}.le " + ty[len(f"{carrier}.lt "):]
        # An equality weakened to a STRICT bound: `a = b` rendered `a < b`. The
        # non-strict weakening `a <= b` would be a faithful consequence and so a
        # correct accept, which is exactly why the strict one is the corruption
        # worth injecting -- `a = b` does not entail it.
        eq = _eq_sides(ty, carrier)
        if eq is not None:
            return f"{carrier}.lt {eq[0]} {eq[1]}"
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
        if isinstance(expr, str):
            return None
        if len(expr) == 4 and expr[0] in EQ_HEADS:
            return f"{expr[0]} {_render(expr[1])} {_render(expr[3])} {_render(expr[2])}"
        if len(expr) != 3:
            return None
        return f"{expr[0]} {_render(expr[2])} {_render(expr[1])}"
    if kind == "shift-constant":
        needle = f"{carrier}.zero"
        at = ty.rfind(needle)
        if at >= 0:
            return (
                ty[:at]
                + f"({carrier}.add {carrier}.one {carrier}.zero)"
                + ty[at + len(needle) :]
            )
        # No `.zero` to grow. The Diophantine route renders bare numerals as
        # repeated `.one`, so shifting one of THOSE is the same off-by-one bug:
        # `x = 4` becomes `x = 5`.
        needle = f"{carrier}.one"
        at = ty.rfind(needle)
        if at < 0:
            return None
        return (
            ty[:at]
            + f"({carrier}.add {carrier}.one {carrier}.one)"
            + ty[at + len(needle) :]
        )
    if kind == "duplicate-term":
        # `(C.add A B)` -> `(C.add A (C.add A B))`: one summand counted twice.
        # The Diophantine route renders a coefficient AS repetition, so this is
        # precisely an off-by-one coefficient there -- `4x` rendered as `5x`.
        needle = f"({carrier}.add "
        at = ty.find(needle)
        if at < 0:
            return None
        body = _balanced_body(ty, at, len(needle))
        if body is None:
            return None
        inner, end = body
        parts = _split_spine(inner)
        if len(parts) != 2:
            return None
        return (
            ty[:at]
            + f"({carrier}.add {parts[0]} ({carrier}.add {parts[0]} {parts[1]}))"
            + ty[end + 1 :]
        )
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


def _eq_sides(ty: str, carrier: str) -> tuple[str, str] | None:
    """`(lhs, rhs)` of a rendered `Eq.{1} <carrier> lhs rhs`, else `None`."""
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return None
    if isinstance(expr, str) or len(expr) != 4 or expr[0] not in EQ_HEADS:
        return None
    if expr[1] != carrier:
        return None
    return (_render(expr[2]), _render(expr[3]))


def _balanced_body(ty: str, at: int, head_len: int) -> tuple[str, int] | None:
    """`(body, index of the closing paren)` for the application opening at `at`."""
    depth = 0
    for i in range(at, len(ty)):
        if ty[i] == "(":
            depth += 1
        elif ty[i] == ")":
            depth -= 1
            if depth == 0:
                return (ty[at + head_len : i], i)
    return None


STRUCTURAL_MUTATIONS = (
    "swap-arguments",
    "drop-argument",
    "retarget-leaf",
    "collapse-two-constants",
)


def mutate_structural(ty: str, kind: str) -> str | None:
    """One corruption of a rendered structural type, or `None` if inapplicable.

    Operates on the parsed tree and re-renders, so a corruption is a corruption
    of the STATEMENT and not of the text around it. `swap-arguments` and
    `drop-argument` remove no name, so the only thing that can reject them is
    the match against the query — which is the guard being controlled.
    """
    try:
        expr = lean_expr(ty)
    except Unsupported:
        return None
    eqs = _eq_nodes(expr)
    if not eqs:
        return None

    def first_app(node):
        """The first application with at least two arguments, pre-order."""
        if isinstance(node, str):
            return None
        if len(node) >= 3:
            return node
        for item in node[1:]:
            hit = first_app(item)
            if hit is not None:
                return hit
        return None

    def leaves(node, out):
        if isinstance(node, str):
            out.append(node)
            return
        for item in node[1:]:
            leaves(item, out)

    # Every side of every equality in the type, so the corruption reaches a
    # `¬(r₁ ∧ … ∧ rₙ)` module too. Corrupting only the first conjunct of one of
    # those would leave the controls looking live while most of the statement
    # went unmutated.
    sides = [side for node in eqs for side in (node[2], node[3])]
    if kind in ("swap-arguments", "drop-argument"):
        target = next((first_app(side) for side in sides if first_app(side)), None)
        if target is None:
            return None
        if kind == "swap-arguments":
            replacement = [target[0], target[2], target[1], *target[3:]]
        else:
            replacement = target[:-1]
        rendered = _render(target)
        damaged = _render(replacement)
        if rendered == damaged:
            return None
        return ty.replace(rendered, damaged, 1)
    names: list[str] = []
    for side in sides:
        leaves(side, names)
    distinct = sorted({name for name in names if name.startswith(QUERY_NAMESPACE)})
    if len(distinct) < 2:
        return None
    if kind == "retarget-leaf":
        # One occurrence points at a different query symbol.
        return ty.replace(distinct[0], distinct[1], 1)
    if kind == "collapse-two-constants":
        # Two distinct constants become one, which no injective renaming admits.
        return ty.replace(distinct[0], distinct[1])
    raise Unsupported(f"structural mutation `{kind}`")


def mutate_structural_module(source: str, kind: str) -> str | None:
    """`source` with every hypothesis type corrupted the same way, or `None`."""
    lines, changed = [], False
    for line in source.splitlines():
        match = AXIOM_LINE.match(line.strip())
        if match and match.group(1).startswith(ATTESTATION_HYP_PREFIXES):
            damaged = mutate_structural(match.group(2).strip(), kind)
            if damaged is not None:
                lines.append(f"axiom {match.group(1)} : {damaged}")
                changed = True
                continue
        lines.append(line)
    return "\n".join(lines) if changed else None


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
    parser.add_argument(
        "--expect",
        choices=("bound", "structural", "structural-anchored", "anchored", "attested"),
        default="bound",
        help="the verdict every --instance must reach. `bound` (the default) "
        "requires the module's hypotheses to bind to the query's assertions; "
        "`structural` requires every rendered term to be a subterm of the query "
        "under one injective correspondence AND that the query does NOT force the "
        "disequality; `structural-anchored` requires both to hold; `anchored` "
        "requires the query's own assertions to FORCE the disequality the module "
        "assumes, to force exactly one the module could stand for, AND that the "
        "structural binder cannot grip it; `attested` requires it to be a "
        "content-free opaque skeleton AND to fail both the structural and the "
        "anchored check. The four are a PARTITION and each is required to fail the "
        "checks of its neighbours, so an instance cannot quietly move between them "
        "in either direction. Which verdict is required comes from the MANIFEST "
        "when no --instance is given.",
    )
    parser.add_argument("--min-instances", type=int, default=MIN_INSTANCES)
    parser.add_argument("--min-hypotheses", type=int, default=MIN_HYPOTHESES)
    parser.add_argument(
        "--min-required-mutations", type=int, default=MIN_REQUIRED_MUTATIONS
    )
    parser.add_argument("--min-attestations", type=int, default=MIN_ATTESTATIONS)
    parser.add_argument("--min-structural", type=int, default=MIN_STRUCTURAL)
    parser.add_argument(
        "--min-structural-nodes", type=int, default=MIN_STRUCTURAL_NODES
    )
    parser.add_argument(
        "--min-structural-mutations", type=int, default=MIN_STRUCTURAL_MUTATIONS
    )
    parser.add_argument(
        "--min-structural-anchored", type=int, default=MIN_STRUCTURAL_ANCHORED
    )
    parser.add_argument("--min-anchored", type=int, default=MIN_ANCHORED)
    parser.add_argument("--min-anchored-nodes", type=int, default=MIN_ANCHORED_NODES)
    parser.add_argument(
        "--min-anchored-mutations", type=int, default=MIN_ANCHORED_MUTATIONS
    )
    parser.add_argument("--min-represented", type=int, default=MIN_REPRESENTED)
    parser.add_argument(
        "--max-undecomposable-spine", type=int, default=MAX_UNDECOMPOSABLE_SPINE
    )
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)

    if args.instance:
        targets = [(pathlib.Path(p), args.expect) for p in args.instance]
    else:
        targets = [(pathlib.Path(p), "bound") for p in manifest_instances()]
        targets += [(pathlib.Path(p), "structural") for p in structural_instances()]
        targets += [
            (pathlib.Path(p), "structural-anchored")
            for p in structural_anchored_instances()
        ]
        targets += [(pathlib.Path(p), "anchored") for p in anchored_instances()]
        targets += [(pathlib.Path(p), "attested") for p in attestation_instances()]
    instances = [path for path, want in targets if want == "bound"]
    if args.module is not None and len(targets) != 1:
        raise SystemExit("--module takes exactly one --instance")
    binary = None if args.module else dumper_binary(build=not args.no_build)

    failures: list[str] = []
    total_hypotheses = 0
    caught_mutations = 0
    accepted_mutations = 0
    attested = 0
    attested_vacuous = 0
    structural = 0
    structural_nodes = 0
    structural_caught = 0
    structural_accepted = 0
    anchored = 0
    structural_anchored = 0
    anchored_nodes = 0
    anchored_caught = 0
    anchored_accepted = 0
    spine_assertions = 0
    represented = 0
    undecomposable_spine = 0
    escaped: list[str] = []

    for instance, want in targets:
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

        if want in ("structural", "structural-anchored", "anchored"):
            wants_structural = want in ("structural", "structural-anchored")
            wants_anchored = want in ("structural-anchored", "anchored")
            s_ok, s_why, s_nodes = bind_structural(source, path)
            a_ok, a_why, a_nodes = bind_anchored(source, path)

            # The POSITIVE half of the pin: what this class claims holds.
            if wants_structural and not s_ok:
                failures.append(f"{instance}: pinned as structurally bound, but {s_why}")
                continue
            if wants_anchored and not a_ok:
                failures.append(
                    f"{instance}: pinned as anchored to an asserted disequality, but {a_why}"
                )
                continue
            # The NEGATIVE half, and the half that keeps the four verdicts a
            # partition rather than four places an instance may sit. A row that
            # starts satisfying its neighbour's check must MOVE: the gate refuses
            # to go on recording the weaker of two true statements, and it refuses
            # to let a class quietly absorb instances it no longer describes.
            if not wants_anchored and a_ok:
                failures.append(
                    f"{instance}: pinned as structurally bound ONLY, but this query also "
                    "FORCES exactly one disequality its rendered sides can stand for. "
                    "A strictly stronger statement holds than the one recorded; pin it "
                    "as `structural-anchored`"
                )
                continue
            if not wants_structural and s_ok:
                failures.append(
                    f"{instance}: pinned as anchored ONLY, but its rendered terms ARE "
                    f"{s_nodes} nodes of this query under an injective renaming. A "
                    "strictly stronger statement holds than the one recorded; pin it as "
                    "`structural-anchored`"
                )
                continue

            if wants_structural:
                structural += 1
                structural_nodes += s_nodes
            if wants_anchored:
                anchored += 1
                anchored_nodes += a_nodes
            if want == "structural-anchored":
                structural_anchored += 1
            if not args.no_self_check:
                # Corrupt this module's own statement, four ways, and require
                # each corruption to stop being a subterm of THIS query (and, for
                # an anchored pin, to stop being the disequality THIS query
                # forces). A matcher that accepts everything reports a beautiful
                # clean pass; these are the numbers that say it does not.
                #
                # The two tallies are kept independent even for a dual instance:
                # a corruption the structural binder catches and the anchor does
                # not is one caught and one accepted, not one of either. Merging
                # them would let a dead anchor hide behind a live structural
                # matcher, which is the exact shape of the masking defect found in
                # `mutation_controls.py` on 2026-08-18.
                for kind in STRUCTURAL_MUTATIONS:
                    mutant = mutate_structural_module(source, kind)
                    if mutant is None:
                        continue
                    if wants_structural:
                        mutated, _why, _nodes = bind_structural(mutant, path)
                        if mutated:
                            # Not automatically a defect: a swapped `bvadd` can
                            # name a different genuine subterm of the same file.
                            # Counted, not failed — the floor is on the CAUGHT side.
                            structural_accepted += 1
                        else:
                            structural_caught += 1
                    if wants_anchored:
                        # For a module whose sides are bare constants only
                        # `retarget-leaf` and `collapse-two-constants` apply --
                        # there is no application to damage -- and both are caught
                        # by the match against the query's forced pairs, not by
                        # anything internal to the module.
                        mutated, _why, _nodes = bind_anchored(mutant, path)
                        if mutated:
                            anchored_accepted += 1
                        else:
                            anchored_caught += 1
            if args.verbose:
                print(
                    f"  {instance} [{fragment}] {want}, {s_nodes} structural / "
                    f"{a_nodes} anchored term nodes"
                )
            continue

        if want == "attested":
            # The guard that keeps the two classes from absorbing each other. An
            # attestation's claim is that nothing relates the module to the
            # query; if the structural binder can relate it, that claim is FALSE
            # and the instance belongs in the manifest above. Without this, a
            # renderer that started transcribing would leave every pinned
            # attestation green while the words `transcribes NOTHING` quietly
            # stopped being true.
            bound_anyway, _why, nodes = bind_structural(source, path)
            if bound_anyway:
                failures.append(
                    f"{instance}: pinned as a content-free attestation, but its rendered "
                    f"terms ARE {nodes} nodes of this query under an injective renaming. "
                    "It transcribes something; pin it as `structural`"
                )
                continue
            # The same guard, one notch weaker and therefore one notch harder to
            # stay on the right side of: an attestation also claims the query does
            # not ENTAIL what the module assumes. If it does -- uniquely -- the
            # instance belongs in the anchored manifest. Without this the anchored
            # class could never grow, because a module that started being
            # anchorable would sit green in this one.
            anchored_anyway, _why, _nodes = bind_anchored(source, path)
            if anchored_anyway:
                failures.append(
                    f"{instance}: pinned as a content-free attestation, but this query "
                    "FORCES exactly one disequality its rendered sides can stand for. "
                    "The module's assumption is entailed by the file; pin it as "
                    "`anchored`"
                )
                continue
            ok, why, vacuous = classify_attestation(source)
            if not ok:
                failures.append(
                    f"{instance}: pinned as a content-free attestation, but {why}"
                )
                continue
            attested_vacuous += vacuous
            if vacuous:
                # A module whose `False` follows from ONE axiom by `rfl` alone is
                # not even the propositional step it appears to take: it needs no
                # other axiom, and would need none if the `.smt2` file said
                # something else. Counting it was the previous behaviour and it
                # is not enough -- a number nobody's exit status depends on is a
                # number a regression can raise.
                failures.append(
                    f"{instance}: {vacuous} of its hypothesis axioms is SELF-REFUTING "
                    "(`Not (Eq α t t)`, which Lean's own `rfl` refutes), so the "
                    "module's `False` needs none of its other axioms and nothing at "
                    "all from the query. The route must decline instead of rendering "
                    "this"
                )
                continue
            attested += 1
            if args.verbose:
                print(f"  {instance} [{fragment}] attestation, nothing transcribed")
            continue

        phi, hypotheses, allowed, detail = check_instance(source, indices, sorts, assertions)
        if phi is None:
            failures.append(f"{instance}: {detail}")
            continue
        if not hypotheses:
            # A module with no hypothesis in any bound route binds VACUOUSLY: the
            # empty renaming satisfies every requirement. Without this, a renderer
            # regression that degraded a pinned instance to a content-free
            # skeleton would leave the ratchet green -- only the run-wide
            # `--min-hypotheses` floor would notice, and only in bulk.
            failures.append(
                f"{instance}: the module carries no hypothesis in any bound route, so "
                "the binding is vacuous; it is either an attestation (pin it as one) "
                "or a regression"
            )
            continue
        total_hypotheses += len(hypotheses)
        spine, covered, opaque_rows = represented_assertions(
            phi, hypotheses, indices, assertions
        )
        spine_assertions += spine
        represented += covered
        undecomposable_spine += opaque_rows
        if args.verbose:
            print(
                f"  {instance} [{fragment}] {len(hypotheses)} hypotheses bound, "
                f"{covered}/{spine} spine assertions represented"
            )
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
        f"unjustified={len(escaped)}|structural={structural}|"
        f"structural_nodes={structural_nodes}|structural_caught={structural_caught}|"
        f"structural_accepted={structural_accepted}|anchored={anchored}|"
        f"anchored_nodes={anchored_nodes}|anchored_caught={anchored_caught}|"
        f"anchored_accepted={anchored_accepted}|"
        f"structural_anchored={structural_anchored}|attested={attested}|"
        f"attested_vacuous={attested_vacuous}|spine_assertions={spine_assertions}|"
        f"represented_assertions={represented}|"
        f"undecomposable_spine={undecomposable_spine}|failures={len(failures)}"
    )

    failures.extend(escaped)
    if len(instances) < args.min_instances:
        failures.append(
            f"only {len(instances)} instances were checked (floor {args.min_instances})"
        )
    if any(want == "attested" for _p, want in targets) and attested < args.min_attestations:
        failures.append(
            f"only {attested} modules were confirmed content-free attestations (floor "
            f"{args.min_attestations}). This number is not coverage -- it is the part "
            "of the corpus whose Lean evidence transcribes NOTHING from the query, and "
            "a checker that stopped confirming that would stop reporting it"
        )
    if any(want in ("structural", "structural-anchored") for _p, want in targets):
        if structural < args.min_structural:
            failures.append(
                f"only {structural} modules were structurally bound to their query "
                f"(floor {args.min_structural})"
            )
        if (
            not args.no_self_check
            and structural_caught < args.min_structural_mutations
        ):
            failures.append(
                f"only {structural_caught} corruptions of a structural module were "
                f"CAUGHT (floor {args.min_structural_mutations}). A matcher that "
                "accepts every corruption of the statement it is checking is not a "
                "check"
            )
        if structural_nodes < args.min_structural_nodes:
            failures.append(
                f"only {structural_nodes} term nodes were structurally matched (floor "
                f"{args.min_structural_nodes}). The instance count alone cannot see a "
                "renderer that degraded to bare constants: those still bind, and bind "
                "vacuously"
            )
    if (
        any(want == "structural-anchored" for _p, want in targets)
        and structural_anchored < args.min_structural_anchored
    ):
        failures.append(
            f"only {structural_anchored} modules earned BOTH verdicts (floor "
            f"{args.min_structural_anchored}). This is the overlap between "
            "containing the module's terms and forcing its disequality, and a drop "
            "means instances stopped satisfying the stronger of the two statements "
            "that used to hold of them"
        )
    if any(want in ("anchored", "structural-anchored") for _p, want in targets):
        if anchored < args.min_anchored:
            failures.append(
                f"only {anchored} modules were anchored to a disequality their query "
                f"forces (floor {args.min_anchored})"
            )
        if anchored_nodes < args.min_anchored_nodes:
            failures.append(
                f"only {anchored_nodes} rendered term nodes were anchored (floor "
                f"{args.min_anchored_nodes}). The instance count alone cannot see a "
                "renderer that degraded a structured side back to a bare constant: a "
                "bare pair still anchors, on uniqueness alone"
            )
        if not args.no_self_check and anchored_caught < args.min_anchored_mutations:
            failures.append(
                f"only {anchored_caught} corruptions of an anchored module were CAUGHT "
                f"(floor {args.min_anchored_mutations}). An anchor that holds whatever "
                "the module says is not an anchor"
            )
    if total_hypotheses < args.min_hypotheses:
        failures.append(
            f"only {total_hypotheses} hypothesis axioms were bound (floor "
            f"{args.min_hypotheses}); a run that binds nothing proves nothing"
        )
    if undecomposable_spine > args.max_undecomposable_spine:
        failures.append(
            f"{undecomposable_spine} spine assertions yielded NO atoms to this "
            f"parser (ceiling {args.max_undecomposable_spine}). Such a row cannot be "
            "represented whatever the module renders, so it would show up as a lower "
            "`represented_assertions` and be read as the refutation resting on less "
            "of the query -- when it is this script that stopped understanding the "
            "query. The two must not be confusable, so a blind row fails the run "
            "instead of quietly shrinking the number that describes the refutations"
        )
    if instances and represented < args.min_represented:
        failures.append(
            f"only {represented} of {spine_assertions} spine assertions are represented "
            f"by a rendered hypothesis (floor {args.min_represented}). This is the "
            "CONVERSE of what binding proves: a drop here means the modules started "
            "resting on less of the query than they used to, which the subset check "
            "cannot see"
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
    """φ applied factor-by-factor inside every monomial, then re-canonicalized.

    Re-sorting BOTH the factors within a monomial and the monomials within the
    atom matters: φ need not be order-preserving, so `(a, b) -> (y, x)` has to
    come back as the `(x, y)` the query side produced.
    """
    rel, terms, const = atom
    renamed = tuple(
        sorted((tuple(sorted(phi.get(f, f) for f in mono)), c) for mono, c in terms)
    )
    return (rel, renamed, const)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
