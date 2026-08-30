#!/usr/bin/env python3
"""The D3 counterexample-first fixture pack: definitions, and theorem-proposal
false statements, checked against independent references BEFORE a producer is
ever dispatched at them (roadmap phase D3,
`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`).

This is a SIBLING of S3's `scripts/semantic_control_fixtures.py`
(ADR-0752), not a replacement or an import of it -- this module is composed
with S3 at the process boundary (this lane's checker shells out to S3's
checker and reads its JSON) rather than importing S3's internals, per this
lane's scope: S3's files are read-only here.

Two kinds of retained specimen, and they answer different halves of the D3
exit criterion:

``FALSE_STATEMENTS``
    Theorem-shaped PROPOSALS this repository would have dispatched a proof
    producer at, that are false.  Every entry here is genuinely NEW relative
    to S3's 13 fixtures (checked: neither `lor` nor `bitwise` appears in
    `semantic_control_fixtures.py`) -- both are drawn from the bitwise-fuel
    family in CLAUDE.md's Gotchas, both verified by running the recursion in
    Python before being trusted (the roadmap's own retrospective: a traced
    plan's "verified numerically" was itself false at 26/26 non-coprime pairs,
    because nobody re-ran the numbers).  The `run()` callable returns an
    ``Outcome`` whose `counterexamples` list is the discriminating witness --
    not a hand-computed one, a COMPUTED one.

``DEFINITIONS``
    Candidate *definitions* (not theorems) reviewed by: an executable
    equation set, an independent reference implementation on a bounded
    domain, non-degenerate witnesses (with a stated reason each
    discriminates), and at least one deliberate MUTATION of the definition
    that must move an observation relative to the reference.  A mutation that
    changes nothing is exactly the vacuity this repository has shipped before
    (`Nat.lor`'s absorbing-zero base case, copied from `Nat.land`, would have
    silently dropped every bit of `n` at `m = 0` -- type-correct, admitted,
    wrong).  Some definitions in this pack ARE the historical bug (as the
    mutation); none of the CORRECT candidates is.

``REVIEW_OBLIGATIONS``
    Definitions this pack does NOT execute, each carrying an explicit reason
    a human review is required instead -- limit/Cauchy-sequence constructions
    where a from-scratch "independent reference" would just re-derive the
    same machinery under test, testing nothing (the exact vacuity-by-shape
    problem ADR-0752 catalogues for certificates, arriving here for
    definitions).
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable

# ---------------------------------------------------------------------------
# shared result types (mirrors semantic_control_fixtures.Outcome/Mutation in
# shape only -- this module does not import that one; see module docstring)
# ---------------------------------------------------------------------------


@dataclass
class Outcome:
    executed: int
    counterexamples: list[str] = field(default_factory=list)
    note: str = ""


@dataclass
class Mutation:
    """A deliberate perturbation of a CORRECT candidate definition.

    `moves_observation` is computed by `run()`, never asserted: the mutation
    is applied, compared against the SAME independent reference over the SAME
    bounded domain, and the guard checks whether at least one point diverged.
    A mutation that changes nothing (`moved == False`) is not a passing
    control -- it is a vacuous one, and the gate reports it by name.
    """

    id: str
    description: str
    run: Callable[[], "MutationOutcome"]


@dataclass
class MutationOutcome:
    executed: int
    moved: bool
    first_divergence: str = ""


@dataclass
class Witness:
    args: tuple
    reason: str  # why THIS instance discriminates, stated up front


@dataclass
class FalseStatement:
    id: str
    family: str
    statement: str
    provenance: str
    run: Callable[[], Outcome]


@dataclass
class DefinitionReview:
    id: str
    domain_note: str
    provenance: str
    reference_note: str
    witnesses: list[Witness]
    run_reference_check: Callable[[], Outcome]  # correct candidate vs reference
    mutations: list[Mutation]


@dataclass
class ReviewObligation:
    id: str
    reason: str
    status: str  # "open" | "reviewed"


FALSE_STATEMENTS: list[FalseStatement] = []
DEFINITIONS: list[DefinitionReview] = []
REVIEW_OBLIGATIONS: list[ReviewObligation] = []


def _register_false(fx: FalseStatement) -> FalseStatement:
    FALSE_STATEMENTS.append(fx)
    return fx


def _register_def(d: DefinitionReview) -> DefinitionReview:
    DEFINITIONS.append(d)
    return d


def _register_review(r: ReviewObligation) -> ReviewObligation:
    REVIEW_OBLIGATIONS.append(r)
    return r


# ===========================================================================
# shared small-domain bitwise-fuel model.
#
# Verified against Python's native &, |, ^ over the full 16x16 domain before
# being trusted (0 mismatches) -- this is the model, not a transcription of
# the Rust kernel source, and it is used only to reproduce the SHAPE of two
# documented CLAUDE.md defects with a genuinely independent reference (the
# native bitwise operators), not to certify the Rust kernel itself.
# ===========================================================================


def bitwise_aux(f: Callable[[bool, bool], bool], fuel: int, m: int, n: int) -> int:
    """`bitwiseAux`'s fuel-exhaustion row is `if f false true then n else 0`
    (CLAUDE.md, the `Nat.bitwise_and_eq_land` / `_or_eq_lor` entry)."""
    if fuel == 0:
        return n if f(False, True) else 0
    bit_m, bit_n = m % 2, n % 2
    combine = 1 if f(bool(bit_m), bool(bit_n)) else 0
    return combine + 2 * bitwise_aux(f, fuel - 1, m // 2, n // 2)


def bitwise(f: Callable[[bool, bool], bool], m: int, n: int) -> int:
    """Canonical entry point: fuel = m (structural recursion on the first
    operand, per CLAUDE.md's `Nat.mul`/`Nat.add` asymmetry entries)."""
    return bitwise_aux(f, m, m, n)


def lor_aux(fuel: int, m: int, n: int) -> int:
    """`lor`'s fuel-exhaustion row returns `n` (pass-through, NOT the
    absorbing `0` that `land`/`ldiff` use) -- OR has no absorbing element."""
    if fuel == 0:
        return n
    return (1 if (m % 2 or n % 2) else 0) + 2 * lor_aux(fuel - 1, m // 2, n // 2)


AND_F = lambda a, b: a and b
OR_F = lambda a, b: a or b
XOR_F = lambda a, b: a != b
FST_F = lambda a, b: a  # deliberately non-commutative: f(a, b) = a


BOUND = 12  # small: unary Nat numerals make magnitude, not depth, the cost driver


# ===========================================================================
# FALSE_STATEMENTS -- theorem-shaped proposals this repository would have
# dispatched a producer at.  Neither id below exists in S3's fixture pack.
# ===========================================================================


def _run_lor_comm_unconditional() -> Outcome:
    """`Nat.lor_aux_comm_of_fuel` WITHOUT the `Le m fuel -> Le n fuel`
    sufficiency hypothesis: `forall fuel m n, lorAux fuel m n = lorAux fuel n m`.

    False.  CLAUDE.md's own witness: `lorAux 0 0 1 = 1` against
    `lorAux 0 1 0 = 0` -- the fuel-exhaustion row returns `n`, which is not
    symmetric in `m`/`n` when `m` and `n` are not both already exhausted.
    """
    ce = []
    executed = 0
    for fuel in range(0, 4):
        for m in range(0, BOUND):
            for n in range(0, BOUND):
                executed += 1
                lhs = lor_aux(fuel, m, n)
                rhs = lor_aux(fuel, n, m)
                if lhs != rhs:
                    ce.append(
                        f"fuel={fuel} m={m} n={n}: lorAux(fuel,m,n)={lhs} != "
                        f"lorAux(fuel,n,m)={rhs}"
                    )
    return Outcome(executed=executed, counterexamples=ce)


_register_false(
    FalseStatement(
        id="lor-aux-comm-of-fuel-unconditional",
        family="bitwise-fuel",
        statement=(
            "forall fuel m n : Nat, lorAux fuel m n = lorAux fuel n m "
            "(no Le m fuel / Le n fuel hypothesis)"
        ),
        provenance=(
            "CLAUDE.md Gotchas, the 'Nat.mul HAS THE SAME ASYMMETRY' entry: "
            "'the obvious lor analogue is not merely harder to prove -- it is "
            "false -- lorAux 0 0 1 = 1 against lorAux 0 1 0 = 0'"
        ),
        run=_run_lor_comm_unconditional,
    )
)


def _run_bitwise_comm_unconditional() -> Outcome:
    """`forall f m n, bitwise f m n = bitwise f n m` for an ARBITRARY boolean
    combinator `f` -- no `hf : forall a b, f a b = f b a` hypothesis.

    False whenever `f` is not itself commutative.  Witness: `f = fst`
    (projection onto the first bit), `bitwise(fst, 0, 1) = 0` against
    `bitwise(fst, 1, 0) = 1` -- and by construction `bitwise(fst, m, n) = m`,
    which cannot be a symmetric function of `m` and `n`.
    """
    ce = []
    executed = 0
    combinators = {"and": AND_F, "or": OR_F, "xor": XOR_F, "fst": FST_F}
    for name, f in combinators.items():
        for m in range(0, BOUND):
            for n in range(0, BOUND):
                executed += 1
                lhs = bitwise(f, m, n)
                rhs = bitwise(f, n, m)
                if lhs != rhs:
                    ce.append(f"f={name} m={m} n={n}: bitwise(f,m,n)={lhs} != bitwise(f,n,m)={rhs}")
    return Outcome(executed=executed, counterexamples=ce)


_register_false(
    FalseStatement(
        id="bitwise-comm-unconditional-arbitrary-f",
        family="bitwise-fuel",
        statement="forall f m n : Nat, bitwise f m n = bitwise f n m (no hf : forall a b, f a b = f b a)",
        provenance=(
            "CLAUDE.md Gotchas, 'Nat.mul HAS THE SAME ASYMMETRY': "
            "'the unconditional form is false whenever f false true = true "
            "(so for or and xor, and true only for and)' -- and the fully "
            "unconstrained forall-f statement is false for ANY non-commutative "
            "f regardless of that boundary detail, which f=fst demonstrates "
            "directly and is the witness this fixture uses"
        ),
        run=_run_bitwise_comm_unconditional,
    )
)


# ===========================================================================
# DEFINITIONS -- candidate definitions, an independent reference, and at
# least one mutation each that must move an observation.
# ===========================================================================


def _check_definition(candidate, reference, domain) -> Outcome:
    executed = 0
    ce = []
    for args in domain:
        executed += 1
        c = candidate(*args)
        r = reference(*args)
        if c != r:
            ce.append(f"args={args}: candidate={c} reference={r}")
    return Outcome(executed=executed, counterexamples=ce)


def _mutation_outcome(mutant, reference, domain) -> MutationOutcome:
    executed = 0
    for args in domain:
        executed += 1
        m = mutant(*args)
        r = reference(*args)
        if m != r:
            return MutationOutcome(
                executed=executed, moved=True, first_divergence=f"args={args}: mutant={m} reference={r}"
            )
    return MutationOutcome(executed=executed, moved=False)


# --- Nat.land ---------------------------------------------------------------

_DOMAIN_2 = [(m, n) for m in range(0, BOUND) for n in range(0, BOUND)]


def land_correct(m: int, n: int) -> int:
    return bitwise(AND_F, m, n)


def land_ref(m: int, n: int) -> int:
    return m & n


def land_mutant_passthrough_base(m: int, n: int) -> int:
    """A land whose fuel-exhaustion base row copies `lor`'s pass-through
    (`n`) instead of the absorbing `0`.  A perturbation of `land`'s OWN
    definition, deliberately in the direction CLAUDE.md documents as wrong
    for the sibling operator, to show the harness catches it on either side."""

    def aux(fuel, m_, n_):
        if fuel == 0:
            return n_  # wrong: should be 0
        bm, bn = m_ % 2, n_ % 2
        return (1 if (bm and bn) else 0) + 2 * aux(fuel - 1, m_ // 2, n_ // 2)

    return aux(m, m, n)


_register_def(
    DefinitionReview(
        id="Nat.land",
        domain_note=f"m, n in [0, {BOUND}) -- unary Nat numerals, small magnitudes only",
        provenance="CLAUDE.md: 'land has an absorbing zero (m = 0 => result 0 regardless of n)'",
        reference_note="Python's native `&` -- a wholly different (non-recursive, machine-word) implementation",
        witnesses=[
            Witness((0, 7), "m=0 discriminates the absorbing-zero base case from any pass-through variant"),
            Witness((5, 3), "a case with no zero operand exercises the per-bit combine, not just the base"),
        ],
        run_reference_check=lambda: _check_definition(land_correct, land_ref, _DOMAIN_2),
        mutations=[
            Mutation(
                id="land-passthrough-base",
                description="fuel-exhaustion base returns n instead of the absorbing 0",
                run=lambda: _mutation_outcome(land_mutant_passthrough_base, land_ref, _DOMAIN_2),
            )
        ],
    )
)


# --- Nat.lor -----------------------------------------------------------------


def lor_correct(m: int, n: int) -> int:
    return bitwise(OR_F, m, n)


def lor_ref(m: int, n: int) -> int:
    return m | n


def lor_mutant_absorbing_base(m: int, n: int) -> int:
    """THE historical bug: `lor`'s fuel-exhaustion base copied `land`'s
    absorbing-zero shortcut.  `lor 0 1000000 = 0` per CLAUDE.md; this fixture
    uses `lor(0, 7)` to keep magnitudes small (unary numerals)."""

    def aux(fuel, m_, n_):
        if fuel == 0:
            return 0  # wrong: should be n_
        bm, bn = m_ % 2, n_ % 2
        return (1 if (bm or bn) else 0) + 2 * aux(fuel - 1, m_ // 2, n_ // 2)

    return aux(m, m, n)


_register_def(
    DefinitionReview(
        id="Nat.lor",
        domain_note=f"m, n in [0, {BOUND})",
        provenance=(
            "CLAUDE.md: 'Nat.lor would have silently dropped every bit of n "
            "when m = 0, because land's absorbing-zero shortcut was copied to "
            "an operator with no absorbing element. Type-correct, admitted, wrong.'"
        ),
        reference_note="Python's native `|`",
        witnesses=[
            Witness((0, 7), "m=0, n!=0: the exact shape of the shipped defect -- correct answer is 7, buggy answer is 0"),
        ],
        run_reference_check=lambda: _check_definition(lor_correct, lor_ref, _DOMAIN_2),
        mutations=[
            Mutation(
                id="lor-absorbing-base",
                description="fuel-exhaustion base returns 0 instead of the pass-through n (the real shipped bug)",
                run=lambda: _mutation_outcome(lor_mutant_absorbing_base, lor_ref, _DOMAIN_2),
            )
        ],
    )
)


# --- Nat.ldiff ---------------------------------------------------------------


def ldiff_correct(m: int, n: int) -> int:
    def aux(fuel, m_, n_):
        if fuel == 0:
            return 0
        bm, bn = m_ % 2, n_ % 2
        return (1 if (bm and not bn) else 0) + 2 * aux(fuel - 1, m_ // 2, n_ // 2)

    return aux(m, m, n)


def ldiff_ref(m: int, n: int) -> int:
    return m & ~n  # Python ints: infinite two's-complement makes this exact for m, n >= 0


def ldiff_mutant_passthrough_base(m: int, n: int) -> int:
    def aux(fuel, m_, n_):
        if fuel == 0:
            return n_  # wrong: ldiff's base is absorbing-0 like land, not pass-through like lor
        bm, bn = m_ % 2, n_ % 2
        return (1 if (bm and not bn) else 0) + 2 * aux(fuel - 1, m_ // 2, n_ // 2)

    return aux(m, m, n)


_register_def(
    DefinitionReview(
        id="Nat.ldiff",
        domain_note=f"m, n in [0, {BOUND})",
        provenance=(
            "CLAUDE.md: 'ldiff is the instructive one: it takes land's base case "
            "but its inner succ-row guard is a hybrid' and gives the asymmetry "
            "witness 'ldiff 3 5 = 2 against ldiff 5 3 = 4'"
        ),
        reference_note="Python's native `m & ~n`",
        witnesses=[
            Witness((3, 5), "CLAUDE.md's own asymmetry witness: ldiff(3,5)=2"),
            Witness((5, 3), "swapped operands give a DIFFERENT value (4) -- proves ldiff is not commutative, so a commutativity mutation would be vacuous here and is correctly not attempted"),
            Witness((0, 7), "m=0 discriminates the absorbing-zero base from lor's pass-through"),
        ],
        run_reference_check=lambda: _check_definition(ldiff_correct, ldiff_ref, _DOMAIN_2),
        mutations=[
            Mutation(
                id="ldiff-passthrough-base",
                description="fuel-exhaustion base returns n instead of the absorbing 0 (copying lor's shape onto an operator that needs land's)",
                run=lambda: _mutation_outcome(ldiff_mutant_passthrough_base, ldiff_ref, _DOMAIN_2),
            )
        ],
    )
)


# --- Nat.dist ----------------------------------------------------------------


def dist_correct(m: int, n: int) -> int:
    return (m - n) if m >= n else (n - m)


def dist_ref(m: int, n: int) -> int:
    return abs(m - n)


def dist_mutant_one_directional_sub(m: int, n: int) -> int:
    """Silent Nat.sub truncation: always `m - n` truncated at 0, never checks
    which side is larger.  The general hazard CLAUDE.md documents for
    `Nat.descFactorial` ('only evaluation past the base exercises Nat.sub's
    silent truncation'), applied to the definition ADR-0645 names directly
    (`Nat.dist_comm`, `Nat.dist_self`)."""
    return m - n if m >= n else 0


_register_def(
    DefinitionReview(
        id="Nat.dist",
        domain_note=f"m, n in [0, {BOUND})",
        provenance=(
            "ADR-0645 names Nat.dist_comm / Nat.dist_self directly; the general "
            "hazard is CLAUDE.md's 'Nat.sub's silent truncation' theme"
        ),
        reference_note="Python's native abs(m - n)",
        witnesses=[
            Witness((2, 5), "m < n: exercises the branch a one-directional subtraction drops entirely"),
            Witness((5, 2), "m > n: the mutant is accidentally correct here -- included to show the mutation is NOT symmetric-safe, only order-dependent"),
        ],
        run_reference_check=lambda: _check_definition(dist_correct, dist_ref, _DOMAIN_2),
        mutations=[
            Mutation(
                id="dist-one-directional-sub",
                description="m - n truncated at 0, missing the n > m branch entirely",
                run=lambda: _mutation_outcome(dist_mutant_one_directional_sub, dist_ref, _DOMAIN_2),
            )
        ],
    )
)


# --- Nat.descFactorial --------------------------------------------------------


def _satsub(a: int, b: int) -> int:
    return a - b if a >= b else 0


def desc_factorial_correct(n: int, k: int) -> int:
    v = 1
    for j in range(k):
        v = _satsub(n, j) * v
    return v


def desc_factorial_ref(n: int, k: int) -> int:
    if k > n:
        return 0
    return math.factorial(n) // math.factorial(n - k)


def desc_factorial_mutant_off_by_one(n: int, k: int) -> int:
    """Off-by-one term index: `n - (j+1)` instead of `n - j` at each step --
    the exact shape of the 'silent truncation' hazard CLAUDE.md names for this
    definition, arriving one step early."""
    v = 1
    for j in range(k):
        v = _satsub(n, j + 1) * v
    return v


_DOMAIN_NK = [(n, k) for n in range(0, 8) for k in range(0, 8)]

_register_def(
    DefinitionReview(
        id="Nat.descFactorial",
        domain_note="n, k in [0, 8) -- small enough that factorial(n) never dominates cost",
        provenance="CLAUDE.md: 'only evaluation past the base exercises Nat.sub's silent truncation'",
        reference_note="math.factorial(n) // math.factorial(n - k) for k <= n, else 0 (independent, non-recursive)",
        witnesses=[
            Witness((3, 1), "smallest case where the off-by-one term index changes the very first factor: correct=3, mutant=2"),
            Witness((5, 3), "a multi-step case so the discrepancy is not an artifact of a single-term product"),
        ],
        run_reference_check=lambda: _check_definition(desc_factorial_correct, desc_factorial_ref, _DOMAIN_NK),
        mutations=[
            Mutation(
                id="descfactorial-off-by-one-term",
                description="each factor uses n - (j+1) instead of n - j",
                run=lambda: _mutation_outcome(desc_factorial_mutant_off_by_one, desc_factorial_ref, _DOMAIN_NK),
            )
        ],
    )
)


# --- Int.bezout_witnesses ------------------------------------------------------


def egcd_correct(a: int, b: int) -> tuple[int, int, int]:
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def egcd_mutant_sign_flip(a: int, b: int) -> tuple[int, int, int]:
    """A hand-computation-shaped sign error in the coefficient update: `+`
    instead of `-`.  CLAUDE.md: 'the identity is satisfied by SOME pair for
    any correct gcd, so type-checking pinned down nothing ... evaluation at
    13 points across four sign branches caught a wrong hand-computation.'"""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s + q * s  # bug: should be old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def _bezout_identity_holds(a: int, b: int, fn) -> bool:
    g, x, y = fn(a, b)
    return a * x + b * y == g


def _bezout_check(fn, domain) -> Outcome:
    executed = 0
    ce = []
    for a, b in domain:
        executed += 1
        if not _bezout_identity_holds(a, b, fn):
            ce.append(f"a={a} b={b}: a*x+b*y != g for {fn.__name__}")
    return Outcome(executed=executed, counterexamples=ce)


def _bezout_mutation_outcome(domain) -> MutationOutcome:
    executed = 0
    for a, b in domain:
        executed += 1
        if not _bezout_identity_holds(a, b, egcd_mutant_sign_flip):
            return MutationOutcome(executed=executed, moved=True, first_divergence=f"a={a} b={b}: identity fails under the sign-flip mutation")
    return MutationOutcome(executed=executed, moved=False)


# Chosen to discriminate: same-sign pairs are where the sign-flip mutation
# breaks the identity. VACUOUS EXCLUDED BEFORE USE: (-12, 18), (12, -18) and
# (-7, 5), (7, -5) were checked and the mutant identity HOLDS at every one of
# them -- a mixed-sign pair is a vacuous witness for this specific mutation,
# so it is intentionally left out of the witness/domain list below (recorded
# in this lane's report, not silently dropped).
_BEZOUT_DOMAIN = [(12, 18), (7, 5), (9, 6), (11, 4)]

_register_def(
    DefinitionReview(
        id="Int.bezout_witnesses",
        domain_note="a, b same-sign pairs, |a|,|b| <= 18 -- see the vacuous-witness note below",
        provenance="CLAUDE.md: Bezout witnesses caught a wrong hand-computation via evaluation across sign branches",
        reference_note="the Bezout identity a*x + b*y = g, checked directly (an equation reference, not a second full algorithm) plus a differently-structured iterative implementation as the candidate",
        witnesses=[
            Witness((12, 18), "same-sign, gcd != min(a,b): the sign-flip mutation breaks the identity here"),
            Witness((7, 5), "coprime same-sign pair: g=1, a tight identity check"),
        ],
        run_reference_check=lambda: _bezout_check(egcd_correct, _BEZOUT_DOMAIN),
        mutations=[
            Mutation(
                id="bezout-coefficient-sign-flip",
                description="coefficient update uses + instead of - for old_s (a hand-computation-shaped sign error)",
                run=lambda: _bezout_mutation_outcome(_BEZOUT_DOMAIN),
            )
        ],
    )
)


# ===========================================================================
# REVIEW_OBLIGATIONS -- definitions this pack does not execute.
# ===========================================================================

_register_review(
    ReviewObligation(
        id="CReal.integral",
        reason=(
            "Defined via limits of Riemann sums over a Cauchy sequence of "
            "rationals with an INTERVAL-RELATIVE mesh (2026-08-27 architecture "
            "review); there is no closed finite equation over Q, and a "
            "bounded-precision rational approximation would have to replicate "
            "CReal's own regularity/completion machinery to serve as a "
            "genuinely INDEPENDENT reference -- doing so would test the "
            "reimplementation against itself, which is the certificate-shaped "
            "vacuity ADR-0752 already catalogues, arriving here for a definition."
        ),
        status="open",
    )
)

_register_review(
    ReviewObligation(
        id="CReal.e",
        reason=(
            "Defined as the limit of a Cauchy sequence of rational partial "
            "sums; evaluating it to any fixed rational precision needs the same "
            "regularity witness the definition itself supplies, so no "
            "structurally-independent reference exists at reasonable cost. "
            "Needs a human-reviewed bounded-precision approximation with an "
            "explicitly audited error budget before this pack can execute it."
        ),
        status="open",
    )
)
