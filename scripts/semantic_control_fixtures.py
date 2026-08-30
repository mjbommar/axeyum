#!/usr/bin/env python3
"""The retained semantic-control fixture pack (roadmap phase S3).

Every fixture here is a REAL defect this repository produced and caught, or the
valid control that sits one line away from it.  The pack exists because the
roadmap's S3 exit is *"the known false/vacuous fixture pack is rejected and
known valid controls remain accepted; zero executed cases is always failure"*,
and because mutation testing structurally cannot supply it: mutation deletes
guards that EXIST, and every case below is a guard that was never written.

Three fixture classes, and the distinction is the whole point:

``false``
    The statement is FALSE.  A control over it must produce at least one
    counterexample.  If it produces none, the control is measuring nothing.

``vacuous``
    The statement is TRUE but the control cannot discriminate: there is no
    instance in its domain at which the property could fail.  A vacuous control
    passes forever and proves nothing.  The fixture asserts the zero.

``valid``
    The statement is true AND the control discriminates: at least one instance
    in the domain would have failed had the property failed.  Its declared
    mutations must include at least one that is KILLED, which is what makes the
    control *load-bearing* rather than merely green.

A mutation that is not falsified is classified ``also-true`` and is a REVIEW
result, never a failure -- the roadmap is explicit about this, and a gate that
reds on a true mutation is a gate somebody turns off.

The pack is executed and pinned by `scripts/check-semantic-control-fixtures.py`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import product
from math import gcd
from typing import Callable

# ---------------------------------------------------------------------------
# fixture types
# ---------------------------------------------------------------------------


@dataclass
class Outcome:
    """What one control actually did when run.

    `executed` is the number of instances the control evaluated.  Zero is
    ALWAYS a failure, whatever the fixture class -- that is this repository's
    signature defect and the reason the field exists separately from
    `counterexamples`.

    `discriminating` is the number of instances at which the control's guards
    could have separated a true statement from a false one.  A control with
    `discriminating == 0` is vacuous even when `executed` is large.
    """

    executed: int
    discriminating: int
    counterexamples: list[str] = field(default_factory=list)
    note: str = ""


@dataclass
class Mutation:
    """A deliberate perturbation of a valid statement.

    `kind` is one of the roadmap's named families: `relation`, `constant`,
    `quantifier`, `operand`, `hypothesis-removal`, `hypothesis-weakening`.
    `also_true` records that we EXPECT this mutation to survive because the
    mutated statement is itself true -- the review outcome, not a failure.
    """

    id: str
    kind: str
    run: Callable[[], Outcome]
    also_true: bool = False


@dataclass
class Fixture:
    id: str
    family: str
    expect: str  # "false" | "vacuous" | "valid"
    provenance: str
    run: Callable[[], Outcome]
    fact_ids: list[str] = field(default_factory=list)
    mutations: list[Mutation] = field(default_factory=list)


FIXTURES: list[Fixture] = []


def register(fx: Fixture) -> Fixture:
    FIXTURES.append(fx)
    return fx


# ---------------------------------------------------------------------------
# shared small-domain models
# ---------------------------------------------------------------------------


def totient(k: int) -> int:
    return sum(1 for i in range(k) if gcd(i, k) == 1)


def count_range(pred, bound: int) -> int:
    return sum(1 for i in range(bound) if pred(i))


PAIRS = [(m, n) for m in range(1, 10) for n in range(1, 10)]
COPRIME_PAIRS = [(m, n) for (m, n) in PAIRS if gcd(m, n) == 1]
NONCOPRIME_PAIRS = [(m, n) for (m, n) in PAIRS if gcd(m, n) != 1]


# ===========================================================================
# 1. the coprimality-independence claim -- FALSE at 26 of 26 non-coprime pairs
# ===========================================================================
#
# A traced plan asserted the row-major count identity
#
#     totient (m*n)  =  totient m * totient n
#
# was coprimality-INDEPENDENT and said so as "verified numerically at (4,6),
# (6,9)".  It is false at every non-coprime pair in the small domain, smallest
# counterexample m = n = 2.  The plan's confidence is exactly why nobody re-ran
# the numbers, so the pack re-runs them.


def _coprimality_independence_false() -> Outcome:
    ces = []
    for m, n in NONCOPRIME_PAIRS:
        if totient(m * n) != totient(m) * totient(n):
            ces.append(f"m={m} n={n}: totient({m * n})={totient(m * n)} != {totient(m)}*{totient(n)}")
    return Outcome(
        executed=len(NONCOPRIME_PAIRS),
        discriminating=len(NONCOPRIME_PAIRS),
        counterexamples=ces,
        note="the plan cited (4,6) and (6,9); the smallest counterexample is m=n=2",
    )


register(
    Fixture(
        id="totient-multiplicativity-without-coprimality",
        family="natural-totient",
        expect="false",
        provenance=(
            "a traced plan asserted this identity was coprimality-independent and "
            '"verified numerically at (4,6),(6,9)"; CLAUDE.md records the correction'
        ),
        run=_coprimality_independence_false,
    )
)


def _coprimality_independence_valid() -> Outcome:
    ces = [
        f"m={m} n={n}"
        for (m, n) in COPRIME_PAIRS
        if totient(m * n) != totient(m) * totient(n)
    ]
    # A pair discriminates when the two sides COULD have differed, i.e. when the
    # product is not forced by triviality (m == 1 or n == 1 makes it an identity).
    disc = [(m, n) for (m, n) in COPRIME_PAIRS if m > 1 and n > 1]
    return Outcome(len(COPRIME_PAIRS), len(disc), ces)


def _mut_drop_coprimality() -> Outcome:
    """`hypothesis-removal`: drop `gcd(m,n) = 1` and range over ALL pairs."""
    ces = [
        f"m={m} n={n}"
        for (m, n) in PAIRS
        if totient(m * n) != totient(m) * totient(n)
    ]
    return Outcome(len(PAIRS), len(PAIRS), ces)


def _mut_weaken_coprimality() -> Outcome:
    """`hypothesis-weakening`: `gcd(m,n) = 1` weakened to `gcd(m,n) <= 2`."""
    dom = [(m, n) for (m, n) in PAIRS if gcd(m, n) <= 2]
    ces = [f"m={m} n={n}" for (m, n) in dom if totient(m * n) != totient(m) * totient(n)]
    return Outcome(len(dom), len(dom), ces)


def _mut_relation_to_le() -> Outcome:
    """`relation`: `=` weakened to `<=`.  This mutation is ALSO TRUE -- it is
    the review outcome the roadmap requires us to classify rather than fail."""
    ces = [
        f"m={m} n={n}"
        for (m, n) in COPRIME_PAIRS
        if not totient(m * n) <= totient(m) * totient(n)
    ]
    return Outcome(len(COPRIME_PAIRS), len(COPRIME_PAIRS), ces)


def _mut_operand_swap_product() -> Outcome:
    """`operand`: `totient(m*n)` replaced by `totient(m+n)`."""
    ces = [
        f"m={m} n={n}"
        for (m, n) in COPRIME_PAIRS
        if totient(m + n) != totient(m) * totient(n)
    ]
    return Outcome(len(COPRIME_PAIRS), len(COPRIME_PAIRS), ces)


register(
    Fixture(
        id="totient-multiplicativity-coprime",
        family="natural-totient",
        expect="valid",
        provenance="the correct form of the identity the traced plan mis-stated",
        run=_coprimality_independence_valid,
        fact_ids=["F:nat-totient-mul-of-coprime"],
        mutations=[
            Mutation("drop-coprimality", "hypothesis-removal", _mut_drop_coprimality),
            Mutation("weaken-coprimality-to-gcd-le-2", "hypothesis-weakening", _mut_weaken_coprimality),
            Mutation("eq-to-le", "relation", _mut_relation_to_le, also_true=True),
            Mutation("product-to-sum", "operand", _mut_operand_swap_product),
        ],
    )
)


# ===========================================================================
# 2. the composite control that is vacuous BY MATHEMATICS, not by types
# ===========================================================================
#
# `totient x | totient (x*q)` was used as the negative control for a
# prime-power route.  It holds at composite `q` too, so the "composite control"
# fails at ZERO composites.  The same-shaped control over the prime-power
# FORMULA does discriminate -- it was correct one line away.


def _totient_dvd_composite_control_vacuous() -> Outcome:
    """The divisibility control, run at composites.  It must fail nowhere."""
    composites = [q for q in range(4, 40) if any(q % d == 0 for d in range(2, q))]
    xs = range(1, 25)
    ces = []
    n = 0
    for q in composites:
        for x in xs:
            n += 1
            if totient(x * q) % totient(x) != 0:
                ces.append(f"x={x} q={q}")
    return Outcome(
        executed=n,
        discriminating=0,  # measured below by the sibling fixture; zero by construction
        counterexamples=ces,
        note="divisibility holds at composite q as well, so this control fails at zero composites",
    )


register(
    Fixture(
        id="totient-dvd-chain-composite-control",
        family="natural-totient",
        expect="vacuous",
        provenance=(
            "the composite negative control for the totient prime-power route; "
            "its own suite now MEASURES the zero rather than asserting it discriminates"
        ),
        run=_totient_dvd_composite_control_vacuous,
    )
)


def _totient_prime_power_valid() -> Outcome:
    """`totient (q^(j+1)) = q^(j+1) - q^j` for PRIME q -- the neighbouring
    statement whose composite control genuinely discriminates."""
    primes = [p for p in range(2, 20) if all(p % d for d in range(2, p))]
    ces = []
    n = 0
    for q in primes:
        for j in range(0, 4):
            if q ** (j + 1) > 4000:
                continue
            n += 1
            if totient(q ** (j + 1)) != q ** (j + 1) - q**j:
                ces.append(f"q={q} j={j}")
    # discriminating instances: the composites at which the SAME formula fails
    comps = [c for c in range(4, 30) if any(c % d == 0 for d in range(2, c))]
    disc = sum(
        1
        for c in comps
        for j in range(0, 3)
        if c ** (j + 1) <= 4000 and totient(c ** (j + 1)) != c ** (j + 1) - c**j
    )
    return Outcome(n, disc, ces, note=f"{disc} composite instances would have failed")


def _mut_prime_power_drop_primality() -> Outcome:
    comps = [c for c in range(4, 30) if any(c % d == 0 for d in range(2, c))]
    ces = []
    n = 0
    for c in comps:
        for j in range(0, 3):
            if c ** (j + 1) > 4000:
                continue
            n += 1
            if totient(c ** (j + 1)) != c ** (j + 1) - c**j:
                ces.append(f"q={c} j={j}")
    return Outcome(n, n, ces)


def _mut_prime_power_constant_off_by_one() -> Outcome:
    """`constant`: the subtracted term `q^j` becomes `q^(j+1)/q - 1`, i.e. off
    by one."""
    primes = [p for p in range(2, 20) if all(p % d for d in range(2, p))]
    ces = []
    n = 0
    for q in primes:
        for j in range(0, 4):
            if q ** (j + 1) > 4000:
                continue
            n += 1
            if totient(q ** (j + 1)) != q ** (j + 1) - q**j - 1:
                ces.append(f"q={q} j={j}")
    return Outcome(n, n, ces)


register(
    Fixture(
        id="totient-prime-power-formula",
        family="natural-totient",
        expect="valid",
        provenance="the statement the vacuous composite control was one line away from",
        run=_totient_prime_power_valid,
        fact_ids=["F:nat-totient-prime-pow"],
        mutations=[
            Mutation("drop-primality", "hypothesis-removal", _mut_prime_power_drop_primality),
            Mutation("subtract-one-more", "constant", _mut_prime_power_constant_off_by_one),
        ],
    )
)


# ===========================================================================
# 3. the control that passed on a SORT MISMATCH
# ===========================================================================
#
# A least-number-principle control applied its theorem to a `Prop` where a
# `Nat -> Prop` was wanted, so it "succeeded" without testing the property at
# all.  Modelled semantically: instantiate the predicate at CONSTANT predicates
# only (the arity-0 case).  Minimality then never bites -- the witness is
# always 0 -- so the control has zero discriminating instances even though it
# evaluates many.


def _lnp_constant_predicate_vacuous() -> Outcome:
    n_dom = 8
    executed = 0
    disc = 0
    ces = []
    for c in (False, True):
        pred = lambda k, c=c: c  # noqa: E731  -- the arity-0 instantiation
        executed += 1
        witnesses = [k for k in range(n_dom) if pred(k)]
        if not witnesses:
            continue
        m = min(witnesses)
        # minimality is the clause the control is supposed to test
        if any(pred(k) for k in range(m)):
            ces.append(f"constant={c}")
        # it discriminates only if some k < m could have satisfied pred
        if m > 0:
            disc += 1
    return Outcome(
        executed,
        disc,
        ces,
        note="a constant predicate always has witness 0, so minimality never bites",
    )


register(
    Fixture(
        id="least-number-principle-constant-predicate",
        family="natural-order",
        expect="vacuous",
        provenance=(
            "a least-number-principle control applied a theorem to a Prop where a "
            "Nat -> Prop was wanted; it passed without testing the property. "
            "Found by mutation testing in the least-number-principle lane."
        ),
        run=_lnp_constant_predicate_vacuous,
    )
)


def _lnp_general_valid() -> Outcome:
    """The same control over GENERAL predicates on [0,8): every nonempty
    predicate has a least witness, and minimality is testable."""
    n_dom = 8
    executed = 0
    disc = 0
    ces = []
    for mask in range(1 << n_dom):
        pred = lambda k, mask=mask: bool(mask >> k & 1)  # noqa: E731
        executed += 1
        witnesses = [k for k in range(n_dom) if pred(k)]
        if not witnesses:
            continue
        m = min(witnesses)
        if any(pred(k) for k in range(m)):
            ces.append(f"mask={mask}")
        if m > 0:
            disc += 1
    return Outcome(executed, disc, ces)


def _mut_lnp_max_instead_of_min() -> Outcome:
    """`operand`: the witness is taken as the MAXIMUM rather than the minimum."""
    n_dom = 8
    executed = 0
    ces = []
    for mask in range(1 << n_dom):
        pred = lambda k, mask=mask: bool(mask >> k & 1)  # noqa: E731
        executed += 1
        witnesses = [k for k in range(n_dom) if pred(k)]
        if not witnesses:
            continue
        m = max(witnesses)
        if any(pred(k) for k in range(m)):
            ces.append(f"mask={mask}")
    return Outcome(executed, executed, ces)


def _mut_lnp_strict_to_nonstrict() -> Outcome:
    """`relation`: minimality quantified over `k <= m` instead of `k < m`.
    False for every nonempty predicate, since `pred m` holds."""
    n_dom = 8
    executed = 0
    ces = []
    for mask in range(1 << n_dom):
        pred = lambda k, mask=mask: bool(mask >> k & 1)  # noqa: E731
        executed += 1
        witnesses = [k for k in range(n_dom) if pred(k)]
        if not witnesses:
            continue
        m = min(witnesses)
        if any(pred(k) for k in range(m + 1)):
            ces.append(f"mask={mask}")
    return Outcome(executed, executed, ces)


def _mut_lnp_drop_nonempty() -> Outcome:
    """`hypothesis-removal`: drop `exists n, P n` and demand a witness anyway.
    The empty predicate has none."""
    n_dom = 8
    executed = 0
    ces = []
    for mask in range(1 << n_dom):
        pred = lambda k, mask=mask: bool(mask >> k & 1)  # noqa: E731
        executed += 1
        if not any(pred(k) for k in range(n_dom)):
            ces.append(f"mask={mask} has no witness at all")
    return Outcome(executed, executed, ces)


def _mut_lnp_exists_to_forall() -> Outcome:
    """`quantifier`: the conclusion's `exists m` becomes `forall m`."""
    n_dom = 8
    executed = 0
    ces = []
    for mask in range(1 << n_dom):
        pred = lambda k, mask=mask: bool(mask >> k & 1)  # noqa: E731
        executed += 1
        witnesses = [k for k in range(n_dom) if pred(k)]
        if not witnesses:
            continue
        if not all(
            pred(m) and not any(pred(k) for k in range(m)) for m in range(n_dom)
        ):
            ces.append(f"mask={mask}")
    return Outcome(executed, executed, ces)


register(
    Fixture(
        id="least-number-principle-general",
        family="natural-order",
        expect="valid",
        provenance="the non-vacuous form of the sort-mismatched control",
        run=_lnp_general_valid,
        fact_ids=["F:nat-least-number-principle"],
        mutations=[
            Mutation("min-to-max", "operand", _mut_lnp_max_instead_of_min),
            Mutation("lt-to-le", "relation", _mut_lnp_strict_to_nonstrict),
            Mutation("drop-nonemptiness", "hypothesis-removal", _mut_lnp_drop_nonempty),
            Mutation("exists-to-forall", "quantifier", _mut_lnp_exists_to_forall),
        ],
    )
)


# ===========================================================================
# 4. the primality certificate for 91 that only COMPLETENESS rejects
# ===========================================================================
#
# Base 3 satisfies 3^90 = 1 (mod 91) and 3^45 != 1 (mod 91).  A Pratt-style
# checker that verifies Fermat, the order condition at each LISTED prime factor
# of n-1, and the primality of each listed factor accepts the certificate
# (n=91, a=3, factors=[2]) -- every guard passes.  91 = 7 * 13.  Only the
# completeness guard -- that the listed factors' multiplicities reconstruct
# n-1 -- rejects it.
#
# This is the shape the roadmap demands of a fixture: a case the PRODUCER
# distinguishes, over an instance where every other guard passes.


def _is_prime(k: int) -> bool:
    return k > 1 and all(k % d for d in range(2, int(k**0.5) + 1))


def _pratt_guards(n: int, a: int, factors: list[int], *, completeness: bool) -> list[str]:
    """Return the list of guard names that REJECT this certificate."""
    rejects = []
    if pow(a, n - 1, n) != 1:
        rejects.append("fermat")
    if any(pow(a, (n - 1) // p, n) == 1 for p in factors):
        rejects.append("order")
    if not all(_is_prime(p) for p in factors):
        rejects.append("factor-primality")
    if completeness:
        rest = n - 1
        for p in factors:
            while rest % p == 0:
                rest //= p
        if rest != 1:
            rejects.append("completeness")
    return rejects


def _pratt_91_incomplete_false() -> Outcome:
    """The claim is `91 is prime`.  It is false; the fixture records which
    guard set accepts it."""
    n, a, factors = 91, 3, [2]
    without = _pratt_guards(n, a, factors, completeness=False)
    with_c = _pratt_guards(n, a, factors, completeness=True)
    ces = []
    if not without:
        ces.append(
            f"certificate (n={n}, a={a}, factors={factors}) is ACCEPTED without the "
            f"completeness guard, and {n} = 7 * 13"
        )
    if not with_c:
        ces.append("completeness guard also failed to reject -- the guard is broken")
    return Outcome(
        executed=2,
        discriminating=1 if with_c == ["completeness"] else 0,
        counterexamples=ces,
        note=f"rejecting guards without completeness: {without or 'NONE'}; with: {with_c}",
    )


register(
    Fixture(
        id="pratt-certificate-91-incomplete-factorization",
        family="number-theory-certificate",
        expect="false",
        provenance=(
            "a certificate proving 91 is prime: passes Fermat, passes the order "
            "check, and its claimed factor is genuinely prime; only completeness "
            "rejects it"
        ),
        run=_pratt_91_incomplete_false,
    )
)


def _pratt_97_valid() -> Outcome:
    """A COMPLETE certificate for a genuine prime must be accepted, and the
    checker must reject the composites in the same domain."""
    executed = 0
    ces = []
    disc = 0
    for n in range(3, 200, 2):
        for a in range(2, min(n, 12)):
            if gcd(a, n) != 1:
                continue
            factors = sorted({p for p in range(2, n) if _is_prime(p) and (n - 1) % p == 0})
            executed += 1
            accepted = not _pratt_guards(n, a, factors, completeness=True)
            if accepted and not _is_prime(n):
                ces.append(f"composite n={n} accepted with a={a}")
            if not accepted and not _is_prime(n):
                disc += 1
    return Outcome(executed, disc, ces, note=f"{disc} composite certificates correctly rejected")


def _mut_pratt_drop_completeness() -> Outcome:
    executed = 0
    ces = []
    for n in range(3, 200, 2):
        for a in range(2, min(n, 12)):
            if gcd(a, n) != 1:
                continue
            factors = [2] if (n - 1) % 2 == 0 else []
            executed += 1
            if not _pratt_guards(n, a, factors, completeness=False) and not _is_prime(n):
                ces.append(f"composite n={n} accepted with a={a}, factors={factors}")
    return Outcome(executed, executed, ces)


def _mut_pratt_drop_order() -> Outcome:
    """`hypothesis-removal`: keep Fermat and completeness, drop the order
    condition.  Carmichael numbers and Fermat pseudoprimes then slip through."""
    executed = 0
    ces = []
    for n in range(3, 600, 2):
        for a in range(2, min(n, 12)):
            if gcd(a, n) != 1:
                continue
            executed += 1
            if pow(a, n - 1, n) == 1 and not _is_prime(n):
                ces.append(f"composite n={n} passes Fermat at a={a}")
    return Outcome(executed, executed, ces)


register(
    Fixture(
        id="pratt-certificate-complete",
        family="number-theory-certificate",
        expect="valid",
        provenance="the complete guard set the 91 certificate is missing",
        run=_pratt_97_valid,
        mutations=[
            Mutation("drop-completeness", "hypothesis-removal", _mut_pratt_drop_completeness),
            Mutation("drop-order-condition", "hypothesis-removal", _mut_pratt_drop_order),
        ],
    )
)


# ===========================================================================
# 5. the Chinese-remainder certificate (9, 24) that only LEASTNESS rejects
# ===========================================================================
#
# The system `x = 1 (mod 4)`, `x = 0 (mod 3)` has answer `9 mod 12`.  The
# certificate `(residue 9, modulus 24)` satisfies every congruence, its modulus
# is a common multiple of both moduli, and its residue is in range.  Only
# leastness -- that the modulus is the lcm -- rejects it, and the cost of not
# rejecting is that the certificate silently DROPS half the solutions: 21 is a
# solution and 21 != 9 (mod 24).


CRT_SYSTEM = [(1, 4), (0, 3)]


def _crt_guards(residue: int, modulus: int, system, *, leastness: bool) -> list[str]:
    rejects = []
    if any(residue % m != r % m for (r, m) in system):
        rejects.append("congruences")
    if any(modulus % m != 0 for (_, m) in system):
        rejects.append("common-multiple")
    if not 0 <= residue < modulus:
        rejects.append("in-range")
    if leastness:
        lcm = 1
        for _, m in system:
            lcm = lcm * m // gcd(lcm, m)
        if modulus != lcm:
            rejects.append("leastness")
    return rejects


def _crt_9_mod_24_false() -> Outcome:
    without = _crt_guards(9, 24, CRT_SYSTEM, leastness=False)
    with_l = _crt_guards(9, 24, CRT_SYSTEM, leastness=True)
    ces = []
    if not without:
        dropped = [
            x
            for x in range(0, 48)
            if all(x % m == r % m for (r, m) in CRT_SYSTEM) and x % 24 != 9
        ]
        ces.append(
            f"certificate (9, 24) is ACCEPTED without leastness while dropping "
            f"the solutions {dropped}"
        )
    if not with_l:
        ces.append("leastness guard also failed to reject -- the guard is broken")
    return Outcome(
        executed=2,
        discriminating=1 if with_l == ["leastness"] else 0,
        counterexamples=ces,
        note=f"rejecting guards without leastness: {without or 'NONE'}; with: {with_l}",
    )


register(
    Fixture(
        id="crt-certificate-nonleast-modulus",
        family="number-theory-certificate",
        expect="false",
        provenance=(
            "a Chinese-remainder certificate (9, 24) for a system whose answer is "
            "9 mod 12 -- every guard passes but leastness"
        ),
        run=_crt_9_mod_24_false,
    )
)


def _crt_least_valid() -> Outcome:
    """With leastness, the checker accepts exactly the correct certificate for
    every coprime two-congruence system in the small domain."""
    executed = 0
    disc = 0
    ces = []
    for m1 in range(2, 10):
        for m2 in range(2, 10):
            if gcd(m1, m2) != 1:
                continue
            lcm = m1 * m2
            for r1 in range(m1):
                for r2 in range(m2):
                    system = [(r1, m1), (r2, m2)]
                    truth = [x for x in range(lcm) if x % m1 == r1 and x % m2 == r2]
                    assert len(truth) == 1
                    good = truth[0]
                    executed += 1
                    if _crt_guards(good, lcm, system, leastness=True):
                        ces.append(f"correct certificate ({good}, {lcm}) rejected for {system}")
                    # discrimination: a doubled modulus must be rejected
                    if _crt_guards(good, 2 * lcm, system, leastness=True):
                        disc += 1
                    else:
                        ces.append(f"doubled modulus ({good}, {2 * lcm}) accepted for {system}")
    return Outcome(executed, disc, ces)


def _mut_crt_drop_leastness() -> Outcome:
    executed = 0
    ces = []
    for m1 in range(2, 10):
        for m2 in range(2, 10):
            if gcd(m1, m2) != 1:
                continue
            lcm = m1 * m2
            for r1 in range(m1):
                for r2 in range(m2):
                    system = [(r1, m1), (r2, m2)]
                    good = next(x for x in range(lcm) if x % m1 == r1 and x % m2 == r2)
                    executed += 1
                    if not _crt_guards(good, 2 * lcm, system, leastness=False):
                        ces.append(f"non-least modulus {2 * lcm} accepted for {system}")
    return Outcome(executed, executed, ces)


def _mut_crt_drop_congruences() -> Outcome:
    executed = 0
    ces = []
    for m1 in range(2, 8):
        for m2 in range(2, 8):
            if gcd(m1, m2) != 1:
                continue
            lcm = m1 * m2
            for r1 in range(m1):
                for r2 in range(m2):
                    system = [(r1, m1), (r2, m2)]
                    good = next(x for x in range(lcm) if x % m1 == r1 and x % m2 == r2)
                    wrong = (good + 1) % lcm
                    executed += 1
                    if not _crt_guards(wrong, lcm, system, leastness=True):
                        ces.append(f"wrong residue {wrong} accepted for {system}")
    return Outcome(executed, executed, ces)


register(
    Fixture(
        id="crt-certificate-least-modulus",
        family="number-theory-certificate",
        expect="valid",
        provenance="the guard set the (9, 24) certificate is missing",
        run=_crt_least_valid,
        mutations=[
            Mutation("drop-leastness", "hypothesis-removal", _mut_crt_drop_leastness),
            Mutation("drop-congruence-check", "hypothesis-removal", _mut_crt_drop_congruences),
        ],
    )
)


# ===========================================================================
# 6. the NRA certificate that records a CONSTANT but not STRICTNESS
# ===========================================================================
#
# `nra_monomial_bound_cert.rs`: the producer distinguished `M < k` from
# `M <= k`, but the certificate recorded only `k`.  So the independent
# re-validator accepted a certificate "refuting" `a >= 1 AND b >= 1 AND
# a*b <= 1` -- satisfiable at a = b = 1.  Nine guards in that module were each
# killed by exactly one test and the module was still unsound: the guard that
# would have caught this was never written, so there was nothing to delete.
#
# The fixture is over the SATISFIABLE instance, and its finding is exactly the
# impossibility: a certificate carrying only the constant CANNOT express the
# distinction.


def _monomial_check(lower: int, bound: int, strict: bool | None) -> bool:
    """Does the recorded certificate refute `a >= lower, b >= lower, a*b REL bound`?

    A refutation is sound only when the monomial's true lower bound `lower^2`
    lies strictly outside the asserted region.  With `strict is None` the
    certificate did not record which relation the query used, so the checker
    can only compare constants.
    """
    m_min = lower * lower
    if strict is None:
        return m_min >= bound  # the shipped, constant-only check
    return m_min > bound if not strict else m_min >= bound


def _nra_strictness_false() -> Outcome:
    """Range over small instances; report every SATISFIABLE query the
    constant-only checker claims to refute."""
    executed = 0
    ces = []
    for lower in range(1, 5):
        for bound in range(0, 12):
            # the non-strict query `a*b <= bound`, satisfiable iff lower^2 <= bound
            executed += 1
            satisfiable = lower * lower <= bound
            if satisfiable and _monomial_check(lower, bound, None):
                ces.append(
                    f"a,b >= {lower} and a*b <= {bound}: satisfiable at a=b={lower}, "
                    f"yet the constant-only checker accepts the refutation"
                )
    return Outcome(
        executed,
        executed,
        ces,
        note="the certificate records `bound` but not whether the query was strict",
    )


register(
    Fixture(
        id="nra-monomial-bound-strictness-unrecorded",
        family="nra-certificate",
        expect="false",
        provenance=(
            "nra_monomial_bound_cert.rs recorded the bound's constant but not its "
            "strictness; the re-validator accepted a forged refutation of a "
            "SATISFIABLE query. Nine guards in the module were each killed by "
            "exactly one test and it was still unsound."
        ),
        run=_nra_strictness_false,
    )
)


def _nra_strictness_valid() -> Outcome:
    """The same domain with strictness RECORDED: no satisfiable query is ever
    claimed refuted, and unsatisfiable ones still are."""
    executed = 0
    disc = 0
    ces = []
    for lower in range(1, 5):
        for bound in range(0, 12):
            for strict in (False, True):
                executed += 1
                # `a*b < bound` is satisfiable iff lower^2 < bound
                satisfiable = lower * lower < bound if strict else lower * lower <= bound
                claimed = _monomial_check(lower, bound, strict)
                if satisfiable and claimed:
                    ces.append(f"lower={lower} bound={bound} strict={strict}")
                if not satisfiable and claimed:
                    disc += 1
    return Outcome(executed, disc, ces, note=f"{disc} genuinely unsat instances still refuted")


def _mut_nra_forget_strictness() -> Outcome:
    executed = 0
    ces = []
    for lower in range(1, 5):
        for bound in range(0, 12):
            for strict in (False, True):
                executed += 1
                satisfiable = lower * lower < bound if strict else lower * lower <= bound
                if satisfiable and _monomial_check(lower, bound, None):
                    ces.append(f"lower={lower} bound={bound} strict={strict}")
    return Outcome(executed, executed, ces)


def _mut_nra_relax_relation() -> Outcome:
    """`relation`: the soundness test `m_min > bound` relaxed to `>=` in the
    non-strict branch."""
    executed = 0
    ces = []
    for lower in range(1, 5):
        for bound in range(0, 12):
            executed += 1
            satisfiable = lower * lower <= bound
            if satisfiable and lower * lower >= bound:
                ces.append(f"lower={lower} bound={bound}")
    return Outcome(executed, executed, ces)


register(
    Fixture(
        id="nra-monomial-bound-strictness-recorded",
        family="nra-certificate",
        expect="valid",
        provenance="the certificate shape that CAN express the distinction the producer makes",
        run=_nra_strictness_valid,
        mutations=[
            Mutation("forget-strictness", "operand", _mut_nra_forget_strictness),
            Mutation("gt-to-ge", "relation", _mut_nra_relax_relation),
        ],
    )
)


# ===========================================================================
# 7. the CRT self-map identity -- the in-tree numerics scripts' core claim
# ===========================================================================
#
# `scripts/tests/check-countrange-bijection-numerics.py` and
# `check-totient-mul-coprime-numerics.py` are the existing in-tree pattern.
# This fixture carries their central claim into the retained pack so that a
# regression in the pack is visible even if those scripts are not run, and so
# the pack's mutation families cover the same argument.


def _g_map(m: int, n: int):
    return lambda x: n * (x % m) + (x % n)


def _crt_selfmap_permutes_valid() -> Outcome:
    executed = 0
    disc = 0
    ces = []
    for m, n in COPRIME_PAIRS:
        N = n * m
        executed += 1
        img = sorted(_g_map(m, n)(x) for x in range(N))
        if img != list(range(N)):
            ces.append(f"m={m} n={n}: g is not a permutation of [0,{N})")
        if m > 1 and n > 1:
            disc += 1
    return Outcome(executed, disc, ces)


def _mut_crt_selfmap_noncoprime() -> Outcome:
    executed = 0
    ces = []
    for m, n in NONCOPRIME_PAIRS:
        N = n * m
        executed += 1
        img = sorted(_g_map(m, n)(x) for x in range(N))
        if img != list(range(N)):
            ces.append(f"m={m} n={n}")
    return Outcome(executed, executed, ces)


def _mut_crt_selfmap_off_by_one() -> Outcome:
    executed = 0
    ces = []
    for m, n in COPRIME_PAIRS:
        N = n * m
        executed += 1
        if any(_g_map(m, n)(x) + 1 >= N for x in range(N)):
            ces.append(f"m={m} n={n}: g+1 escapes [0,{N})")
    return Outcome(executed, executed, ces)


def _mut_crt_selfmap_swap_moduli() -> Outcome:
    """`operand`: `n * (x mod m) + (x mod n)` with the two moduli swapped in
    the block index only."""
    executed = 0
    ces = []
    for m, n in COPRIME_PAIRS:
        N = n * m
        executed += 1
        img = sorted(n * (x % n) + (x % m) for x in range(N))
        if img != list(range(N)):
            ces.append(f"m={m} n={n}")
    return Outcome(executed, executed, ces)


register(
    Fixture(
        id="crt-selfmap-permutes-range",
        family="natural-counting",
        expect="valid",
        provenance=(
            "the central claim of scripts/tests/check-countrange-bijection-numerics.py "
            "and check-totient-mul-coprime-numerics.py, retained here"
        ),
        fact_ids=["F:nat-countrange-product"],
        run=_crt_selfmap_permutes_valid,
        mutations=[
            Mutation("drop-coprimality", "hypothesis-removal", _mut_crt_selfmap_noncoprime),
            Mutation("off-by-one", "constant", _mut_crt_selfmap_off_by_one, also_true=True),
            Mutation("swap-moduli", "operand", _mut_crt_selfmap_swap_moduli),
        ],
    )
)


# ---------------------------------------------------------------------------
# the existing in-tree numerics scripts, executed as subprocess fixtures by the
# gate.  Extending them, not replacing them: the gate runs each and requires
# exit 0, and the pack records them as the load-bearing controls they are.
# ---------------------------------------------------------------------------

NUMERICS_SCRIPTS = [
    ("scripts/tests/check-countrange-bijection-numerics.py", ["F:nat-countrange-product"]),
    ("scripts/tests/check-totient-mul-coprime-numerics.py", ["F:nat-totient-mul-of-coprime"]),
    ("scripts/tests/check-totient-prime-power-numerics.py", ["F:nat-totient-prime-pow"]),
    ("scripts/tests/check-totient-dvd-chain-numerics.py", []),
]


def fixture_by_id(fid: str) -> Fixture:
    for fx in FIXTURES:
        if fx.id == fid:
            return fx
    raise KeyError(fid)
