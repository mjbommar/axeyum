#!/usr/bin/env python3
"""Numeric checks behind ADR-1557 (lane `quadratic-reciprocity-2`).

Six claims (C1-C6) and eight controls (K1-K8). **The exit status depends on
the finding**: a claim that fails, or a control that behaves other than as
recorded here, exits 1. Three controls are recorded SURVIVORS -- printed as
survivors, not failures, because the ADR records them as things no numeric
check can see.

Everything is recomputed from the kernel definitions, not from any prior
document and not from the Rust tests:

    leastResidue  pp a k = (a*k) mod pp
    gaussSignNeg  pp a k = (pp // 2) < leastResidue pp a k
    gaussNegCount pp a m = #{ 1 <= k <= m : sign }
    legendreSym   m a    = (-1)^(gaussNegCount (2m+1) a m)
"""

from __future__ import annotations

import sys
from math import gcd

FAILURES: list[str] = []
SURVIVORS: list[str] = []


def record(ok: bool, label: str, detail: str = "") -> None:
    if ok:
        print(f"  ok   {label} {detail}")
    else:
        print(f"  FAIL {label} {detail}")
        FAILURES.append(label)


def survivor(label: str, detail: str) -> None:
    print(f"  SURVIVOR {label} {detail}")
    SURVIVORS.append(label)


# --- the kernel definitions, recomputed --------------------------------------


def sign_neg(pp: int, a: int, k: int) -> bool:
    return pp // 2 < (a * k) % pp


def neg_count(pp: int, a: int, m: int) -> int:
    return sum(1 for k in range(1, m + 1) if sign_neg(pp, a, k))


def legendre(m: int, a: int) -> int:
    return (-1) ** neg_count(2 * m + 1, a, m)


def row_sum(pp: int, q: int, m: int) -> int:
    """`Sigma_{x<m} floor(q*(x+1)/pp)` -- the min-free floor sum."""
    return sum((q * (x + 1)) // pp for x in range(m))


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


BOUND = 24
COPRIME_PAIRS = [
    (m, n)
    for m in range(1, BOUND)
    for n in range(1, BOUND)
    if gcd(2 * m + 1, 2 * n + 1) == 1
]
ODD_PRIMES = [p for p in range(3, 60, 2) if is_prime(p)]
PRIME_PAIRS = [(p, q) for p in ODD_PRIMES for q in ODD_PRIMES if p != q]


# --- claims ------------------------------------------------------------------


def c1() -> None:
    """`Nat.eisenstein_floor_sum_min_free`: F_p + F_q = n*m."""
    bad = [
        (m, n)
        for (m, n) in COPRIME_PAIRS
        if row_sum(2 * m + 1, 2 * n + 1, m) + row_sum(2 * n + 1, 2 * m + 1, n) != n * m
    ]
    record(
        not bad,
        "C1",
        f"the min-free floor identity holds at all {len(COPRIME_PAIRS)} coprime (m,n) below {BOUND}",
    )


def c2() -> None:
    """`Nat.eisenstein_lemma`, in both orientations."""
    bad = []
    for m, n in COPRIME_PAIRS:
        pp, q = 2 * m + 1, 2 * n + 1
        if (row_sum(pp, q, m) + neg_count(pp, q, m)) % 2 != 0:
            bad.append((m, n, "p"))
        if (row_sum(q, pp, n) + neg_count(q, pp, n)) % 2 != 0:
            bad.append((m, n, "q"))
    record(not bad, "C2", f"Even (F + N) at both orientations of all {len(COPRIME_PAIRS)} pairs")


def c3() -> None:
    """`Nat.gaussCount_sum_even`: Even ((N_p + N_q) + n*m)."""
    bad = [
        (m, n)
        for (m, n) in COPRIME_PAIRS
        if (neg_count(2 * m + 1, 2 * n + 1, m) + neg_count(2 * n + 1, 2 * m + 1, n) + n * m)
        % 2
        != 0
    ]
    record(not bad, "C3", f"the parity statement holds at all {len(COPRIME_PAIRS)} coprime pairs")
    # And it is not vacuous: the sum is genuinely nonzero somewhere.
    nonzero = sum(
        1
        for (m, n) in COPRIME_PAIRS
        if neg_count(2 * m + 1, 2 * n + 1, m) + neg_count(2 * n + 1, 2 * m + 1, n) > 0
    )
    record(nonzero > 0, "C3b", f"and the count sum is nonzero at {nonzero} of them")


def c4() -> None:
    """`Nat.gaussCount_sum_modEq`, in `Nat.modEq`'s BALANCED form.

    `modEq d a b := exists u v, a + d*u = b + d*v`, and the declaration's
    witnesses are `u := n*m` and `v := k` where `S + T = k + k`.
    """
    bad = []
    for m, n in COPRIME_PAIRS:
        s = neg_count(2 * m + 1, 2 * n + 1, m) + neg_count(2 * n + 1, 2 * m + 1, n)
        t = n * m
        if (s - t) % 2 != 0:
            bad.append((m, n))
            continue
        k, u, v = (s + t) // 2, t, (s + t) // 2
        if s + 2 * u != t + 2 * v:
            bad.append((m, n, "witness"))
        if s + t != k + k:
            bad.append((m, n, "even"))
    record(not bad, "C4", f"the balanced witnesses u := n*m, v := k work at all {len(COPRIME_PAIRS)} pairs")


def c5() -> None:
    """`Int.quadraticReciprocity`, and that it IS the classical law."""
    bad = []
    for p, q in PRIME_PAIRS:
        m, n = (p - 1) // 2, (q - 1) // 2
        lhs = legendre(m, q) * legendre(n, p)
        rhs = (-1) ** (n * m)
        classical = -1 if (p % 4 == 3 and q % 4 == 3) else 1
        if lhs != rhs or lhs != classical:
            bad.append((p, q, lhs, rhs, classical))
    record(
        not bad,
        "C5",
        f"the law holds, and equals the `both 3 mod 4` reading, at all {len(PRIME_PAIRS)} ordered pairs of distinct odd primes below 60",
    )
    minus = sum(1 for p, q in PRIME_PAIRS if p % 4 == 3 and q % 4 == 3)
    record(minus > 0, "C5b", f"and {minus} of those are the -1 case, so C5 is not one-sided")
    # The general (coprime, not necessarily prime) form the kernel states.
    bad2 = [
        (m, n)
        for (m, n) in COPRIME_PAIRS
        if legendre(m, 2 * n + 1) * legendre(n, 2 * m + 1) != (-1) ** (n * m)
    ]
    record(
        not bad2,
        "C5c",
        f"and the COPRIME-only generalization the kernel actually states holds at all {len(COPRIME_PAIRS)} pairs",
    )


def c6() -> None:
    """`Int.legendreSym_modEq_pow`: a^m == legendreSym m a (mod 2m+1)."""
    bad = []
    checked = 0
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        for a in range(1, 3 * p):
            if gcd(a, p) != 1:
                continue
            checked += 1
            if pow(a, m, p) != legendre(m, a) % p:
                bad.append((p, a))
    record(not bad, "C6", f"Euler's criterion for this symbol at {checked} (prime, coprime a) instances")


# --- controls ----------------------------------------------------------------


def controls() -> None:
    # K1: coprimality is load-bearing -- the refuting witness.
    m = n = 1
    s = neg_count(3, 3, m) + neg_count(3, 3, n)
    record(
        (s + n * m) % 2 == 1 and s == 0 and n * m == 1,
        "K1",
        "REFUTED: at pp = q = 3 (gcd 3) the parity statement gives S + T = 1, which is odd",
    )
    record(
        legendre(1, 3) * legendre(1, 3) != (-1) ** 1,
        "K1b",
        "REFUTED: and the law itself gives +1 against -1 there",
    )

    # K2: SURVIVOR -- the OTHER obvious non-coprime witness does not separate.
    s2 = neg_count(5, 5, 2) + neg_count(5, 5, 2)
    if (s2 + 2 * 2) % 2 == 0 and legendre(2, 5) * legendre(2, 5) == (-1) ** 4:
        survivor(
            "K2",
            "at pp = q = 5 (gcd 5) BOTH statements are still true, so a "
            "non-coprime control drawn there passes while checking nothing -- "
            "derive the witness from the statement, never from a neighbour",
        )
    else:
        record(False, "K2", "the recorded survivor no longer survives; re-derive it")

    # K3: transposing gaussNegCount's modulus and multiplier breaks it.
    bad = [
        (m, n)
        for (m, n) in COPRIME_PAIRS
        if (neg_count(2 * n + 1, 2 * m + 1, m) + neg_count(2 * n + 1, 2 * m + 1, n) + n * m)
        % 2
        != 0
    ]
    record(
        bool(bad),
        f"K3",
        f"REFUTED: transposing the first count's modulus and multiplier fails at {len(bad)} of {len(COPRIME_PAIRS)} pairs, e.g. {bad[0] if bad else None}",
    )

    # K4: SURVIVOR -- `mul n m` against `mul m n`.
    survivor(
        "K4",
        "n*m and m*n are equal as numbers and DIFFERENT as kernel terms (Nat.mul "
        "recurses on its right argument, so they are not definitionally equal at "
        "symbolic arguments). No numeric check can separate them; the kernel "
        "REJECTS the transposed statement, and the character-for-character type "
        "pins record which one is declared",
    )

    # K5: SURVIVOR -- swapping N_p and N_q inside the sum.
    survivor(
        "K5",
        "N_p + N_q and N_q + N_p: the same number at every instance. Which one "
        "is declared is visible only in the type pins",
    )

    # K6: the brief this lane worked from predicted the wrong sign twice.
    record(
        legendre(1, 5) * legendre(2, 3) == 1 and legendre(2, 7) * legendre(3, 5) == 1,
        "K6",
        "REFUTED: (3,5) and (5,7) are +1, not -1 -- the product is -1 only when "
        "BOTH primes are 3 mod 4, and 5 is 1 mod 4",
    )
    record(
        legendre(1, 7) * legendre(3, 3) == -1,
        "K6b",
        "and (3,7) IS the -1 case, so the sign is not constant",
    )

    # K7: base +1 instead of -1 in the symbol collapses the law.
    def bad_legendre(m: int, a: int) -> int:
        return 1 ** neg_count(2 * m + 1, a, m)

    broken = [
        (p, q)
        for (p, q) in PRIME_PAIRS
        if bad_legendre((p - 1) // 2, q) * bad_legendre((q - 1) // 2, p)
        != (-1) ** (((q - 1) // 2) * ((p - 1) // 2))
    ]
    record(
        bool(broken),
        "K7",
        f"REFUTED: a symbol with base +1 breaks the law at {len(broken)} of {len(PRIME_PAIRS)} prime pairs",
    )

    # K8: the congruence is NOT an equality.
    unequal = [
        (m, n)
        for (m, n) in COPRIME_PAIRS
        if neg_count(2 * m + 1, 2 * n + 1, m) + neg_count(2 * n + 1, 2 * m + 1, n) != n * m
    ]
    record(
        bool(unequal),
        "K8",
        f"REFUTED: dropping the `mod 2` is false at {len(unequal)} of {len(COPRIME_PAIRS)} pairs, e.g. {unequal[0] if unequal else None}",
    )


def main() -> int:
    print("ADR-1557 numeric checks (lane quadratic-reciprocity-2)")
    c1()
    c2()
    c3()
    c4()
    c5()
    c6()
    controls()
    print()
    print(f"claims/controls failed: {len(FAILURES)}")
    print(f"recorded survivors:     {len(SURVIVORS)} ({', '.join(SURVIVORS)})")
    if FAILURES:
        print("RESULT: FAIL -- " + ", ".join(FAILURES))
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
