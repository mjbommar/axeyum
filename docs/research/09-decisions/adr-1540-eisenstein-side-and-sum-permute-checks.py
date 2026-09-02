#!/usr/bin/env python3
"""Numeric verification for ADR-1540.

Five claims (C1-C5) and seven controls (M1-M7). **The exit status depends on
the finding**: a claim that fails, or a control that behaves other than as
recorded, exits 1. One control is recorded as a deliberate SURVIVOR and is
asserted to survive; if it ever starts failing, that is also an exit 1, because
the reason it survives is a fact about the statement.

Run it:

    python3 docs/research/09-decisions/adr-1540-eisenstein-side-and-sum-permute-checks.py

Nothing here is a proof. The kernel theorems are the proofs; this script exists
so the ADR's arithmetic claims are re-runnable rather than asserted, and so the
two false readings the declared types are pinned against are shown to be false
at named witnesses rather than merely described as false.
"""

from __future__ import annotations

import math
import sys
from itertools import permutations

FAILURES: list[str] = []


def claim(name: str, ok: bool, detail: str) -> None:
    print(f"  {'ok  ' if ok else 'FAIL'} {name}: {detail}")
    if not ok:
        FAILURES.append(name)


def control(name: str, refuted: bool, detail: str) -> None:
    """A control must be REFUTED (a counterexample exists)."""
    print(f"  {'ok  ' if refuted else 'FAIL'} {name} refuted: {detail}")
    if not refuted:
        FAILURES.append(f"{name} SURVIVED but is not recorded as a survivor")


def survivor(name: str, survived: bool, detail: str) -> None:
    """A control recorded as DELIBERATELY surviving. It must survive."""
    print(f"  {'ok  ' if survived else 'FAIL'} {name} survived (as recorded): {detail}")
    if not survived:
        FAILURES.append(f"{name} was refuted but is recorded as a survivor")


def primes_below(limit: int) -> list[int]:
    return [n for n in range(2, limit) if all(n % d for d in range(2, int(n**0.5) + 1))]


# ---------------------------------------------------------------------------
# C1 -- Nat.mul_ne_mul_of_coprime_of_lt
#   gcd p q = 1, 0 < x < p  =>  p*y != q*x
# ---------------------------------------------------------------------------
print("C1  the side condition, over all coprime (p,q) with p,q <= 40")
pairs = 0
witnesses = 0
bad: list[tuple[int, int, int, int]] = []
for p in range(1, 41):
    for q in range(1, 41):
        if math.gcd(p, q) != 1:
            continue
        pairs += 1
        for x in range(1, p):
            for y in range(0, 41):
                witnesses += 1
                if p * y == q * x:
                    bad.append((p, q, x, y))
claim(
    "C1",
    not bad,
    f"{pairs} coprime pairs, {witnesses} (x,y) witnesses, {len(bad)} violations",
)

# ---------------------------------------------------------------------------
# C2 -- Nat.mul_succ_ne_mul_succ_of_coprime, the 1-based corollary.
#   gcd p q = 1, succ x < p  =>  p*(y+1) != q*(x+1)
# The positivity hypothesis is discharged by the succ shape, so this is C1 with
# x, y shifted -- checked separately because the SHIFT is where an off-by-one
# in the corollary would live.
# ---------------------------------------------------------------------------
print("C2  the 1-based corollary")
bad2 = [
    (p, q, x, y)
    for p in range(1, 41)
    for q in range(1, 41)
    if math.gcd(p, q) == 1
    for x in range(0, p - 1)
    for y in range(0, 41)
    if p * (y + 1) == q * (x + 1)
]
claim("C2", not bad2, f"{len(bad2)} violations over the same (p,q) sweep")

# ---------------------------------------------------------------------------
# C3 -- the consequence the rectangle partition needs.
# For distinct odd primes p, q with m = (p-1)/2, n = (q-1)/2, EXACTLY ONE of
# p*(y+1) < q*(x+1) and q*(x+1) < p*(y+1) holds at every lattice point of
# [0,m) x [0,n). That "exactly one" is precisely
# Nat.countRectangle_partition's per-point hypothesis (ADR-1260), and the side
# condition is the only thing standing between the two STRICT predicates and it.
# ---------------------------------------------------------------------------
print("C3  the two strict half-plane predicates are complementary")
odd_primes = [r for r in primes_below(60) if r != 2]
points = 0
ties = 0
for p in odd_primes:
    for q in odd_primes:
        if p == q:
            continue
        m, n = (p - 1) // 2, (q - 1) // 2
        for x in range(m):
            for y in range(n):
                points += 1
                lhs, rhs = p * (y + 1), q * (x + 1)
                sel = int(lhs < rhs) + int(rhs < lhs)
                if sel != 1:
                    ties += 1
claim(
    "C3",
    ties == 0,
    f"{len(odd_primes)} odd primes, {points} lattice points, {ties} on the line",
)

# ---------------------------------------------------------------------------
# C4 -- Nat.sumRange_point_change
#   a, b agree on [0,n) except possibly at i0  =>
#   sum a + b i0 = sum b + a i0
# ---------------------------------------------------------------------------
print("C4  the point-change law")


def total(fn, n: int) -> int:
    return sum(fn(k) for k in range(n))


bad4 = 0
cases4 = 0
for n in range(1, 9):
    for i0 in range(n):
        for delta in (0, 1, 3, 7):
            a = lambda k, i0=i0, delta=delta: k * k + (delta if k == i0 else 0)
            b = lambda k: k * k
            cases4 += 1
            if total(a, n) + b(i0) != total(b, n) + a(i0):
                bad4 += 1
claim("C4", bad4 == 0, f"{cases4} (n, i0, delta) cases, {bad4} violations")

# ---------------------------------------------------------------------------
# C5 -- Nat.sumRange_permute
#   sigma an injective self-map of [0,n)  =>  sum f = sum (f . sigma)
# Checked over EVERY permutation of [0,n) for n <= 6, not a sample: the theorem
# quantifies over all of them and a sampled check could miss the one that
# breaks.
# ---------------------------------------------------------------------------
print("C5  the permutation law, over every permutation of [0,n) for n <= 6")
bad5 = 0
perms = 0
f5 = lambda k: k * k + 3 * k + 1
for n in range(0, 7):
    for sigma in permutations(range(n)):
        perms += 1
        if total(f5, n) != sum(f5(sigma[k]) for k in range(n)):
            bad5 += 1
claim("C5", bad5 == 0, f"{perms} permutations, {bad5} violations")

# ---------------------------------------------------------------------------
# Controls.
# ---------------------------------------------------------------------------
print("\ncontrols")

# M1 -- drop `x < p`. The theorem is then FALSE, and 3*5 = 5*3 is the witness
# the declared type is pinned against.
m1 = [
    (p, q, x, y)
    for p in range(1, 12)
    for q in range(1, 12)
    if math.gcd(p, q) == 1
    for x in range(1, 12)
    for y in range(0, 12)
    if p * y == q * x and not x < p
]
control(
    "M1 (drop x < p)",
    (3, 5, 3, 5) in m1,
    f"{len(m1)} counterexamples including the named witness 3*5 = 5*3",
)

# M2 -- bound the WRONG index: `0 < y < p` instead of `0 < x < p`. Also false,
# and the witness is the MIRROR of M1's: (p,q,x,y) = (5,3,5,3), where
# 5*3 = 3*5 with gcd 5 3 = 1 and 0 < y = 3 < 5 = p. The intended theorem does
# not reach it (x = 5 is not below p = 5); the transposed one does, and is
# refuted there. `p*y = q*x` forces `p | x`, never `p | y`, which is why the
# asymmetry is real rather than cosmetic.
m2 = [
    (p, q, x, y)
    for p in range(1, 12)
    for q in range(1, 12)
    if math.gcd(p, q) == 1
    for x in range(1, 12)
    for y in range(1, 12)
    if p * y == q * x and y < p
]
control(
    "M2 (bound y instead of x)",
    (5, 3, 5, 3) in m2,
    f"{len(m2)} counterexamples including the named witness (p,q,x,y) = (5,3,5,3)",
)

# M3 -- drop coprimality. False at (4,6,2,3): 4*3 = 6*2 with 0 < 2 < 4.
m3 = [
    (p, q, x, y)
    for p in range(1, 12)
    for q in range(1, 12)
    if math.gcd(p, q) != 1
    for x in range(1, p)
    for y in range(0, 12)
    if p * y == q * x
]
control(
    "M3 (drop gcd p q = 1)",
    (4, 6, 2, 3) in m3,
    f"{len(m3)} counterexamples including the named witness 4*3 = 6*2, 0 < 2 < 4",
)

# M4 -- drop InjectiveOn in the permutation law. sigma k := 0 maps [0,n) into
# itself and is not injective; at f k = k*k, n = 3 the two sides are 5 and 0.
lhs4 = total(lambda k: k * k, 3)
rhs4 = sum((0 * 0) for _ in range(3))
control("M4 (drop InjectiveOn)", lhs4 != rhs4, f"sigma k := 0 gives {lhs4} against {rhs4}")

# M5 -- drop MapsInto. sigma k := k+1 IS injective and maps out of [0,n); at
# f k = k*k, n = 3 the two sides are 5 and 14.
lhs5 = total(lambda k: k * k, 3)
rhs5 = sum((k + 1) * (k + 1) for k in range(3))
control("M5 (drop MapsInto)", lhs5 != rhs5, f"sigma k := k+1 gives {lhs5} against {rhs5}")

# M6 -- SURVIVOR, deliberately. Swapping `a` and `b` throughout
# `sumRange_point_change` leaves a TRUE statement: the equation
# `sum a + b i0 = sum b + a i0` is symmetric in that swap. No numeric check can
# separate the two readings, which is why the declared type is pinned character
# for character in sum_range_permute_tests::the_permutation_family_states_the_
# intended_types. It matters to the CONSUMER, because the permutation proof
# feeds `f . tau` on the left and `f . sigma` on the right and then rewrites
# only the left index.
swap_ok = True
for n in range(1, 9):
    for i0 in range(n):
        a = lambda k, i0=i0: k * k + (5 if k == i0 else 0)
        b = lambda k: k * k
        if total(b, n) + a(i0) != total(a, n) + b(i0):
            swap_ok = False
survivor("M6 (swap a and b in point_change)", swap_ok, "the equation is symmetric in the swap")

# M7 -- drop the one-index-differs hypothesis from the point-change law. Two
# families differing at TWO indices break it.
a7 = lambda k: k * k + (5 if k in (1, 2) else 0)
b7 = lambda k: k * k
lhs7 = total(a7, 4) + b7(1)
rhs7 = total(b7, 4) + a7(1)
control("M7 (two indices differ)", lhs7 != rhs7, f"{lhs7} against {rhs7}")

print()
if FAILURES:
    print(f"FAILED: {', '.join(FAILURES)}")
    sys.exit(1)
print("all claims hold and every control behaves as recorded")
