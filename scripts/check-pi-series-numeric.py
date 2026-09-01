#!/usr/bin/env python3
"""Numeric pre-registration for `CReal.pi` (creal-pi lane).

Checks -- each one a claim the Rust proof will make symbolically -- that:

  1. the recursion `t 0 = 1`, `t (k+1) = t k * (k+1)/(2k+3)` really is the
     closed form `2^k (k!)^2 / (2k+1)!`;
  2. `sum_k t k = pi/2`;
  3. the per-step ratio `(k+1)/(2k+3) <= 1/2` for every k (this is what makes
     `t k <= 2^-k`, and it is the only rational fact the domination needs);
  4. `t k <= (1/2)^k` for every k, the domination bound proved by induction;
  5. the UPPER bound route: every partial sum is `<= 2`, hence `pi <= 4`;
  6. the LOWER bound route: `S 4 = 32/21 >= 3/2`, hence `pi >= 3`;
  7. the magnitudes actually formed by the bound proofs stay small (the unary
     numeral hazard).

Mutations that MUST be refuted are run at the end: each perturbs one claim and
the script fails if the perturbed claim still passes.

Run:  python3 scripts/check-pi-series-numeric.py
"""

from fractions import Fraction
import math
import sys

FAIL = []


def check(name, ok, detail=""):
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")
    if not ok:
        FAIL.append(name)


def terms(n, ratio=lambda k: Fraction(k + 1, 2 * k + 3)):
    """t 0 = 1; t (k+1) = t k * ratio k."""
    t = Fraction(1)
    out = []
    for k in range(n):
        out.append(t)
        t = t * ratio(k)
    return out


def closed_form(k):
    return Fraction(2**k * math.factorial(k) ** 2, math.factorial(2 * k + 1))


N = 60
ts = terms(N)

# 1. recursion == closed form
check(
    "recursion equals 2^k (k!)^2/(2k+1)!",
    all(ts[k] == closed_form(k) for k in range(N)),
)

# 2. the sum is pi/2
s = float(sum(ts))
check("sum equals pi/2", abs(s - math.pi / 2) < 1e-12, f"|S-pi/2| = {abs(s - math.pi / 2):.3e}")

# 3. ratio <= 1/2 everywhere
check(
    "ratio (k+1)/(2k+3) <= 1/2 for all k",
    all(Fraction(k + 1, 2 * k + 3) <= Fraction(1, 2) for k in range(N)),
)

# 4. t k <= (1/2)^k
check("t k <= (1/2)^k", all(ts[k] <= Fraction(1, 2**k) for k in range(N)))

# 5. every partial sum <= 2  (via termwise t k <= (1/2)^k and geom_sum_bounded)
partials = [sum(ts[:n]) for n in range(N + 1)]
check("every partial sum <= 2", all(p <= 2 for p in partials), f"sup = {float(partials[-1]):.6f}")
check("hence pi <= 4", 2 * float(partials[-1]) <= 4)

# 6. lower bound from S 4
s4 = sum(ts[:4])
check("S 4 == 32/21", s4 == Fraction(32, 21), f"S4 = {s4}")
check("S 4 >= 3/2", s4 >= Fraction(3, 2), "32*2 = 64 >= 63 = 3*21")
check("hence pi >= 3", 2 * float(s4) >= 3.0, f"2*S4 = {2 * float(s4):.6f}")

# 7. magnitudes formed by the bound proofs
formed = [n for f in ts[:4] for n in (abs(f.numerator), f.denominator)]
formed += [s4.numerator, s4.denominator, 32 * 2, 3 * 21]
check("largest Nat formed by the bound proofs <= 128", max(formed) <= 128, f"max = {max(formed)}")

# ---------------------------------------------------------------- mutations --
print("\n-- mutations (each MUST be refuted) --")

# M1: wrong ratio (k+1)/(2k+2) -- must NOT sum to pi/2
m1 = terms(N, ratio=lambda k: Fraction(k + 1, 2 * k + 2))
check("M1 ratio (k+1)/(2k+2) does NOT give pi/2", abs(float(sum(m1)) - math.pi / 2) > 1e-3)

# M2: ratio (k+2)/(2k+3) -- must NOT stay <= 1/2 (so domination would break)
check(
    "M2 ratio (k+2)/(2k+3) is NOT <= 1/2",
    any(Fraction(k + 2, 2 * k + 3) > Fraction(1, 2) for k in range(N)),
)

# M3: S 3 (one term short) must NOT reach 3/2 -- so the lower bound really
# needs four terms and the choice of 4 is not arbitrary.
check("M3 S 3 < 3/2 (four terms are needed)", sum(ts[:3]) < Fraction(3, 2), f"S3 = {sum(ts[:3])}")

# M4: the bound 2 on partial sums must be tight enough to be non-vacuous:
# a claimed bound of 3/2 must FAIL, or "every partial sum <= B" would be
# checking nothing about B.
check("M4 a claimed bound of 3/2 on partial sums FAILS", any(p > Fraction(3, 2) for p in partials))

# M5: t k <= (1/2)^k must be refuted for a WRONG start t 0 = 2
m5 = [2 * t for t in ts]
check("M5 t0=2 breaks t k <= (1/2)^k", any(m5[k] > Fraction(1, 2**k) for k in range(N)))

# ------------------------------------------- what the kernel CANNOT catch --
#
# `CReal.piHalfCoef` is a `Definition`. `Kernel::add_declaration` type-checks
# it and cannot tell anyone it computes the wrong rational. So the question
# that matters is: which OTHER series would satisfy every theorem this file
# proves? Measure it rather than assert it.
print("\n-- the gap the kernel cannot close (why the evaluation test exists) --")

decoy = [Fraction(1, 2**k) for k in range(N)]  # t k = (1/2)^k, sum = 2
decoy_ok = (
    all(Fraction(1, 2) <= Fraction(1, 2) for _ in range(N))  # ratio <= 1/2: equality
    and all(decoy[k] <= Fraction(1, 2**k) for k in range(N))  # domination holds
    and all(sum(decoy[:n]) <= 2 for n in range(N + 1))  # every partial sum <= 2
    and sum(decoy[:4]) >= Fraction(3, 2)  # S 4 >= 3/2
    and all(t >= 0 for t in decoy)  # every term nonnegative
)
check(
    "the decoy series t k = (1/2)^k satisfies EVERY theorem in creal/pi.rs",
    decoy_ok,
    f"its sum is {float(sum(decoy)):.6f}, so its 'pi' would be 4, not {math.pi:.6f}",
)
check(
    "and the evaluation test separates it at k = 1",
    ts[1] != decoy[1],
    f"piHalfCoef 1 = {ts[1]} against the decoy's {decoy[1]}",
)
print(
    "  => the numeric bounds `3 <= pi <= 4` do NOT pin the series; only\n"
    "     creal::pi::tests::pi_half_coef_computes_its_first_four_values does."
)

print()
if FAIL:
    print(f"FAILED: {len(FAIL)} check(s): {', '.join(FAIL)}")
    sys.exit(1)
print("ALL CHECKS PASSED")
