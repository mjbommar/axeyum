#!/usr/bin/env python3
"""Numeric checks for ADR-1260 -- the Eisenstein route to quadratic reciprocity.

Re-runnable:

    python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py

Every CLAIM below is a statement this lane either LANDED in the kernel or is
about to size.  Every CONTROL is a deliberately mutated form of one of those
claims that MUST be refuted; if a mutation survives, the corresponding claim
is not pinned down by the check and the script exits nonzero.

The claims split into two groups, and keeping them apart is the point of the
ADR:

  * C1-C5  are the RECTANGLE PARTITION -- pure counting over `sumRange` /
    `countRange`, with no primality, no division and no set of lattice points
    anywhere.  These are what this lane landed.
  * C6-C8  are EISENSTEIN'S LEMMA and the assembled reciprocity law -- the
    part that still needs signed sums, which this kernel's `Int` prelude does
    not have (`Int.sumRange` does not exist; only `Int.prodRange` does).
    They are verified here so the ADR's statement of what REMAINS is measured
    rather than asserted.
"""

from __future__ import annotations

import sys
from itertools import product

FAILURES: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    tag = "ok " if ok else "FAIL"
    print(f"  [{tag}] {name}" + (f": {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def refute(name: str, ok_when_false: bool, detail: str = "") -> None:
    """`ok_when_false` is True when the mutated claim FAILED, as it must."""
    tag = "ok " if ok_when_false else "FAIL"
    verdict = "refuted" if ok_when_false else "SURVIVED -- the claim is not pinned"
    print(f"  [{tag}] {name}: {verdict}" + (f" {detail}" if detail else ""))
    if not ok_when_false:
        FAILURES.append(f"control {name}")


# ---------------------------------------------------------------------------
# The kernel's own aggregates, transcribed.
# ---------------------------------------------------------------------------


def sum_range(f, n: int) -> int:
    """`Nat.sumRange f n = Nat.rec 0 (fun j ih => ih + f j) n`."""
    total = 0
    for j in range(n):
        total += f(j)
    return total


def sel(b: bool) -> int:
    """`Nat.bool_select_nat b 1 0` -- `countRange`'s per-index increment."""
    return 1 if b else 0


def count_range(f, n: int) -> int:
    """`Nat.countRange f n = Nat.rec 0 (fun j ih => ih + sel (f j)) n`."""
    total = 0
    for j in range(n):
        total += sel(f(j))
    return total


def primes_upto(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, limit + 1, i):
                sieve[j] = False
    return [i for i, ok in enumerate(sieve) if ok]


ODD_PRIMES = [p for p in primes_upto(120) if p > 2]


def gauss_neg_count(pp: int, a: int, m: int) -> int:
    """`Nat.gaussNegCount pp a m` -- ADR-1130's engine, transcribed from
    `nat_prelude/gauss_lemma.rs`: count of `k` in `[1, m]` whose least
    residue `a*k mod pp` exceeds `pp/2`."""
    return count_range(lambda j: (a * (j + 1)) % pp > pp // 2, m)


# A sample of doubly-indexed families, deliberately NOT symmetric in its two
# arguments -- a symmetric family would make the Fubini swap vacuous.
FAMILIES = [
    ("F1", lambda i, j: 3 * i + 5 * j + 1),
    ("F2", lambda i, j: (i + 1) * (2 * j + 3)),
    ("F3", lambda i, j: i * i + 7 * j),
    ("F4", lambda i, j: (i * 11 + j * 4) % 13),
]

# Doubly-indexed Bool predicates, likewise asymmetric.
PREDICATES = [
    ("Q1", lambda x, y: 3 * (y + 1) < 5 * (x + 1)),
    ("Q2", lambda x, y: (x * 7 + y * 3) % 5 == 0),
    ("Q3", lambda x, y: x > y),
    ("Q4", lambda x, y: (x + 2 * y) % 3 == 1),
]

BOUNDS = [(m, n) for m in range(0, 8) for n in range(0, 8)]


# ---------------------------------------------------------------------------
# C1-C5 -- the rectangle partition (landed).
# ---------------------------------------------------------------------------

print("CLAIMS -- the rectangle partition (no primality, no division, no sets)")

# C1: Nat.sumRange_swap.
bad = [
    (name, m, n)
    for name, F in FAMILIES
    for (m, n) in BOUNDS
    if sum_range(lambda i: sum_range(lambda j: F(i, j), n), m)
    != sum_range(lambda j: sum_range(lambda i: F(i, j), m), n)
]
check(
    "C1 sumRange_swap: sum_{i<m} sum_{j<n} F i j = sum_{j<n} sum_{i<m} F i j",
    not bad,
    f"{len(FAMILIES) * len(BOUNDS)} (family, bound) pairs",
)

# C2: countRange is sumRange of the selector -- claimed DEFEQ in the kernel,
# so the numeric check here is only a sanity floor on the transcription.
bad = [
    (name, n)
    for name, Q in PREDICATES
    for n in range(0, 12)
    if count_range(lambda k: Q(k, 3), n) != sum_range(lambda k: sel(Q(k, 3)), n)
]
check("C2 countRange f n = sumRange (fun k => sel (f k)) n", not bad)

# C3: sumRange of a constant.  Operand order matters: `Nat.mul` recurses on
# its RIGHT argument and `sumRange (fun _ => c) (succ j)` reduces to
# `add (sumRange .. j) c`, which is `mul c (succ j)`'s own reduct -- so the
# provable orientation is `mul c n`, NOT `mul n c`.
bad = [
    (c, n) for c in range(0, 9) for n in range(0, 9) if sum_range(lambda _: c, n) != c * n
]
check("C3 sumRange (fun _ => c) n = mul c n", not bad)

# C4: the headline rectangle partition.
bad = []
for name, Q in PREDICATES:
    for (m, n) in BOUNDS:
        lhs = sum_range(lambda x: count_range(lambda y: Q(x, y), n), m)
        rhs = sum_range(lambda y: count_range(lambda x: not Q(x, y), m), n)
        if lhs + rhs != n * m:
            bad.append((name, m, n))
check(
    "C4 rectangle partition: "
    "sum_{x<m} #{y<n : Q x y} + sum_{y<n} #{x<m : not Q x y} = mul n m",
    not bad,
    f"{len(PREDICATES) * len(BOUNDS)} (predicate, bound) pairs",
)

# C5: at the Eisenstein predicate `Q x y := p*(y+1) < q*(x+1)` over distinct
# odd primes with m = (p-1)/2, n = (q-1)/2, the row count IS the floor term,
# so C4 specialises to the classical lattice identity
#     sum_{x=1..m} floor(q x / p) + sum_{y=1..n} floor(p y / q) = m n.
pairs = [(p, q) for p in ODD_PRIMES for q in ODD_PRIMES if p != q and p * q < 3000]
bad_rowcount = []
bad_lattice = []
bad_never_equal = []
for p, q in pairs:
    m, n = (p - 1) // 2, (q - 1) // 2
    # the row count equals the floor
    for x in range(m):
        got = count_range(lambda y: p * (y + 1) < q * (x + 1), n)
        want = (q * (x + 1)) // p
        if got != want:
            bad_rowcount.append((p, q, x))
    # no lattice point sits on the line
    for x in range(1, m + 1):
        for y in range(1, n + 1):
            if p * y == q * x:
                bad_never_equal.append((p, q, x, y))
    lhs = sum(((q * x) // p) for x in range(1, m + 1))
    rhs = sum(((p * y) // q) for y in range(1, n + 1))
    if lhs + rhs != m * n:
        bad_lattice.append((p, q))
check(
    "C5a row count = floor: #{y in [1,n] : p*y < q*x} = floor(q*x/p)",
    not bad_rowcount,
    f"{len(pairs)} prime pairs",
)
check("C5b no lattice point on the line p*y = q*x", not bad_never_equal)
check(
    "C5c lattice identity: sum floor(qx/p) + sum floor(py/q) = m*n",
    not bad_lattice,
    f"{len(pairs)} prime pairs",
)

# ---------------------------------------------------------------------------
# C6-C8 -- Eisenstein's lemma and the law (NOT landed; sized here).
# ---------------------------------------------------------------------------

print()
print("CLAIMS -- Eisenstein's lemma and the law (this lane does NOT prove these)")

# C6: Eisenstein's lemma.  Needs `a` ODD; the control below shows it fails
# without that.
bad = []
for p in ODD_PRIMES:
    m = (p - 1) // 2
    for a in range(1, min(p, 40)):
        if a % p == 0 or a % 2 == 0:
            continue
        lhs = gauss_neg_count(p, a, m) % 2
        rhs = sum((a * k) // p for k in range(1, m + 1)) % 2
        if lhs != rhs:
            bad.append((p, a))
check(
    "C6 Eisenstein's lemma: gaussNegCount p a m = sum_{k=1..m} floor(ak/p)  (mod 2), a odd",
    not bad,
)

# C7: the Legendre symbol from Gauss's lemma.
def legendre(a: int, p: int) -> int:
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


bad = [
    (p, a)
    for p in ODD_PRIMES
    for a in range(1, p)
    if legendre(a, p) != (-1) ** gauss_neg_count(p, a, (p - 1) // 2)
]
check("C7 Gauss's lemma in Legendre form: (a|p) = (-1)^gaussNegCount(p,a,m)", not bad)

# C8: quadratic reciprocity itself, assembled from C5 + C6 + C7.
bad = [
    (p, q)
    for p, q in pairs
    if legendre(p, q) * legendre(q, p)
    != (-1) ** (((p - 1) // 2) * ((q - 1) // 2))
]
check(
    "C8 quadratic reciprocity: (p|q)(q|p) = (-1)^(((p-1)/2)((q-1)/2))",
    not bad,
    f"{len(pairs)} prime pairs",
)

# ---------------------------------------------------------------------------
# Controls.  Each mutates ONE claim; every one must be refuted.
# ---------------------------------------------------------------------------

print()
print("CONTROLS -- every mutated claim must be REFUTED")

# M1: sumRange_swap with the two BOUNDS left unswapped on the right.
survived = all(
    sum_range(lambda i: sum_range(lambda j: F(i, j), n), m)
    == sum_range(lambda j: sum_range(lambda i: F(i, j), n), m)
    for name, F in FAMILIES
    for (m, n) in BOUNDS
)
refute("M1 C1 with the bounds NOT swapped on the right", not survived)

# M2: the partition with `not` dropped from the second count.
survived = all(
    sum_range(lambda x: count_range(lambda y: Q(x, y), n), m)
    + sum_range(lambda y: count_range(lambda x: Q(x, y), m), n)
    == n * m
    for name, Q in PREDICATES
    for (m, n) in BOUNDS
)
refute("M2 C4 with the complement dropped from the second term", not survived)

# M3: the partition with the SECOND term's two bounds transposed -- outer
# `y < m`, inner `x < n` -- which is what a proof that swapped the summation
# order without also swapping the bounds would produce.
survived = all(
    sum_range(lambda x: count_range(lambda y: Q(x, y), n), m)
    + sum_range(lambda y: count_range(lambda x: not Q(x, y), n), m)
    == n * m
    for name, Q in PREDICATES
    for (m, n) in BOUNDS
)
refute("M3 C4 with the second term's bounds transposed", not survived)

# M3b: RECORDED AS VACUOUS, deliberately.  On the SQUARE `m = n`, transposing
# the predicate (`Q y x` for `Q x y`) AND the summation order together is the
# identity map on the set being counted, so the total is unchanged and the
# mutation SURVIVES.  It is kept, and reported as surviving, because the first
# draft of this script used it as a control and it is exactly the vacuous
# shape this repository's standing rule warns about: a control that cannot
# fail is worse than no control.  What separates "swap the summation order"
# (Fubini -- true) from "transpose the predicate" (a different statement) is
# not the TOTAL but which of the two sums is then identifiable with
# `(q|p)`, and no numeric total can see that.  See the ADR's
# "what the controls do not catch".
survived = all(
    sum_range(lambda x: count_range(lambda y: Q(x, y), n), m)
    + sum_range(lambda y: count_range(lambda x: not Q(y, x), m), n)
    == n * m
    for name, Q in PREDICATES
    for (m, n) in BOUNDS
    if m == n
)
check(
    "M3b C4 with predicate AND summation order both transposed on the square "
    "SURVIVES (recorded as a VACUOUS control, not a passing one)",
    survived,
)

# M4: C3 with the multiplication in the other order.  This one must SURVIVE
# numerically (`Nat.mul` is commutative), and is recorded to make the point
# that the orientation in C3 is a DEFEQ constraint of the kernel's `Nat.mul`,
# not a mathematical one -- so this script cannot pin it and the Rust proof
# must.
survived = all(
    sum_range(lambda _: c, n) == n * c for c in range(0, 9) for n in range(0, 9)
)
check(
    "M4 C3 with mul's operands transposed SURVIVES numerically (as it must)",
    survived,
    "the orientation is a kernel defeq constraint, not a numeric one -- see the ADR",
)

# M5: Eisenstein's lemma at EVEN `a`.
survived = True
for p in ODD_PRIMES:
    m = (p - 1) // 2
    for a in range(2, min(p, 40), 2):
        if a % p == 0:
            continue
        if gauss_neg_count(p, a, m) % 2 != sum((a * k) // p for k in range(1, m + 1)) % 2:
            survived = False
            break
    if not survived:
        break
refute("M5 C6 extended to EVEN a", not survived)

# M6: Eisenstein's floor sum truncated to k = 1..m-1.
survived = True
for p in ODD_PRIMES:
    m = (p - 1) // 2
    for a in range(1, min(p, 40), 2):
        if a % p == 0:
            continue
        if gauss_neg_count(p, a, m) % 2 != sum((a * k) // p for k in range(1, m)) % 2:
            survived = False
            break
    if not survived:
        break
refute("M6 C6 with the floor sum truncated to k = 1..m-1", not survived)

# M7: the lattice identity with m taken as (p+1)/2.
survived = all(
    sum(((q * x) // p) for x in range(1, (p + 1) // 2 + 1))
    + sum(((p * y) // q) for y in range(1, (q - 1) // 2 + 1))
    == ((p + 1) // 2) * ((q - 1) // 2)
    for p, q in pairs
)
refute("M7 C5c with m shifted to (p+1)/2", not survived)

# M8: reciprocity with the sign exponent m*n replaced by m+n.
survived = all(
    legendre(p, q) * legendre(q, p)
    == (-1) ** (((p - 1) // 2) + ((q - 1) // 2))
    for p, q in pairs
)
refute("M8 C8 with the sign exponent m*n replaced by m+n", not survived)

# M9: reciprocity claimed unconditionally for p = 2.
survived = all(
    legendre(2, q) * (1 if q % 2 == 1 else 0) == (-1) ** (((2 - 1) // 2) * ((q - 1) // 2))
    for q in ODD_PRIMES
)
refute("M9 C8 extended to the even prime p = 2", not survived)

# M10: the row-count-equals-floor claim WITHOUT the bound `floor(qx/p) <= n`,
# i.e. taking the count over a range shorter than n.
survived = True
for p, q in pairs[:200]:
    m, n = (p - 1) // 2, (q - 1) // 2
    if n == 0:
        continue
    for x in range(m):
        if count_range(lambda y: p * (y + 1) < q * (x + 1), n - 1) != (q * (x + 1)) // p:
            survived = False
            break
    if not survived:
        break
refute("M10 C5a with the inner range shortened to n-1", not survived)

print()
if FAILURES:
    print(f"FAIL: {len(FAILURES)} check(s) failed: {FAILURES}")
    sys.exit(1)
print("PASS: every claim holds and every control behaves as recorded")
