#!/usr/bin/env python3
"""Numeric checks for the `Nat.countRange` bijection primitive and its
CRT consumer, run BEFORE any kernel term was built.

Every claim this lane relies on is checked here, each with a NEGATIVE
control that must genuinely fail, so a check that silently measures
nothing is visible.

Re-execute with:

    python3 scripts/tests/check-countrange-bijection-numerics.py

Exit 0 = every positive claim held and every negative control failed as
it must; exit 1 names the first claim that did not.
"""

from itertools import permutations
from math import gcd
import sys

FAIL = []


def check(name, ok):
    print(f"{'ok  ' if ok else 'FAIL'}  {name}")
    if not ok:
        FAIL.append(name)


def count_range(p, n):
    """`Nat.countRange p n` — |{k < n : p k}|."""
    return sum(1 for k in range(n) if p(k))


def skip_at(j, x):
    """`Nat.skipAt j x` — the order-preserving injection `[0,n) -> [0,n+1)`
    whose image omits exactly `j`.  `if j <= x then x+1 else x`."""
    return x + 1 if j <= x else x


# ---------------------------------------------------------------------------
# 1. `skipAt` really is an injection onto [0, n+1) \ {j}.
# ---------------------------------------------------------------------------
ok = True
for n in range(0, 9):
    for j in range(0, n + 1):
        img = [skip_at(j, x) for x in range(n)]
        ok &= len(set(img)) == n                      # injective
        ok &= all(0 <= y < n + 1 for y in img)        # into [0, n+1)
        ok &= j not in img                            # misses j
        ok &= sorted(img) == sorted(set(range(n + 1)) - {j})
check("skipAt is a bijection [0,n) -> [0,n+1) \\ {j} for all j <= n <= 8", ok)

# NEGATIVE CONTROL: the *wrong* comparison direction (`j < x`) is not injective.
def skip_wrong(j, x):
    return x + 1 if j < x else x


bad = False
for n in range(0, 9):
    for j in range(0, n + 1):
        img = [skip_wrong(j, x) for x in range(n)]
        if len(set(img)) != n or j in img:
            bad = True
check("NEGATIVE CONTROL: `j < x` variant of skipAt is NOT an injection missing j", bad)

# ---------------------------------------------------------------------------
# 2. `countRange_erase`: count f (n+1) = count (f o skipAt j) n + [f j].
# ---------------------------------------------------------------------------
ok = True
for n in range(0, 8):
    for j in range(0, n + 1):
        for mask in range(1 << (n + 1)):
            f = lambda k, mask=mask: bool(mask >> k & 1) if k <= n else False
            lhs = count_range(f, n + 1)
            rhs = count_range(lambda x: f(skip_at(j, x)), n) + (1 if f(j) else 0)
            ok &= lhs == rhs
check("countRange_erase holds for every predicate on [0,n+1), n <= 7, every j <= n", ok)

# NEGATIVE CONTROL: dropping the `+ [f j]` term makes it false somewhere.
bad = False
for n in range(0, 6):
    for j in range(0, n + 1):
        for mask in range(1 << (n + 1)):
            f = lambda k, mask=mask: bool(mask >> k & 1) if k <= n else False
            if count_range(f, n + 1) != count_range(lambda x: f(skip_at(j, x)), n):
                bad = True
check("NEGATIVE CONTROL: countRange_erase without the `+ [f j]` term is false", bad)

# ---------------------------------------------------------------------------
# 3. The primitive itself: injective self-map on [0,n) + pointwise
#    agreement below n  =>  equal counts.
# ---------------------------------------------------------------------------
ok = True
for n in range(0, 7):
    for g_tuple in permutations(range(n)):
        g = lambda x, t=g_tuple: t[x] if x < n else 0
        for mask in range(1 << n):
            q = lambda y, mask=mask: bool(mask >> y & 1) if y < n else False
            p = lambda x: q(g(x))
            ok &= count_range(p, n) == count_range(q, n)
check("countRange_bijection holds for EVERY permutation of [0,n), n <= 6", ok)

# NEGATIVE CONTROL: drop injectivity (keep MapsInto) and it fails.
bad = False
for n in range(2, 7):
    for c in range(n):
        g = lambda x, c=c: c                       # constant: MapsInto, NOT injective
        for mask in range(1 << n):
            q = lambda y, mask=mask: bool(mask >> y & 1) if y < n else False
            p = lambda x: q(g(x))
            if count_range(p, n) != count_range(q, n):
                bad = True
check("NEGATIVE CONTROL: without InjectiveOn the conclusion is false", bad)

# NEGATIVE CONTROL: drop MapsInto (keep injectivity) and it fails.
bad = False
for n in range(1, 7):
    g = lambda x: x + n                            # injective, escapes [0,n)
    for mask in range(1 << (2 * n)):
        q = lambda y, mask=mask: bool(mask >> y & 1) if y < 2 * n else False
        p = lambda x: q(g(x))
        if count_range(p, n) != count_range(q, n):
            bad = True
check("NEGATIVE CONTROL: without MapsInto the conclusion is false", bad)

# ---------------------------------------------------------------------------
# 4. The CRT consumer.  g(x) = (x mod m)*n + (x mod n) on [0, m*n).
# ---------------------------------------------------------------------------
def crt_map(m, n, x):
    return (x % m) * n + (x % n)


ok_cop, bad_noncop = True, False
for m in range(1, 10):
    for n in range(1, 10):
        img = [crt_map(m, n, x) for x in range(m * n)]
        injective = len(set(img)) == m * n
        into = all(0 <= y < m * n for y in img)
        if gcd(m, n) == 1:
            ok_cop &= injective and into
        elif injective:
            bad_noncop = True
check("CRT self-map is injective on [0,mn) for every coprime 1<=m,n<=9", ok_cop)
check(
    "NEGATIVE CONTROL: CRT self-map is NOT injective at any non-coprime pair",
    not bad_noncop,
)

# The pointwise predicate identity, holding for ALL x (not only x < mn):
#   gcd(x, m*n) == 1   iff   gcd(x mod m, m) == 1 and gcd(x mod n, n) == 1
ok = True
for m in range(1, 10):
    for n in range(1, 10):
        for x in range(0, 60):
            left = gcd(x, m * n) == 1
            right = gcd(x % m, m) == 1 and gcd(x % n, n) == 1
            ok &= left == right
check("predicate identity gcd(x,mn)=1 <-> gcd(x%m,m)=1 & gcd(x%n,n)=1, ALL x < 60", ok)

# ---------------------------------------------------------------------------
# 5. The claim a prior traced plan got WRONG, re-checked here.
#    totient(m*n) == totient(m)*totient(n) is COPRIMALITY-DEPENDENT.
# ---------------------------------------------------------------------------
def totient(k):
    return count_range(lambda x: gcd(x, k) == 1, k)


ok_cop, noncop_failures, noncop_total = True, 0, 0
for m in range(1, 10):
    for n in range(1, 10):
        if gcd(m, n) == 1:
            ok_cop &= totient(m * n) == totient(m) * totient(n)
        else:
            noncop_total += 1
            if totient(m * n) != totient(m) * totient(n):
                noncop_failures += 1
check("totient(mn) = totient(m)totient(n) for every coprime 1<=m,n<=9", ok_cop)
print(f"      non-coprime pairs 1<=m,n<=9: {noncop_failures} of {noncop_total} FAIL the identity")
check(
    "NEGATIVE CONTROL: the identity fails at EVERY non-coprime pair (26 of 26)",
    noncop_failures == noncop_total == 26,
)
check(
    "NEGATIVE CONTROL: smallest counterexample is m=n=2, totient(4)=2 vs 1*1",
    totient(4) == 2 and totient(2) * totient(2) == 1,
)

# ---------------------------------------------------------------------------
# 6. The Fubini step the CRT route needs AFTER the bijection primitive:
#    counting over [0, n*m) a predicate that factors through (y/n, y%n).
#    This one IS coprimality-independent -- it is not the identity above.
# ---------------------------------------------------------------------------
ok = True
for n in range(1, 8):
    for m in range(0, 8):
        for rmask in range(1 << m):
            for smask in range(1 << n):
                r = lambda a, rmask=rmask: bool(rmask >> a & 1) if a < m else False
                s = lambda b, smask=smask: bool(smask >> b & 1) if b < n else False
                lhs = count_range(lambda y: r(y // n) and s(y % n), n * m)
                rhs = count_range(s, n) * count_range(r, m)
                ok &= lhs == rhs
check("countRange product/Fubini step over [0, n*m), 1<=n<=7, m<=7", ok)

# ---------------------------------------------------------------------------
# 7. The exact concrete instance the Rust test certifies:
#    sigma := Nat.transposition 1 2 (swaps 1 and 2, fixes the rest), n = 4,
#    f k := (2 <= k).  Both sides must count 2, over DIFFERENT index sets.
# ---------------------------------------------------------------------------
def transposition(i, j, k):
    return j if k == i else (i if k == j else k)


sigma = lambda k: transposition(1, 2, k)
f = lambda k: 2 <= k
lhs_set = [k for k in range(4) if f(k)]
rhs_set = [k for k in range(4) if f(sigma(k))]
check("concrete instance: countRange f 4 == 2", count_range(f, 4) == 2)
check(
    "concrete instance: countRange (f o transposition 1 2) 4 == 2",
    count_range(lambda k: f(sigma(k)), 4) == 2,
)
print(f"      index sets: f -> {lhs_set}, f o sigma -> {rhs_set}")
check(
    "the two index sets DIFFER, so the equality is not a syntactic identity",
    lhs_set != rhs_set,
)
check(
    "NEGATIVE CONTROL: with the constant-0 map (MapsInto, not injective) the "
    "counts differ, 2 vs 0",
    count_range(f, 4) == 2 and count_range(lambda k: f(0), 4) == 0,
)

# ---------------------------------------------------------------------------
# 8. The concrete `countRange_product` instance the Rust test uses, and its
#    negative control.  n = 2, m = 3; R a := (a == 1), S b := (b == 0);
#    P y := (y == 2) is exactly the factoring predicate.
# ---------------------------------------------------------------------------
R8 = lambda a: a == 1
S8 = lambda b: b == 0
P8 = lambda y: y == 2
check(
    "product instance: countRange P 6 == countRange S 2 * countRange R 3 == 1",
    count_range(P8, 6) == count_range(S8, 2) * count_range(R8, 3) == 1,
)
ok = all(
    P8(2 * a + b) == (S8(b) if R8(a) else False)
    for a in range(0, 12)
    for b in range(0, 2)
)
check("product instance: P really factors through (y // 2, y % 2), a < 12", ok)
check(
    "NEGATIVE CONTROL: a non-factoring P (y >= 4) breaks the identity, 2 vs 1",
    count_range(lambda y: y >= 4, 6) == 2
    and count_range(S8, 2) * count_range(R8, 3) == 1,
)
check(
    "the degenerate n = 0 instance holds with NO positivity hypothesis",
    count_range(P8, 0 * 5) == count_range(S8, 0) * count_range(R8, 5) == 0,
)

# ---------------------------------------------------------------------------
# 9. `div_mod_block`: an index written n*a + b with b < n reads back as
#    quotient a, remainder b -- and the `b < n` side condition is essential.
# ---------------------------------------------------------------------------
ok = all(
    (n * a + b) // n == a and (n * a + b) % n == b
    for n in range(1, 10)
    for a in range(0, 10)
    for b in range(0, n)
)
check("div_mod_block: (n*a + b)//n == a and %n == b for every b < n <= 9, a <= 9", ok)
check(
    "NEGATIVE CONTROL: at b = n the readback fails -- n=3,a=2,b=3 gives 9//3=3, 9%3=0",
    (3 * 2 + 3) // 3 == 3 and (3 * 2 + 3) % 3 == 0,
)
check(
    "the concrete instance the Rust test certifies: 3*2+1 = 7, 7//3 = 2, 7%3 = 1",
    3 * 2 + 1 == 7 and 7 // 3 == 2 and 7 % 3 == 1,
)

print()
if FAIL:
    print(f"{len(FAIL)} CHECK(S) FAILED: {FAIL}")
    sys.exit(1)
print("all checks passed")
