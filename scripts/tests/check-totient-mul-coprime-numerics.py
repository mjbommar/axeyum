#!/usr/bin/env python3
"""Re-derive, numerically, every claim the `Nat.totient_mul_of_coprime` route
makes -- BEFORE any of it is written as a proof term.

This is the companion to `check-countrange-bijection-numerics.py`, which
checked lane `344`'s primitives.  This one checks the specific CRT self-map
`g` that lane `349` builds on top of them, and it exists because a traced plan
for this exact argument once asserted a `count_range_row_major` identity was
coprimality-INDEPENDENT and "verified numerically" -- and it is false at 26 of
26 non-coprime pairs.  A plan's numeric claims are re-run here, never
inherited.

The route under test, with `N = n*m` throughout (block width `n`, `m` blocks,
matching `Nat.countRange_product`'s `mul n m`):

    g x  := n * (x mod m) + (x mod n)          the CRT self-map on [0, N)
    R a  := gcd(a, m) == 1                      == totient m's predicate
    S b  := gcd(b, n) == 1                      == totient n's predicate
    V y  := R (y div n) AND S (y mod n)         the block-factoring predicate
    P x  := gcd(x, m*n) == 1                    == totient (m*n)'s predicate

    countRange P N  =  countRange (V . g) N     pointwise, NO coprimality
                    =  countRange V N           permute along g, NEEDS coprime
                    =  countRange S n * countRange R m    Fubini, NO coprimality
                    =  totient n * totient m

Every check that must hold prints `ok`; every negative control must GENUINELY
fail (the script asserts that it does).  Exit status is the finding.
"""

from math import gcd

FAILURES = []


def check(label, condition, detail=""):
    if condition:
        print(f"ok    {label}")
    else:
        print(f"FAIL  {label}   {detail}")
        FAILURES.append(label)


def note(text):
    print(f"      {text}")


# --------------------------------------------------------------------------
# the model
# --------------------------------------------------------------------------


def totient(k):
    return sum(1 for i in range(k) if gcd(i, k) == 1)


def count_range(pred, bound):
    return sum(1 for i in range(bound) if pred(i))


def g_map(m, n):
    return lambda x: n * (x % m) + (x % n)


def R_pred(m):
    return lambda a: gcd(a, m) == 1


def S_pred(n):
    return lambda b: gcd(b, n) == 1


def V_pred(m, n):
    r, s = R_pred(m), S_pred(n)
    return lambda y: r(y // n) and s(y % n)


def P_pred(m, n):
    return lambda x: gcd(x, m * n) == 1


PAIRS = [(m, n) for m in range(1, 10) for n in range(1, 10)]
COPRIME = [(m, n) for (m, n) in PAIRS if gcd(m, n) == 1]
NONCOPRIME = [(m, n) for (m, n) in PAIRS if gcd(m, n) != 1]


# --------------------------------------------------------------------------
# (1) MapsInto -- needs 0 < m and 0 < n and NOTHING else
# --------------------------------------------------------------------------

bad = [
    (m, n, x)
    for (m, n) in PAIRS
    for x in range(n * m)
    if not g_map(m, n)(x) < n * m
]
check("MapsInto: g maps [0, n*m) into itself at every 1<=m,n<=9", not bad, str(bad[:3]))
note("this holds at NON-coprime pairs too -- MapsInto never sees coprimality")
bad_nc = [
    (m, n, x)
    for (m, n) in NONCOPRIME
    for x in range(n * m)
    if not g_map(m, n)(x) < n * m
]
check("MapsInto holds at all 26 non-coprime pairs as well", not bad_nc, str(bad_nc[:3]))

# NEGATIVE CONTROL: an off-by-one g must break MapsInto somewhere.
off_by_one_escapes = [
    (m, n, x)
    for (m, n) in PAIRS
    for x in range(n * m)
    if not (g_map(m, n)(x) + 1) < n * m
]
check(
    "NEGATIVE CONTROL: g+1 escapes the range (so the check is not vacuous)",
    off_by_one_escapes,
    "g+1 never escaped -- the MapsInto check proves nothing",
)
note(f"g+1 escapes at {len(off_by_one_escapes)} (m,n,x) triples, e.g. {off_by_one_escapes[0]}")


# --------------------------------------------------------------------------
# (2) InjectiveOn -- THE only place coprimality enters
# --------------------------------------------------------------------------


def injective_on(f, bound):
    seen = {}
    for i in range(bound):
        v = f(i)
        if v in seen:
            return (seen[v], i)
        seen[v] = i
    return None


non_injective_coprime = [
    (m, n, injective_on(g_map(m, n), n * m))
    for (m, n) in COPRIME
    if injective_on(g_map(m, n), n * m) is not None
]
check(
    "InjectiveOn: g is injective on [0,n*m) at EVERY coprime pair",
    not non_injective_coprime,
    str(non_injective_coprime[:3]),
)

injective_noncoprime = [
    (m, n) for (m, n) in NONCOPRIME if injective_on(g_map(m, n), n * m) is None
]
check(
    "NEGATIVE CONTROL: g is injective at NO non-coprime pair (0 of 26)",
    not injective_noncoprime,
    str(injective_noncoprime[:5]),
)
note(f"{len(NONCOPRIME)} non-coprime pairs, all non-injective; smallest collision at "
     f"m=n=2: g(0)={g_map(2,2)(0)}, g(2)={g_map(2,2)(2)}")
check(
    "NEGATIVE CONTROL: the collision witness at m=n=2 is real (0 and 2 collide)",
    g_map(2, 2)(0) == g_map(2, 2)(2) and 0 != 2,
)


# --------------------------------------------------------------------------
# (3) the pointwise identity P x = V (g x) -- coprimality-INDEPENDENT
# --------------------------------------------------------------------------

bad_pointwise = [
    (m, n, x)
    for (m, n) in PAIRS
    for x in range(60)
    if P_pred(m, n)(x) != V_pred(m, n)(g_map(m, n)(x))
]
check(
    "pointwise: P x == V (g x) for ALL x < 60 at every 1<=m,n<=9",
    not bad_pointwise,
    str(bad_pointwise[:3]),
)
bad_pointwise_nc = [
    (m, n, x)
    for (m, n) in NONCOPRIME
    for x in range(60)
    if P_pred(m, n)(x) != V_pred(m, n)(g_map(m, n)(x))
]
check(
    "pointwise identity holds at NON-coprime pairs too (no hypothesis needed)",
    not bad_pointwise_nc,
    str(bad_pointwise_nc[:3]),
)
note("so `Nat.countRange_congr` (unconditional) suffices for this step, and the")
note("coprimality hypothesis must NOT be smuggled into it")

# NEGATIVE CONTROL: swapping the two moduli inside V must break the identity.
def V_swapped(m, n):
    return lambda y: (gcd(y // n, n) == 1) and (gcd(y % n, m) == 1)


swap_breaks = [
    (m, n, x)
    for (m, n) in PAIRS
    for x in range(60)
    if P_pred(m, n)(x) != V_swapped(m, n)(g_map(m, n)(x))
]
check(
    "NEGATIVE CONTROL: swapping m/n inside V breaks the pointwise identity",
    swap_breaks,
    "the swapped V agreed everywhere -- the check does not pin the moduli",
)
note(f"the swapped V disagrees at {len(swap_breaks)} triples, e.g. {swap_breaks[0]}")


# --------------------------------------------------------------------------
# (4) the Fubini step over V -- coprimality-INDEPENDENT
# --------------------------------------------------------------------------

bad_fubini = [
    (m, n, count_range(V_pred(m, n), n * m), totient(n) * totient(m))
    for (m, n) in PAIRS
    if count_range(V_pred(m, n), n * m) != totient(n) * totient(m)
]
check(
    "Fubini: countRange V (n*m) == totient n * totient m at every 1<=m,n<=9",
    not bad_fubini,
    str(bad_fubini[:3]),
)
bad_fubini_nc = [
    (m, n)
    for (m, n) in NONCOPRIME
    if count_range(V_pred(m, n), n * m) != totient(n) * totient(m)
]
check(
    "Fubini holds at all 26 NON-coprime pairs -- this step never needs coprimality",
    not bad_fubini_nc,
    str(bad_fubini_nc[:5]),
)
note("this is exactly the claim the earlier traced plan got RIGHT; what it got")
note("wrong was attributing the same independence to the totient identity below")

# The two block hypotheses `countRange_product` actually asks for.
bad_block = []
for (m, n) in PAIRS:
    V, R, S = V_pred(m, n), R_pred(m), S_pred(n)
    for a in range(m + 2):
        for b in range(n):
            if R(a) and V(n * a + b) != S(b):
                bad_block.append(("true-branch", m, n, a, b))
            if (not R(a)) and V(n * a + b) is not False:
                bad_block.append(("false-branch", m, n, a, b))
check(
    "countRange_product's two per-block hypotheses hold for V, a<=m+1, b<n",
    not bad_block,
    str(bad_block[:3]),
)


# --------------------------------------------------------------------------
# (5) where coprimality actually bites: countRange P N == countRange V N
# --------------------------------------------------------------------------

bad_permute = [
    (m, n) for (m, n) in COPRIME
    if count_range(P_pred(m, n), n * m) != count_range(V_pred(m, n), n * m)
]
check(
    "permute step: countRange P N == countRange V N at every coprime pair",
    not bad_permute,
    str(bad_permute[:3]),
)
survives_noncoprime = [
    (m, n) for (m, n) in NONCOPRIME
    if count_range(P_pred(m, n), n * m) == count_range(V_pred(m, n), n * m)
]
check(
    "NEGATIVE CONTROL: the permute step FAILS at all 26 non-coprime pairs",
    not survives_noncoprime,
    f"it survived at {survives_noncoprime[:5]}",
)
note("so the whole coprimality hypothesis is carried by ONE step -- g's injectivity")


# --------------------------------------------------------------------------
# (6) the theorem itself, and its negative control
# --------------------------------------------------------------------------

bad_final = [
    (m, n, totient(m * n), totient(m) * totient(n))
    for (m, n) in COPRIME
    if totient(m * n) != totient(m) * totient(n)
]
check(
    "totient(m*n) == totient(m)*totient(n) at every coprime 1<=m,n<=9",
    not bad_final,
    str(bad_final[:3]),
)
survivors = [(m, n) for (m, n) in NONCOPRIME if totient(m * n) == totient(m) * totient(n)]
check(
    "NEGATIVE CONTROL: the identity fails at ALL 26 non-coprime pairs",
    not survivors,
    f"it survived at {survivors[:5]}",
)
check(
    "NEGATIVE CONTROL: smallest counterexample is m=n=2 -- totient(4)=2 vs 1*1",
    totient(4) == 2 and totient(2) * totient(2) == 1,
)


# --------------------------------------------------------------------------
# (7) the zero boundary, where the Rust proof case-splits before doing any work
# --------------------------------------------------------------------------

check(
    "n = 0: both sides are 0 for every m<=9 (Nat.mul recurses right, so mul m 0 is defeq 0)",
    all(totient(m * 0) == totient(m) * totient(0) for m in range(10)),
)
check(
    "m = 0: both sides are 0 for every n<=9 (needs Nat.zero_mul, not defeq)",
    all(totient(0 * n) == totient(0) * totient(n) for n in range(10)),
)


# --------------------------------------------------------------------------
# (8) the successor form `div_mod_exec` needs: N = succ (n*m' + n')
# --------------------------------------------------------------------------

bad_succ = [
    (mp, np)
    for mp in range(9)
    for np in range(9)
    if (np + 1) * (mp + 1) != 1 + ((np + 1) * mp + np)
]
check(
    "N = mul (succ n') (succ m') is succ (mul (succ n') m' + n'), so div_mod_exec applies",
    not bad_succ,
    str(bad_succ[:3]),
)
check(
    "NEGATIVE CONTROL: the predecessor is NOT n'*m' + n' (a plausible mis-derivation)",
    any(
        (np + 1) * (mp + 1) != 1 + (np * mp + np)
        for mp in range(9)
        for np in range(9)
    ),
)


# --------------------------------------------------------------------------
# (9) the two Mathlib mirrors: exactly how far this theorem gets them
# --------------------------------------------------------------------------
# F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
#   forall a b, totient(gcd a b) * totient(a*b) = totient a * totient b * gcd a b
# F:ml430-nat-totient-dvd-of-dvd-9622e44a
#   forall a b, a | b -> totient a | totient b

RANGE = range(1, 13)

bad_gcd_mul = [
    (a, b)
    for a in RANGE
    for b in RANGE
    if totient(gcd(a, b)) * totient(a * b) != totient(a) * totient(b) * gcd(a, b)
]
check(
    "MIRROR gcd_mul_totient_mul holds at every 1<=a,b<=12 (the statement is right)",
    not bad_gcd_mul,
    str(bad_gcd_mul[:3]),
)

# At a COPRIME pair the mirror collapses to `totient_mul_of_coprime`, because
# totient(1) = 1 and the trailing gcd factor is 1. So the landed theorem
# already covers that half exactly -- and only that half.
collapses = [
    (a, b)
    for a in RANGE
    for b in RANGE
    if gcd(a, b) == 1
    and not (totient(gcd(a, b)) == 1 and gcd(a, b) == 1)
]
check(
    "MIRROR at coprime pairs collapses to totient(a*b) = totient a * totient b",
    not collapses,
    str(collapses[:3]),
)
# NEGATIVE CONTROL: at a NON-coprime pair it does NOT collapse -- both the
# leading totient(gcd) and the trailing gcd differ from 1, so the landed
# theorem says nothing there and the mirror is strictly stronger.
non_collapsing = [
    (a, b)
    for a in RANGE
    for b in RANGE
    if gcd(a, b) != 1 and (totient(gcd(a, b)) != 1 or gcd(a, b) != 1)
]
check(
    "NEGATIVE CONTROL: at every non-coprime pair the mirror does NOT collapse",
    len(non_collapsing) == len([1 for a in RANGE for b in RANGE if gcd(a, b) != 1]),
    "some non-coprime pair collapsed, so the mirror would be no stronger there",
)
note(f"{len(non_collapsing)} non-coprime pairs with 1<=a,b<=12 where the mirror is")
note("strictly stronger than the landed theorem -- that gap is the whole task")

bad_dvd = [
    (a, b)
    for a in RANGE
    for b in RANGE
    if b % a == 0 and totient(b) % totient(a) != 0
]
check(
    "MIRROR totient_dvd_of_dvd holds at every 1<=a,b<=12 with a | b",
    not bad_dvd,
    str(bad_dvd[:3]),
)
# NEGATIVE CONTROL: dropping the divisibility hypothesis breaks it, so the
# mirror is not a disguised unconditional fact.
non_dvd_failures = [
    (a, b)
    for a in RANGE
    for b in RANGE
    if b % a != 0 and totient(b) % totient(a) != 0
]
check(
    "NEGATIVE CONTROL: without a | b the totient divisibility fails somewhere",
    non_dvd_failures,
    "totient a | totient b held for every pair, so the hypothesis is untested",
)
note(f"fails at {len(non_dvd_failures)} non-dividing pairs, e.g. {non_dvd_failures[0]}")
note("NEITHER mirror follows from totient_mul_of_coprime: both quantify over ALL")
note("pairs, and the coprime half of each is what the landed theorem already gives.")


print()
if FAILURES:
    print(f"{len(FAILURES)} CHECK(S) FAILED: {FAILURES}")
    raise SystemExit(1)
print("all checks passed")
