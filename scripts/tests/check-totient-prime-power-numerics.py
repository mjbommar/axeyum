#!/usr/bin/env python3
"""Numeric checks for the `totient-prime-power` lane.

Every claim this lane makes in Rust, or in its reachability assessment, is
checked here FIRST, exhaustively over a small range, and each check is paired
with a negative control that this script asserts must GENUINELY FAIL.  A
control that cannot fail measures nothing; a control copied from a sibling
operator can be vacuous.  Both have happened in this area.

Re-execute with:

    python3 scripts/tests/check-totient-prime-power-numerics.py

Exit 0 iff every positive check holds over its whole range AND every negative
control actually fails somewhere.  Prints one line per check.
"""

from __future__ import annotations

import sys
from math import gcd

FAILURES: list[str] = []
CHECKS = 0


def check(name: str, ok: bool, detail: str = "") -> None:
    global CHECKS
    CHECKS += 1
    status = "ok  " if ok else "FAIL"
    print(f"[{status}] {name}" + (f"  -- {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def totient(n: int) -> int:
    """Exactly the kernel's definition: |{k < n : gcd(k, n) = 1}|.

    Note the kernel counts over [0, n), not [1, n]; the two agree for every n
    (k = 0 is coprime to n only at n = 1, and n itself is out of range).
    """
    return sum(1 for k in range(n) if gcd(k, n) == 1)


def count_range(pred, n: int) -> int:
    return sum(1 for k in range(n) if pred(k))


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    return all(p % q for q in range(2, int(p**0.5) + 1))


PRIMES = [p for p in range(2, 30) if is_prime(p)]
COMPOSITES = [c for c in range(4, 30) if not is_prime(c)]


# ---------------------------------------------------------------------------
# 0. The kernel's totient convention, against hand-computed values.
# ---------------------------------------------------------------------------

HAND = {0: 0, 1: 1, 2: 1, 3: 2, 4: 2, 5: 4, 6: 2, 8: 4, 9: 6, 12: 4, 16: 8, 36: 12}
check(
    "0. totient matches hand-computed values (incl. totient 0 = 0)",
    all(totient(n) == v for n, v in HAND.items()),
    f"{ {n: totient(n) for n in sorted(HAND)} }",
)


# ---------------------------------------------------------------------------
# 1. Periodicity of the coprimality predicate: gcd(m + k, m) = gcd(k, m).
#    This is what makes the count over [0, m*j) split into j equal blocks.
# ---------------------------------------------------------------------------

bad = [
    (m, k)
    for m in range(1, 40)
    for k in range(0, 40)
    if gcd(m + k, m) != gcd(k, m)
]
check("1. gcd (m+k) m = gcd k m for all 1<=m<40, 0<=k<40", not bad, f"{len(bad)} bad")


# ---------------------------------------------------------------------------
# 2. Block counting: an m-periodic predicate counts j identical blocks.
#       (forall k, P (m+k) = P k)  ->  countRange P (m*j) = j * countRange P m
#    Checked with the coprimality predicate, which is the only consumer, and
#    with a NEGATIVE control: a NON-periodic predicate for which it fails.
# ---------------------------------------------------------------------------

bad = []
for m in range(1, 16):
    P = lambda k, m=m: gcd(k, m) == 1
    base = count_range(P, m)
    for j in range(0, 10):
        if count_range(P, m * j) != j * base:
            bad.append((m, j))
check("2. block counting holds for the coprimality predicate", not bad, f"{len(bad)} bad")

# Negative control: P k := (k < 3) is not 4-periodic.
Q = lambda k: k < 3
ctrl_fails = count_range(Q, 4 * 3) != 3 * count_range(Q, 4)
check(
    "2N. block counting GENUINELY FAILS for a non-periodic predicate",
    ctrl_fails,
    f"countRange Q 12 = {count_range(Q, 12)} vs 3*countRange Q 4 = {3 * count_range(Q, 4)}",
)


# ---------------------------------------------------------------------------
# 3. The gcd bridge, which is the ONLY place `d | m` is used:
#       d | m  ->  ( gcd(k, m*d) = 1  <->  gcd(k, m) = 1 )
#    No primality anywhere.  Negative control at d NOT dividing m.
# ---------------------------------------------------------------------------

bad = []
for m in range(1, 16):
    for d in range(1, 16):
        if m % d:
            continue
        for k in range(0, m * d):
            if (gcd(k, m * d) == 1) != (gcd(k, m) == 1):
                bad.append((m, d, k))
check("3. gcd bridge holds whenever d | m", not bad, f"{len(bad)} bad")

nondiv_fail = [
    (m, d)
    for m in range(1, 16)
    for d in range(1, 16)
    if m % d
    and any((gcd(k, m * d) == 1) != (gcd(k, m) == 1) for k in range(m * d))
]
check(
    "3N. the gcd bridge GENUINELY FAILS at d not dividing m",
    len(nondiv_fail) > 0,
    f"fails at {len(nondiv_fail)} non-dividing pairs, smallest {nondiv_fail[0] if nondiv_fail else None}",
)


# ---------------------------------------------------------------------------
# 4. LEMMA B -- the lane's central new counting result:
#       d | m  ->  totient (m * d) = totient m * d
#    NO primality, NO positivity, NO factorization.
# ---------------------------------------------------------------------------

bad = [
    (m, d)
    for m in range(0, 26)
    for d in range(1, 26)
    if m % d == 0 and totient(m * d) != totient(m) * d
]
check("4. LEMMA B: d | m -> totient (m*d) = totient m * d", not bad, f"{len(bad)} bad")

lb_ctrl = [
    (m, d)
    for m in range(1, 26)
    for d in range(1, 26)
    if m % d and totient(m * d) != totient(m) * d
]
check(
    "4N. LEMMA B GENUINELY FAILS at d not dividing m",
    len(lb_ctrl) > 0,
    f"fails at {len(lb_ctrl)} non-dividing pairs, smallest {lb_ctrl[0] if lb_ctrl else None}",
)

# d = 0 boundary: 0 | m forces m = 0, and both sides are 0.
check(
    "4B. LEMMA B boundary at d = 0 (forces m = 0) and at m = 0",
    totient(0 * 0) == totient(0) * 0 and all(totient(0 * d) == totient(0) * d for d in range(1, 9)),
)


# ---------------------------------------------------------------------------
# 5. totient_prime_pow: totient (p^k) = p^k - p^(k-1) for p prime, k >= 1.
#    Magnitudes kept small deliberately (kernel numerals are unary).
#    Negative control: a COMPOSITE base, where it genuinely fails.
# ---------------------------------------------------------------------------

bad = [
    (p, k)
    for p in PRIMES
    for k in range(1, 5)
    if p**k <= 2000 and totient(p**k) != p**k - p ** (k - 1)
]
check("5. totient (p^k) = p^k - p^(k-1) for prime p, 1<=k<=4", not bad, f"{len(bad)} bad")

tpp_ctrl = [
    (c, k)
    for c in COMPOSITES
    for k in range(1, 4)
    if c**k <= 2000 and totient(c**k) != c**k - c ** (k - 1)
]
check(
    "5N. totient (p^k) = p^k - p^(k-1) GENUINELY FAILS at composite bases",
    len(tpp_ctrl) > 0,
    f"fails at {len(tpp_ctrl)} composite (c,k), smallest {tpp_ctrl[0] if tpp_ctrl else None}"
    + (f": totient({tpp_ctrl[0][0]}^{tpp_ctrl[0][1]}) = {totient(tpp_ctrl[0][0] ** tpp_ctrl[0][1])}" if tpp_ctrl else ""),
)

# The k = 1 instance must reduce to the already-landed totient_prime.
check(
    "5A. k = 1 collapses to the landed totient_prime (p - 1)",
    all(totient(p) == p - 1 for p in PRIMES),
)

# The multiplicative form the Rust proof actually builds, avoiding Nat.sub in
# the induction: totient (p^(j+1)) = (p-1) * p^j.
bad = [
    (p, j)
    for p in PRIMES
    for j in range(0, 4)
    if p ** (j + 1) <= 2000 and totient(p ** (j + 1)) != (p - 1) * p**j
]
check("5M. multiplicative form: totient (p^(j+1)) = (p-1) * p^j", not bad, f"{len(bad)} bad")

# ...and that the two forms agree, which is the final Nat.sub step.
bad = [
    (p, j)
    for p in PRIMES
    for j in range(0, 5)
    if p ** (j + 1) <= 4000 and p ** (j + 1) - p**j != (p - 1) * p**j
]
check("5S. p^(j+1) - p^j = (p-1) * p^j (the closing Nat.sub step)", not bad, f"{len(bad)} bad")


# ---------------------------------------------------------------------------
# 6. LEMMA A -- the prime step.  eps(x) = p if p | x else p - 1.
#       p prime  ->  totient (p * x) = eps(x) * totient x     (x >= 1)
#    Case p | x is LEMMA B at d = p; case p not| x is the landed
#    totient_mul_of_coprime plus totient_prime.
# ---------------------------------------------------------------------------


def eps(p: int, x: int) -> int:
    return p if x % p == 0 else p - 1


bad = [
    (p, x)
    for p in PRIMES
    for x in range(1, 30)
    if totient(p * x) != eps(p, x) * totient(x)
]
check("6. LEMMA A: totient (p*x) = eps(x) * totient x, p prime", not bad, f"{len(bad)} bad")

la_ctrl = [
    (c, x)
    for c in COMPOSITES
    for x in range(1, 30)
    if totient(c * x) != eps(c, x) * totient(x)
]
check(
    "6N. LEMMA A GENUINELY FAILS at a composite multiplier",
    len(la_ctrl) > 0,
    f"fails at {len(la_ctrl)} composite (c,x), smallest {la_ctrl[0] if la_ctrl else None}",
)


# ---------------------------------------------------------------------------
# 7. TARGET 1 -- totient_dvd_of_dvd, and its uniqueness-free route.
#    Route: a | b, write b = a*d, peel ONE prime p from d at a time.  Each
#    step multiplies totient by eps (>= 1), so divisibility is preserved.
#    Uses only: every d > 1 has a prime divisor, plus LEMMA A.  No multiset.
# ---------------------------------------------------------------------------

bad = [
    (a, b)
    for a in range(1, 40)
    for b in range(1, 120)
    if b % a == 0 and totient(b) % totient(a) != 0
]
check("7. TARGET 1: a | b -> totient a | totient b", not bad, f"{len(bad)} bad")

t1_ctrl = [
    (a, b)
    for a in range(1, 40)
    for b in range(1, 120)
    if b % a and totient(a) and totient(b) % totient(a) != 0
]
check(
    "7N. TARGET 1's divisibility hypothesis is LOAD-BEARING",
    len(t1_ctrl) > 0,
    f"conclusion fails at {len(t1_ctrl)} non-dividing pairs, smallest {t1_ctrl[0] if t1_ctrl else None}",
)


def least_prime_factor(n: int) -> int:
    for q in range(2, n + 1):
        if n % q == 0:
            return q
    raise AssertionError


def target1_by_peeling(a: int, b: int) -> bool:
    """Simulate the induction the Rust proof would run.

    Strong induction on d = b/a: if d = 1 we are done; otherwise peel any
    prime p | d and step a -> a*p, d -> d/p.  At each step LEMMA A gives
    totient(a) | totient(a*p).  Uniqueness of the factorisation is never
    consulted -- ANY prime divisor works, and the chain is by transitivity.
    """
    d = b // a
    cur = a
    while d > 1:
        p = least_prime_factor(d)
        # the single step this induction rests on:
        if totient(cur * p) % totient(cur) != 0:
            return False
        if totient(cur * p) != eps(p, cur) * totient(cur):
            return False
        cur *= p
        d //= p
    return cur == b and totient(b) % totient(a) == 0


bad = [
    (a, b)
    for a in range(1, 30)
    for b in range(1, 120)
    if b % a == 0 and not target1_by_peeling(a, b)
]
check(
    "7R. TARGET 1's peeling induction terminates and every step holds",
    not bad,
    f"{len(bad)} bad",
)


# ---------------------------------------------------------------------------
# 8. TARGET 2 -- totient_gcd_mul_totient_mul, and the eps identity the
#    uniqueness-free induction reduces to.
#
#    Peel a prime p | gcd(m,n).  With m = p*m1, n = p*n', gcd(m,n) = p*d1
#    where d1 = gcd(m1,n'), the whole identity reduces by LEMMA A to
#
#        eps(m1 * n') * eps(gcd(m1,n')) = eps(m1) * eps(n')
#
#    which is a four-case truth table in [p|m1], [p|n'] -- and the ONLY
#    place primality is used, via Euclid's lemma p | ab -> p|a or p|b.
# ---------------------------------------------------------------------------

bad = [
    (a, b)
    for a in range(0, 26)
    for b in range(0, 26)
    if totient(gcd(a, b)) * totient(a * b) != totient(a) * totient(b) * gcd(a, b)
]
check("8. TARGET 2 identity holds over 0<=a,b<26 (incl. the a=0/b=0 boundary)", not bad, f"{len(bad)} bad")

collapse = [
    (a, b)
    for a in range(1, 26)
    for b in range(1, 26)
    if gcd(a, b) == 1 and totient(a * b) != totient(a) * totient(b)
]
check(
    "8A. TARGET 2 collapses to the LANDED theorem at coprime pairs",
    not collapse,
    "so the coprime half is already done",
)

noncoprime = [
    (a, b)
    for a in range(1, 13)
    for b in range(1, 13)
    if gcd(a, b) > 1 and totient(a * b) != totient(a) * totient(b)
]
check(
    "8N. TARGET 2 is STRICTLY STRONGER than multiplicativity",
    len(noncoprime) > 0,
    f"multiplicativity alone fails at {len(noncoprime)} non-coprime pairs with 1<=a,b<=12",
)

# The eps identity, exhaustively, at PRIME p -- the reduction's whole content.
bad = [
    (p, m1, n1)
    for p in PRIMES
    for m1 in range(1, 20)
    for n1 in range(1, 20)
    if eps(p, m1 * n1) * eps(p, gcd(m1, n1)) != eps(p, m1) * eps(p, n1)
]
check("8E. the eps identity holds for every PRIME p", not bad, f"{len(bad)} bad")

eps_ctrl = [
    (c, m1, n1)
    for c in COMPOSITES
    for m1 in range(1, 20)
    for n1 in range(1, 20)
    if eps(c, m1 * n1) * eps(c, gcd(m1, n1)) != eps(c, m1) * eps(c, n1)
]
check(
    "8EN. the eps identity GENUINELY FAILS at composite p (Euclid is load-bearing)",
    len(eps_ctrl) > 0,
    f"fails at {len(eps_ctrl)} composite triples, smallest {eps_ctrl[0] if eps_ctrl else None}",
)

# Euclid's lemma is exactly the step that makes the eps identity true.
check(
    "8EU. p | m*n <-> p|m or p|n for prime p (the ONLY use of primality)",
    all(
        ((m * n) % p == 0) == (m % p == 0 or n % p == 0)
        for p in PRIMES
        for m in range(1, 20)
        for n in range(1, 20)
    ),
)
euclid_ctrl = [
    (c, m, n)
    for c in COMPOSITES
    for m in range(1, 20)
    for n in range(1, 20)
    if ((m * n) % c == 0) != (m % c == 0 or n % c == 0)
]
check(
    "8EUN. Euclid's lemma GENUINELY FAILS at composite moduli",
    len(euclid_ctrl) > 0,
    f"smallest {euclid_ctrl[0] if euclid_ctrl else None}",
)

# gcd(p*a, p*b) = p*gcd(a,b) -- the other structural step of the reduction.
check(
    "8G. gcd (p*a) (p*b) = p * gcd a b",
    all(gcd(p * a, p * b) == p * gcd(a, b) for p in range(1, 13) for a in range(0, 20) for b in range(0, 20)),
)


def target2_by_peeling(m: int, n: int) -> bool:
    """Simulate TARGET 2's induction on d = gcd(m,n), peeling one prime.

    Reduces (m, n) to (m/p, n/p) whose gcd is strictly smaller, terminating at
    the coprime base case = the landed theorem.  Uniqueness is never used.
    """
    if m == 0 or n == 0:
        return totient(gcd(m, n)) * totient(m * n) == totient(m) * totient(n) * gcd(m, n)
    while gcd(m, n) > 1:
        p = least_prime_factor(gcd(m, n))
        m1, n1 = m // p, n // p
        # the reduction is exactly the eps identity plus LEMMA A four times
        if eps(p, m1 * n1) * eps(p, gcd(m1, n1)) != eps(p, m1) * eps(p, n1):
            return False
        if gcd(m, n) != p * gcd(m1, n1):
            return False
        m, n = m1, n1
    # base: coprime, i.e. the landed theorem
    return totient(m * n) == totient(m) * totient(n)


bad = [(m, n) for m in range(0, 26) for n in range(0, 26) if not target2_by_peeling(m, n)]
check("8R. TARGET 2's peeling induction terminates and every step holds", not bad, f"{len(bad)} bad")


# ---------------------------------------------------------------------------
# 9. TARGET 3 -- eq_or_eq_of_totient_eq_totient.
#    a | b, totient a = totient b  ->  a = b  or  2*a = b.
#    Route: the same peeling chain as TARGET 1.  Each step multiplies totient
#    by eps >= 1, and eps = 1 ONLY when p = 2 and 2 does not divide the
#    current value.  Two such steps are impossible (the first makes it even),
#    so the chain has length 0 or 1.
# ---------------------------------------------------------------------------

bad = [
    (a, b)
    for a in range(1, 60)
    for b in range(1, 200)
    if b % a == 0 and totient(a) == totient(b) and not (a == b or 2 * a == b)
]
check("9. TARGET 3 holds over 1<=a<60, 1<=b<200", not bad, f"{len(bad)} bad")

# Both disjuncts are REACHED, so neither is vacuous.
hits_eq = [(a, b) for a in range(1, 40) for b in range(1, 120) if b % a == 0 and totient(a) == totient(b) and a == b]
hits_two = [(a, b) for a in range(1, 40) for b in range(1, 120) if b % a == 0 and totient(a) == totient(b) and 2 * a == b]
check(
    "9A. BOTH disjuncts of TARGET 3 are reached (neither is vacuous)",
    len(hits_eq) > 0 and len(hits_two) > 0,
    f"a=b at {len(hits_eq)} pairs; 2a=b at {len(hits_two)} pairs, e.g. {hits_two[:4]}",
)

# eps = 1 exactly when p = 2 and x is odd -- the whole content of TARGET 3.
check(
    "9E. eps(p,x) = 1 iff p = 2 and x is odd",
    all(
        (eps(p, x) == 1) == (p == 2 and x % 2 == 1)
        for p in PRIMES
        for x in range(1, 40)
    ),
)

# ...and that the eps=1 step cannot happen twice: it makes x even.
check(
    "9T. after an eps = 1 step (p=2, x odd), x*2 is even so eps becomes 2",
    all(eps(2, x * 2) == 2 for x in range(1, 40) if x % 2 == 1),
)

# The divisibility hypothesis in TARGET 3 is load-bearing.
t3_ctrl = [
    (a, b)
    for a in range(1, 40)
    for b in range(1, 120)
    if b % a and totient(a) == totient(b) and not (a == b or 2 * a == b)
]
check(
    "9N. TARGET 3's divisibility hypothesis is LOAD-BEARING",
    len(t3_ctrl) > 0,
    f"conclusion fails at {len(t3_ctrl)} non-dividing pairs, smallest {t3_ctrl[0] if t3_ctrl else None}",
)


# ---------------------------------------------------------------------------
# 10. THE ASSESSMENT ITSELF: no step of any of the three routes consults a
#     factor MULTISET.  Checked by re-running TARGET 1 and TARGET 2's
#     inductions with a DIFFERENT (largest-first) choice of prime divisor and
#     requiring the same verdict -- if uniqueness were load-bearing, the two
#     orders could disagree.
# ---------------------------------------------------------------------------


def greatest_prime_factor(n: int) -> int:
    best = None
    for q in range(2, n + 1):
        if n % q == 0 and is_prime(q):
            best = q
    assert best is not None
    return best


def target1_by_peeling_greatest(a: int, b: int) -> bool:
    d, cur = b // a, a
    while d > 1:
        p = greatest_prime_factor(d)
        if totient(cur * p) % totient(cur) != 0:
            return False
        cur *= p
        d //= p
    return totient(b) % totient(a) == 0


agree = all(
    target1_by_peeling(a, b) == target1_by_peeling_greatest(a, b)
    for a in range(1, 26)
    for b in range(1, 100)
    if b % a == 0
)
check(
    "10. TARGET 1's route gives the same verdict for ANY choice of prime",
    agree,
    "least-first and greatest-first peeling agree -- the argument never needs the factorisation to be unique",
)


# ---------------------------------------------------------------------------
# 11. THE PRIME STEP AS A DIVISIBILITY, and a warning about its control.
#
#     Nat.totient_dvd_totient_mul_prime : q prime -> totient x | totient (x*q)
#
#     A composite-q control on THIS statement would be VACUOUS, and that is
#     worth measuring rather than assuming: the statement is TARGET 1
#     specialised (x always divides x*q), so it is true for EVERY q, prime or
#     not.  Primality is needed by the proof ROUTE -- `coprime_or_dvd_of_prime`
#     is what decides the case split -- not by the proposition.
#
#     Copying the composite control from `totient_prime_pow`, where it IS
#     discriminating, would produce a control that cannot fail.  The honest
#     discriminating control is the TRANSPOSED divisibility.
# ---------------------------------------------------------------------------

bad = [
    (x, q)
    for x in range(1, 40)
    for q in PRIMES
    if totient(x * q) % totient(x) != 0
]
check("11. the prime step: totient x | totient (x*q) for prime q", not bad, f"{len(bad)} bad")

composite_ctrl = [
    (x, c)
    for x in range(1, 40)
    for c in COMPOSITES
    if totient(x * c) % totient(x) != 0
]
check(
    "11V. a COMPOSITE control on the prime step would be VACUOUS -- it never fails",
    len(composite_ctrl) == 0,
    "true at every composite q too, because x | x*q always; primality is a "
    "requirement of the proof ROUTE, not of the statement",
)

transposed_ctrl = [
    (x, q)
    for x in range(1, 20)
    for q in PRIMES
    if q < 20 and totient(x) % totient(x * q) != 0
]
check(
    "11N. the TRANSPOSED divisibility GENUINELY FAILS (the usable control)",
    len(transposed_ctrl) > 0,
    f"fails at {len(transposed_ctrl)} pairs, smallest {transposed_ctrl[0] if transposed_ctrl else None}",
)


# ---------------------------------------------------------------------------

print()
print(f"{CHECKS} checks, {len(FAILURES)} failed")
if FAILURES:
    for f in FAILURES:
        print("  FAILED:", f)
    sys.exit(1)
print("all positive checks hold over their stated ranges;")
print("every negative control was asserted to GENUINELY fail and did.")
sys.exit(0)
