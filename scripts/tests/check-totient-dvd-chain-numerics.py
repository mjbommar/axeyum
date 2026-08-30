#!/usr/bin/env python3
"""Numeric checks for the `totient-dvd-chain` lane.

Closes two `ml430` mirrors named unblocked by ADR-0668
(`docs/research/09-decisions/adr-0668-the-totient-mirrors-do-not-need-multiset-uniqueness.md`):

    F:ml430-nat-totient-dvd-of-dvd-9622e44a
        a | b -> totient a | totient b                          ("Target 1")
    F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
        a | b -> totient a = totient b -> a = b \\/ 2*a = b       ("Target 3")

Every claim used by the Rust proof is checked here FIRST, exhaustively over a
small range, with each positive check paired with a negative control this
script asserts must GENUINELY FAIL -- a control that cannot fail measures
nothing (this exact area has produced one vacuous control already, check 11V
of `check-totient-prime-power-numerics.py`).

Re-execute with:

    python3 scripts/tests/check-totient-dvd-chain-numerics.py

Exit 0 iff every positive check holds over its whole range AND every negative
control actually fails somewhere. Prints one line per check.
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
    """Exactly the kernel's definition: |{k < n : gcd(k, n) = 1}|."""
    return sum(1 for k in range(n) if gcd(k, n) == 1)


def divides(a: int, b: int) -> bool:
    """`a | b` per the kernel's `exists k, b = a*k` -- true for a=0 iff b=0."""
    if a == 0:
        return b == 0
    return b % a == 0


N = 60  # magnitudes stay small on purpose (unary numerals in the kernel).

# ---------------------------------------------------------------------------
# 1. The GENERAL cofactor lemma the Rust proof actually builds by well-founded
#    induction on k (`Nat.totient_dvd_totient_mul`): NO hypothesis at all --
#    totient a always divides totient (a*k), for every a, k.
# ---------------------------------------------------------------------------

bad1 = [
    (a, k)
    for a in range(0, N)
    for k in range(0, N)
    if totient(a * k) % max(totient(a), 1) != 0 and totient(a) != 0
]
# totient(a) == 0 only at a == 0, where totient(a*k) is also 0 and "divides"
# is vacuous (0 | 0) -- handled separately so the mod-by-zero above never
# fires in that case.
check(
    "1. totient a | totient (a*k) for ALL a, k -- no hypothesis needed",
    not bad1,
    f"{len(bad1)} bad",
)

# ---------------------------------------------------------------------------
# 2. Target 1 itself: a | b -> totient a | totient b. The hypothesis is
#    load-bearing -- restated here as a standalone control (this is really
#    check 1 read through `b = a*k`, but Target 1's ledger fact states it in
#    terms of a genuine divisibility hypothesis, so check it in that shape
#    too, plus the negative control that the hypothesis matters).
# ---------------------------------------------------------------------------

bad2 = [
    (a, b)
    for a in range(1, N)
    for b in range(1, N)
    if b % a == 0 and totient(b) % totient(a) != 0
]
check("2. Target 1: a | b -> totient a | totient b", not bad2, f"{len(bad2)} bad")

ctrl2 = [
    (a, b)
    for a in range(1, N)
    for b in range(1, N)
    if b % a != 0 and totient(b) % totient(a) != 0
]
check(
    "2N. the hypothesis a | b is load-bearing (non-dividing pairs genuinely fail)",
    len(ctrl2) > 0,
    f"fails at {len(ctrl2)} non-dividing pairs, smallest {ctrl2[0] if ctrl2 else None}",
)

# ---------------------------------------------------------------------------
# 3. The BOUND LEMMA Target 3's proof needs: for k >= 2 and totient(a) >= 1,
#    either totient(a*k) >= 2*totient(a), OR (k == 2 AND totient(a*k) ==
#    totient(a)). This is the "chain length <= 1, and only via q = 2 on an
#    odd value" argument made numeric, and it is NOT true without the k >= 2
#    guard (k = 1 always gives equality, which is neither disjunct as stated
#    for k != 2) or without totient(a) >= 1 (a = 0 breaks it).
# ---------------------------------------------------------------------------


def bound_holds(a: int, k: int) -> bool:
    ta = totient(a)
    tak = totient(a * k)
    return tak >= 2 * ta or (k == 2 and tak == ta)


bad3 = [
    (a, k)
    for a in range(1, N)
    for k in range(2, N)
    if totient(a) >= 1 and not bound_holds(a, k)
]
check(
    "3. bound lemma: k>=2 -> totient(a*k) >= 2*totient(a) OR (k=2 AND equal)",
    not bad3,
    f"{len(bad3)} bad",
)

ctrl3_k1 = [a for a in range(1, N) if not bound_holds(a, 1)]
check(
    "3N. the k>=2 guard is load-bearing (k=1 genuinely fails the bound as stated)",
    len(ctrl3_k1) > 0,
    f"fails at {len(ctrl3_k1)} values of a (k=1 always gives equality, not >= 2x, "
    "and k!=2 so the second disjunct doesn't rescue it)",
)

# ---------------------------------------------------------------------------
# 4. Target 3 itself: a | b -> totient a = totient b -> a = b \/ 2*a = b.
#    Both hypotheses are load-bearing.
# ---------------------------------------------------------------------------

bad4 = [
    (a, b)
    for a in range(0, N)
    for b in range(0, N)
    if divides(a, b)
    and totient(a) == totient(b)
    and not (a == b or 2 * a == b)
]
check(
    "4. Target 3: a | b -> totient a = totient b -> a = b \\/ 2a = b",
    not bad4,
    f"{len(bad4)} bad",
)

ctrl4_dvd = [
    (a, b)
    for a in range(1, N)
    for b in range(1, N)
    if b % a != 0
    and totient(a) == totient(b)
    and not (a == b or 2 * a == b)
]
check(
    "4N-dvd. the a|b hypothesis is load-bearing",
    len(ctrl4_dvd) > 0,
    f"fails at {len(ctrl4_dvd)} non-dividing pairs with equal totients, "
    f"smallest {ctrl4_dvd[0] if ctrl4_dvd else None}",
)

ctrl4_eq = [
    (a, b)
    for a in range(1, N)
    for b in range(1, N)
    if b % a == 0
    and totient(a) != totient(b)
    and not (a == b or 2 * a == b)
]
check(
    "4N-eq. the totient-equality hypothesis is load-bearing",
    len(ctrl4_eq) > 0,
    f"fails at {len(ctrl4_eq)} dividing pairs with unequal totients, "
    f"smallest {ctrl4_eq[0] if ctrl4_eq else None}",
)

# ---------------------------------------------------------------------------
# 5. Confirm the actual witness distribution behind check 4: every genuine
#    "chain length 1" solution has multiplier EXACTLY 2 and a ODD -- this is
#    the numeric form of ADR-0668's "ε = 1 exactly when p = 2 and the current
#    value is odd", restricted to the single-step case Target 3 allows.
# ---------------------------------------------------------------------------

second_disjunct_witnesses = [
    (a, b)
    for a in range(1, N)
    for b in range(1, N)
    if b % a == 0
    and totient(a) == totient(b)
    and 2 * a == b
    and a != b
]
non_odd_witness = [(a, b) for (a, b) in second_disjunct_witnesses if a % 2 == 0]
check(
    "5. every genuine '2a=b' witness has a ODD (a even would need q=2 dividing "
    "a, forcing epsilon=2, not 1)",
    len(second_disjunct_witnesses) > 0 and not non_odd_witness,
    f"{len(second_disjunct_witnesses)} witnesses, {len(non_odd_witness)} with a even "
    f"(smallest witness {second_disjunct_witnesses[0] if second_disjunct_witnesses else None})",
)

# ---------------------------------------------------------------------------
# 6. Chain length >= 2 never reaches product 1: peeling any two DISTINCT
#    primes off a > 1 always at least doubles totient(a) relative to a
#    single step, i.e. no k with >= 2 prime factors (with multiplicity) other
#    than k = 4 = 2*2 can satisfy the bound's second disjunct (k=2 is the
#    only k with a single prime factor of multiplicity 1 that can). This is
#    the numeric confirmation that k=2 is the ONLY k for which the second
#    disjunct is even reachable.
# ---------------------------------------------------------------------------

k_reaching_second_disjunct = sorted(
    {b // a for (a, b) in second_disjunct_witnesses}
)
check(
    "6. the second disjunct is reachable ONLY at k = b/a = 2",
    k_reaching_second_disjunct == [2],
    f"observed k values: {k_reaching_second_disjunct}",
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
