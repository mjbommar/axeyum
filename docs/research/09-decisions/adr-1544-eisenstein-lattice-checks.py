#!/usr/bin/env python3
"""Numeric checks for ADR-1544.

Claims C1-C5 and controls M1-M10 for the three declarations the `eisenstein-2`
lane landed:

    Nat.ble_select_add_of_ne
    Nat.eisenstein_floor_sum
    Nat.gauss_fold_sumRange_eq

**The exit status depends on the finding**, not on the run completing: a claim
that fails, or a control that behaves other than as recorded, prints and exits
1. Two controls are recorded as DELIBERATE SURVIVORS and asserted to survive;
each records something no numeric check can separate, which is why the
corresponding declared type is pinned character for character in the module's
own test file.

Run:  python3 docs/research/09-decisions/adr-1544-eisenstein-lattice-checks.py
"""

from __future__ import annotations

import sys
from math import gcd

FAILURES: list[str] = []


def ok(message: str) -> None:
    print(f"  ok    {message}")


def bad(label: str, detail: str = "") -> None:
    suffix = f" -- {detail}" if detail else ""
    print(f"  FAIL  {label}{suffix}")
    FAILURES.append(label)


ODD_PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]


# ---------------------------------------------------------------------------
# The three declarations, recomputed.
# ---------------------------------------------------------------------------


def selector_sum(a: int, b: int, strict: bool = False) -> int:
    """`bool_select_nat (ble a b) 1 0 + bool_select_nat (ble b a) 1 0`.

    With ``strict`` the two comparisons are `<` instead of `<=` -- the spelling
    ADR-1260 and ADR-1540 describe, and the one M10 records as numerically
    indistinguishable away from `a = b`.
    """
    if strict:
        return int(a < b) + int(b < a)
    return int(a <= b) + int(b <= a)


def floor_sum(pp: int, q: int, m: int, n: int, use_min: bool = True) -> int:
    """The left-hand side of `Nat.eisenstein_floor_sum`."""
    if use_min:
        rows = sum(min(n, (q * (x + 1)) // pp) for x in range(m))
        cols = sum(min(m, (pp * (y + 1)) // q) for y in range(n))
    else:
        rows = sum((q * (x + 1)) // pp for x in range(m))
        cols = sum((pp * (y + 1)) // q for y in range(n))
    return rows + cols


def gauss_fold(pp: int, a: int, k: int, fold: bool = True) -> int:
    """`Nat.gaussFold pp a k`; with ``fold=False``, the bare least residue."""
    residue = (a * k) % pp
    if fold and pp // 2 < residue:
        return pp - residue
    return residue


def fold_sum(m: int, a: int, fold: bool = True) -> int:
    """The right-hand side of `Nat.gauss_fold_sumRange_eq`."""
    pp = 2 * m + 1
    return sum(gauss_fold(pp, a, k, fold=fold) for k in range(1, m + 1))


# ---------------------------------------------------------------------------
# C1 -- the selector partition.
# ---------------------------------------------------------------------------


def c1(strict: bool = False, allow_equal: bool = False) -> tuple[bool, str]:
    pairs = 0
    for a in range(0, 41):
        for b in range(0, 41):
            if a == b and not allow_equal:
                continue
            if selector_sum(a, b, strict=strict) != 1:
                return False, f"a={a} b={b}: {selector_sum(a, b, strict=strict)} != 1"
            pairs += 1
    return True, f"{pairs} ordered pairs below 41"


# ---------------------------------------------------------------------------
# C2 -- the floor identity, in the generality the theorem states.
# ---------------------------------------------------------------------------


def c2(
    require_coprime: bool = True,
    require_bound: bool = True,
    use_min: bool = True,
    rhs=lambda m, n: None,
) -> tuple[bool, str]:
    instances = 0
    for pp in range(1, 21):
        for q in range(1, 21):
            if require_coprime and gcd(pp, q) != 1:
                continue
            bound = pp if require_bound else pp + 4
            for m in range(0, bound):
                for n in range(0, 12):
                    want = rhs(m, n)
                    if want is None:
                        want = n * m
                    if floor_sum(pp, q, m, n, use_min=use_min) != want:
                        return False, f"pp={pp} q={q} m={m} n={n}"
                    instances += 1
    return True, f"{instances} instances"


# ---------------------------------------------------------------------------
# C3 -- Eisenstein's own instance is INSIDE the theorem's hypotheses.
# ---------------------------------------------------------------------------


def c3(m_of=lambda p: (p - 1) // 2) -> tuple[bool, str]:
    """At distinct odd primes `p`, `q` with `m = (p-1)/2`: `gcd p q = 1` and
    `m < p`, so the theorem applies; and the identity holds there.

    This is what makes the restatement (coprimality + `m < p`, instead of two
    odd primes and the specific `m`, `n`) a GENERALIZATION rather than a
    different theorem.
    """
    pairs = 0
    for p in ODD_PRIMES:
        for q in ODD_PRIMES:
            if p == q:
                continue
            m, n = m_of(p), (q - 1) // 2
            if gcd(p, q) != 1:
                return False, f"p={p} q={q}: not coprime"
            if not m < p:
                return False, f"p={p} q={q}: m={m} is not below p"
            if floor_sum(p, q, m, n) != n * m:
                return False, f"p={p} q={q}: identity fails"
            pairs += 1
    return True, f"{pairs} ordered odd-prime pairs"


# ---------------------------------------------------------------------------
# C4 -- the additive Gauss bijection.
# ---------------------------------------------------------------------------


def c4(require_coprime: bool = True, fold: bool = True, lhs=None) -> tuple[bool, str]:
    instances = 0
    for m in range(0, 21):
        pp = 2 * m + 1
        for a in range(0, pp + 6):
            if require_coprime and gcd(a, pp) != 1:
                continue
            want = (m * (m + 1)) // 2 if lhs is None else lhs(m)
            if fold_sum(m, a, fold=fold) != want:
                return False, f"m={m} a={a}: {fold_sum(m, a, fold=fold)} != {want}"
            instances += 1
    return True, f"{instances} (m, a) instances"


# ---------------------------------------------------------------------------
# C5 -- the fold is a BIJECTION of [1,m], not merely sum-preserving.
# ---------------------------------------------------------------------------


def c5() -> tuple[bool, str]:
    instances = 0
    for m in range(1, 21):
        pp = 2 * m + 1
        for a in range(1, pp):
            if gcd(a, pp) != 1:
                continue
            image = sorted(gauss_fold(pp, a, k) for k in range(1, m + 1))
            if image != list(range(1, m + 1)):
                return False, f"m={m} a={a}: image {image}"
            instances += 1
    return True, f"{instances} (m, a) instances"


# ---------------------------------------------------------------------------

print("CLAIMS")
for label, fn in [
    ("C1 a <> b  =>  ble a b + ble b a (as selectors) = 1", c1),
    ("C2 the floor identity at coprime pp, q with m < pp and any n", c2),
    ("C3 Eisenstein's own instance satisfies both hypotheses", c3),
    ("C4 sum of folded least residues = 1 + 2 + ... + m", c4),
    ("C5 the fold is a bijection of [1,m], not merely sum-preserving", c5),
]:
    good, detail = fn()
    if good:
        ok(f"{label}: {detail}")
    else:
        bad(label, detail)

print()
print("CONTROLS -- each mutated claim must behave as recorded")

MUTATIONS = [
    (
        "M1",
        "C1 with the a = b case admitted (the hypothesis dropped)",
        lambda: c1(allow_equal=True)[0],
        False,
    ),
    (
        "M2",
        "C2 with coprimality dropped",
        lambda: c2(require_coprime=False)[0],
        False,
    ),
    (
        "M3",
        "C2 with the m < pp bound dropped",
        lambda: c2(require_bound=False)[0],
        False,
    ),
    (
        "M4",
        "C2 with the min dropped, over the coprime range the theorem states",
        lambda: c2(use_min=False)[0],
        False,
    ),
    (
        "M5",
        "the SAME min-free mutation restricted to odd prime pairs",
        lambda: _min_free_at_prime_pairs(),
        True,
    ),
    (
        "M6",
        "C2 with the right-hand side m + n instead of n * m",
        lambda: c2(rhs=lambda m, n: m + n)[0],
        False,
    ),
    (
        "M7",
        "C4 with coprimality dropped",
        lambda: c4(require_coprime=False)[0],
        False,
    ),
    (
        "M8",
        "C4 with the bare least residue in place of the fold",
        lambda: c4(fold=False)[0],
        False,
    ),
    (
        "M9",
        "C4 with the left-hand side m * m instead of m(m+1)/2",
        lambda: c4(lhs=lambda m: m * m)[0],
        False,
    ),
    (
        "M10",
        "C1 with STRICT comparisons, the spelling ADR-1260 describes",
        lambda: c1(strict=True)[0],
        True,
    ),
]


def _min_free_at_prime_pairs() -> bool:
    """M5: the min-free reading, at Eisenstein's own instances only.

    Recorded as a SURVIVOR, matching ADR-1290's `M8`: the `min` never binds
    when `m = (p-1)/2` and `n = (q-1)/2`, because `floor(q*x/p) <= (q-1)/2`
    there. `Nat.eisenstein_floor_sum` still carries the `min`, because M4
    shows the min-free reading is FALSE in the generality the theorem states.
    """
    for p in ODD_PRIMES:
        for q in ODD_PRIMES:
            if p >= q:
                continue
            m, n = (p - 1) // 2, (q - 1) // 2
            if floor_sum(p, q, m, n, use_min=False) != n * m:
                return False
    return True


for tag, desc, run, expect_survive in MUTATIONS:
    survived = run()
    if survived == expect_survive:
        if expect_survive:
            ok(f"{tag} {desc} SURVIVES (recorded as a survivor, not a passing control)")
        else:
            ok(f"{tag} {desc}: refuted")
    else:
        bad(
            f"{tag} {desc}",
            f"survived={survived}, recorded={expect_survive}",
        )

print()
if FAILURES:
    print(f"FAIL: {len(FAILURES)} check(s) did not behave as recorded")
    for name in FAILURES:
        print(f"  - {name}")
    sys.exit(1)
print("PASS: 5 claims and 10 controls behaved as recorded (2 recorded survivors)")
