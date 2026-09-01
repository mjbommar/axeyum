#!/usr/bin/env python3
"""Numeric verification for ADR-1290: the floor-counting family.

Re-runnable:

    python3 docs/research/09-decisions/adr-1290-floor-count-checks.py

Every claim C* is paired with mutations M* that must be REFUTED. Two
mutations are recorded as SURVIVING, deliberately; the script asserts that
they survive, so a change that made either of them fail would also fail this
script. Exit status depends on the finding: any mutation that behaves other
than recorded exits 1.

The subject is the bridge between ADR-1260's rectangle partition (which is
phrased entirely in counts and needs no division) and the floor language
Eisenstein's lemma is classically stated in:

    countRange (fun j => ble (mul a (succ j)) B) n  =  min n (div B a)

with an intermediate, division-free counting core

    countRange (fun y => ble (succ y) c) n  =  min n c

and a relational bridge that never reduces `Nat.div` at all:

    divMod a B q r  ->  (a * s <= B  <->  s <= q)
"""

from __future__ import annotations

import sys

FAILURES: list[str] = []


def ok(label: str) -> None:
    print(f"  [ok ] {label}")


def bad(label: str, detail: str) -> None:
    print(f"  [FAIL] {label} -- {detail}")
    FAILURES.append(label)


def count_range(pred, n: int) -> int:
    """`Nat.countRange p n` -- the count of `j < n` with `p j` true."""
    return sum(1 for j in range(n) if pred(j))


def primes_upto(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for k in range(i * i, limit + 1, i):
                sieve[k] = False
    return [i for i, v in enumerate(sieve) if v]


ODD_PRIMES = [p for p in primes_upto(60) if p != 2]

# --------------------------------------------------------------------------
# C1 -- the counting core. No division anywhere in the statement.
# --------------------------------------------------------------------------


def c1(min_fn=min, pred_builder=None) -> tuple[bool, str]:
    if pred_builder is None:

        def pred_builder(c):
            return lambda y: y + 1 <= c

    for c in range(0, 41):
        for n in range(0, 41):
            lhs = count_range(pred_builder(c), n)
            rhs = min_fn(n, c)
            if lhs != rhs:
                return False, f"c={c} n={n}: {lhs} != {rhs}"
    return True, "1681 (c, n) pairs"


# --------------------------------------------------------------------------
# C2 -- the relational floor adjunction, the step that decides EMIT vs stuck.
# --------------------------------------------------------------------------


def c2(quotient_fn=lambda b, a: b // a) -> tuple[bool, str]:
    for a in range(1, 21):
        for b in range(0, 61):
            q = quotient_fn(b, a)
            for s in range(0, 31):
                left = a * s <= b
                right = s <= q
                if left != right:
                    return False, f"a={a} B={b} s={s}: ({left}) != ({right})"
    return True, "20*61*31 = 37820 (a, B, s) triples"


# --------------------------------------------------------------------------
# C3 -- the two composed: the floor-counting lemma itself.
# --------------------------------------------------------------------------


def c3(use_min=True) -> tuple[bool, str]:
    for a in range(1, 21):
        for b in range(0, 61):
            for n in range(0, 31):
                lhs = count_range(lambda j: a * (j + 1) <= b, n)
                rhs = min(n, b // a) if use_min else b // a
                if lhs != rhs:
                    return False, f"a={a} B={b} n={n}: {lhs} != {rhs}"
    return True, "20*61*31 = 37820 (a, B, n) triples"


# --------------------------------------------------------------------------
# C4 -- Eisenstein's row count is this lemma, and the `min` never binds there.
# --------------------------------------------------------------------------


def c4(m_of=lambda p: (p - 1) // 2) -> tuple[bool, str]:
    pairs = 0
    for p in ODD_PRIMES:
        for q in ODD_PRIMES:
            if p == q:
                continue
            m, n = m_of(p), (q - 1) // 2
            for x in range(1, m + 1):
                b = q * x
                # strict and non-strict agree: no lattice point on p*y = q*x
                strict = count_range(lambda y: p * (y + 1) < b, n)
                nonstrict = count_range(lambda y: p * (y + 1) <= b, n)
                if strict != nonstrict:
                    return False, f"p={p} q={q} x={x}: strict {strict} != non-strict {nonstrict}"
                if nonstrict != min(n, b // p):
                    return False, f"p={p} q={q} x={x}: {nonstrict} != min({n},{b // p})"
                if b // p > n:
                    return False, f"p={p} q={q} x={x}: floor {b // p} exceeds n={n}"
            pairs += 1
    return True, f"{pairs} ordered prime pairs"


# --------------------------------------------------------------------------
# C5 -- the assembled lattice identity, in the min form the lemma produces.
# --------------------------------------------------------------------------


def c5(exponent=lambda m, n: m * n) -> tuple[bool, str]:
    pairs = 0
    for p in ODD_PRIMES:
        for q in ODD_PRIMES:
            if p >= q:
                continue
            m, n = (p - 1) // 2, (q - 1) // 2
            left = sum(min(n, (q * (x + 1)) // p) for x in range(m))
            right = sum(min(m, (p * (y + 1)) // q) for y in range(n))
            if left + right != exponent(m, n):
                return False, f"p={p} q={q}: {left}+{right} != {exponent(m, n)}"
            pairs += 1
    return True, f"{pairs} unordered prime pairs"


# --------------------------------------------------------------------------

print("CLAIMS")
for label, fn in [
    ("C1 countRange (fun y => ble (succ y) c) n = min n c", c1),
    ("C2 divMod a B q r -> (a*s <= B <-> s <= q), at q = div B a", c2),
    ("C3 countRange (fun j => ble (mul a (succ j)) B) n = min n (div B a)", c3),
    ("C4 Eisenstein's row count IS C3, and its min never binds", c4),
    ("C5 the assembled lattice identity in min form", c5),
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
        "C1 with min replaced by max",
        lambda: c1(min_fn=max)[0],
        False,
    ),
    (
        "M2",
        "C1 with the predicate off by one (ble y c instead of ble (succ y) c)",
        lambda: c1(pred_builder=lambda c: (lambda y: y <= c))[0],
        False,
    ),
    (
        "M3",
        "C2 with the quotient taken as div (pred B) a",
        lambda: c2(quotient_fn=lambda b, a: (b - 1) // a if b > 0 else 0)[0],
        False,
    ),
    (
        "M4",
        "C3 with the min dropped (claiming = div B a unconditionally)",
        lambda: c3(use_min=False)[0],
        False,
    ),
    (
        "M5",
        "C4 with m taken as (p+1)/2 instead of (p-1)/2",
        lambda: c4(m_of=lambda p: (p + 1) // 2)[0],
        False,
    ),
    (
        "M6",
        "C5 with the right-hand side m+n instead of m*n",
        lambda: c5(exponent=lambda m, n: m + n)[0],
        False,
    ),
    (
        "M7",
        "C1 stated as min c n rather than min n c",
        lambda: c1(min_fn=lambda a, b: min(b, a))[0],
        True,
    ),
    (
        "M8",
        "C5 with the min dropped entirely (bare floors)",
        lambda: _c5_no_min(),
        True,
    ),
]


def _c5_no_min() -> bool:
    for p in ODD_PRIMES:
        for q in ODD_PRIMES:
            if p >= q:
                continue
            m, n = (p - 1) // 2, (q - 1) // 2
            left = sum((q * (x + 1)) // p for x in range(m))
            right = sum((p * (y + 1)) // q for y in range(n))
            if left + right != m * n:
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
            "survived but was expected to be refuted"
            if survived
            else "was refuted but is recorded as a survivor",
        )

print()
if FAILURES:
    print(f"FAIL: {len(FAILURES)} check(s) did not behave as recorded")
    sys.exit(1)
print("PASS: every claim holds and every control behaves as recorded")
