#!/usr/bin/env python3
"""Numeric checks for ADR-1235 -- the RESIDUE half of the first supplementary law.

Every claim below is a step the Rust proof actually takes, in the order it takes
it, so a claim that is false here is a proof that would not have closed. Each
claim is paired with a MUTATED form that must be refuted; the script exits 1 if
any claim fails OR if any mutation survives.

Re-runnable:

    python3 docs/research/09-decisions/adr-1235-first-supplementary-residue-checks.py
"""

from __future__ import annotations

import sys

LIMIT = 500


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


ODD_PRIMES = [p for p in range(3, LIMIT) if is_prime(p)]
EVEN_M_PRIMES = [p for p in ODD_PRIMES if ((p - 1) // 2) % 2 == 0]


def nsub(a: int, b: int) -> int:
    """`Nat.sub` -- truncated, exactly what the kernel computes."""
    return a - b if a > b else 0


def npred(a: int) -> int:
    return nsub(a, 1)


def fact(n: int) -> int:
    r = 1
    for k in range(1, n + 1):
        r *= k
    return r


# ---------------------------------------------------------------------------
# claims
# ---------------------------------------------------------------------------

Claim = tuple[str, int, int]  # label, failures, cases
claims: list[Claim] = []
controls: list[tuple[str, bool]] = []


def claim(label: str, cases: list, pred) -> None:
    bad = [c for c in cases if not pred(c)]
    claims.append((label, len(bad), len(cases)))
    if bad:
        claims[-1] = (label + f"  first bad: {bad[0]!r}", len(bad), len(cases))


def control(label: str, cases: list, pred) -> None:
    """The mutated form MUST fail somewhere."""
    refuted = any(not pred(c) for c in cases)
    controls.append((label, refuted))


# --- C1: the reflection is an involution on [0,m), and ONLY there -----------
#
# rho_m(k) := Nat.sub (Nat.pred m) k.  `InjectiveOn rho m` is derived from the
# BOUNDED involution law, never a global one -- rho is NOT a global involution,
# because Nat.sub truncates.

pairs_in = [(m, k) for m in range(0, 40) for k in range(0, m)]
claim(
    "C1  rho(rho k) = k for k < m   (the bounded involution law)",
    pairs_in,
    lambda mk: nsub(npred(mk[0]), nsub(npred(mk[0]), mk[1])) == mk[1],
)
pairs_all = [(m, k) for m in range(0, 40) for k in range(0, 45)]
control(
    "C1 with the k < m bound dropped (rho is NOT a global involution)",
    pairs_all,
    lambda mk: nsub(npred(mk[0]), nsub(npred(mk[0]), mk[1])) == mk[1],
)

# --- C2: MapsInto ----------------------------------------------------------
claim(
    "C2  rho k < m for k < m   (MapsInto; needs m > 0, which k < m supplies)",
    pairs_in,
    lambda mk: nsub(npred(mk[0]), mk[1]) < mk[0],
)
control(
    "C2 with the k < m bound dropped (fails at m = 0)",
    pairs_all,
    lambda mk: nsub(npred(mk[0]), mk[1]) < mk[0],
)

# --- C3: Nat.sub_sub_self, the lemma that has to be BUILT -------------------
#
# sub n (sub n k) = k given k <= n.  Route: sub_add_cancel gives
# add (sub n k) k = n; rewrite the OUTER n only; add_sub_cancel_left closes.
le_pairs = [(n, k) for n in range(0, 40) for k in range(0, n + 1)]
claim(
    "C3  sub n (sub n k) = k for k <= n   (Nat.sub_sub_self)",
    le_pairs,
    lambda nk: nsub(nk[0], nsub(nk[0], nk[1])) == nk[1],
)
claim(
    "C3b add (sub n k) k = n for k <= n   (Nat.sub_add_cancel, the input)",
    le_pairs,
    lambda nk: nsub(nk[0], nk[1]) + nk[1] == nk[0],
)
control(
    "C3 with the k <= n hypothesis dropped",
    [(n, k) for n in range(0, 40) for k in range(0, 45)],
    lambda nk: nsub(nk[0], nsub(nk[0], nk[1])) == nk[1],
)

# --- C4: the pointwise index identity --------------------------------------
#
# The upper-half factor at reflected index k is
#     G(rho k) = ofNat (succ (add m (rho k)))
# and the Rust proof needs, in Nat:
#     succ (m + rho k) + succ k = succ (2m)      for k < m.
claim(
    "C4  succ (m + rho k) + succ k = succ (2m) for k < m   (pointwise index)",
    pairs_in,
    lambda mk: (1 + mk[0] + nsub(npred(mk[0]), mk[1])) + (1 + mk[1])
    == 1 + 2 * mk[0],
)
control(
    "C4 at k = m (one past the range) -- must NOT hold",
    [(m, m) for m in range(1, 40)],
    lambda mk: (1 + mk[0] + nsub(npred(mk[0]), mk[1])) + (1 + mk[1])
    == 1 + 2 * mk[0],
)
control(
    "C4 with succ dropped from the reflected factor",
    pairs_in,
    lambda mk: (mk[0] + nsub(npred(mk[0]), mk[1])) + (1 + mk[1]) == 1 + 2 * mk[0],
)

# --- C5: the split ---------------------------------------------------------
#
# prodRange_split F m m:  (2m)! = m! * prod_{k<m} (m + k + 1).
claim(
    "C5  (2m)! = m! * prod_{k<m} (m+k+1)   (Int.prodRange_split at a=b=m)",
    list(range(0, 25)),
    lambda m: fact(2 * m)
    == fact(m) * __import__("math").prod(m + k + 1 for k in range(m)),
)
control(
    "C5 with the split point moved to m-1",
    list(range(2, 25)),
    lambda m: fact(2 * m)
    == fact(m - 1) * __import__("math").prod(m - 1 + k + 1 for k in range(m)),
)

# --- C6: the permutation actually reverses the upper half -------------------
claim(
    "C6  prod_{k<m} (m + rho k + 1) = prod_{k<m} (2m - k)   (the reversal)",
    list(range(0, 30)),
    lambda m: __import__("math").prod(m + nsub(npred(m), k) + 1 for k in range(m))
    == __import__("math").prod(2 * m - k for k in range(m)),
)

# --- C7: the pointwise congruence, over real primes ------------------------
claim(
    "C7  ofNat(succ(m + rho k)) = -(k+1)  (mod p),  p = 2m+1, k < m",
    [(p, k) for p in ODD_PRIMES for k in range((p - 1) // 2)],
    lambda pk: (1 + (pk[0] - 1) // 2 + nsub(npred((pk[0] - 1) // 2), pk[1]))
    % pk[0]
    == (-(pk[1] + 1)) % pk[0],
)
control(
    "C7 without the reflection (upper half taken in increasing order)",
    [(p, k) for p in ODD_PRIMES for k in range((p - 1) // 2)],
    lambda pk: (1 + (pk[0] - 1) // 2 + pk[1]) % pk[0] == (-(pk[1] + 1)) % pk[0],
)

# --- C8: the scaled-index collapse and the sign ----------------------------
claim(
    "C8  prod_{k<m} ((-1)*(k+1)) = (-1)^m * m!   (prodRange_scaledIndex...)",
    list(range(0, 30)),
    lambda m: __import__("math").prod(-(k + 1) for k in range(m))
    == ((-1) ** m) * fact(m),
)
claim(
    "C8b (-1)^m = 1 for even m   (Int.pow_neg_one_of_even)",
    [m for m in range(0, 40) if m % 2 == 0],
    lambda m: (-1) ** m == 1,
)
control(
    "C8b extended to odd m",
    list(range(0, 40)),
    lambda m: (-1) ** m == 1,
)

# --- C9: the assembly, end to end, at real primes --------------------------
claim(
    "C9  m even => (m!)^2 = -1 (mod p) and m! is the residue witness",
    EVEN_M_PRIMES,
    lambda p: (fact((p - 1) // 2) ** 2) % p == (p - 1) % p,
)
control(
    "C9 extended to odd m (the half this lane does NOT prove)",
    ODD_PRIMES,
    lambda p: (fact((p - 1) // 2) ** 2) % p == (p - 1) % p,
)

# --- C10: the hypotheses are SATISFIABLE, and vacuous exactly at m = 0 ------
#
# The kernel proof never constructs a PrimeCond witness, so this is the
# outside-the-kernel evidence that the theorem is not vacuously true.
claim(
    "C10 there exist m with m even AND 2m+1 prime (non-vacuity, from outside)",
    [0],
    lambda _: len(EVEN_M_PRIMES) > 0,
)
claim(
    "C10b at m = 0 the modulus is 1, which is NOT prime (the excluded boundary)",
    [0],
    lambda _: not is_prime(1),
)

# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------

print(f"odd primes checked: {len(ODD_PRIMES)} (p < {LIMIT})")
print(f"of which m = (p-1)/2 is even: {len(EVEN_M_PRIMES)}")
print()
print("CLAIMS -- every row must be 0 failures")
ok = True
for label, bad, total in claims:
    mark = "ok " if bad == 0 else "FAIL"
    if bad:
        ok = False
    print(f"  [{mark}] {label}: {bad} failures of {total}")

print()
print("CONTROLS -- every mutated claim must be REFUTED")
for label, refuted in controls:
    mark = "ok " if refuted else "FAIL"
    if not refuted:
        ok = False
    print(f"  [{mark}] {label}: {'refuted' if refuted else 'SURVIVED'}")

print()
if ok:
    print("PASS: every claim holds and every control is refuted")
    sys.exit(0)
print("FAIL: a claim failed or a mutation survived")
sys.exit(1)
