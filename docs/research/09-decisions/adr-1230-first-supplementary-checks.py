#!/usr/bin/env python3
"""Re-runnable numeric checks for ADR-1230, the first supplementary law.

    python3 docs/research/09-decisions/adr-1230-first-supplementary-checks.py

Exit 0 only when every claim below holds AND every negative control fails.
The controls are the point: a checker whose claims are all trivially true
cannot tell you it measured anything, so each claim is paired with a mutated
form that MUST be refuted, and the script fails if a mutation survives.

Claims, in the order the proof uses them:

  C1  `-1` is a quadratic residue mod an odd prime `p` iff `p = 1 (mod 4)`.
      This is the law itself.
  C2  With `p = 2m+1`, `m` is ODD exactly when `p = 3 (mod 4)`. This is why
      `Int.firstSupplementaryLawNotResidue` takes `Nat.Odd m` rather than a
      hypothesis about `p mod 4`: `Nat.div`/`Nat.mod` are stuck at symbolic
      arguments, while `Nat.Odd`'s witness EMITS the shape `m = succ (k+k)`.
  C3  `(2m)^m = (-1)^m (mod p)` -- the half-power at `-1`'s natural
      representative `aa := 2m`, which is what Euler's criterion's
      non-residue detector is applied to (it quantifies over a NATURAL `aa`
      with `0 < aa < p`, so `-1` cannot be substituted directly).
  C4  `0 < 2m`, `2m < p` and `2 < p` all hold once `m >= 1`, and TWO of the
      three fail at `m = 0` -- `0 < 2m` and `2 < p`, while `2m < p` is
      `0 < 1` and holds regardless. This is why the two that need it take
      `m >= 1` from `Odd m` rather than from primality. (The first draft of
      this script asserted all three fail; this row refuted it.)
  C5  (the half NOT proved, recorded so the route can be checked before it is
      built) `(p-1)! = (-1)^m (m!)^2 (mod p)`, so at EVEN `m` Wilson's
      theorem gives `(m!)^2 = -1 (mod p)` and `m!` is an explicit residue
      witness for `-1`. This needs no converse of Euler's criterion.
"""

from __future__ import annotations

import sys

LIMIT = 500


def primes_up_to(n: int) -> list[int]:
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, n + 1, i):
                sieve[j] = False
    return [i for i, ok in enumerate(sieve) if ok]


ODD_PRIMES = [p for p in primes_up_to(LIMIT) if p > 2]


def is_residue(a: int, p: int) -> bool:
    """Brute force: is `a` a square mod `p`?"""
    target = a % p
    return any((x * x) % p == target for x in range(p))


def factorial_mod(n: int, p: int) -> int:
    acc = 1
    for j in range(1, n + 1):
        acc = acc * j % p
    return acc


def check(name: str, rows: list[tuple[object, bool]]) -> tuple[str, int, int]:
    """Return (name, failures, total)."""
    bad = sum(1 for _, ok in rows if not ok)
    return name, bad, len(rows)


def claims() -> list[tuple[str, int, int]]:
    out = []

    # C1 -- the law.
    out.append(
        check(
            "C1  -1 is a residue mod p  <=>  p = 1 (mod 4)",
            [(p, is_residue(-1, p) == (p % 4 == 1)) for p in ODD_PRIMES],
        )
    )

    # C2 -- the parity bridge the statement is phrased over.
    out.append(
        check(
            "C2  p = 2m+1:  m odd  <=>  p = 3 (mod 4)",
            [(p, (((p - 1) // 2) % 2 == 1) == (p % 4 == 3)) for p in ODD_PRIMES],
        )
    )

    # C3 -- the half-power at the natural representative of -1.
    out.append(
        check(
            "C3  (2m)^m = (-1)^m (mod p)",
            [
                (p, pow(p - 1, (p - 1) // 2, p) == pow(-1, (p - 1) // 2) % p)
                for p in ODD_PRIMES
            ],
        )
    )

    # C4 -- the three side conditions, and that all three FAIL at m = 0.
    side = []
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        side.append((p, 0 < 2 * m and 2 * m < p and 2 < p))
    # At `m = 0` the modulus is `1`: `0 < 2m` and `2 < p` both FAIL, while
    # `2m < p` (i.e. `0 < 1`) still HOLDS. So exactly two of the three need
    # `m >= 1`, not all three -- the first draft of this script claimed all
    # three and this row is what caught it.
    side.append(("m=0: 0 < 2m fails", not 0 < 2 * 0))
    side.append(("m=0: 2 < p fails", not 2 < 2 * 0 + 1))
    side.append(("m=0: 2m < p still HOLDS", 2 * 0 < 2 * 0 + 1))
    out.append(
        check("C4  0 < 2m < p and 2 < p; two of the three fail at m = 0", side)
    )

    # C5 -- the Wilson route to the half that is NOT proved.
    wilson = []
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        lhs = factorial_mod(p - 1, p)
        fm = factorial_mod(m, p)
        rhs = pow(-1, m) * fm * fm % p
        wilson.append((p, lhs == rhs))
    out.append(check("C5a (p-1)! = (-1)^m (m!)^2 (mod p)", wilson))

    witness = []
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        if m % 2 == 0:
            fm = factorial_mod(m, p)
            witness.append((p, fm * fm % p == (p - 1) % p))
    out.append(check("C5b m even  =>  (m!)^2 = -1 (mod p), witness m!", witness))

    return out


def controls() -> list[tuple[str, bool]]:
    """Each entry is (description, `the mutated claim was correctly refuted`).

    A control that PASSES its own mutated claim would mean the corresponding
    check cannot fail, which is worse than having no check.
    """
    out = []

    # Mutate C1's residue class: `p = 3 (mod 4)` instead of `p = 1 (mod 4)`.
    bad = sum(1 for p in ODD_PRIMES if is_residue(-1, p) != (p % 4 == 3))
    out.append(("C1 with the residue class transposed", bad > 0))

    # Mutate C2's parity: `m` EVEN against `p = 3 (mod 4)`.
    bad = sum(
        1 for p in ODD_PRIMES if ((((p - 1) // 2) % 2 == 0) != (p % 4 == 3))
    )
    out.append(("C2 with the parity transposed", bad > 0))

    # Mutate C3's sign: `(2m)^m = (-1)^(m+1)`.
    bad = sum(
        1
        for p in ODD_PRIMES
        if pow(p - 1, (p - 1) // 2, p) != pow(-1, (p - 1) // 2 + 1) % p
    )
    out.append(("C3 with the sign exponent shifted by one", bad > 0))

    # Mutate C5a's sign: drop the `(-1)^m` factor entirely.
    bad = 0
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        fm = factorial_mod(m, p)
        if factorial_mod(p - 1, p) != fm * fm % p:
            bad += 1
    out.append(("C5a without the (-1)^m factor", bad > 0))

    # Mutate C5b's parity: claim `(m!)^2 = -1` at ODD `m` too. This is the
    # one that would make the unproved half look free, so it matters most.
    bad = 0
    tried = 0
    for p in ODD_PRIMES:
        m = (p - 1) // 2
        if m % 2 == 1:
            tried += 1
            fm = factorial_mod(m, p)
            if fm * fm % p != (p - 1) % p:
                bad += 1
    out.append((f"C5b extended to odd m ({tried} cases)", bad > 0))

    return out


def main() -> int:
    print(f"odd primes checked: {len(ODD_PRIMES)} (p < {LIMIT})\n")
    failed = 0

    print("CLAIMS -- every row must be 0 failures")
    for name, bad, total in claims():
        status = "ok " if bad == 0 else "FAIL"
        print(f"  [{status}] {name}: {bad} failures of {total}")
        if bad:
            failed += 1

    print("\nCONTROLS -- every mutated claim must be REFUTED")
    for name, refuted in controls():
        status = "ok " if refuted else "FAIL"
        print(f"  [{status}] {name}: {'refuted' if refuted else 'SURVIVED'}")
        if not refuted:
            failed += 1

    if failed:
        print(f"\nFAILED: {failed} row(s)")
        return 1
    print("\nPASS: every claim holds and every control is refuted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
