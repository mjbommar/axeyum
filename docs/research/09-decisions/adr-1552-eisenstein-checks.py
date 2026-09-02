#!/usr/bin/env python3
"""Numeric checks behind ADR-1552 (lane `eisenstein-3`).

Six claims (C1-C6) and eleven controls (M1-M11). **The exit status depends on
the finding**: a claim that fails, or a control that behaves other than as
recorded here, exits 1. Two controls are recorded SURVIVORS -- they are
printed as survivors and do NOT fail the run, because the ADR records them as
things no numeric check can see.

Everything is recomputed from the kernel definitions, not from any prior
document:

    leastResidue pp a k = (a*k) mod pp
    gaussSignNeg pp a k = (pp // 2) < leastResidue pp a k
    gaussFold    pp a k = pp - r if sign else r
    gaussNegCount pp a m = #{ 1 <= k <= m : sign }
    sumRangeIf   p f n  = sum of f over the indices below n satisfying p
"""

from __future__ import annotations

import math
import sys

FAILURES: list[str] = []
SURVIVORS: list[str] = []


def record(ok: bool, label: str, detail: str = "") -> None:
    if ok:
        print(f"  ok   {label} {detail}")
    else:
        print(f"  FAIL {label} {detail}")
        FAILURES.append(label)


def survivor(label: str, detail: str) -> None:
    print(f"  SURVIVOR {label} {detail}")
    SURVIVORS.append(label)


# --- the kernel definitions, recomputed --------------------------------------


def residue(pp: int, a: int, k: int) -> int:
    return (a * k) % pp


def sign_neg(pp: int, a: int, k: int) -> bool:
    return pp // 2 < residue(pp, a, k)


def fold(pp: int, a: int, k: int) -> int:
    r = residue(pp, a, k)
    return pp - r if sign_neg(pp, a, k) else r


def neg_count(pp: int, a: int, m: int) -> int:
    return sum(1 for k in range(1, m + 1) if sign_neg(pp, a, k))


def residue_sum(pp: int, a: int, m: int) -> int:
    return sum(residue(pp, a, k) for k in range(1, m + 1))


def fold_sum(pp: int, a: int, m: int) -> int:
    return sum(fold(pp, a, k) for k in range(1, m + 1))


def negative_fold_sum(pp: int, a: int, m: int) -> int:
    return sum(fold(pp, a, k) for k in range(1, m + 1) if sign_neg(pp, a, k))


def positive_fold_sum(pp: int, a: int, m: int) -> int:
    return sum(fold(pp, a, k) for k in range(1, m + 1) if not sign_neg(pp, a, k))


def negative_residue_sum(pp: int, a: int, m: int) -> int:
    return sum(residue(pp, a, k) for k in range(1, m + 1) if sign_neg(pp, a, k))


def floor_sum(pp: int, a: int, m: int) -> int:
    return sum((a * k) // pp for k in range(1, m + 1))


def triangular(m: int) -> int:
    return m * (m + 1) // 2


def sum_range_if(pred, f, n: int) -> int:
    return sum(f(i) for i in range(n) if pred(i))


def sum_range(f, n: int) -> int:
    return sum(f(i) for i in range(n))


# --- C1: `Nat.sumRangeIf` and its complement split ----------------------------


def c1() -> None:
    print("C1  sumRangeIf selects, and splits against setCompl")
    preds = [
        ("3 <= i", lambda i: 3 <= i),
        ("i <= 1", lambda i: i <= 1),
        ("i odd", lambda i: i % 2 == 1),
        ("always", lambda _i: True),
        ("never", lambda _i: False),
    ]
    funs = [
        ("succ", lambda i: i + 1),
        ("square", lambda i: i * i),
        ("const 0", lambda _i: 0),
    ]
    split_ok = True
    selection_ok = True
    count = 0
    for pname, pred in preds:
        for fname, f in funs:
            for n in range(0, 12):
                count += 1
                lhs = sum_range_if(pred, f, n) + sum_range_if(
                    lambda i, pred=pred: not pred(i), f, n
                )
                if lhs != sum_range(f, n):
                    split_ok = False
                    print(f"       split fails at {pname}/{fname}/n={n}")
                # The selected sum really is the sum over the subset.
                direct = sum(f(i) for i in range(n) if pred(i))
                if sum_range_if(pred, f, n) != direct:
                    selection_ok = False
    record(split_ok, "C1a", f"the complement split holds at {count} instances")
    record(selection_ok, "C1b", "sumRangeIf is the sum over the p-subset")
    # The empty and full predicates are the two degenerate corners.
    record(
        sum_range_if(lambda _i: False, lambda i: i + 1, 6) == 0,
        "C1c",
        "the empty predicate selects nothing",
    )
    record(
        sum_range_if(lambda _i: True, lambda i: i + 1, 6) == sum_range(lambda i: i + 1, 6),
        "C1d",
        "the full predicate selects everything",
    )


# --- C2: residue 2, the residue/fold reconciliation ---------------------------


def reconcile_holds(pp: int, a: int, m: int) -> bool:
    lhs = residue_sum(pp, a, m) + 2 * negative_fold_sum(pp, a, m)
    rhs = fold_sum(pp, a, m) + pp * neg_count(pp, a, m)
    return lhs == rhs


def c2() -> None:
    print("C2  residue 2: SUM leastResidue + 2*SUM_neg fold = SUM fold + pp*N")
    count = 0
    ok = True
    composite = 0
    non_coprime = 0
    for pp in range(1, 26):
        for a in range(0, 26):
            for m in range(0, 13):
                count += 1
                if not reconcile_holds(pp, a, m):
                    ok = False
                    print(f"       fails at pp={pp}, a={a}, m={m}")
                if pp > 1 and not all(pp % d for d in range(2, pp)):
                    composite += 1
                if math.gcd(a, pp) != 1:
                    non_coprime += 1
    record(ok, "C2", f"holds at {count} instances")
    record(
        composite > 0 and non_coprime > 0,
        "C2b",
        f"the sweep includes {composite} composite-modulus and "
        f"{non_coprime} non-coprime instances, so the theorem's "
        "hypothesis-freedom is exercised",
    )


# --- C3: step 1, the summed division algorithm --------------------------------


def c3() -> None:
    print("C3  step 1: a*T = pp*F + SUM leastResidue")
    count = 0
    ok = True
    for pp in range(1, 26):
        for a in range(0, 26):
            for m in range(0, 13):
                count += 1
                lhs = a * triangular(m)
                rhs = pp * floor_sum(pp, a, m) + residue_sum(pp, a, m)
                if lhs != rhs:
                    ok = False
                    print(f"       fails at pp={pp}, a={a}, m={m}")
    record(ok, "C3", f"holds at {count} instances, with NO hypothesis")


# --- C4: the counting identity ------------------------------------------------


def count_identity_holds(m: int, a: int) -> bool:
    pp = 2 * m + 1
    lhs = a * triangular(m) + 2 * negative_fold_sum(pp, a, m)
    rhs = pp * (floor_sum(pp, a, m) + neg_count(pp, a, m)) + triangular(m)
    return lhs == rhs


def c4() -> None:
    print("C4  step 2: a*T + 2*S = pp*(F+N) + T, for a coprime to pp = 2m+1")
    count = 0
    ok = True
    for m in range(0, 16):
        pp = 2 * m + 1
        for a in range(0, 40):
            if math.gcd(a, pp) != 1:
                continue
            count += 1
            if not count_identity_holds(m, a):
                ok = False
                print(f"       fails at m={m}, a={a}")
    record(ok, "C4", f"holds at {count} coprime instances")


# --- C5: Eisenstein's lemma ---------------------------------------------------


def eisenstein_holds(m: int, n: int) -> bool:
    pp, q = 2 * m + 1, 2 * n + 1
    return (floor_sum(pp, q, m) + neg_count(pp, q, m)) % 2 == 0


def c5() -> None:
    print("C5  Eisenstein: F + N is EVEN whenever gcd(2n+1, 2m+1) = 1")
    count = 0
    ok = True
    for m in range(0, 22):
        for n in range(0, 22):
            if math.gcd(2 * n + 1, 2 * m + 1) != 1:
                continue
            count += 1
            if not eisenstein_holds(m, n):
                ok = False
                print(f"       fails at m={m}, n={n}")
    record(ok, "C5", f"holds at {count} coprime odd pairs")

    # And the classical instance really is covered: for distinct odd primes
    # p, q with m = (p-1)/2, n = (q-1)/2 the hypothesis holds.
    primes = [p for p in range(3, 60) if all(p % d for d in range(2, p))]
    pairs = 0
    covered = True
    for p in primes:
        for q in primes:
            if p == q:
                continue
            m, n = (p - 1) // 2, (q - 1) // 2
            pairs += 1
            if math.gcd(2 * n + 1, 2 * m + 1) != 1:
                covered = False
            if not eisenstein_holds(m, n):
                covered = False
    record(
        covered and pairs > 0,
        "C5b",
        f"every one of {pairs} ordered pairs of distinct odd primes below 60 "
        "satisfies the hypothesis and the conclusion",
    )



# --- C6: residue 5, the min-free floor sum ------------------------------------


def bare_row_sum(pp: int, q: int, m: int) -> int:
    return sum((q * (x + 1)) // pp for x in range(m))


def max_row_floor(pp: int, q: int, m: int) -> int:
    return max(((q * (x + 1)) // pp for x in range(m)), default=0)


def c6() -> None:
    print("C6  residue 5: the min-free floor sum at pp = 2m+1, q = 2n+1")
    count = 0
    ok = True
    cap_ok = True
    for m in range(0, 20):
        for n in range(0, 20):
            pp, q = 2 * m + 1, 2 * n + 1
            if math.gcd(pp, q) != 1:
                continue
            count += 1
            if bare_row_sum(pp, q, m) + bare_row_sum(q, pp, n) != n * m:
                ok = False
                print(f"       fails at m={m}, n={n}")
            # The cap never binds on EITHER axis -- the fact the kernel lemma
            # `Nat.div_mul_succ_le_of_le` states.
            if max_row_floor(pp, q, m) > n or max_row_floor(q, pp, n) > m:
                cap_ok = False
                print(f"       the cap BINDS at m={m}, n={n}")
    record(ok, "C6", f"holds at {count} coprime odd pairs")
    record(cap_ok, "C6b", "and the min never binds at any of them")

# --- controls -----------------------------------------------------------------


def controls() -> None:
    print("M   controls")
    pp, a, m = 7, 3, 3

    # M1: residue 2 with the doubling dropped.
    record(
        residue_sum(pp, a, m) != fold_sum(pp, a, m) + pp * neg_count(pp, a, m),
        "M1",
        "REFUTED: dropping the doubling (11 vs 13 at pp=7, a=3, m=3)",
    )

    # M2: residue 2 doubling the COMPLEMENT's fold sum.
    record(
        residue_sum(pp, a, m) + 2 * positive_fold_sum(pp, a, m)
        != fold_sum(pp, a, m) + pp * neg_count(pp, a, m),
        "M2",
        "REFUTED: doubling the unselected folds (21 vs 13)",
    )

    # M3: residue 2 conditioning the RESIDUES rather than the folds.
    record(
        residue_sum(pp, a, m) + 2 * negative_residue_sum(pp, a, m)
        != fold_sum(pp, a, m) + pp * neg_count(pp, a, m),
        "M3",
        "REFUTED: conditioning residues instead of folds (23 vs 13)",
    )

    # M4: residue 2 without coprimality. It SURVIVES, because the theorem is
    # deliberately hypothesis-free -- this is the claim, not a defect.
    non_coprime = [(pp2, a2, m2) for pp2 in (4, 6, 9) for a2 in (2, 3) for m2 in range(0, 8)]
    record(
        all(reconcile_holds(*t) for t in non_coprime),
        "M4",
        f"residue 2 needs NO coprimality: holds at {len(non_coprime)} "
        "non-coprime instances (this is the claim, not a survivor)",
    )

    # M5: Eisenstein's lemma without coprimality.
    bad = [(m2, n2) for m2 in range(0, 22) for n2 in range(0, 22)
           if math.gcd(2 * n2 + 1, 2 * m2 + 1) != 1 and not eisenstein_holds(m2, n2)]
    record(
        (4, 1) in bad,
        "M5",
        f"REFUTED at pp=9, q=3 (F+N = 3, odd); {len(bad)} of the "
        "non-coprime pairs below 22 are counterexamples",
    )

    # M6: the counting identity without coprimality.
    record(
        not count_identity_holds(4, 3),
        "M6",
        "REFUTED: the counting identity fails at m=4, a=3 "
        f"({3 * triangular(4) + 2 * negative_fold_sum(9, 3, 4)} vs "
        f"{9 * (floor_sum(9, 3, 4) + neg_count(9, 3, 4)) + triangular(4)})",
    )

    # M7: step 1 has NO hypothesis to drop -- recorded, not a control.
    record(
        all(
            a2 * triangular(m2) == pp2 * floor_sum(pp2, a2, m2) + residue_sum(pp2, a2, m2)
            for pp2 in range(1, 12)
            for a2 in range(0, 12)
            for m2 in range(0, 8)
        ),
        "M7",
        "step 1 has no hypothesis to drop: it is the division algorithm, "
        "true at every modulus, multiplier and bound",
    )

    # M8: the complement split with a NON-complementary second predicate.
    bad_split = sum_range_if(lambda i: 3 <= i, lambda i: i + 1, 6) + sum_range_if(
        lambda i: i <= 1, lambda i: i + 1, 6
    )
    record(
        bad_split != sum_range(lambda i: i + 1, 6),
        "M8",
        f"REFUTED: `i <= 1` is not the complement of `3 <= i` ({bad_split} vs 21)",
    )

    # M11: the SAME min-free reading at a general instance
    # `Nat.eisenstein_floor_sum` also reaches -- pp = 2, q = 5, m = 1, n = 0,
    # coprime and within the bound -- where the cap DOES bind.
    record(
        max_row_floor(2, 5, 1) > 0
        and bare_row_sum(2, 5, 1) + bare_row_sum(5, 2, 0) != 0 * 1,
        "M11",
        "REFUTED: dropping the min at pp=2, q=5, m=1, n=0 gives 2 against 0, "
        "so residue 5 is a fact about the Eisenstein shape and not about "
        "counting (this reproduces ADR-1544's M4)",
    )

    # M9: SURVIVOR -- the congruence form is symmetric in F and N, so no
    # numeric check can see which side is which.
    survivor(
        "M9",
        "modEq 2 F N and modEq 2 N F are the same claim; the ARGUMENT ORDER "
        "is invisible to every numeric check and is guarded only by the "
        "character-for-character type pin in eisenstein_lemma_tests.rs",
    )

    # M10: SURVIVOR -- `Even (F + N)` cannot be numerically distinguished from
    # `Even (N + F)`, nor from any statement equal to it after commuting.
    survivor(
        "M10",
        "Even (F + N) vs Even (N + F): equal as numbers, different as kernel "
        "terms, and no consumer chaining through one can use the other "
        "without a commutation step. Guarded only by the type pin",
    )


def main() -> int:
    print("ADR-1552 numeric checks (lane eisenstein-3)")
    c1()
    c2()
    c3()
    c4()
    c5()
    c6()
    controls()
    print()
    print(f"claims/controls failed: {len(FAILURES)}")
    print(f"recorded survivors:     {len(SURVIVORS)} ({', '.join(SURVIVORS)})")
    if FAILURES:
        print("RESULT: FAIL -- " + ", ".join(FAILURES))
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
