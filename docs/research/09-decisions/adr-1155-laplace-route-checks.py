#!/usr/bin/env python3
"""Re-runnable numeric checks behind ADR-1155 (general-row determinant
expansion over `Rat.det`).

Every claim ADR-1155 makes about index arithmetic, about the two hypotheses
being load-bearing, and about the double-expansion pairing is re-derived here
against a direct simulation of `Rat.matSkip`, `Rat.matMinor` and `Rat.det` at
the definitions `rat_prelude/matrix_det.rs` uses. CLAUDE.md's rule is that a
plan's numeric claims must be re-executable rather than believed -- and the
first draft of the sign check below was WRONG (28 mismatches from a typo in
the check, not in the claim), which is the reason to write it down.

    python3 docs/research/09-decisions/adr-1155-laplace-route-checks.py

Exits 0 when every claim holds, 1 otherwise.
"""
from fractions import Fraction
from itertools import product
import random

def skip(p, x):
    return x + 1 if p <= x else x

def minor(A, i, j):
    return lambda r, c: A(skip(i, r), skip(j, c))

def det(A, n):
    if n == 0:
        return Fraction(1)
    return sum(((-1) ** j) * A(0, j) * det(minor(A, 0, j), n - 1)
               for j in range(n))

def rowexp(A, i, n):
    """Expansion along row i of an n x n matrix."""
    return sum(((-1) ** (i + j)) * A(i, j) * det(minor(A, i, j), n - 1)
               for j in range(n))

fail = 0

# --- 1. matSkip_comm, and that its hypothesis is load-bearing --------------
holds = broken = 0
for a, b, x in product(range(6), repeat=3):
    lhs, rhs = skip(a, skip(b, x)), skip(b + 1, skip(a, x))
    if a <= b:
        holds += 1
        if lhs != rhs:
            print(f"FAIL matSkip_comm at {a},{b},{x}"); fail += 1
    elif lhs != rhs:
        broken += 1
print(f"matSkip_comm: {holds} instances with a<=b all hold; "
      f"{broken} instances with a>b are FALSE (so the premise is needed)")
if broken == 0:
    print("FAIL: the hypothesis would be discardable"); fail += 1
# the exact pair the Rust control uses
assert skip(1, skip(0, 0)) == 2 and skip(1, skip(1, 0)) == 0
assert skip(0, skip(1, 0)) == skip(2, skip(0, 0)) == 1
print("  control pair (a,b,x)=(1,0,0): 2 vs 0; (0,1,0): 1 vs 1")

# --- 2. sumRange_matSkip ----------------------------------------------------
random.seed(11)
holds = broken = 0
for _ in range(400):
    n = random.randrange(0, 7)
    j = random.randrange(0, 8)
    vals = [Fraction(random.randrange(-4, 5)) for _ in range(20)]
    f = lambda k: vals[k]
    lhs = sum(f(skip(j, k)) for k in range(n)) + f(j)
    rhs = sum(f(i) for i in range(n + 1))
    if j <= n:
        holds += 1
        if lhs != rhs:
            print(f"FAIL sumRange_matSkip at n={n} j={j}"); fail += 1
    elif lhs != rhs:
        broken += 1
print(f"sumRange_matSkip: {holds} instances with j<=n hold; "
      f"{broken} random instances with j>n are FALSE")
if broken == 0:
    print("FAIL: premise looked discardable on this sample"); fail += 1

# --- 3. general-row expansion is TRUE of this det ---------------------------
random.seed(5)
for n in range(1, 6):
    for _ in range(30):
        cells = {(r, c): Fraction(random.randrange(-3, 4))
                 for r in range(n) for c in range(n)}
        A = lambda r, c: cells.get((r, c), Fraction(0))
        d = det(A, n)
        for i in range(n):
            if rowexp(A, i, n) != d:
                print(f"FAIL rowexp n={n} i={i}"); fail += 1
print("general-row expansion agrees with det at every row, n = 1..5, "
      "30 random matrices each")

# --- 4. the double-expansion pairing, at the level of ordered column pairs ---
# LHS (expand row 0, then row 0 of each minor) and RHS (row-1 expansion, then
# row 0 of each minor) are both sums over ORDERED PAIRS of distinct columns.
def lhs_terms(A, n):
    out = {}
    for j in range(n):
        M = minor(A, 0, j)
        for k in range(n - 1):
            q = skip(j, k)
            out[(j, q)] = ((-1) ** (j + k)) * A(0, j) * M(0, k) * \
                det(minor(M, 0, k), n - 2)
    return out

def rhs_terms(A, n):
    out = {}
    for a in range(n):
        M = minor(A, 1, a)
        for b in range(n - 1):
            pcol = skip(a, b)
            out[(pcol, a)] = ((-1) ** (1 + a + b)) * A(1, a) * M(0, b) * \
                det(minor(M, 0, b), n - 2)
    return out

random.seed(7)
for n in (2, 3, 4, 5):
    for _ in range(20):
        cells = {(r, c): Fraction(random.randrange(-3, 4))
                 for r in range(n) for c in range(n)}
        A = lambda r, c: cells.get((r, c), Fraction(0))
        L, R = lhs_terms(A, n), rhs_terms(A, n)
        if set(L) != set(R):
            print(f"FAIL index sets differ at n={n}"); fail += 1; break
        for key in L:
            if L[key] != R[key]:
                print(f"FAIL termwise at n={n} key={key}: {L[key]} vs {R[key]}")
                fail += 1
                break
print("double expansion: LHS and RHS are indexed by the SAME set of ordered "
      "distinct column pairs and agree TERMWISE, n = 2..5")

# --- 5. the square-with-zero-diagonal reformulation --------------------------
# W(pcol, qcol) := the common term above, and 0 on the diagonal. Then
#   LHS = sum_j sum_{k<n-1} W(j, skip j k)   = sum_j sum_q W(j, q)
#   RHS = sum_a sum_{b<n-1} W(skip a b, a)   = sum_a sum_p W(p, a)
# and the two square sums differ only by the order of summation.
random.seed(13)
for n in (2, 3, 4, 5):
    for _ in range(20):
        cells = {(r, c): Fraction(random.randrange(-3, 4))
                 for r in range(n) for c in range(n)}
        A = lambda r, c: cells.get((r, c), Fraction(0))
        L = lhs_terms(A, n)
        W = lambda pq: L.get(pq, Fraction(0))
        square_rows = sum(W((j, q)) for j in range(n) for q in range(n))
        square_cols = sum(W((pp, a)) for a in range(n) for pp in range(n))
        if square_rows != square_cols:
            print(f"FAIL Fubini at n={n}"); fail += 1
        if square_rows != det(A, n):
            print(f"FAIL square sum != det at n={n}"); fail += 1
        if sum(rhs_terms(A, n).values()) != rowexp(A, 1, n):
            print(f"FAIL rhs != row-1 expansion at n={n}"); fail += 1
print("square-with-zero-diagonal: both parametrisations sum to det, and the "
      "two orders of summation agree (plain rectangle Fubini), n = 2..5")



def L_terms(A, n, i):
    out = {}
    for j in range(n):
        M = minor(A, 0, j)
        for k in range(n - 1):
            q = skip(j, k)
            out[(j, q)] = ((-1) ** (j + (i - 1) + k)) * A(0, j) * M(i - 1, k) \
                * det(minor(M, i - 1, k), n - 2)
    return out

def R_terms(A, n, i):
    out = {}
    for a in range(n):
        M = minor(A, i, a)
        for b in range(n - 1):
            p = skip(a, b)
            out[(p, a)] = ((-1) ** (i + a + b)) * A(i, a) * M(0, b) \
                * det(minor(M, 0, b), n - 2)
    return out

random.seed(3)
checked = 0
for n in range(2, 7):
    for i in range(1, n):
        for _ in range(15):
            cells = {(r, c): Fraction(random.randrange(-3, 4))
                     for r in range(n) for c in range(n)}
            A = lambda r, c: cells.get((r, c), Fraction(0))
            L, R = L_terms(A, n, i), R_terms(A, n, i)
            if set(L) != set(R):
                print(f"FAIL index sets differ n={n} i={i}"); fail += 1; continue
            for key in L:
                if L[key] != R[key]:
                    print(f"FAIL termwise n={n} i={i} key={key}: "
                          f"{L[key]} vs {R[key]}")
                    fail += 1
                    break
            if sum(L.values()) != det(A, n):
                print(f"FAIL L != det, n={n} i={i}"); fail += 1
            checked += 1
print(f"general-row pairing: {checked} (n, i, matrix) cases, "
      f"L and R indexed identically and equal TERMWISE, n = 2..6, 1 <= i < n")

# The two row-index maps in the double minors must agree; this is matSkip_comm
# at a = 0, b = i-1.
bad = 0
for i in range(1, 8):
    for r in range(8):
        if skip(0, skip(i - 1, r)) != skip(i, skip(0, r)):
            bad += 1
print(f"row maps of the two double minors agree at every (i, r): "
      f"{bad} mismatches (this is matSkip_comm at a=0, b=i-1)")
if bad:
    fail += 1

# The sign identity the RHS identification needs, stated over the pair (a, b).
bad = 0
for a in range(8):
    for b in range(8):
        p = skip(a, b)
        kprime = a - 1 if p < a else a       # index of a in the range missing p
        if a == p:
            continue
        if (-1) ** (p + kprime) != (-1) ** (1 + a + b):
            bad += 1
print(f"sign identity altSign(p) * altSign(unskip p a) = altSign(1+a+b): "
      f"{bad} mismatches")
if bad:
    fail += 1


import sys
print()
print("FAILURES:", fail)
sys.exit(0 if fail == 0 else 1)
