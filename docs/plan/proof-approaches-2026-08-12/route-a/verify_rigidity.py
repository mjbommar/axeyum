"""Rigidity cross-check against the orchestrator's cut-vector enumeration.

The orchestrator freed the cut vector (0, c_2, ..., c_{k-1}) -- keeping the
valuation strata fixed -- and found that at b = a-1 the canonical vector
(widths L_i = a^{i-1} b) is the UNIQUE feasible one at N = N_shell, and that no
vector is feasible at N+1; whereas for b < a-1 the shape is slack (many feasible
vectors, and just as many at N+1).

This script (1) reproduces that enumeration independently, and (2) answers the
question that matters for the paper: for each cut, WHICH branch B1..B7 of my
case analysis is the one that breaks when that cut is perturbed by +-1?  If my
case analysis is the right set of constraints, every single-coordinate
perturbation must be refuted by one of my branches, and the branch that refutes
it tells me which inequality is saturated at the canonical widths.
"""

import sys
from itertools import combinations
from math import gcd

import numpy as np

from shell import N_shell, cuts, valuation


def chi_general(a, k, N, cv):
    """Colouring array for an ARBITRARY cut vector cv = (c_1=0, c_2, ..., c_{k-1}).

    Valuation strata are fixed (forced, by FACT 1); only the unit shells move.
    """
    C = np.zeros(N + 1, dtype=np.int64)
    C[1:] = k
    for i in range(2, k):
        C[cv[i - 1] + 1 : cv[i] + 1] = i
        C[N - cv[i] + 1 : N - cv[i - 1] + 1] = i
    for e in range(1, k + 1):
        step = a**e
        if step <= N:
            C[step::step] = e
    return C


def first_mono(a, b, k, N, cv):
    """First monochromatic solution (smallest t, then smallest y), or None."""
    C = chi_general(a, k, N, cv)
    t = 1
    while a * t <= N:
        d = b * t
        if d > N - 1:
            break
        z = a * t
        c = C[z]
        ys = C[1 : N - d + 1]
        xs = C[1 + d : N + 1]
        hit = np.flatnonzero((ys == c) & (xs == c))
        if hit.size:
            y = int(hit[0]) + 1
            return (y + d, y, z, int(c))
        t += 1
    return None


def branch_of(a, b, k, N, cv, x, y, c):
    """Classify the monochromatic pair (x,y) of colour c into B1..B7."""
    vx, vy = valuation(x, a), valuation(y, a)
    ux, uy = vx == 0, vy == 0
    if c == 1:
        return "B1"
    if ux != uy:
        return "B3"
    if c <= k - 1:
        if not ux:
            return "B2"
        left = (cv[c - 1] + 1, cv[c])
        right = (N - cv[c] + 1, N - cv[c - 1])
        inl = lambda j, iv: iv[0] <= j <= iv[1]
        if (inl(x, left) and inl(y, left)) or (inl(x, right) and inl(y, right)):
            return "B4"
        if inl(x, right) and inl(y, left):
            return "B5"
        return "B?-shell"
    if not ux:
        return "B6"
    lo, hi = cv[k - 1] + 1, N - cv[k - 1]
    return "B7" if (lo <= y and x <= hi) else "B?-core"


def enumerate_feasible(a, b, k, N):
    """All strictly increasing (0, c_2, ..., c_{k-1}) with 0 < c_2 < ... < N/2."""
    hi = (N - 1) // 2
    feasible, tested = [], 0
    for combo in combinations(range(1, hi + 1), k - 2):
        cv = {1: 0}
        for idx, val in enumerate(combo, start=2):
            cv[idx] = val
        tested += 1
        if first_mono(a, b, k, N, cv) is None:
            feasible.append(tuple(combo))
    return tested, feasible


def main():
    print("### Part 1: reproduce the uniqueness enumeration")
    print(f"{'(a,b,k)':>10} {'N':>6} {'canonical':>18} {'tested':>9} {'feas@N':>7} {'feas@N+1':>9}")
    table = [(3, 2, 3), (4, 3, 3), (5, 4, 3), (6, 5, 3), (3, 2, 4), (4, 3, 4),
             (5, 3, 4), (4, 1, 4), (3, 1, 3)]
    for a, b, k in table:
        N = N_shell(a, b, k)
        can = cuts(a, b, k)
        canon = tuple(can[i] for i in range(2, k))
        tested, feas = enumerate_feasible(a, b, k, N)
        _, feas1 = enumerate_feasible(a, b, k, N + 1)
        mark = " <-- canonical is the unique one" if feas == [canon] else ""
        print(f"{str((a,b,k)):>10} {N:>6} {str(canon):>18} {tested:>9} {len(feas):>7} {len(feas1):>9}{mark}")

    print("\n### Part 2: which branch refutes each single-cut perturbation?")
    print("   (canonical vector, one cut moved by +-1, at N = N_shell)")
    print(f"{'(a,b,k)':>10} {'cut':>5} {'delta':>6} {'witness (x,y,z) col':>26} {'branch':>8}")
    rows = {}
    for a, b, k in [(3, 2, 3), (4, 3, 3), (5, 4, 3), (3, 2, 4), (4, 3, 4), (3, 2, 5)]:
        N = N_shell(a, b, k)
        can = cuts(a, b, k)
        for i in range(2, k):
            for delta in (-1, +1):
                cv = dict(can)
                cv[i] = can[i] + delta
                # keep it a legal strictly-increasing vector inside (0, N/2)
                vals = [cv[j] for j in range(2, k)]
                if vals != sorted(set(vals)) or vals[0] < 1 or vals[-1] >= N / 2:
                    print(f"{str((a,b,k)):>10} {i:>5} {delta:>+6}   (illegal vector, skipped)")
                    continue
                m = first_mono(a, b, k, N, cv)
                if m is None:
                    print(f"{str((a,b,k)):>10} {i:>5} {delta:>+6}   STILL FEASIBLE -- rigidity claim false here")
                    continue
                x, y, z, c = m
                br = branch_of(a, b, k, N, cv, x, y, c)
                rows[br] = rows.get(br, 0) + 1
                print(f"{str((a,b,k)):>10} {i:>5} {delta:>+6} {str((x,y,z))+' c='+str(c):>26} {br:>8}")
    print(f"\n   branch histogram over all perturbations: {dict(sorted(rows.items()))}")

    print("\n### Part 3: slack of Lemma 4 at the canonical widths, by (b,c)")
    print("   slack = b[ a^{k-2}(a-b) + 2 a^{c-1} T (a-b) - a^{c-1} ]  (0 == tight)")
    print(f"{'(a,b,k)':>10} {'c':>3} {'slack':>12} {'tight?':>7}")
    for a, b, k in [(3, 2, 4), (3, 2, 5), (4, 3, 4), (5, 4, 4), (5, 3, 4), (4, 1, 4)]:
        for c in range(2, k):
            T = (a ** (k - 1 - c) - 1) // (a - 1)
            slack = b * (a ** (k - 2) * (a - b) + 2 * a ** (c - 1) * T * (a - b) - a ** (c - 1))
            print(f"{str((a,b,k)):>10} {c:>3} {slack:>12} {'TIGHT' if slack == 0 else '':>7}")


    print("\n### Part 4: WHY rigidity is a b=a-1 phenomenon")
    print("   A width constraint at colour c can only bite if the minimal witness")
    print("   z = a^c (i.e. s=1) fits in [1,N].  For c <= k-1 that is automatic,")
    print("   since N >= b a^{k-1} >= a^{k-1} >= a^c.  For c = k (branch B7, the")
    print("   core) it needs a^k <= N -- which is exactly Proposition 'beat'.")
    print(f"{'(a,b,k)':>10} {'N':>6} {'a^k':>7} {'B7 active?':>11} {'b=a-1 & k>=3':>14} {'feasible':>9}")
    n, bad = 0, []
    for a, b, k, feas in [(3, 2, 3, 1), (4, 3, 3, 1), (5, 4, 3, 1), (6, 5, 3, 1),
                          (3, 2, 4, 1), (4, 3, 4, 1), (5, 3, 4, 1125),
                          (4, 1, 4, 64), (3, 1, 3, 3)]:
        N = N_shell(a, b, k)
        active = a**k <= N
        pred = (b == a - 1 and k >= 3)
        n += 1
        if active != pred or (active != (feas == 1)):
            bad.append((a, b, k))
        print(f"{str((a,b,k)):>10} {N:>6} {a**k:>7} {str(active):>11} {str(pred):>14} {feas:>9}")
    print(f"\n   B7-active == (b=a-1 and k>=3) == (unique feasible vector):"
          f" {n} points, {len(bad)} mismatches {bad}")

    # the equivalence itself, on a wide grid
    n2, bad2 = 0, []
    for a in range(2, 60):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, 15):
                n2 += 1
                if (a**k <= N_shell(a, b, k)) != (b == a - 1 and k >= 3):
                    bad2.append((a, b, k))
    print(f"   a^k <= N  <=>  b = a-1 and k >= 3 : {n2} cases, {len(bad2)} failures {bad2[:4]}")
    # all inner width constraints are always active
    n3, bad3 = 0, []
    for a in range(2, 40):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(3, 13):
                N = N_shell(a, b, k)
                for c in range(2, k):
                    n3 += 1
                    if a**c > N:
                        bad3.append((a, b, k, c))
    print(f"   a^c <= N for every 2<=c<=k-1 (inner constraints always active):"
          f" {n3} cases, {len(bad3)} failures {bad3[:4]}")


if __name__ == "__main__":
    main()
