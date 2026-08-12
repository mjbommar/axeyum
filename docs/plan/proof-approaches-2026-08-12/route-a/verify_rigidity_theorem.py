"""The Rigidity Theorem: proof pivots + the a = 2 case that the residue argument
does not reach.

Proof being tested (b = a-1, k >= 3, so that a^k <= N):

  WIDTH BOUND.  If shell c (2<=c<=k-1) has width w_c >= L_c + 1, or the core has
  width W >= L_k + 1, the colouring has a monochromatic solution -- UNLESS a
  residue obstruction holds, and that obstruction forces M = -1 (mod a).
    * w_c - L_c >= 2  =>  two consecutive candidate starts, one is a unit. Done.
    * w_c - L_c == 1  =>  one candidate per interval: y_L = c_{c-1}+1 and
      y_R = M - c_c + 1.  Bad only if a | both, which forces M = -1 (mod a).
    * core, W - L_k == 1 => single candidate c_{k-1}+1; bad forces M = -1 (mod a).

  PIGEONHOLE.  If every width bound holds then
  M = 2*sum(w_c) + W <= 2*sum(L_c) + L_k = N.

  CONCLUSION.  M = N: a|N so M = 0 != -1 (mod a) for a>=2 -> bounds hold ->
  M <= N with equality -> every w_c = L_c and W = L_k -> canonical, unique.
  M = N+1: M = 1 (mod a); 1 = -1 (mod a) iff a|2 iff a=2.  So for a >= 3 the
  bounds hold, giving M <= N, contradiction -> infeasible.
  a = 2 at M = N+1 is NOT reached by the residue argument; it is closed by the
  defect induction (see verify_defect_induction.py) and tested below.
"""

import sys
from itertools import combinations
from math import gcd

import numpy as np

from shell import N_shell, cuts
from verify_rigidity import chi_general, enumerate_feasible, first_mono


from math import comb


def n_vectors(M, k):
    """How many cut vectors the enumeration would visit."""
    return comb((M - 1) // 2, k - 2)


BUDGET = 60000


def canonical(a, b, k):
    cu = cuts(a, b, k)
    return tuple(cu[i] for i in range(2, k))


def widths(a, b, k, M, cv):
    """(w_2..w_{k-1}, W) for cut vector cv given as a tuple (c_2..c_{k-1})."""
    c = (0,) + cv
    w = [c[i] - c[i - 1] for i in range(1, k - 1)]
    W = M - 2 * c[-1]
    return w, W


def main():
    print("### A. The residue pivot, symbolically checked on the rigidity line")
    n, bad = 0, []
    for a in range(2, 60):
        b = a - 1
        if b < 1 or gcd(a, b) != 1:
            continue
        for k in range(3, 13):
            N = N_shell(a, b, k)
            n += 1
            if N % a != 0:
                bad.append(("a|N", a, k))
            if a**k > N:
                bad.append(("core witness a^k<=N", a, k))
            for c in range(2, k):
                if (a ** (c - 1) * b) % a != 0:
                    bad.append(("a|L_c", a, k, c))
    print(f"    a|N, a|L_c, a^k<=N on the line: {n} points, {len(bad)} failures {bad[:4]}")
    print("    => M=N   : M=0 mod a, bad case needs -1 => a|1, impossible (all a>=2)")
    print("    => M=N+1 : M=1 mod a, bad case needs -1 => a|2, ONLY a=2")

    print("\n### B. M = N: is the canonical vector the unique solution-free one?")
    print(f"    {'(a,b,k)':>10} {'N':>6} {'vectors':>9} {'feasible':>9}  verdict")
    for a, k in [(2, 3), (2, 4), (2, 5), (2, 6), (3, 3), (3, 4), (4, 3), (5, 3), (6, 3), (3, 5)]:
        b = a - 1
        N = N_shell(a, b, k)
        nv = n_vectors(N, k)
        if nv > BUDGET:
            print(f"    {str((a,b,k)):>10} {N:>6} {nv:>9}   (skipped: over budget)")
            continue
        tested, feas = enumerate_feasible(a, b, k, N)
        can = canonical(a, b, k)
        ok = feas == [can]
        print(f"    {str((a,b,k)):>10} {N:>6} {tested:>9} {len(feas):>9}  "
              f"{'UNIQUE=canonical' if ok else 'MISMATCH ' + str(feas[:3])}")

    print("\n### C. M = N+1: infeasible?  (a=2 is the case the proof does NOT reach)")
    print(f"    {'(a,b,k)':>10} {'M':>6} {'vectors':>9} {'feasible':>9}  verdict")
    for a, k in [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 3), (3, 4), (4, 3), (5, 3), (6, 3)]:
        b = a - 1
        N = N_shell(a, b, k)
        M = N + 1
        nv = n_vectors(M, k)
        if nv > BUDGET:
            print(f"    {str((a,b,k)):>10} {M:>6} {nv:>9}   (skipped: over budget)")
            continue
        tested, feas = enumerate_feasible(a, b, k, M)
        tag = "INFEASIBLE (as claimed)" if not feas else f"FEASIBLE {feas[:3]} -- THEOREM FALSE"
        star = "   <-- a=2: residue argument alone is insufficient; needs defect induction" if a == 2 else ""
        print(f"    {str((a,b,k)):>10} {M:>6} {tested:>9} {len(feas):>9}  {tag}{star}")

    print("\n### D. a=2 close-up: which width bounds can fail, and do they?")
    print("    At a=2, c_1 = 0 is EVEN, so shell 2's bad case (needs c_1 odd) is")
    print("    impossible: w_2 <= L_2 always.  Track the partial sums.")
    print("    Also: c_{c-1} = (a^{c-1}-2)/... ; at a=2, sum L_i = 2^{c-1}-2 is EVEN,")
    print("    so c_{c-1} is odd iff the accumulated defect sum is odd.")
    for k in [3, 4, 5, 6]:
        a, b = 2, 1
        N = N_shell(a, b, k)
        M = N + 1
        if n_vectors(M, k) > BUDGET:
            print(f"    (2,1,{k}): M={M} skipped (over budget: {n_vectors(M,k)} vectors)")
            continue
        tested, feas = enumerate_feasible(a, b, k, M)
        # among ALL vectors at M=N+1, how many satisfy every width bound?
        allbounds = 0
        for combo in combinations(range(1, (M - 1) // 2 + 1), k - 2):
            w, W = widths(a, b, k, M, combo)
            Ls = [a ** (i - 1) * b for i in range(2, k)]
            if all(w[i] <= Ls[i] for i in range(len(w))) and W <= a ** (k - 1) * b:
                allbounds += 1
        print(f"    (2,1,{k}): M={M:>4} vectors={tested:>7} feasible={len(feas)} "
              f"vectors-satisfying-all-width-bounds={allbounds}  "
              f"(must be 0, since sum would give M<=N)")

    print("\n### E. Do the width bounds actually HOLD for every solution-free")
    print("    vector at M=N (the pigeonhole hypothesis)?")
    print(f"    {'(a,b,k)':>10} {'feasible':>9} {'violating a width bound':>26}")
    for a, k in [(2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (4, 3), (5, 3), (6, 3)]:
        b = a - 1
        N = N_shell(a, b, k)
        if n_vectors(N, k) > BUDGET:
            continue
        tested, feas = enumerate_feasible(a, b, k, N)
        Ls = [a ** (i - 1) * b for i in range(2, k)]
        viol = 0
        for cv in feas:
            w, W = widths(a, b, k, N, cv)
            if any(w[i] > Ls[i] for i in range(len(w))) or W > a ** (k - 1) * b:
                viol += 1
        print(f"    {str((a,b,k)):>10} {len(feas):>9} {viol:>26}")

    print("\n### F. OFF the line (b <= a-2): width bounds must FAIL (a^k > N),")
    print("    reproducing the orchestrator's slack table.")
    print(f"    {'(a,b,k)':>10} {'N':>6} {'a^k':>6} {'feasible':>9} {'violating widths':>18}")
    for a, b, k in [(3, 1, 3), (4, 1, 3), (5, 3, 3), (4, 1, 4)]:
        N = N_shell(a, b, k)
        tested, feas = enumerate_feasible(a, b, k, N)
        Ls = [a ** (i - 1) * b for i in range(2, k)]
        viol = 0
        for cv in feas:
            w, W = widths(a, b, k, N, cv)
            if any(w[i] > Ls[i] for i in range(len(w))) or W > a ** (k - 1) * b:
                viol += 1
        print(f"    {str((a,b,k)):>10} {N:>6} {a**k:>6} {len(feas):>9} {viol:>18}")


if __name__ == "__main__":
    main()
