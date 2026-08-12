"""Direct test of the WIDTH LEMMA -- the constructive core of the Rigidity Theorem.

WIDTH LEMMA.  Fix the shell shape on [1,M] with arbitrary cuts.  Let c in 2..k-1
with w_c >= L_c + 1 (or the core with W >= L_k + 1), and suppose a^c <= M
(resp. a^k <= M).  Then the colouring has a monochromatic solution, UNLESS
   w_c = L_c + 1  and  a | c_{c-1}+1  and  a | M-c_c+1     (shell), or
   W  = L_k + 1   and  a | c_{k-1}+1                        (core),
and either obstruction forces M = -1 (mod a).

The witness is explicit: y a unit among the candidate starts, x = y + L_c,
z = a^c.  This script checks, over every cut vector at M in {N, N+1} on the
rigidity line, that whenever the lemma claims a witness, the witness IS one.
"""
import sys
from itertools import combinations
from math import comb, gcd

from shell import N_shell, cuts, valuation
from verify_rigidity import chi_general

BUDGET = 60000

def check(a, b, k, M):
    Ls = {i: a**(i-1)*b for i in range(2, k+1)}
    hi = (M-1)//2
    n_claims = n_ok = n_obstructed = 0
    bad = []
    for combo in combinations(range(1, hi+1), k-2):
        cv = {1: 0}
        for idx, val in enumerate(combo, start=2):
            cv[idx] = val
        C = chi_general(a, k, M, cv)
        # shells
        for c in range(2, k):
            w = cv[c] - cv[c-1]
            if w <= Ls[c] or a**c > M:
                continue
            starts = [cv[c-1]+1, M-cv[c]+1]           # left and right interval starts
            cand = []
            for lo in starts:
                cand += [lo + d for d in range(w - Ls[c])]
            units = [y for y in cand if valuation(y, a) == 0]
            if w == Ls[c]+1 and not units:
                n_obstructed += 1
                if (M + 1) % a != 0:
                    bad.append(("obstruction without M=-1 mod a", a,b,k,M,combo,c))
                continue
            n_claims += 1
            if not units:
                bad.append(("lemma claims witness, none found", a,b,k,M,combo,c)); continue
            y = units[0]; x = y + Ls[c]; z = a**c
            if (a*(x-y) == b*z and 1 <= y < x <= M and z <= M
                    and int(C[x]) == int(C[y]) == int(C[z]) == c):
                n_ok += 1
            else:
                bad.append(("witness not monochromatic", a,b,k,M,combo,c,(x,y,z),
                            (int(C[x]),int(C[y]),int(C[z]))))
        # core
        W = M - 2*cv[k-1]
        if W > Ls[k] and a**k <= M:
            cand = [cv[k-1]+1+d for d in range(W - Ls[k])]
            units = [y for y in cand if valuation(y, a) == 0]
            if W == Ls[k]+1 and not units:
                n_obstructed += 1
                if (M + 1) % a != 0:
                    bad.append(("core obstruction without M=-1 mod a", a,b,k,M,combo))
            else:
                n_claims += 1
                if not units:
                    bad.append(("core: lemma claims witness, none found", a,b,k,M,combo))
                else:
                    y = units[0]; x = y + Ls[k]; z = a**k
                    if (a*(x-y) == b*z and 1 <= y < x <= M and z <= M
                            and int(C[x]) == int(C[y]) == int(C[z]) == k):
                        n_ok += 1
                    else:
                        bad.append(("core witness not monochromatic", a,b,k,M,combo,(x,y,z)))
    return n_claims, n_ok, n_obstructed, bad

def main():
    print(f"{'(a,b,k)':>10} {'M':>6} {'claims':>8} {'verified':>9} {'obstructed':>11}  status")
    tot_c = tot_o = 0; allbad = []
    for a in range(2, 8):
        b = a-1
        if b < 1 or gcd(a,b) != 1: continue
        for k in range(3, 7):
            N = N_shell(a, b, k)
            for M in (N, N+1):
                if comb((M-1)//2, k-2) > BUDGET: continue
                nc, nok, nob, bad = check(a, b, k, M)
                tot_c += nc; tot_o += nob; allbad += bad
                st = "OK" if (nc == nok and not bad) else f"FAIL {bad[:1]}"
                print(f"{str((a,b,k)):>10} {M:>6} {nc:>8} {nok:>9} {nob:>11}  {st}")
    print(f"\ntotal witness claims verified: {tot_c}")
    print(f"total residue obstructions   : {tot_o}  (each must have M = -1 mod a)")
    print(f"failures                     : {len(allbad)}")
    for x in allbad[:5]: print("   ", x)
    sys.exit(1 if allbad else 0)

if __name__ == "__main__":
    main()
