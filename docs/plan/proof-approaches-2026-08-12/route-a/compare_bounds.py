"""Where the shell bound wins, and where it does not.

Three lower-bound constructions for R_k(a(x-y) = bz), b < a, gcd(a,b)=1:

  (P)  pure a-adic          chi(j) = min(v(j), k-1)      solution-free on [1, a^k - 1]
  (L)  recursive lifting    f(k) = a^{k-1}(b+1) - 1      (orchestrator's FACT 2)
  (S)  shell (this paper)   N = b(a^{k-1} + 2 S_{k-2})

Also checks the closed form N = a^k + a^{k-1} - 2a at b = a-1, and reproduces
the brief's table of N+1 vs a^k.
"""

import sys
from math import gcd

from shell import N_shell


def S(a, m):
    return sum(a**i for i in range(1, m + 1))


def main():
    print("### closed form at b = a-1:  N = a^k + a^{k-1} - 2a")
    n, bad = 0, []
    for a in range(2, 60):
        for k in range(2, 15):
            n += 1
            if N_shell(a, a - 1, k) != a**k + a ** (k - 1) - 2 * a:
                bad.append((a, k))
    print(f"    cases={n} failures={len(bad)} {bad[:5]}")

    print("\n### brief's table (N+1 vs a^k), reproduced")
    for a, b, k in [(3,2,3),(4,3,3),(3,2,4),(4,3,4),(5,4,4),(6,5,4),(3,2,5),
                    (3,1,3),(5,2,4),(5,3,4)]:
        N = N_shell(a, b, k)
        win = "shell" if N + 1 > a**k else "a^k"
        print(f"    ({a},{b},{k})  N+1={N+1:>6}  a^k={a**k:>6}  winner={win}")

    # NOTE (2026-08-12): the lifting bound is DOMINATED by the pure bound.
    # The orchestrator's original figure a^{k-1}(b+1)-1 was retracted; the
    # correct lifting result is a^k - 1 uniformly in b <= a-1.  The check below
    # confirms a^{k-1}(b+1)-1 <= a^k - 1 with equality iff b = a-1, so the
    # lifting family is never the best bound and is not a rival to the shell.
    n3, bad3 = 0, []
    for a in range(2, 40):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, 13):
                n3 += 1
                L = a ** (k - 1) * (b + 1) - 1
                P = a**k - 1
                if not (L <= P and ((L == P) == (b == a - 1))):
                    bad3.append((a, b, k))
    print(f"\n### lifting bound a^(k-1)(b+1)-1 <= a^k-1, equality iff b=a-1")
    print(f"    cases={n3} failures={len(bad3)} {bad3[:5]}")

    # Proposition 'beat' of the paper: N+1 > a^k  <=>  b = a-1 and k >= 3
    n4, bad4 = 0, []
    for a in range(2, 60):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, 15):
                n4 += 1
                N = N_shell(a, b, k)
                if (N + 1 > a**k) != (b == a - 1 and k >= 3):
                    bad4.append((a, b, k))
                if (a - 1) * N != b * (a**k + a ** (k - 1) - 2 * a):
                    bad4.append(("identity", a, b, k))
    print(f"\n### Proposition 'beat':  N+1 > a^k  <=>  b = a-1 and k >= 3")
    print(f"    (plus the identity (a-1)N = b(a^k + a^(k-1) - 2a))")
    print(f"    cases={n4} failures={len(bad4)} {bad4[:5]}")

    print("\n### shell vs recursive lifting:  N+1 > a^{k-1}(b+1) ?")
    print("    equivalent algebraic form: 2b(a^{k-1}-a) > (a-1)(a^{k-1}-1)")
    n2, bad2 = 0, []
    for a in range(2, 40):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, 13):
                n2 += 1
                lhs = N_shell(a, b, k) + 1 > a ** (k - 1) * (b + 1)
                rhs = 2 * b * (a ** (k - 1) - a) > (a - 1) * (a ** (k - 1) - 1)
                if lhs != rhs:
                    bad2.append((a, b, k))
    print(f"    equivalence cases={n2} failures={len(bad2)} {bad2[:5]}")

    print("\n    who wins, by (a,b,k):")
    print(f"    {'a':>3} {'b':>3} {'k':>3} {'a^k-1':>10} {'lift':>10} {'shell N':>10}  best")
    for a, b, k in [(3,1,3),(3,2,3),(3,1,5),(3,2,5),(2,1,4),(4,1,4),(4,3,4),
                    (5,2,4),(5,4,4),(6,5,4),(7,1,5),(7,6,5)]:
        P = a**k - 1
        L = a ** (k - 1) * (b + 1) - 1
        Sh = N_shell(a, b, k)
        best = max([(P, "pure"), (L, "lift"), (Sh, "shell")])
        print(f"    {a:>3} {b:>3} {k:>3} {P:>10} {L:>10} {Sh:>10}  {best[1]} ({best[0]})")

    print("\n### how often does the shell bound beat BOTH others? (b<a, gcd=1)")
    tot = win = 0
    for a in range(2, 25):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(2, 11):
                tot += 1
                if N_shell(a, b, k) > max(a**k - 1, a ** (k - 1) * (b + 1) - 1):
                    win += 1
    print(f"    shell strictly best in {win} of {tot} parameter points")

    print("\n### b = a-1 specifically (shell vs pure and lift)")
    tot2 = win2 = 0
    for a in range(2, 25):
        b = a - 1
        if gcd(a, b) != 1 or b < 1:
            continue
        for k in range(3, 11):
            tot2 += 1
            if N_shell(a, b, k) > max(a**k - 1, a ** (k - 1) * (b + 1) - 1):
                win2 += 1
    print(f"    shell strictly best in {win2} of {tot2} points with b=a-1, k>=3")
    sys.exit(1 if (bad or bad2 or bad3 or bad4) else 0)


if __name__ == "__main__":
    main()
