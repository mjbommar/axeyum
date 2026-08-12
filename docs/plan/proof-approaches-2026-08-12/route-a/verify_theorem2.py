"""Theorem 2 (sharpness): the shell colouring is DEFECTIVE whenever b > a, k >= 3.

Claimed closed-form defect, for a >= 2, gcd(a,b) = 1, b > a, k >= 3:

    Y = 1,
    X = N - ab + 1,
    W = N/b - a = a^{k-1} + 2 S_{k-2} - a,
    Z = a W,

all three of colour 2.

Also tested here: the brief's stated family (a b^2 + 1, 1, a^2 b) for b = a+1.
My prediction, to be confirmed or refuted by this script, is that it is
monochromatic at k = 3 ONLY, and is *not* a defect for k >= 4 (where the true
defect is X = N - ab + 1, which is strictly larger).
"""

import sys
from math import gcd

from shell import N_shell, chi_array, chi_scalar, cuts, valuation


def family(a, b, k):
    N = N_shell(a, b, k)
    assert N % b == 0
    W = N // b - a
    return (N - a * b + 1, 1, a * W), W, N


def is_solution(a, b, x, y, z, N):
    return (
        1 <= x <= N and 1 <= y <= N and 1 <= z <= N and a * (x - y) == b * z and x > y
    )


def report(tag, rows):
    print(f"\n### {tag}")
    for r in rows:
        print("   ", r)


def main():
    a_max = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    b_max = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    k_max = int(sys.argv[3]) if len(sys.argv) > 3 else 8

    # ---------------- Claim 1: the family is a monochromatic solution --------
    n, bad = 0, []
    for a in range(2, a_max + 1):
        for b in range(a + 1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            for k in range(3, k_max + 1):
                (x, y, z), W, N = family(a, b, k)
                n += 1
                if N > 4_000_000:
                    # still verify arithmetically, just skip the colour array
                    cx, cy, cz = (
                        chi_scalar(x, a, b, k),
                        chi_scalar(y, a, b, k),
                        chi_scalar(z, a, b, k),
                    )
                else:
                    C = chi_array(a, b, k)
                    cx, cy, cz = int(C[x]), int(C[y]), int(C[z])
                    assert (cx, cy, cz) == (
                        chi_scalar(x, a, b, k),
                        chi_scalar(y, a, b, k),
                        chi_scalar(z, a, b, k),
                    )
                ok = (
                    is_solution(a, b, x, y, z, N)
                    and cx == cy == cz == 2
                    and valuation(z, a) == 2
                    and valuation(W, a) == 1
                    and x == N - cuts(a, b, k)[2] + 1
                )
                if not ok and len(bad) < 6:
                    bad.append((a, b, k, N, (x, y, z), (cx, cy, cz)))
    print(f"[Claim 1] family is a colour-2 monochromatic solution, b>a, k>=3")
    print(f"          cases={n}  failures={len(bad)}")
    report("failures", bad) if bad else None

    # ---------------- Claim 2: k=3 specialisation ---------------------------
    n2, bad2 = 0, []
    for a in range(2, a_max + 1):
        b = a + 1
        (x, y, z), W, N = family(a, b, 3)
        n2 += 1
        if not (x == a * b * b + 1 and z == a * a * b):
            bad2.append((a, b, (x, y, z), (a * b * b + 1, 1, a * a * b)))
    print(f"\n[Claim 2] at k=3, b=a+1 the family equals (a b^2 + 1, 1, a^2 b)")
    print(f"          cases={n2}  failures={len(bad2)}")
    report("failures", bad2) if bad2 else None

    # general-b k=3 form
    n2b, bad2b = 0, []
    for a in range(2, a_max + 1):
        for b in range(a + 1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            (x, y, z), W, N = family(a, b, 3)
            n2b += 1
            if not (x == a * b * (a + 1) + 1 and z == a * a * (a + 1)):
                bad2b.append((a, b, (x, y, z)))
    print(f"\n[Claim 2b] at k=3, general b>a: X = ab(a+1)+1, Z = a^2(a+1)")
    print(f"           cases={n2b}  failures={len(bad2b)}")
    report("failures", bad2b) if bad2b else None

    # ---------------- Claim 3: the brief's (a b^2+1, 1, a^2 b) at k >= 4 ----
    print(f"\n[Claim 3] TEST OF THE BRIEF'S STATED FAMILY (a b^2+1, 1, a^2 b), b=a+1")
    print(f"          {'a':>3} {'b':>3} {'k':>3} {'N':>9}  {'x':>9} {'y':>3} {'z':>8}"
          f"  chi(x) chi(y) chi(z)  mono?")
    mono_by_k = {}
    for a in range(2, 7):
        b = a + 1
        for k in range(3, 7):
            N = N_shell(a, b, k)
            x, y, z = a * b * b + 1, 1, a * a * b
            if not (x <= N and z <= N):
                print(f"          {a:>3} {b:>3} {k:>3} {N:>9}  out of range")
                continue
            cx, cy, cz = (
                chi_scalar(x, a, b, k),
                chi_scalar(y, a, b, k),
                chi_scalar(z, a, b, k),
            )
            assert a * (x - y) == b * z, "arithmetic identity must hold always"
            m = cx == cy == cz
            mono_by_k.setdefault(k, []).append(m)
            print(f"          {a:>3} {b:>3} {k:>3} {N:>9}  {x:>9} {y:>3} {z:>8}"
                  f"  {cx:>6} {cy:>6} {cz:>6}  {m}")
    print("\n          summary by k:", {k: f"{sum(v)}/{len(v)} mono" for k, v in sorted(mono_by_k.items())})

    # ---------------- Claim 4: for b < a the family is out of range ---------
    n4, bad4 = 0, []
    for a in range(2, a_max + 1):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            for k in range(3, k_max + 1):
                (x, y, z), W, N = family(a, b, k)
                n4 += 1
                if z <= N:
                    bad4.append((a, b, k, N, z))
    print(f"\n[Claim 4] for b < a the same family has Z > N (escapes the interval)")
    print(f"          cases={n4}  violations={len(bad4)}")
    report("violations", bad4) if bad4 else None

    # ---------------- Claim 5: Z <= N  <=>  N(a-b) <= a^2 b -----------------
    n5, bad5 = 0, []
    for a in range(2, a_max + 1):
        for b in range(1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            for k in range(3, k_max + 1):
                (x, y, z), W, N = family(a, b, k)
                n5 += 1
                if (z <= N) != (N * (a - b) <= a * a * b):
                    bad5.append((a, b, k))
    print(f"\n[Claim 5] Z <= N  <=>  N(a-b) <= a^2 b   (all b coprime to a)")
    print(f"          cases={n5}  failures={len(bad5)}")
    report("failures", bad5) if bad5 else None

    # ---------------- Claim 6: why k=2 escapes ------------------------------
    n6, bad6 = 0, []
    for a in range(2, a_max + 1):
        for b in range(1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            N = N_shell(a, b, 2)
            X = N - a * b + 1
            n6 += 1
            if not (N == a * b and X == 1):
                bad6.append((a, b, N, X))
    print(f"\n[Claim 6] at k=2:  N = ab  and  X = N-ab+1 = 1 = Y  (family degenerates)")
    print(f"          cases={n6}  failures={len(bad6)}")
    report("failures", bad6) if bad6 else None

    total_bad = len(bad) + len(bad2) + len(bad2b) + len(bad4) + len(bad5) + len(bad6)
    print(f"\nTOTAL FAILURES (claims 1,2,2b,4,5,6): {total_bad}")
    sys.exit(1 if total_bad else 0)


if __name__ == "__main__":
    main()
