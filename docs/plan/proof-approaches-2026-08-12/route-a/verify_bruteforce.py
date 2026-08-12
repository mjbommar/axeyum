"""Brute force: is the shell colouring solution-free?

Reports, for every (a,b,k) in range, the number of solution triples examined
and the first monochromatic solution found (if any).  A NONZERO triple count
is printed for every parameter point; a run that examines 0 triples is not
evidence of anything.
"""

import sys
from math import gcd

import numpy as np

from shell import N_shell, chi_array, chi_scalar, cuts


def scan(a: int, b: int, k: int):
    """Return (n_triples_examined, first_mono or None)."""
    N = N_shell(a, b, k)
    C = chi_array(a, b, k)
    examined = 0
    first = None
    t = 1
    while a * t <= N:
        d = b * t
        if d > N - 1:
            break
        z = a * t
        c = C[z]
        ys = C[1 : N - d + 1]
        xs = C[1 + d : N + 1]
        examined += N - d
        if first is None:
            hit = np.flatnonzero((ys == c) & (xs == c))
            if hit.size:
                y = int(hit[0]) + 1
                first = (y + d, y, z)
        t += 1
    return examined, first


def check_array_matches_scalar(a, b, k, sample=400):
    """chi_array must agree with the straight-from-definition chi_scalar."""
    N = N_shell(a, b, k)
    C = chi_array(a, b, k)
    idx = range(1, N + 1) if N <= sample else np.linspace(1, N, sample, dtype=int)
    bad = [j for j in idx if int(C[int(j)]) != chi_scalar(int(j), a, b, k)]
    return bad


def main():
    a_max = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    k_max = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    b_max = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    mode = sys.argv[4] if len(sys.argv) > 4 else "blt"  # blt | bgt

    total_triples = 0
    n_points = 0
    failures = []
    print(f"{'a':>3} {'b':>3} {'k':>3} {'N':>8} {'triples':>12}  verdict")
    for a in range(2, a_max + 1):
        for b in range(1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            if mode == "blt" and not b < a:
                continue
            if mode == "bgt" and not b > a:
                continue
            for k in range(2, k_max + 1):
                N = N_shell(a, b, k)
                if N > 300_000:
                    continue
                bad = check_array_matches_scalar(a, b, k)
                assert not bad, f"chi mismatch at {(a,b,k)}: {bad[:5]}"
                ex, first = scan(a, b, k)
                total_triples += ex
                n_points += 1
                if first is None:
                    verdict = "solution-free"
                else:
                    verdict = f"MONOCHROMATIC {first} colour={chi_scalar(first[0],a,b,k)}"
                    failures.append(((a, b, k), first))
                print(f"{a:>3} {b:>3} {k:>3} {N:>8} {ex:>12}  {verdict}")
    print()
    print(f"parameter points: {n_points}")
    print(f"solution triples examined: {total_triples}")
    print(f"defective points: {len(failures)}")
    for pt, sol in failures:
        print("   ", pt, sol)


if __name__ == "__main__":
    main()
