"""Verify the proven infinite family: Lemire holds for n = 2*3^k.

Checks, for k = 0..KMAX, that f_k = x^(2*3^k) + x^(3^k) + 1 = Phi_(3^(k+1)) is
irreducible over F_2, has deg(f_k - x^n) = 3^k = floor(n/2), and that 2 is a
primitive root mod 3^(k+1); and that x^(2k)+x^k+1 is F_2-irreducible for
1 <= k <= 81 exactly when k is a power of 3. Exits nonzero on any failure.
Requires python-flint and sympy.
"""
import sys
import flint
from sympy import n_order, totient


def irr_trinomial(n, k):
    c = [0] * (n + 1); c[0] = 1; c[k] ^= 1; c[n] = 1
    _, facs = flint.nmod_poly(c, 2).factor()
    return len(facs) == 1 and facs[0][1] == 1


def main(kmax=6):
    ok = True
    for k in range(kmax + 1):
        n = 2 * 3 ** k; half = 3 ** k; m = 3 ** (k + 1)
        ir = irr_trinomial(n, half)
        prim = n_order(2, m) == totient(m)
        good = ir and (half == n // 2) and prim
        ok &= good
        print(f"k={k}: n={n}, witness x^n+x^(n/2)+1 irreducible={ir}, "
              f"deg(f-x^n)={half}=floor(n/2)={n//2}, 2 primitive root mod 3^{k+1}={prim} -> {good}")
    irr_k = [k for k in range(1, 82) if irr_trinomial(2 * k, k)]
    pow3 = [3 ** j for j in range(5)]
    match = irr_k == pow3
    ok &= match
    print(f"x^(2k)+x^k+1 F_2-irreducible for k in {irr_k}; powers of 3 = {pow3}; match={match}")
    print("INFINITE FAMILY", "OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 6))
