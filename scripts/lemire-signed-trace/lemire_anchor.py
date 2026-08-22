"""Independent Python anchor for the Lemire / Hayes signed-trace objects over F_2.

Everything here is exact (Python ints / fractions) except the complex character
sums, which use numpy complex128 and are cross-checked against the exact
integer four-population identity.

Conventions (paper, 21 Aug 2026):
  E_j  = (1 + x F_2[x]) / (x^{j+1}),  |E_j| = 2^j
  <F>_j = x^{deg F} F(1/x) mod x^{j+1}            (reversal, then truncate)
  N_j(g) = sum_{F monic, deg F = n, <F>_j = g} Lambda(F)
  H_j(b) = N_j(b) - N_j(b + x^j)   for b in E_j with x^j-coefficient 0
           (so that 2^{j-1} H_j(1) = 2^j N_j(1) - 2^{j-1} N_{j-1}(1))
  P_{j,s} = sum_{g in 2^s E_j} N_j(g)   (2^s E_j = polynomials in x^{2^s} mod x^{j+1})
  h_{j,s} = 2^{j - floor(j/2^s)}
  T_{j,s} = h_{j,s}P_{j,s} - h_{j,s-1}P_{j,s-1} - h_{j-1,s}P_{j-1,s} + h_{j-1,s-1}P_{j-1,s-1}
  C_{l,n} = sum_{j=a}^{l} 2^{j-1} H_j(1),  a = l - ceil(log2 l) - 1

Polynomials over F_2 are ints, bit i = coefficient of x^i.
"""
from __future__ import annotations

import math
import os
import sys
from collections import Counter
from functools import lru_cache
from multiprocessing import Pool

try:
    import flint  # python-flint: fast GF(2)[x] irreducibility
except ImportError:  # pragma: no cover
    flint = None

# ----------------------------------------------------------------------------
# GF(2)[x] as ints
# ----------------------------------------------------------------------------

def pdeg(a: int) -> int:
    return a.bit_length() - 1


def pmul(a: int, b: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def pmod(a: int, m: int) -> int:
    dm = pdeg(m)
    while a and pdeg(a) >= dm:
        a ^= m << (pdeg(a) - dm)
    return a


def pmulmod(a: int, b: int, m: int) -> int:
    return pmod(pmul(a, b), m)


def ppow(a: int, e: int, m: int) -> int:
    r = 1
    a = pmod(a, m)
    while e:
        if e & 1:
            r = pmulmod(r, a, m)
        a = pmulmod(a, a, m)
        e >>= 1
    return r


def pgcd(a: int, b: int) -> int:
    while b:
        a, b = b, pmod(a, b)
    return a


def reverse(F: int, n: int) -> int:
    """x^n F(1/x) for deg F <= n."""
    r = 0
    for i in range(n + 1):
        if (F >> i) & 1:
            r |= 1 << (n - i)
    return r


def cls(F: int, n: int, j: int) -> int:
    """<F>_j as an int with bit 0 set (element of E_j)."""
    return reverse(F, n) & ((1 << (j + 1)) - 1)


def is_irreducible_py(f: int) -> bool:
    """Rabin test, pure Python (fallback when flint is absent)."""
    n = pdeg(f)
    if n <= 0:
        return False
    if n == 1:
        return True
    if not (f & 1):
        return False
    # x^(2^n) == x mod f and gcd(x^(2^(n/p)) - x, f) == 1 for primes p | n
    x = 2
    xp = x
    pw = []
    for _ in range(n):
        xp = pmulmod(xp, xp, f)
        pw.append(xp)
    if pw[n - 1] != x:
        return False
    m = n
    p = 2
    primes = []
    while p * p <= m:
        if m % p == 0:
            primes.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        primes.append(m)
    for p in primes:
        if pgcd(pw[n // p - 1] ^ x, f) != 1:
            return False
    return True


if flint is not None:
    def is_irreducible(f: int) -> bool:
        n = pdeg(f)
        coeffs = [(f >> i) & 1 for i in range(n + 1)]
        _, facs = flint.nmod_poly(coeffs, 2).factor()
        return len(facs) == 1 and facs[0][1] == 1
else:  # pragma: no cover
    is_irreducible = is_irreducible_py


# ----------------------------------------------------------------------------
# Irreducibles and Mangoldt populations
# ----------------------------------------------------------------------------

def _irreducibles_chunk(args):
    d, lo, hi = args
    out = []
    top = 1 << d
    # candidates: x^d + (odd constant term) : f = top | 1 | 2*k, k in [lo,hi)
    for k in range(lo, hi):
        f = top | 1 | (k << 1)
        if is_irreducible(f):
            out.append(f)
    return out


@lru_cache(maxsize=None)
def irreducibles(d: int, procs: int | None = None) -> tuple:
    """All monic irreducibles of degree d over F_2, as ints."""
    if d == 1:
        return (2, 3)  # x, x+1
    # f = x^d + (bits 1..d-1 free) + 1  -> 2^(d-1) candidates, k ranges over 2^(d-1)
    total = 1 << (d - 1)
    procs = procs or max(1, min(os.cpu_count() or 1, 32))
    if total < 1 << 12 or procs == 1:
        return tuple(_irreducibles_chunk((d, 0, total)))
    chunk = (total + 4 * procs - 1) // (4 * procs)
    tasks = [(d, lo, min(total, lo + chunk)) for lo in range(0, total, chunk)]
    with Pool(procs) as pool:
        parts = pool.map(_irreducibles_chunk, tasks)
    return tuple(f for part in parts for f in part)


def populations(n: int, j: int) -> dict[int, int]:
    """N_j(g) for all g in E_j, degree n, Lambda-weighted."""
    assert j <= n
    N = Counter()
    for d in range(1, n + 1):
        if n % d:
            continue
        k = n // d
        for P in irreducibles(d):
            F = P
            for _ in range(k - 1):
                F = pmul(F, P)
            N[cls(F, n, j)] += d
    # every class present
    for g in range(1, 1 << (j + 1), 2):
        N.setdefault(g, 0)
    return dict(N)


def populations_all_levels(n: int, jmax: int) -> dict[int, dict[int, int]]:
    """N_j for every 0<=j<=jmax by projecting the level-jmax populations."""
    top = populations(n, jmax)
    out = {jmax: top}
    for j in range(jmax - 1, -1, -1):
        mask = (1 << (j + 1)) - 1
        N = Counter()
        for g, v in out[j + 1].items():
            N[g & mask] += v
        out[j] = dict(N)
    return out


# ----------------------------------------------------------------------------
# The group E_j: structure, characters, conductors, orders
# ----------------------------------------------------------------------------

def ek(j: int, k: int) -> int:
    """e_k = #{t>=0 : k*2^t <= j}; E_j = prod_{k odd<=j} Z/2^{e_k}."""
    e = 0
    while k << e <= j:
        e += 1
    return e


def odd_gens(j: int) -> list[int]:
    return [k for k in range(1, j + 1, 2)]


def inv_mod(u: int, j: int) -> int:
    """Inverse of u in E_j (u with bit 0 set), via Newton/Hensel: u^{-1} = u^{2^j - 1}? use series."""
    # u^{-1} mod x^{j+1}: iterate v <- v*(2 - u v) -> in char 2: v <- v*(u*v) ... use v <- v*(u v)??
    # simplest: solve by exponent: group order 2^j so u^{-1} = u^{2^j - 1}.
    m = 1 << (j + 1)
    return ppow(u, (1 << j) - 1, m)


def decompose(u: int, j: int) -> dict[int, int]:
    """Write u in E_j as prod_{k odd} (1+x^k)^{a_k}, a_k mod 2^{e_k}. Greedy on lowest term."""
    m = 1 << (j + 1)
    u &= m - 1
    assert u & 1
    a = Counter()
    while u != 1:
        low = (u ^ 1) & -(u ^ 1)  # lowest set bit above 0
        d = pdeg(low)  # degree of lowest nonzero term of u-1
        t = 0
        k = d
        while k % 2 == 0:
            k //= 2
            t += 1
        # multiply by (1+x^k)^{-2^t} = (1 + x^{k 2^t})^{-1}
        a[k] += 1 << t
        g = (1 << d) | 1
        u = pmulmod(u, inv_mod(g, j), m)
    out = {}
    for k in odd_gens(j):
        out[k] = a[k] % (1 << ek(j, k))
    return out


class Characters:
    """All characters of E_j, parametrised by c = (c_k mod 2^{e_k})_{k odd<=j}."""

    def __init__(self, j: int):
        self.j = j
        self.gens = odd_gens(j)
        self.es = {k: ek(j, k) for k in self.gens}
        self.logs = {g: decompose(g, j) for g in range(1, 1 << (j + 1), 2)}
        assert sum(self.es.values()) == j

    def all_c(self):
        import itertools
        ranges = [range(1 << self.es[k]) for k in self.gens]
        for tup in itertools.product(*ranges):
            yield dict(zip(self.gens, tup))

    def order_log2(self, c: dict[int, int]) -> int:
        """log2 of the order of chi_c."""
        s = 0
        for k in self.gens:
            ck = c[k] % (1 << self.es[k])
            if ck:
                v = (ck & -ck).bit_length() - 1
                s = max(s, self.es[k] - v)
        return s

    def conductor(self, c: dict[int, int]) -> int:
        """Least j' such that chi is trivial on ker(E_j -> E_{j'}); 0 for trivial."""
        cond = 0
        for k in self.gens:
            ck = c[k] % (1 << self.es[k])
            if ck:
                v = (ck & -ck).bit_length() - 1
                cond = max(cond, k << (self.es[k] - 1 - v))
        return cond

    def value_phase(self, c: dict[int, int], g: int):
        """Rational phase theta with chi_c(g) = exp(2 pi i theta)."""
        from fractions import Fraction
        th = Fraction(0)
        lg = self.logs[g]
        for k in self.gens:
            th += Fraction(c[k] * lg[k], 1 << self.es[k])
        return th % 1

    def values(self, c):
        import numpy as np
        gs = sorted(self.logs)
        th = np.array([float(self.value_phase(c, g)) for g in gs])
        return gs, np.exp(2j * np.pi * th)


# ----------------------------------------------------------------------------
# Derived quantities
# ----------------------------------------------------------------------------

def H(Nj: dict[int, int], j: int, b: int) -> int:
    """H_j(b) = N_j(b) - N_j(b + x^j), b with x^j-bit clear."""
    assert not (b >> j) & 1
    return Nj[b] - Nj[b | (1 << j)]


def h(j: int, s: int) -> int:
    if s < 0:
        return 0
    return 1 << (j - (j >> s)) if j >= 0 else 0


def P(Nj: dict[int, int], j: int, s: int) -> int:
    """Mass on 2^s E_j = polynomials in x^{2^s} mod x^{j+1}."""
    step = 1 << s
    mask = 0
    for i in range(0, j + 1, step):
        mask |= 1 << i
    return sum(v for g, v in Nj.items() if (g & ~mask) == 0)


def T_four_population(levels: dict[int, dict[int, int]], j: int, s: int) -> int:
    if j == 0:
        return 0
    Nj, Nj1 = levels[j], levels[j - 1]
    return (h(j, s) * P(Nj, j, s) - h(j, s - 1) * P(Nj, j, s - 1)
            - h(j - 1, s) * P(Nj1, j - 1, s) + h(j - 1, s - 1) * P(Nj1, j - 1, s - 1))


def check_order_conductor_reductions(levels: dict[int, dict[int, int]], j: int) -> None:
    """Check the two exact reductions of an order/conductor layer.

    Put q = 2^s and Delta_s = 2 P_{j,s} - P_{j-1,s}.  When q does not
    divide j, the q-power subgroup forces the new x^j coefficient to zero.
    There are then two genuinely different cases:

      * q/2 does not divide j:
        T_{j,s} = 2^(j-1-d_{s-1}) (R Delta_s - Delta_{s-1});
      * q/2 divides j (the conductor/order resonance):
        T_{j,s} = 2^(j-1-d_s) Delta_s.

    The second case has no adjacent-precision difference. This check is
    population-side, independent of the character transform.
    """
    if j == 0:
        return
    for s in range(1, j.bit_length() + 1):
        q = 1 << s
        if j % q == 0:
            continue
        delta_s = 2 * P(levels[j], j, s) - P(levels[j - 1], j - 1, s)
        actual = T_four_population(levels, j, s)
        d_s = (j - 1) // q
        if j % (q >> 1) == 0:
            predicted = (1 << (j - 1 - d_s)) * delta_s
        else:
            d_previous = (j - 1) // (q >> 1)
            delta_previous = (
                2 * P(levels[j], j, s - 1) - P(levels[j - 1], j - 1, s - 1)
            )
            refinement = 1 << (d_previous - d_s)
            predicted = (1 << (j - 1 - d_previous)) * (
                refinement * delta_s - delta_previous
            )
        assert actual == predicted, (j, s, actual, predicted)


def C_ln(levels: dict[int, dict[int, int]], l: int) -> int:
    c = math.ceil(math.log2(l))
    a = l - c - 1
    tot = 0
    for j in range(a, l + 1):
        tot += (1 << (j - 1)) * H(levels[j], j, 1)
    return tot


def B_ln(l: int, n: int) -> int:
    c = math.ceil(math.log2(l))
    a = l - c - 1
    W = (1 << math.ceil(n / 2)) * sum((j - 1) * (1 << (j - 1)) for j in range(1, a))
    return (1 << (2 * l)) - W


if __name__ == "__main__":
    import time
    import numpy as np

    for (l, n) in [(5, 11), (5, 12), (7, 15), (7, 16)]:
        t0 = time.time()
        levels = populations_all_levels(n, l)
        dt = time.time() - t0
        N_id = levels[l][1]
        I_n = len(irreducibles(n))
        for j in range(1, l + 1):
            check_order_conductor_reductions(levels, j)
        print(f"l={l} n={n}: N_l(1)={N_id}  I_n={I_n}  C_{{l,n}}={C_ln(levels, l)}  B={B_ln(l, n)}  "
              f"2^(n-l)-2^l={(1 << (n - l)) - (1 << l)}  ({dt:.1f}s)")
        if n % 2 == 1:
            # odd endpoint identity N_l(1) = 1 + n I_n(1), I_n(1) = irreducibles in identity class
            I1 = sum(1 for Pp in irreducibles(n) if cls(Pp, n, l) == 1)
            print(f"   odd endpoint: N_l(1) = {N_id}, 1 + n*I_n(1) = {1 + n * I1}")

    # Character-side cross-check at (l,n)=(5,11): conductors, orders, Weil, L-polys, T_{j,s}
    l, n = 5, 11
    levels = populations_all_levels(n, l)
    for j in range(1, l + 1):
        ch = Characters(j)
        gs, _ = ch.values(next(ch.all_c()))
        Nvec = np.array([levels[j][g] for g in gs], dtype=float)
        cnt = Counter()
        T_direct = Counter()
        worst = 0.0
        for c in ch.all_c():
            cond = ch.conductor(c)
            s = ch.order_log2(c)
            cnt[(cond, s)] += 1
            _, vals = ch.values(c)
            S = np.sum(Nvec * vals)
            if cond == j:
                worst = max(worst, abs(S) / ((j - 1) * 2 ** math.ceil(n / 2)) if j > 1 else 0)
                T_direct[s] += S
                # L-polynomial from degree balls: c_m = sum_{deg g <= m} chi(g), m < j
                coeffs = []
                for m in range(j):
                    idx = [i for i, g in enumerate(gs) if pdeg(g) <= m]
                    coeffs.append(np.sum(vals[idx]))
                roots = np.roots(coeffs[::-1]) if j > 1 else np.array([])
                if len(roots):
                    inv = 1 / roots
                    assert np.allclose(np.abs(inv), math.sqrt(2), atol=1e-6), (j, c, np.abs(inv))
                    assert np.isclose(-np.sum(inv ** n), S, atol=1e-6), (j, c, -np.sum(inv ** n), S)
        print(f"j={j}: #chars by (conductor, log2 order) = {dict(sorted(cnt.items()))}; "
              f"max |S_n|/((j-1)2^ceil(n/2)) over primitive = {worst:.3f}")
        for s in sorted(T_direct):
            T4 = T_four_population(levels, j, s)
            print(f"    T_{{{j},{s}}}: direct={T_direct[s].real:+.3f}  four-population={T4:+d}  "
                  f"#X={cnt[(j, s)]}  allowance (j-1)2^ceil(n/2)#X/(4l)={(j-1)*2**math.ceil(n/2)*cnt[(j,s)]/(4*l):.1f}")
            assert abs(T_direct[s] - T4) < 1e-6
    print("ALL CROSS-CHECKS PASSED")
