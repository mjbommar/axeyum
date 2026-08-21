"""Galois-ring / Witt-trace dictionary for the Hayes classes E_j over F_2.

Claim to test (derived from the big-Witt-vector structure Lambda(F_2) = prod_{k odd} W(F_2)):
  for alpha in F_{2^n}, the class <charpoly_alpha>_j in E_j is determined by, and
  determines, the vector  ( Tr_{GR(2^s,n)/Z_{2^s}}( teich(alpha)^k )  mod 2^{e_k} )_{k odd <= j},
  where e_k = floor(log2(j/k)) + 1 and teich is the Teichmueller lift.
Consequently  2^s E_j  <->  { Tr(teich(alpha)^k) = 0 mod 2^{min(s, e_k)} for all odd k <= j }.

Implementation: GR(2^s, n) = (Z/2^s)[x]/(h(x)), h a monic lift of an irreducible of degree n.
Teichmueller set = powers of teich(gamma), gamma a primitive root; teich computed by iterating x -> x^{2^n}.
Trace of a Teichmueller element t: sum_i t^{2^i} (Frobenius = squaring on Teichmuellers).
"""
from __future__ import annotations

import numpy as np

from lemire_anchor import (cls, ek, irreducibles, odd_gens, pdeg, pmul, pmulmod, ppow)


def gr_mul(a: np.ndarray, b: np.ndarray, h: np.ndarray, mod: int) -> np.ndarray:
    """Multiply two GR elements given as int64 coefficient vectors (length n), mod (h, 2^s)."""
    n = len(h) - 1
    c = np.convolve(a, b) % mod
    # reduce mod monic h (length n+1, h[n] = 1)
    for d in range(len(c) - 1, n - 1, -1):
        coef = c[d] % mod
        if coef:
            c[d - n:d + 1] = (c[d - n:d + 1] - coef * h) % mod
    return c[:n] % mod


def gr_pow(a, e, h, mod):
    n = len(h) - 1
    r = np.zeros(n, dtype=np.int64); r[0] = 1
    a = a.copy()
    while e:
        if e & 1:
            r = gr_mul(r, a, h, mod)
        a = gr_mul(a, a, h, mod)
        e >>= 1
    return r


def is_primitive(g: int, f: int, n: int) -> bool:
    order = (1 << n) - 1
    # factor order
    m = order; ps = []
    p = 2
    while p * p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        ps.append(m)
    return all(ppow(g, order // p, f) != 1 for p in ps)


def teichmuller_table(n: int, s: int):
    """Return (f, h, T) with f irreducible deg n, h its lift, T[e] = teich(gamma)^e as GR vectors (e < 2^n-1),
    and also the field elements gamma^e as ints (for class computation)."""
    f = irreducibles(n)[0]
    # choose gamma = x if primitive, else search
    g = 2
    while not is_primitive(g, f, n):
        g += 1
    mod = 1 << s
    h = np.array([(f >> i) & 1 for i in range(n + 1)], dtype=np.int64)  # trivial lift
    gvec = np.zeros(n, dtype=np.int64)
    for i in range(n):
        gvec[i] = (g >> i) & 1
    # Teichmueller lift: iterate a -> a^(2^n), s-1 times
    t = gvec.copy()
    for _ in range(s - 1):
        t = gr_pow(t, 1 << n, h, mod)
    assert np.array_equal(gr_pow(t, (1 << n) - 1, h, mod), np.eye(1, n, 0, dtype=np.int64)[0]), "not a root of unity"
    order = (1 << n) - 1
    T = np.zeros((order, n), dtype=np.int64)
    field = np.zeros(order, dtype=np.int64)
    cur = np.zeros(n, dtype=np.int64); cur[0] = 1
    fcur = 1
    for e in range(order):
        T[e] = cur
        field[e] = fcur
        cur = gr_mul(cur, t, h, mod)
        fcur = pmulmod(fcur, g, f)
    return f, h, T, field


def charpoly_class(alpha: int, f: int, n: int, j: int) -> int:
    """<charpoly(alpha)>_j computed from the Frobenius orbit: prod_i (1 - alpha^{2^i} x) mod x^{j+1}."""
    m = 1 << (j + 1)
    g = 1
    a = alpha
    for _ in range(n):
        # multiply g by (1 + a x) in F_{2^n}[x] mod x^{j+1}; coefficients live in the field.
        # we track g as list of field elements
        a = pmulmod(a, a, f)
    # do it properly with field coefficients
    coeffs = [1] + [0] * j
    a = alpha
    for _ in range(n):
        new = coeffs[:]
        for d in range(1, j + 1):
            new[d] ^= pmulmod(coeffs[d - 1], a, f)
        coeffs = new
        a = pmulmod(a, a, f)
    # all coefficients should be in F_2 (0 or 1)
    assert all(c in (0, 1) for c in coeffs), coeffs
    return sum(c << d for d, c in enumerate(coeffs))


def witt_profile(n: int, s: int, kmax: int):
    """For every alpha = gamma^e, the vector (Tr(teich^k) mod 2^s)_{k odd <= kmax}, plus the field element."""
    f, h, T, field = teichmuller_table(n, s)
    order = (1 << n) - 1
    mod = 1 << s
    ks = [k for k in range(1, kmax + 1, 2)]
    prof = np.zeros((order, len(ks)), dtype=np.int64)
    idx = np.arange(order, dtype=np.int64)
    for ki, k in enumerate(ks):
        tr = np.zeros((order, n), dtype=np.int64)
        for i in range(n):
            tr += T[(idx * k * (1 << i)) % order]
        tr %= mod
        assert not tr[:, 1:].any(), f"trace not in Z/2^s for k={k}"
        prof[:, ki] = tr[:, 0]
    return f, field, ks, prof


if __name__ == "__main__":
    import sys
    from collections import defaultdict
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    j = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    smax = max(ek(j, 1), 1)
    f, field, ks, prof = witt_profile(n, smax, j)
    es = {k: ek(j, k) for k in ks}
    fwd = {}
    back = {}
    ok = True
    for e in range(len(field)):
        alpha = int(field[e])
        g = charpoly_class(alpha, f, n, j)
        key = tuple(int(prof[e, ki]) % (1 << es[k]) for ki, k in enumerate(ks))
        if g in fwd and fwd[g] != key:
            ok = False; print("class -> profile not functional", g, fwd[g], key); break
        if key in back and back[key] != g:
            ok = False; print("profile -> class not functional", key, back[key], g); break
        fwd[g] = key
        back[key] = g
    # alpha = 0 has class 1 and profile 0
    print(f"n={n} j={j}: e_k={es}; distinct classes seen={len(fwd)} of {1 << j}; bijective dictionary: {ok}")
    # show the dictionary for small j
    if j <= 4:
        for g in sorted(fwd):
            print(f"  class {bin(g)} -> {fwd[g]}")
    sys.exit(0 if ok else 1)
