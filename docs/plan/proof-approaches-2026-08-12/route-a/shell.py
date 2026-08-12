"""Shell colouring for a(x-y) = bz : definitions used by every check in route-a.

Everything here is a *definition*, transcribed from PROOF-BRIEF.md.  No claims
are made in this file; the claims live in verify_*.py and are checked against
these definitions.

    Level capacities   L_i = a^(i-1) * b            (i = 2..k)
    N = 2*(L_2 + ... + L_{k-1}) + L_k
    Cumulative cuts    c_1 = 0, c_i = c_{i-1} + L_i (i = 2..k-1)

    chi(j) = min(v(j), k)                              if a | j
    chi(j) = i   if j in [c_{i-1}+1, c_i] U [N-c_i+1, N-c_{i-1}], 2<=i<=k-1
    chi(j) = k   otherwise                             (the "core")
"""

from math import gcd

import numpy as np


def valuation(j: int, a: int) -> int:
    """a-adic valuation of j >= 1."""
    e = 0
    while j % a == 0:
        j //= a
        e += 1
    return e


def levels(a: int, b: int, k: int):
    """L_2..L_k as a dict."""
    return {i: a ** (i - 1) * b for i in range(2, k + 1)}


def N_shell(a: int, b: int, k: int) -> int:
    L = levels(a, b, k)
    return 2 * sum(L[i] for i in range(2, k)) + L[k]


def cuts(a: int, b: int, k: int):
    """c_1..c_{k-1} as a dict (c_1 = 0)."""
    L = levels(a, b, k)
    c = {1: 0}
    for i in range(2, k):
        c[i] = c[i - 1] + L[i]
    return c


def chi_scalar(j: int, a: int, b: int, k: int) -> int:
    """Colour of j in [1, N], computed straight from the definition."""
    N = N_shell(a, b, k)
    c = cuts(a, b, k)
    assert 1 <= j <= N
    v = valuation(j, a)
    if v >= 1:
        return min(v, k)
    for i in range(2, k):
        if c[i - 1] + 1 <= j <= c[i]:
            return i
        if N - c[i] + 1 <= j <= N - c[i - 1]:
            return i
    return k


def chi_array(a: int, b: int, k: int) -> np.ndarray:
    """C[1..N] = chi, vectorised.  C[0] is unused (set to 0)."""
    N = N_shell(a, b, k)
    c = cuts(a, b, k)
    C = np.zeros(N + 1, dtype=np.int64)
    C[1:] = k  # units default to the core colour k
    for i in range(2, k):  # unit shells, two-sided
        C[c[i - 1] + 1 : c[i] + 1] = i
        C[N - c[i] + 1 : N - c[i - 1] + 1] = i
    # multiples of a: chi = min(v, k).  Ascending e overwrites, so the final
    # value at j is the largest e <= k with a^e | j, i.e. min(v(j), k).
    for e in range(1, k + 1):
        step = a**e
        if step <= N:
            C[step :: step] = e
    return C


def solutions(a: int, b: int, n: int):
    """All (x, y, z) in [1,n]^3 with a(x-y) = bz, via x-y = bt, z = at, t>=1.

    Requires gcd(a,b) = 1 (Lemma 1); the caller checks that.
    """
    t = 1
    while a * t <= n and b * t <= n - 1:
        z = a * t
        d = b * t
        for y in range(1, n - d + 1):
            yield (y + d, y, z)
        t += 1


def coprime_pairs(a_max: int, b_max: int, require_b_lt_a: bool):
    for a in range(2, a_max + 1):
        for b in range(1, b_max + 1):
            if gcd(a, b) != 1:
                continue
            if require_b_lt_a and not (b < a):
                continue
            yield a, b
