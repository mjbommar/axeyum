"""Exact-order / exact-conductor layer analysis from a population dump.

Input: a dump produced by the branch binary `axeyum-gf2-dump-populations <ell> <degree>`
(mixed-radix class order, generators 1+x^k, first factor fastest), or any file with the
same layout.  Everything here is exact integer arithmetic (numpy int64 / Python ints).

For every level j <= ell and every Witt order 2^s it prints
  P_{j,s}, Delta_{j,s} = 2P_{j,s} - P_{j-1,s}, T_{j,s} (four-population), #X_{j,s},
  ratio = |T| / (#X (j-1) 2^{ceil(n/2)})  and whether ratio <= 1/(4 ell),
and the normalised nested-subgroup form delta_s = Delta_{j,s} / 2^{d_s}.
"""
from __future__ import annotations

import math
import sys

import numpy as np


def ek(j: int, k: int) -> int:
    e = 0
    while k << e <= j:
        e += 1
    return e


def load_dump(path: str):
    with open(path) as fh:
        header = fh.readline().strip()
        struct = fh.readline().strip()
        counts = np.array([int(line) for line in fh if line.strip()], dtype=np.int64)
    kv = dict(item.split("=") for item in header.split("|")[1:])
    ell, degree = int(kv["ell"]), int(kv["degree"])
    # parse factors from the Debug print: odd_degree: k, order: o
    import re
    factors = [(int(k), int(o)) for k, o in re.findall(r"odd_degree: (\d+), order: (\d+)", struct)]
    assert len(counts) == 1 << ell, (len(counts), ell)
    for k, o in factors:
        assert o == 1 << ek(ell, k), (k, o, ek(ell, k))
    return ell, degree, factors, counts


def decode(indices: np.ndarray, factors):
    """Return array of shape (len(indices), len(factors)) of coordinates, first factor fastest."""
    coords = np.empty((len(indices), len(factors)), dtype=np.int64)
    rem = indices.copy()
    for i, (k, o) in enumerate(factors):
        coords[:, i] = rem % o
        rem //= o
    assert not rem.any()
    return coords


def level_populations(ell: int, counts: np.ndarray, j: int):
    """Project the level-ell populations to level j: returns (factors_j, N_j as array in mixed radix)."""
    factors_ell = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    factors_j = [(k, 1 << ek(j, k)) for k in range(1, j + 1, 2)]
    idx = np.arange(len(counts), dtype=np.int64)
    coords = decode(idx, factors_ell)
    proj = np.zeros(len(counts), dtype=np.int64)
    stride = 1
    for i, (k, o) in enumerate(factors_j):
        proj += (coords[:, i] % o) * stride
        stride *= o
    N = np.bincount(proj, weights=counts.astype(np.float64), minlength=1 << j)
    N = np.rint(N).astype(np.int64)
    assert N.sum() == counts.sum()
    return factors_j, N


def subgroup_mask(factors, s: int):
    """Boolean mask over mixed-radix indices of the power subgroup 2^s E_j."""
    size = 1
    for _, o in factors:
        size *= o
    idx = np.arange(size, dtype=np.int64)
    coords = decode(idx, factors)
    m = np.ones(size, dtype=bool)
    for i, (k, o) in enumerate(factors):
        m &= (coords[:, i] % min(o, 1 << s)) == 0
    return m


def h(j: int, s: int) -> int:
    if s < 0:
        return 0
    return 1 << (j - (j >> s))


def analyse(ell: int, degree: int, counts: np.ndarray, jmin: int | None = None, verbose: bool = True):
    n = degree
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    if jmin is None:
        jmin = max(a, 2)
    Q = 1
    while 3 * c * (2 * Q) <= ell:
        Q *= 2
    levels = {}
    for j in range(jmin - 1, ell + 1):
        levels[j] = level_populations(ell, counts, j)
    rows = []
    for j in range(jmin, ell + 1):
        fj, Nj = levels[j]
        fj1, Nj1 = levels[j - 1]
        smax = ek(j, 1)
        P = {}
        P1 = {}
        for s in range(0, smax + 1):
            P[s] = int(Nj[subgroup_mask(fj, s)].sum())
            P1[s] = int(Nj1[subgroup_mask(fj1, s)].sum())
        for s in range(1, smax + 1):
            X = (h(j, s) - h(j, s - 1)) - (h(j - 1, s) - h(j - 1, s - 1))
            if X <= 0:
                continue
            T = h(j, s) * P[s] - h(j, s - 1) * P[s - 1] - h(j - 1, s) * P1[s] + h(j - 1, s - 1) * P1[s - 1]
            D_s = 2 * P[s] - P1[s]
            D_s1 = 2 * P[s - 1] - P1[s - 1]
            d_s = (j - 1) >> s
            d_s1 = (j - 1) >> (s - 1)
            R = 1 << (d_s1 - d_s)
            nsd_lhs = abs(R * D_s - D_s1)
            allowance = (R - 1) * (j - 1) * (1 << math.ceil(n / 2))
            # Exact reduction: the s-part is h_{j-1,s} Delta_{j,s} when 2^s does not divide j
            # (else the layer is empty); the (s-1)-part vanishes when 2^{s-1} divides j.
            expect = h(j - 1, s) * D_s - (0 if j % (1 << (s - 1)) == 0 else h(j - 1, s - 1) * D_s1)
            assert T == expect, (j, s, T, expect)
            ratio = abs(T) / (X * (j - 1) * 2 ** math.ceil(n / 2))
            rows.append(dict(j=j, s=s, X=X, T=T, P=P[s], P1=P1[s], D_s=D_s, D_s1=D_s1, d_s=d_s, R=R,
                             ratio=ratio, ok=ratio <= 1 / (4 * ell), high=(1 << s) > Q))
    if verbose:
        print(f"ell={ell} n={n}: a={a}, c={c}, Q={Q}; threshold 1/(4ell)={1/(4*ell):.5f}; "
              f"N_ell(1)={int(counts[0])} mean={2**(n-ell)}")
        for r in rows:
            print(f"  j={r['j']:2d} s={r['s']} {'HIGH' if r['high'] else 'low '} #X={r['X']:8d} "
                  f"P={r['P']:10d} D_s={r['D_s']:9d} D_s-1={r['D_s1']:9d} R={r['R']:3d} "
                  f"T={r['T']:13d} ratio={r['ratio']:.5f} {'OK' if r['ok'] else 'over'}")
        worst = max((r for r in rows if r['high']), key=lambda r: r['ratio'], default=None)
        if worst:
            print(f"  worst HIGH layer: j={worst['j']} s={worst['s']} ratio={worst['ratio']:.5f} "
                  f"needs factor {worst['ratio']*4*ell:.2f} x (4 ell) ")
    return rows


if __name__ == "__main__":
    path = sys.argv[1]
    jmin = int(sys.argv[2]) if len(sys.argv) > 2 else None
    ell, degree, factors, counts = load_dump(path)
    analyse(ell, degree, counts, jmin)
