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


def conditional_witt_cosets(factors, populations: np.ndarray, j: int, s: int):
    """Exact nonresonant Witt-coset diagnostic for one `(j, 2^s)` layer.

    The parent subgroup is `2^(s-1) E_j` and its child is `2^s E_j`.
    When `2^(s-1)` does not divide `j`, both force the new coefficient to
    zero.  Let `mu_z` be the mean coefficient imbalance over the coset `z` of
    the child in the parent.  The exact-order core is

        R Delta_s - Delta_{s-1} = R |child| (mu_0 - mean_z mu_z).

    Returning every coset aggregate distinguishes genuine conditional bit
    balance from cancellation visible only after averaging the coarse fibres.
    """
    q = 1 << s
    if j % q == 0 or j % (q >> 1) == 0:
        raise ValueError("conditional Witt cosets require a nonresonant layer")

    parent = subgroup_mask(factors, s - 1)
    indices = np.flatnonzero(parent)
    d_s = (j - 1) >> s
    d_previous = (j - 1) >> (s - 1)
    coset_count = 1 << (d_previous - d_s)
    child_size = 1 << d_s
    assert len(indices) == coset_count * child_size

    # Multiplication by 1+x^j adds 2^v2(j) in the Big-Witt factor indexed by
    # odd(j).  Thus this computes H_j(g)=N_j(g)-N_j(g(1+x^j)) without decoding
    # every class back to its polynomial representative.
    odd_part, valuation = j, 0
    while odd_part % 2 == 0:
        odd_part //= 2
        valuation += 1
    coordinate = next(i for i, (k, _) in enumerate(factors) if k == odd_part)
    stride = math.prod(order for _, order in factors[:coordinate])
    order = factors[coordinate][1]
    increment = (1 << valuation) * stride
    digit = (indices // stride) % order
    partners = indices + np.where(digit + (1 << valuation) < order, increment, -increment)
    imbalance = populations[indices] - populations[partners]

    # In the parent/child quotient each factor with order at least q contributes
    # one bit: coordinate q/2 modulo q.  Packing those bits gives its coset.
    labels = np.zeros(len(indices), dtype=np.int64)
    stride = 1
    bit = 0
    for _, factor_order in factors:
        if factor_order >= q:
            digit = (indices // stride) % factor_order
            assert np.all(digit % (q >> 1) == 0)
            labels |= ((digit // (q >> 1)) & 1) << bit
            bit += 1
        stride *= factor_order
    assert (1 << bit) == coset_count
    sums = np.zeros(coset_count, dtype=np.int64)
    np.add.at(sums, labels, imbalance)
    assert int(sums[0]) == int(imbalance[labels == 0].sum())

    total = int(sums.sum())
    identity_sum = int(sums[0])
    identity_deviation = coset_count * identity_sum - total
    deviations = [coset_count * int(value) - total for value in sums]
    return dict(
        j=j,
        s=s,
        q=q,
        coset_count=coset_count,
        child_size=child_size,
        delta_s=identity_sum,
        delta_previous=total,
        core=identity_deviation,
        maximum_absolute_core=max(abs(value) for value in deviations),
        total_absolute_core=sum(abs(value) for value in deviations),
        identity_is_max=abs(identity_deviation) == max(abs(value) for value in deviations),
        nonzero_cosets=sum(value != 0 for value in deviations),
    )


def analyse(
    ell: int,
    degree: int,
    counts: np.ndarray,
    jmin: int | None = None,
    verbose: bool = True,
    conditional_min_order: int | None = None,
):
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
            row = dict(j=j, s=s, X=X, T=T, P=P[s], P1=P1[s], D_s=D_s, D_s1=D_s1, d_s=d_s, R=R,
                       ratio=ratio, ok=ratio <= 1 / (4 * ell), high=(1 << s) > Q,
                       resonant=j % (1 << (s - 1)) == 0)
            if (conditional_min_order is not None and (1 << s) >= conditional_min_order
                    and not row["resonant"]):
                conditional = conditional_witt_cosets(fj, Nj, j, s)
                assert conditional["delta_s"] == D_s
                assert conditional["delta_previous"] == D_s1
                assert conditional["core"] == R * D_s - D_s1
                denominator = (R - 1) * (j - 1) * (1 << math.ceil(n / 2))
                conditional["identity_hwo_ratio"] = abs(conditional["core"]) / denominator
                conditional["maximum_coset_hwo_ratio"] = (
                    conditional["maximum_absolute_core"] / denominator
                )
                assert math.isclose(conditional["identity_hwo_ratio"], ratio, rel_tol=0.0, abs_tol=1e-15)
                row["conditional"] = conditional
            rows.append(row)
    if verbose:
        print(f"ell={ell} n={n}: a={a}, c={c}, Q={Q}; threshold 1/(4ell)={1/(4*ell):.5f}; "
              f"N_ell(1)={int(counts[0])} mean={2**(n-ell)}")
        for r in rows:
            print(f"  j={r['j']:2d} s={r['s']} {'HIGH' if r['high'] else 'low '} "
                  f"{'RSD' if r['resonant'] else 'NSD'} #X={r['X']:8d} "
                  f"P={r['P']:10d} D_s={r['D_s']:9d} D_s-1={r['D_s1']:9d} R={r['R']:3d} "
                  f"T={r['T']:13d} ratio={r['ratio']:.5f} {'OK' if r['ok'] else 'over'}")
            if "conditional" in r:
                d = r["conditional"]
                share = (abs(d["core"]) / d["total_absolute_core"]
                         if d["total_absolute_core"] else 0.0)
                print(f"    CONDITIONAL|cosets={d['coset_count']}|child_cells={d['child_size']}"
                      f"|identity_core={d['core']}|maximum_absolute_core={d['maximum_absolute_core']}"
                      f"|identity_share_of_abs_coset_deviation={share:.5f}"
                      f"|identity_is_max={d['identity_is_max']}|nonzero_cosets={d['nonzero_cosets']}"
                      f"|identity_hwo_ratio={d['identity_hwo_ratio']:.5f}"
                      f"|maximum_coset_hwo_ratio={d['maximum_coset_hwo_ratio']:.5f}")
        worst = max((r for r in rows if r['high']), key=lambda r: r['ratio'], default=None)
        if worst:
            print(f"  worst HIGH layer: j={worst['j']} s={worst['s']} ratio={worst['ratio']:.5f} "
                  f"needs factor {worst['ratio']*4*ell:.2f} x (4 ell) ")
    return rows


if __name__ == "__main__":
    arguments = iter(sys.argv[1:])
    path = next(arguments, None)
    if path is None:
        raise SystemExit("usage: lemire_layers.py <dump> [jmin] [--conditional-min-order Q]")
    jmin = None
    conditional_min_order = None
    for argument in arguments:
        if argument == "--conditional-min-order":
            conditional_min_order = int(next(arguments, None))
        elif jmin is None:
            jmin = int(argument)
        else:
            raise SystemExit("usage: lemire_layers.py <dump> [jmin] [--conditional-min-order Q]")
    ell, degree, factors, counts = load_dump(path)
    analyse(ell, degree, counts, jmin, conditional_min_order=conditional_min_order)
