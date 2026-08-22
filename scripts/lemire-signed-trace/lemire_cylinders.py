"""Cylinder variances for the one-sided (ICV) route, from a population dump.

For a = ell - ceil(log2 ell) - 1, the identity cylinder is the set of level-ell classes
lying over the identity of E_{a-1} (|K| = 2^{ell-a+1} classes). (REL) follows from
  SSD_id := sum_{g in K} (N_ell(g) - mean_K)^2  <  2^{2 ell - 2}
(the branch's (ICV) premise). This script prints SSD for the identity cylinder, the
average SSD over all 2^{a-1} cylinders, the rank of the identity cylinder, the
Sato--Tate (diagonal) prediction, and the threshold.  Exact integer arithmetic.
"""
from __future__ import annotations

import math
import sys

import numpy as np

from lemire_layers import decode, ek, load_dump


def cylinder_stats(ell: int, degree: int, counts: np.ndarray):
    n = degree
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    factors_ell = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    factors_lo = [(k, 1 << ek(a - 1, k)) for k in range(1, a, 2)]
    idx = np.arange(len(counts), dtype=np.int64)
    coords = decode(idx, factors_ell)
    proj = np.zeros(len(counts), dtype=np.int64)
    stride = 1
    for i, (k, o) in enumerate(factors_lo):
        proj += (coords[:, i] % o) * stride
        stride *= o
    ncyl = 1 << (a - 1)
    K = 1 << (ell - a + 1)
    # Keep the scaled variance numerator
    #
    #   V_c = K sum_{g in c} N(g)^2 - (sum_{g in c} N(g))^2 = K * SSD_c
    #
    # as an integer.  At ell=22 the float64 route rounds enough terms to
    # change the identity-cylinder rank, even though it leaves its displayed
    # scientific-notation value unchanged.
    sums = np.zeros(ncyl, dtype=np.int64)
    squares = np.zeros(ncyl, dtype=np.int64)
    np.add.at(sums, proj, counts)
    np.add.at(squares, proj, counts * counts)
    variance_numerators = [
        K * int(square_sum) - int(total) * int(total)
        for total, square_sum in zip(sums, squares, strict=True)
    ]
    ssd_id_num = variance_numerators[0]
    rank = sum(value > ssd_id_num for value in variance_numerators) + 1
    total = int(sums[0])
    mean_id = total / K
    thr = 2 ** (2 * ell - 2)
    st = ell * 2 ** (n - a + 1)  # diagonal prediction ~ ell * cylinder total
    return dict(
        ell=ell,
        n=n,
        a=a,
        K=K,
        ncyl=ncyl,
        N_id=int(counts[0]),
        mean_id=mean_id,
        ssd_id_num=ssd_id_num,
        ssd_average_num=sum(variance_numerators),
        ssd_max_num=max(variance_numerators),
        rank=rank,
        thr=thr,
        st=st,
        dev_id=int(counts[0]) - mean_id,
    )


if __name__ == "__main__":
    for path in sys.argv[1:]:
        ell, degree, factors, counts = load_dump(path)
        r = cylinder_stats(ell, degree, counts)
        ssd_id = r["ssd_id_num"] / r["K"]
        ssd_avg = r["ssd_average_num"] / (r["K"] * r["ncyl"])
        ssd_max = r["ssd_max_num"] / r["K"]
        print(f"ell={r['ell']:2d} n={r['n']:2d} a={r['a']:2d} |K|={r['K']:4d} cylinders={r['ncyl']:7d} "
              f"N_id={r['N_id']:9d} mean_K={r['mean_id']:11.1f} dev_id={r['dev_id']:+9.1f} | "
              f"SSD_id={ssd_id:.3e} avg={ssd_avg:.3e} max={ssd_max:.3e} "
              f"rank={r['rank']}/{r['ncyl']} | ST~{r['st']:.2e} thr=2^(2ell-2)={r['thr']:.2e} "
              f"SSD_id/thr={ssd_id/r['thr']:.2e}")
