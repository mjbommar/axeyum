"""Twisted cylinder sums A_psi^{(h)} for every cylinder h and every character psi of K.

K = ker(E_ell -> E_{a-1}) is elementary abelian (a > ell/2).  For each cylinder h (a
class of E_{a-1}) and each psi in K^dual,
    A_psi^{(h)} = sum_{g in hK} N(g) psi(g h^{-1}),
the prime mass of the cylinder interval twisted by a sign character of the middle
coefficients.  The open fact F:gf2-lemire-cylinder-twist-sup-bound asks
|A_psi^{(1)}| < 2^{ell-1} for psi != 1 (identity cylinder); the data below also report
the sup over all cylinders.  Values are exact integers (Walsh transform over F_2^r).
"""
from __future__ import annotations

import math
import sys

import numpy as np

from lemire_layers import decode, ek, load_dump


def twisted_sums(ell: int, degree: int, counts: np.ndarray):
    n = degree
    c = math.ceil(math.log2(ell))
    a = ell - c - 1
    fe = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    flo = [(k, 1 << ek(a - 1, k)) for k in range(1, a, 2)]
    idx = np.arange(len(counts), dtype=np.int64)
    co = decode(idx, fe)
    proj = np.zeros(len(counts), dtype=np.int64)
    st = 1
    for i, (k, o) in enumerate(flo):
        proj += (co[:, i] % o) * st
        st *= o
    kidx = np.zeros(len(counts), dtype=np.int64)
    st = 1
    kdims = []
    for i, (k, o) in enumerate(fe):
        olo = (1 << ek(a - 1, k)) if k <= a - 1 else 1
        q = o // olo
        if q > 1:
            assert q == 2, "K is elementary abelian only when a > ell/2"
            kidx += (co[:, i] // olo) * st
            st *= q
            kdims.append(k)
    K = st
    ncyl = 1 << (a - 1)
    M = np.zeros((ncyl, K), dtype=np.int64)
    np.add.at(M, (proj, kidx), counts)
    # Walsh--Hadamard transform along the K axis (exact in int64: entries <= 2^n * K)
    A = M.copy()
    hbit = 1
    while hbit < K:
        for start in range(0, K, 2 * hbit):
            x = A[:, start:start + hbit].copy()
            y = A[:, start + hbit:start + 2 * hbit].copy()
            A[:, start:start + hbit] = x + y
            A[:, start + hbit:start + 2 * hbit] = x - y
        hbit *= 2
    return dict(ell=ell, n=n, a=a, K=K, kdims=kdims, ncyl=ncyl, A=A)


if __name__ == "__main__":
    for path in sys.argv[1:]:
        ell, degree, factors, counts = load_dump(path)
        r = twisted_sums(ell, degree, counts)
        A = r["A"]
        thr = 2 ** (ell - 1)
        nontriv = A[:, 1:]
        rms = math.sqrt(float((nontriv.astype(np.float64) ** 2).mean()))
        pred = 2 ** ((degree - r["a"] + 1) / 2) * math.sqrt(ell)
        print(f"ell={ell:2d} n={degree:2d} a={r['a']:2d} |K|={r['K']:4d} cylinders={r['ncyl']:6d} "
              f"rms|A_psi|={rms:.1f} (random-phase {pred:.1f}, ratio {rms/pred:.3f}) | "
              f"max|A_psi| identity={int(np.abs(A[0,1:]).max())} ({np.abs(A[0,1:]).max()/thr:.3f} thr) "
              f"all={int(np.abs(nontriv).max())} ({np.abs(nontriv).max()/thr:.3f} thr) | "
              f"thr 2^(ell-1)={thr} Weil=(ell-1)2^ceil(n/2)={(ell-1)*2**math.ceil(degree/2)}")
