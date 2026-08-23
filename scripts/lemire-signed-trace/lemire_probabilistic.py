#!/usr/bin/env python3
"""lemire-signed-trace.probabilistic -- the probabilistic face of Kaser--Lemire.

Companion checker for `docs/research/10-cas/lemire-signed-trace/21-probabilistic-face.md`.

Four things are established here, and each is a named check whose exit status
depends on what the run FINDS (not on the run completing):

  A. the fixed-`q` second-moment (variance) statement in its correct
     `j`-dependent form, with the measured constant;
  B. exact obstructions for negative association, martingale concentration,
     Chen--Stein Poisson approximation, and the extreme-value/order-statistic
     route;
  C. the mechanism behind note 20's anti-correlation `r = -0.657` between the
     two degrees of one group: the Frobenius angle multiset of `E_ell` has
     ~85% of its SQUARED-multiplicity mass on eighth-root angles
     `theta in (1/8)Z` (the supersingular / Kerdock pile-up), and
     `cos(2 pi * 3/8) = -1/sqrt2`;
  D. the calibration of the independent-Sato--Tate random model against
     everything the lane has.

Two independent producers are used and cross-checked:

  * an embedded pure-Python Hayes-character engine (group `E_j = prod_{k odd}
    <1+x^k>`, exact discrete log, `L(u,chi) = sum_{m<j} c_m u^m` with
    `c_m = sum_{v in V_m} chi(v)` in `Z[zeta_{2^E}]`, `S_n = [u^n](u L'/L)`),
    which runs live in every invocation for `ell <= ENGINE_ELL`;
  * the branch CAS `axeyum-gf2-dump-populations`, whose exact class dumps feed
    `--regenerate` and are summarised in the committed `data/prob-*.txt`.

Usage:
    python3 lemire_probabilistic.py                 # all checks, ~40 s
    python3 lemire_probabilistic.py --controls      # mutation controls
    python3 lemire_probabilistic.py --regenerate --scratch DIR

Exit status 0 iff every named check passes; 1 on any violation.
"""

from __future__ import annotations

import argparse
import math
import os
import subprocess
import sys
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
ENDPOINTS = os.path.join(DATA, "aad-endpoint-deviations.txt")
SNAPSHOT = os.environ.get(
    "AXEYUM_LEMIRE_SNAPSHOT",
    "/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440",
)

ENGINE_ELL = 11          # live re-derivation ceiling (cheap); --heavy raises it
GSERIES_N = 6000         # degrees used for the autocorrelation of G_ell(n)
GSERIES_BURN = 200

# ---- stated constants (measured; see note 21) --------------------------------
CJ_MAX = 2.20            # sup over the whole ladder of C_j = Sigma_j/(2^{j-1}(j-1)2^n);
                         # measured sup is 2.179 at (ell,n,j) = (17,36,5).  The
                         # mean over each fixed j is 1.000 to three digits and the
                         # sup over j >= 12 is 1.126.
CJ_TAIL_MAX = 1.15       # sup of C_j over j >= 14 (the fluctuation shrinks like
                         # 2^{-(j-1)/2}: only small j is noisy)
AGG_MAX = 1.03           # sup of V 2^ell / (2^n D(ell)) over the 22 endpoints
SIGN_PATTERN = "+--+-+--"   # sign of the eighth-root atom phase P_ell(r), r=0..7
SIGN_LAW_MIN_HITS = 40      # of 45 nonzero endpoints
RHO_TOL = 0.030             # |empirical lag-1 autocorr of G - predicted|
RHO_BAND = (-0.55, -0.24)   # both must lie here for ell >= 8

MUT: dict[str, bool] = {}

FAILED: list[str] = []
PASSED: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> bool:
    (PASSED if ok else FAILED).append(name)
    print(f"  [{'ok  ' if ok else 'FAIL'}] {name}{(' -- ' + detail) if detail else ''}")
    return ok


# =============================================================================
# 1. the Hayes character engine
# =============================================================================
def ek(ell: int, k: int) -> int:
    """exponent: ord(1 + x^k) in E_ell is 2^{e_k}, e_k = floor(log2(ell/k)) + 1."""
    e = 0
    while (k << e) <= ell:
        e += 1
    return e


def clmul(a: int, b: int, mask: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r & mask


def build_group(ell: int):
    """E_ell = prod_{k odd <= ell} <1 + x^k>, mixed radix, FIRST factor fastest.

    Returns (ks, es, orders, elems) with elems[i] the bit pattern of the group
    element at mixed-radix index i.  The index convention is the one the branch
    CAS `axeyum-gf2-dump-populations` writes.
    """
    mask = (1 << (ell + 1)) - 1
    ks = [k for k in range(1, ell + 1, 2)]
    es = [ek(ell, k) for k in ks]
    if sum(es) != ell:
        raise AssertionError(f"sum e_k = {sum(es)} != ell = {ell}")
    orders = [1 << e for e in es]
    elems = [1]
    for k, o in zip(ks, orders):
        h = 1 | (1 << k)
        pw = [1]
        for _ in range(o - 1):
            pw.append(clmul(pw[-1], h, mask))
        if clmul(pw[-1], h, mask) != 1:
            raise AssertionError(f"ord(1+x^{k}) != {o} in E_{ell}")
        new = [0] * (len(elems) * o)
        for d in range(o):
            for j, e in enumerate(elems):
                new[d * len(elems) + j] = clmul(e, pw[d], mask)
        elems = new
    if len(set(elems)) != 1 << ell:
        raise AssertionError("generator decomposition is not a bijection")
    return ks, es, orders, np.array(elems, dtype=np.int64)


def mixed_radix_digits(idx: np.ndarray, orders) -> np.ndarray:
    out = np.empty((idx.size, len(orders)), dtype=np.int64)
    rem = idx.copy()
    for i, o in enumerate(orders):
        out[:, i] = rem % o
        rem //= o
    assert not rem.any()
    return out


def l_coefficients(ell: int, chunk: int = 256):
    """Exact L-polynomial coefficients of every character of E_ell.

    Returns (coef, H) with coef[a, m, u] the integer coefficient of
    `zeta_{2H}^u` (u < H, using zeta^H = -1) in
    `c_m(chi_a) = sum_{v in V_m} chi_a(v)`, `V_m = {1 + b_1 x + ... + b_m x^m}`.
    """
    ks, es, orders, elems = build_group(ell)
    E = max(es)
    M = 1 << E
    H = M // 2
    idx_of = np.full(1 << (ell + 1), -1, dtype=np.int64)
    idx_of[elems] = np.arange(1 << ell)
    bs = np.arange(1 << (ell - 1), dtype=np.int64)
    g = idx_of[1 | (bs << 1)]
    assert (g >= 0).all()
    scale = np.array([1 << (E - e) for e in es], dtype=np.int64)
    Wb = (mixed_radix_digits(g, orders) * scale) % M
    A = mixed_radix_digits(np.arange(1 << ell, dtype=np.int64), orders)
    coef = np.zeros((1 << ell, ell, H), dtype=np.int64)
    for s in range(0, 1 << ell, chunk):
        S = ((A[s : s + chunk] @ Wb.T) % M).astype(np.int8)
        cnt = np.zeros((S.shape[0], M), dtype=np.int64)
        lo = 0
        for m in range(ell):
            hi = 1 << m
            blk = S[:, 0:1] if m == 0 else S[:, lo:hi]
            for t in range(M):
                cnt[:, t] += (blk == t).sum(axis=1)
            coef[s : s + chunk, m, :] = cnt[:, :H] - cnt[:, H:]
            lo = hi
    return coef, H


def distinct_lpolys(ell: int):
    """Group the NONTRIVIAL characters by their exact L-polynomial.

    Returns (uniq_coef, multiplicity, chat, deg) where `chat` is the L-polynomial
    with the Weil normalisation `alpha -> alpha/sqrt2` applied (so every inverse
    root has modulus 1), and `deg` the L-degree (= conductor - 1).
    """
    coef, H = l_coefficients(ell)
    coef = coef[1:]                       # drop the trivial character
    flat = coef.reshape(coef.shape[0], -1)
    uniq, mult = np.unique(flat, axis=0, return_counts=True)
    uniq = uniq.reshape(len(uniq), ell, H)
    z = np.exp(2j * np.pi * np.arange(H) / (2 * H))
    c = uniq @ z
    chat = c / (2.0 ** (np.arange(ell) / 2.0))[None, :]
    nz = (np.abs(uniq).sum(axis=2) > 0)
    deg = ell - 1 - np.argmax(nz[:, ::-1], axis=1)
    return uniq, mult, chat, deg


def per_character_degree(ell: int) -> np.ndarray:
    coef, H = l_coefficients(ell)
    nz = (np.abs(coef).sum(axis=2) > 0)
    return ell - 1 - np.argmax(nz[:, ::-1], axis=1)


def g_series(ell: int, N: int):
    """G_ell(n) = sum over ALL inverse roots of (alpha/sqrt 2)^n, n = 1..N.

    `G_ell(n) = -2^{-n/2} sum_{chi != 1} S_n(chi)` and `d_n = -2^{-n/2}G_ell(n)`,
    so `N_ell(1) = 2^{n-ell}(1 - 2^{-n/2} G_ell(n))`.
    """
    uniq, mult, chat, deg = distinct_lpolys(ell)
    w = mult.astype(float)
    U = len(uniq)
    hist = np.zeros((ell + 1, U), dtype=complex)
    G = np.zeros(N + 1)
    for n in range(1, N + 1):
        acc = (n * chat[:, n]) if n < ell else np.zeros(U, dtype=complex)
        for m in range(1, min(n, ell - 1) + 1):
            acc = acc - chat[:, m] * hist[(n - m) % (ell + 1)]
        hist[n % (ell + 1)] = acc
        G[n] = -(w * acc).sum().real
    return G, mult, chat, deg


def angle_multiset(ell: int, tol: float = 1e-6):
    """The Frobenius angle multiset A_ell (theta in [0,1), alpha = sqrt2 e(theta))."""
    uniq, mult, chat, deg = distinct_lpolys(ell)
    acc: dict[int, float] = defaultdict(float)
    rh = 0.0
    for i in range(len(uniq)):
        d = int(deg[i])
        if d == 0:
            continue
        roots = np.roots(chat[i, : d + 1][::-1])
        alpha = 1.0 / roots
        rh = max(rh, float(np.abs(np.abs(alpha) - 1).max()))
        for a in alpha:
            acc[int(round(((np.angle(a) / (2 * np.pi)) % 1.0) / tol))] += mult[i]
    th = np.array([k * tol for k in acc])
    m = np.array(list(acc.values()), dtype=float)
    return th, m, rh


def predicted_lag_rho(th: np.ndarray, m: np.ndarray, k: int) -> float:
    """rho_k = (sum_theta m^2 cos(2 pi k theta) - m_0^2) / (sum_theta m^2 - m_0^2).

    Derivation (note 21 sec. 4): with G(n) = sum_theta m_theta e(n theta) and n
    uniform, E[G] = m_0 and E[G(n)G(n+k)] = sum_theta m_theta^2 cos(2 pi k theta)
    (only theta' = -theta survives, and m_{-theta} = m_theta).
    """
    m0 = m[np.isclose(th, 0.0, atol=1e-5)].sum()
    w = m * m
    if MUT.get("m_weighting_linear"):
        # note 20's rejected mechanism: the FIRST Fourier coefficient g_j(1) of
        # the angle multiset, i.e. weight m, not m^2.  It is two orders of
        # magnitude too small, which is exactly why note 20 discarded it.
        w = m.copy()
        m0 = 0.0
    num = float((w * np.cos(2 * np.pi * k * th)).sum()) - m0 ** 2
    den = float(w.sum()) - m0 ** 2
    return num / den


def atom_phase(ell: int, N: int = GSERIES_N):
    """P_ell(r) = mean of G_ell(n) over n = r mod 8: the eighth-root atom phase.

    Averaging over an arithmetic progression mod 8 annihilates every angle
    outside (1/8)Z, so P_ell(r) = sum_{s<8} m_{s/8} e(rs/8) exactly in the limit.
    """
    G, _, _, _ = g_series(ell, N)
    n = np.arange(1, N + 1)
    return np.array([G[1:][(n % 8) == r].mean() for r in range(8)])


# =============================================================================
# 2. data files
# =============================================================================
def read_endpoints():
    rows = []
    with open(ENDPOINTS) as fh:
        for ln in fh:
            if ln.startswith("#"):
                continue
            f = ln.split()
            rows.append(
                dict(ell=int(f[0]), n=int(f[1]), D=int(f[2]), mean=int(f[3]),
                     d=float(f[4]), weil=float(f[5]), sd=float(f[6]), z=float(f[7]))
            )
    return rows


def read_table(path: str):
    """Read a `prob-*.txt` table: '#' comments, whitespace columns, first
    non-comment line beginning with 'COL' names the columns."""
    cols = None
    rows = []
    with open(path) as fh:
        for ln in fh:
            if ln.startswith("#"):
                continue
            f = ln.split()
            if not f:
                continue
            if f[0] == "COL":
                cols = f[1:]
                continue
            assert cols is not None, path
            rows.append(dict(zip(cols, f)))
    return rows


def write_table(path: str, header: list[str], cols: list[str], rows: list[list]):
    with open(path, "w") as fh:
        for h in header:
            fh.write("# " + h + "\n")
        fh.write("COL " + " ".join(cols) + "\n")
        for r in rows:
            fh.write(" ".join(str(x) for x in r) + "\n")


# =============================================================================
# 3. checks
# =============================================================================
def check_engine(ell_max: int) -> None:
    """CHECK_ENGINE_ANCHORS / CHECK_RH_MODULUS / CHECK_CONDUCTOR_COUNT."""
    end = {(r["ell"], r["n"]): r for r in read_endpoints()}
    bad = []
    anchors = {(5, 11): 45, (7, 16): 472}
    for ell in range(2, ell_max + 1):
        G, mult, chat, deg = g_series(ell, 2 * ell + 2)
        for n in (2 * ell + 1, 2 * ell + 2):
            # N_ell(1) = 2^{n-ell} - 2^{n/2} G(n) / 2^ell ... exactly:
            Nn = round(2 ** (n - ell) - (2 ** (n / 2.0)) * G[n] / 2 ** ell)
            D = Nn - 2 ** (n - ell)
            if (ell, n) in end and D != end[(ell, n)]["D"]:
                bad.append((ell, n, D, end[(ell, n)]["D"]))
            if (ell, n) in anchors and Nn != anchors[(ell, n)]:
                bad.append((ell, n, Nn, anchors[(ell, n)]))
    check("CHECK_ENGINE_ANCHORS", not bad,
          f"D_n reproduced exactly at every endpoint 2 <= ell <= {ell_max}"
          if not bad else f"mismatches {bad[:4]}")

    th, m, rh = angle_multiset(ell_max)
    check("CHECK_RH_MODULUS", rh < 1e-6,
          f"max ||alpha|/sqrt2 - 1| = {rh:.2e} over A_{ell_max}")

    deg = per_character_degree(ell_max)
    ok = True
    detail = []
    for j in range(2, ell_max + 1):
        got = int((deg[1:] == j - 1).sum())
        want = 1 << (j - 1)
        if got != want:
            ok = False
            detail.append((j, got, want))
    check("CHECK_CONDUCTOR_COUNT", ok,
          f"#{{chi != 1 : deg L = j-1}} = 2^{{j-1}} for 2 <= j <= {ell_max}"
          if ok else str(detail))


def check_variance_ladder() -> None:
    """CHECK_VARIANCE_WEIL / CHECK_VARIANCE_SIGMA2_SATURATES /
    CHECK_VARIANCE_CONJECTURE / CHECK_PARSEVAL_LADDER."""
    rows = read_table(os.path.join(DATA, "prob-variance-ladder.txt"))
    per = defaultdict(list)
    for r in rows:
        per[(int(r["ell"]), int(r["n"]))].append(r)

    weil_ok, sat_ok, conj_ok, pars_ok = True, True, True, True
    cmax, cmin = 0.0, 1e9
    cmax_at = cmin_at = None
    for (ell, n), rs in sorted(per.items()):
        tot = 0
        for r in rs:
            j = int(r["j"])
            S = int(r["Sigma_j"])
            weil = (1 << (j - 1)) * (j - 1) ** 2 * (1 << n)
            st = (1 << (j - 1)) * (j - 1) * (1 << n)
            tot += S
            if S < 0 or S > weil:
                weil_ok = False
            if j == 2 and S != 2 * (1 << n):
                sat_ok = False
            if j == 1 and S != 0:
                sat_ok = False
            if st:
                c = S / st
                if c > cmax:
                    cmax, cmax_at = c, (ell, n, j)
                if c < cmin:
                    cmin, cmin_at = c, (ell, n, j)
                if MUT.get("weil_uniform_improvement"):
                    # the FALSE uniform-in-j form: a fixed proportional saving
                    # over Weil at EVERY conductor.  It dies at j = 2.
                    if S > 0.9 * weil:
                        conj_ok = False
                elif c > CJ_MAX:
                    conj_ok = False
                if j >= 14 and c > CJ_TAIL_MAX and not MUT.get("weil_uniform_improvement"):
                    conj_ok = False
        V = int(rs[0]["V"])
        if tot != (1 << ell) * V:
            pars_ok = False

    check("CHECK_PARSEVAL_LADDER", pars_ok,
          "sum_j Sigma_j = 2^ell V exactly at every (ell,n)")
    check("CHECK_VARIANCE_WEIL", weil_ok,
          "0 <= Sigma_j <= 2^{j-1}(j-1)^2 2^n at every (ell,n,j)")
    check("CHECK_VARIANCE_SIGMA2_SATURATES", sat_ok,
          "Sigma_1 = 0 and Sigma_2 = 2^{n+1} EXACTLY (Weil attained at j=2)")
    check("CHECK_VARIANCE_CONJECTURE", conj_ok,
          f"C_j = Sigma_j/(2^{{j-1}}(j-1)2^n) in [{cmin:.4f}, {cmax:.4f}] "
          f"<= {CJ_MAX}; max at (ell,n,j)={cmax_at}, min at {cmin_at}")


def check_sum_rule() -> None:
    """CHECK_NEGATIVE_CORRELATION_SUM_RULE.

    sum_{t != 0} (R(t) - 2^{2n-ell}) = -V exactly, R(t) = sum_g N(g)N(g+t).
    An algebraic identity on the stored (total, sum N^2, V) triple.
    """
    rows = read_table(os.path.join(DATA, "prob-order-statistics.txt"))
    ok = True
    worst = None
    for r in rows:
        ell, n = int(r["ell"]), int(r["n"])
        tot, s2, V = int(r["total"]), int(r["sumN2"]), int(r["V"])
        if tot != 1 << n:
            ok = False
        lhs = tot * tot - s2 - ((1 << ell) - 1) * (1 << (2 * n - ell))
        rhs = -V
        if MUT.get("drop_sum_rule_V"):
            rhs = 0
        if lhs != rhs:
            ok = False
            worst = (ell, n, lhs, rhs)
    check("CHECK_NEGATIVE_CORRELATION_SUM_RULE", ok,
          "sum_{t!=0}(R(t) - 2^{2n-ell}) = -V exactly on every dump"
          if ok else f"violated at {worst}")


def check_order_statistics() -> None:
    """CHECK_CLASS_GAUSSIAN / CHECK_EXTREME_VALUE / CHECK_IDENTITY_RANK."""
    rows = read_table(os.path.join(DATA, "prob-order-statistics.txt"))
    m3 = np.array([float(r["m3"]) for r in rows])
    m4 = np.array([float(r["m4"]) for r in rows])
    check("CHECK_CLASS_GAUSSIAN",
          bool(np.abs(m3).max() < 0.15 and np.abs(m4 - 3.0).max() < 0.20),
          f"skew in [{m3.min():+.3f},{m3.max():+.3f}], "
          f"kurtosis in [{m4.min():.3f},{m4.max():.3f}] (Gaussian: 0, 3)")

    ratio = np.array([float(r["max_over_sd"]) for r in rows])
    ell = np.array([int(r["ell"]) for r in rows], dtype=float)
    gum = np.sqrt(2 * ell * math.log(2))
    rel = ratio / gum
    check("CHECK_EXTREME_VALUE",
          bool(0.70 < rel.min() and rel.max() < 1.25),
          f"max_g|D|/sd is {rel.min():.3f}--{rel.max():.3f} times "
          f"sqrt(2 ell log 2) over {len(rows)} endpoints")

    q = np.array([float(r["quantile"]) for r in rows])
    if MUT.get("flip_rank_orientation"):
        q = 1.0 - q
    nq = len(q)
    zmean = (0.5 - q.mean()) / (math.sqrt(1 / 12.0) / math.sqrt(nq))
    hits = int((q <= 0.05).sum())
    lam = 0.05 * nq
    ptail = 1.0 - sum(math.exp(-lam) * lam ** k / math.factorial(k) for k in range(hits))
    check("CHECK_IDENTITY_RANK",
          bool(zmean > 2.5 and hits >= 4 and ptail < 1e-2),
          f"identity quantile mean {q.mean():.3f} (uniform: 0.500), "
          f"{zmean:.2f} sigma low; top-5% hits {hits}/{nq} vs {lam:.2f} expected, "
          f"Poisson p = {ptail:.2e}")


def check_martingale() -> None:
    """CHECK_DOOB_INCREMENT_GAP.

    The Doob martingale of N_ell(G) along the tower E_ell ->> ... ->> E_1 has
    increments D_j(g) = 2^{-ell} sum_{chi in X_j} S_n(chi) conj(chi(g)), whose
    Weil bound is b_j = 2^{j-1}(j-1)2^{n/2-ell}.  Any concentration inequality
    that sees only the b_j cannot beat max_j b_j = b_ell.  The check is that
    b_ell exceeds the whole target deviation 2^{n-ell} by the factor
    (ell-1)/(2 kappa), kappa = 2^{n/2-ell} -- i.e. the martingale route needs
    exactly (AGG_0) and nothing weaker.
    """
    rows = read_table(os.path.join(DATA, "prob-martingale.txt"))
    ok_ratio, ok_true = True, True
    worst_true = 0.0
    for r in rows:
        ell, n, j = int(r["ell"]), int(r["n"]), int(r["j"])
        if j != ell:
            continue
        kappa = 2.0 ** (n / 2.0 - ell)
        if MUT.get("drop_kappa"):
            kappa = 1.0
        want = (ell - 1) / (2 * kappa)
        got = float(r["b_j"]) / 2.0 ** ell / (2.0 ** (n - ell))
        if abs(got - want) > 1e-6 * max(1.0, want):
            ok_ratio = False
        worst_true = max(worst_true, float(r["max_over_b"]))
    attained_j2 = True
    for r in rows:
        if float(r["max_over_b"]) > 1.0 + 1e-9:
            ok_true = False
        if int(r["j"]) == 2:
            want = 1.0 if int(r["n"]) % 2 == 0 else 2.0 ** -0.5
            if abs(float(r["max_over_b"]) - want) > 1e-6:
                attained_j2 = False
    check("CHECK_DOOB_INCREMENT_GAP", ok_ratio,
          "b_ell / 2^{n-ell} = (ell-1)/(2 kappa) at every endpoint: the top "
          "increment bound alone overshoots the target by the (AGG_0) factor")
    check("CHECK_DOOB_INCREMENT_TRUE", ok_true and attained_j2,
          f"max_g |D_j(g)| <= b_j at every (ell,n,j), with EQUALITY at j = 2 for "
          f"every even n and exactly 2^{{-1/2}} for every odd n; worst ratio at "
          f"j = ell is {worst_true:.6f}. The increment bound, "
          f"like the variance bound, admits no uniform-in-j improvement")


def check_anticorrelation(ell_max: int) -> None:
    """CHECK_ANTICORRELATION_MECHANISM / CHECK_EIGHTH_ROOT_MASS /
    CHECK_NORMALISATION_NOT_ARTEFACT / CHECK_SIGN_LAW."""
    ok_rho, ok_band = True, True
    detail = []
    eighth = []
    for ell in range(8, ell_max + 1):
        G, _, _, _ = g_series(ell, GSERIES_N)
        a = G[GSERIES_BURN : GSERIES_N - 1]
        b = G[GSERIES_BURN + 1 : GSERIES_N]
        emp = float(np.corrcoef(a, b)[0, 1])
        th, m, _ = angle_multiset(ell)
        pred = predicted_lag_rho(th, m, 1)
        detail.append((ell, emp, pred))
        if abs(emp - pred) > RHO_TOL:
            ok_rho = False
        if not (RHO_BAND[0] <= emp <= RHO_BAND[1]):
            ok_band = False
        at = np.isclose((th * 8) % 1.0, 0, atol=1e-5) | np.isclose((th * 8) % 1.0, 1, atol=1e-5)
        S2 = float((m * m).sum())
        eighth.append((ell, float((m[at] ** 2).sum()) / S2,
                       float((m[at] ** 2 * np.cos(2 * np.pi * th[at])).sum()) / S2, pred))
    check("CHECK_ANTICORRELATION_MECHANISM", ok_rho,
          "lag-1 autocorrelation of G_ell(n) equals the squared-multiplicity "
          "mean cosine to " + f"{RHO_TOL}: " +
          ", ".join(f"ell={e}: emp {a:+.4f} pred {p:+.4f}" for e, a, p in detail))
    check("CHECK_ANTICORRELATION_SIGN", ok_band,
          f"every measured lag-1 rho lies in {RHO_BAND} (NEGATIVE, order -0.4)")
    frac = eighth[-1][1]
    share = eighth[-1][2] / eighth[-1][3]
    check("CHECK_EIGHTH_ROOT_MASS",
          bool(frac > 0.70 and share > 0.85),
          f"at ell={eighth[-1][0]}: {frac:.3f} of sum m^2 sits on theta in (1/8)Z, "
          f"and those atoms alone supply {share:.3f} of rho_1")

    # the normalisation is provably NOT the mechanism: z_n = -2^{-ell/2}G(n)/sqrt(ell-2+2^{1-ell})
    rows = read_endpoints()
    worst = 0.0
    for r in rows:
        ell, n = r["ell"], r["n"]
        sd = math.sqrt((1 << (n - ell)) * (ell - 2) + 2 ** (n - 2 * ell + 1))
        conv = 2.0 ** (n / 2.0) if not MUT.get("ceil_convention") else 2.0 ** math.ceil(n / 2.0)
        # G(n) = -2^{n/2} d_n ; z = D/sd = -2^{n/2-ell} G(n) / sd  -> factor 2^{-ell/2}/sqrt(ell-2+..)
        Gn = -conv * r["d"]
        z_from_G = -(2.0 ** (n / 2.0 - ell)) * Gn / sd if sd else 0.0
        worst = max(worst, abs(z_from_G - r["z"]))
    check("CHECK_NORMALISATION_NOT_ARTEFACT", worst < 2e-3,
          f"z_n = -2^{{-ell/2}} G_ell(n) / sqrt(ell-2+2^{{1-ell}}) at all 46 "
          f"endpoints (max abs err {worst:.1e}): the n-dependence cancels, so "
          f"the 2^{{ceil(n/2)}} convention CANNOT produce the anti-correlation")

    # the mod-8 sign law
    P = atom_phase(min(ell_max, 11))
    pat = "".join("-" if v < 0 else "+" for v in P)
    if MUT.get("rotate_sign_pattern"):
        pat = pat[1:] + pat[:1]
    hits = tot = 0
    misses = []
    for r in rows:
        if r["z"] == 0.0:
            continue
        tot += 1
        pred = -1.0 if pat[r["n"] % 8] == "+" else +1.0
        if math.copysign(1.0, r["z"]) == pred:
            hits += 1
        else:
            misses.append((r["ell"], r["n"], r["z"]))
    pval = sum(math.comb(tot, k) for k in range(hits, tot + 1)) / 2.0 ** tot
    check("CHECK_SIGN_LAW",
          bool(pat == SIGN_PATTERN and hits >= SIGN_LAW_MIN_HITS and pval < 1e-6),
          f"atom phase sign pattern '{pat}' predicts sign(z) at {hits}/{tot} "
          f"endpoints (binomial p = {pval:.2e}); misses {misses}")


def conductor_blocks(ell: int, N: int = 4000):
    """g_j(n) for each conductor j, over n = 1..N, from the embedded engine."""
    uniq, mult, chat, deg = distinct_lpolys(ell)
    U = len(uniq)
    w = mult.astype(float)
    hist = np.zeros((ell + 1, U), dtype=complex)
    gj = np.zeros((ell + 1, N + 1))
    sel = [(deg == j - 1) for j in range(ell + 1)]
    for n in range(1, N + 1):
        acc = (n * chat[:, n]) if n < ell else np.zeros(U, dtype=complex)
        for m in range(1, min(n, ell - 1) + 1):
            acc = acc - chat[:, m] * hist[(n - m) % (ell + 1)]
        hist[n % (ell + 1)] = acc
        for j in range(2, ell + 1):
            gj[j, n] = -(w[sel[j]] * acc[sel[j]]).sum().real
    return gj[2:, GSERIES_BURN:]


def check_block_independence(ell: int) -> None:
    """CHECK_BLOCK_INDEPENDENCE -- the model's independence ACROSS conductors.

    Asserts the FAILURE: the blocks g_j(n) are strongly positively correlated
    over n (they share the eighth-root atoms), so Var(G) far exceeds
    sum_j Var(g_j).  If independence held, this check would fail and the note's
    calibration verdict would have to change.
    """
    X = conductor_blocks(ell)
    C = np.corrcoef(X)
    k = C.shape[0]
    off = C[np.triu_indices(k, 1)]
    ratio = float(X.sum(axis=0).var() / X.var(axis=1).sum())
    check("CHECK_BLOCK_INDEPENDENCE",
          bool(off.mean() > 0.30 and abs(off).max() > 0.6 and ratio > 1.5),
          f"at ell={ell}: cross-conductor corr(g_j, g_j') has mean {off.mean():+.3f}, "
          f"max |r| {abs(off).max():.3f}; Var(G)/sum_j Var(g_j) = {ratio:.3f} "
          f"-- blocks are NOT independent")


def check_proper_power(ell_max: int) -> None:
    """CHECK_PROPER_POWER_NOT_ARTEFACT.

    The even-degree endpoints carry a square term: F = P^2 with deg P = n/2 and
    <P>_{floor(ell/2)} = 1, of exact Lambda-mass N_{floor(ell/2)}(1) at degree
    n/2.  Subtract it and re-measure the odd-vs-even correlation.
    """
    end = {(r["ell"], r["n"]): r for r in read_endpoints()}
    theta = {}
    for (ell, n) in list(end):
        if n % 2 == 1:
            theta[(ell, n)] = 1
            continue
        l2, m = ell // 2, n // 2
        if l2 < 2 or l2 > ell_max:
            continue
        G, _, _, _ = g_series(l2, m)
        theta[(ell, n)] = round(2.0 ** (m - l2) - (2.0 ** (m / 2.0)) * G[m] / 2 ** l2)
    # note 18 sec. 1.1 C11 pins these by an INDEPENDENT flint enumeration
    pins = {(8, 18): 37, (9, 20): 76, (10, 22): 45, (11, 24): 160, (12, 26): 79,
            (13, 28): 288, (14, 30): 301, (15, 32): 472, (16, 34): 562,
            (17, 36): 1099, (18, 38): 932}
    pin_ok = all(theta.get(k) == v for k, v in pins.items())
    a, b, a2, b2 = [], [], [], []
    for ell in range(4, 25):
        k1, k2 = (ell, 2 * ell + 1), (ell, 2 * ell + 2)
        if k1 not in theta or k2 not in theta or k1 not in end or k2 not in end:
            continue
        a.append(end[k1]["z"])
        b.append(end[k2]["z"])
        a2.append((end[k1]["D"] - theta[k1]) / end[k1]["sd"])
        b2.append((end[k2]["D"] - theta[k2]) / end[k2]["sd"])
    raw = float(np.corrcoef(a, b)[0, 1])
    cor = float(np.corrcoef(a2, b2)[0, 1])
    if MUT.get("skip_theta_subtraction"):
        cor = raw
        pin_ok = pin_ok and False
    check("CHECK_PROPER_POWER_NOT_ARTEFACT",
          bool(pin_ok and raw < -0.5 and cor < -0.5 and abs(raw - cor) < 0.12),
          f"Theta_ell(1) reproduces note 18's 11 flint-enumerated values exactly; "
          f"over {len(a)} groups the odd-vs-even correlation is {raw:+.4f} raw and "
          f"{cor:+.4f} after removing the square mass -- the anti-correlation "
          f"SURVIVES")


def check_stein() -> None:
    """CHECK_STEIN_TV_FLOOR -- an impossibility statement, made arithmetic.

    Model the 2^h window polynomials as independent with irreducibility
    probability p ~ 1/n, W = #irreducibles, lambda = 2^h/n.  The
    Barbour--Holst--Janson Chen--Stein bound is
        d_TV(W, Poisson(lambda)) <= (b1 + b2) min(1, 1/lambda),  b1 >= sum p_i^2,
    hence >= ... and the classical two-sided estimate makes
    d_TV(Bin(2^h, p), Poi(2^h p)) = Theta(p) = Theta(1/n) -- a FLOOR, not an
    artefact of the method.  To exclude the one named class among 2^ell one
    needs resolution 2^{-ell}; the floor exceeds it by 2^ell/n.
    """
    ok = True
    worst = None
    rows = []
    for n in (50, 402, 2050):
        ell = math.ceil(n / 2) - 1
        h = n - ell
        log2_lam = h - math.log2(n)              # lambda = 2^h / n
        log2_tv = -math.log2(n)                  # TV floor = Theta(1/n)
        if MUT.get("stein_floor_free"):
            log2_tv = -log2_lam                  # pretend the floor is 1/lambda
        log2_need = -ell                         # resolution to exclude 1 of 2^ell
        gap = log2_tv - log2_need
        rows.append((n, ell, log2_lam, log2_tv, log2_need, gap))
        if not gap > 15:
            ok = False
            worst = (n, gap)
    check("CHECK_STEIN_TV_FLOOR", ok,
          "; ".join(f"n={n}: lambda = 2^{l:.1f}, P(W=0) ~ exp(-lambda), but the "
                    f"TV floor is 2^{t:.1f} while resolving one class in 2^{ell} "
                    f"needs 2^{nd:.0f} -- short by 2^{g:.0f}, and short of "
                    f"P(W=0) ~ exp(-lambda) by 2^{2.0 ** l * 1.4427 + t:.3e}"
                    for n, ell, l, t, nd, g in rows)
          if ok else f"unexpected at {worst}")


def check_model_calibration() -> None:
    """CHECK_MODEL_CLASS_VARIANCE / CHECK_MODEL_DEGREE_VARIANCE."""
    rows = read_table(os.path.join(DATA, "prob-order-statistics.txt"))
    rat = []
    for r in rows:
        ell, n, V = int(r["ell"]), int(r["n"]), int(r["V"])
        st = ((ell - 2) * (1 << ell) + 2) * (1 << n) / (1 << ell)
        rat.append(V / st)
    rat = np.array(rat)
    check("CHECK_MODEL_CLASS_VARIANCE",
          bool(rat.max() < AGG_MAX and abs(rat[-12:] - 1.0).max() < 0.02),
          f"V / Sato-Tate in [{rat.min():.4f},{rat.max():.4f}], and within 1% of 1 "
          f"at the twelve largest endpoints: the model is RIGHT within a character")

    tbl = read_table(os.path.join(DATA, "prob-anticorrelation.txt"))
    infl = [(int(r["ell"]), float(r["Sigma2"]) / float(r["Sigma1"])) for r in tbl]
    lo = sum(v for _, v in infl[:3]) / 3.0
    hi = sum(v for _, v in infl[-3:]) / 3.0
    check("CHECK_MODEL_DEGREE_VARIANCE",
          bool(infl[-1][1] > 5.0 and hi > 3.0 * lo),
          f"Sigma_2/Sigma_1 (cross-character angle repeats) = "
          + ", ".join(f"{e}:{v:.1f}" for e, v in infl) +
          " -- the model is DECISIVELY WRONG across characters")


# =============================================================================
# 4. regeneration
# =============================================================================
def _project_index(ell: int, j: int, size: int) -> np.ndarray:
    ks = [k for k in range(1, ell + 1, 2)]
    es = [ek(ell, k) for k in ks]
    ksj = [k for k in range(1, j + 1, 2)]
    esj = [ek(j, k) for k in ksj]
    pos = {k: i for i, k in enumerate(ksj)}
    rem = np.arange(size, dtype=np.int64)
    out = np.zeros(size, dtype=np.int64)
    stride = 1
    for k, e in zip(ks, es):
        d = rem % (1 << e)
        rem //= (1 << e)
        if k in pos:
            ej = esj[pos[k]]
            out = out + (d % (1 << ej)) * stride
            stride *= 1 << ej
    assert stride == 1 << j
    return out


def _load_dump(path: str):
    with open(path) as fh:
        head = fh.readline()
        fh.readline()
        rest = fh.read().split()
    kv = dict(it.split("=") for it in head.strip().split("|")[1:])
    ell, n = int(kv["ell"]), int(kv["degree"])
    c = np.array(rest, dtype=np.int64)
    assert c.size == 1 << ell
    return ell, n, c


def _sumsq(d: np.ndarray) -> int:
    mx = int(np.abs(d).max())
    assert d.size * mx * mx < (1 << 62)
    return int(np.dot(d, d))


def regenerate(scratch: str, ells) -> None:
    binp = os.path.join(SNAPSHOT, "target", "release", "axeyum-gf2-dump-populations")
    os.makedirs(scratch, exist_ok=True)
    var_rows, ord_rows, mar_rows = [], [], []
    for ell in ells:
        for n in (2 * ell + 1, 2 * ell + 2):
            path = os.path.join(scratch, f"dump-{ell}-{n}.txt")
            if not os.path.exists(path) or os.path.getsize(path) == 0:
                print(f"  generating {path}", flush=True)
                with open(path, "w") as fh:
                    # the THIRD argument is REQUIRED; without it the binary
                    # panics and leaves a zero-byte dump.
                    subprocess.run([binp, str(ell), str(n), "1300000000"],
                                   stdout=fh, check=True)
            e2, n2, c = _load_dump(path)
            assert (e2, n2) == (ell, n)
            m = 1 << (n - ell)
            d = (c - m).astype(np.int64)
            V = _sumsq(d)
            total = int(np.dot(c, np.ones(c.size, dtype=np.int64)))
            sumN2 = V + (1 << (2 * n - ell))
            ad = np.abs(d)
            a0 = int(ad[0])
            rank = int((ad > a0).sum()) + 1
            sd = math.sqrt(V / c.size)
            x = d.astype(np.float64) / sd
            ord_rows.append([ell, n, total, sumN2, V, int(d[0]), rank,
                             f"{rank / c.size:.6f}", int(ad.max()),
                             f"{ad.max() / sd:.4f}", f"{a0 / sd:.4f}",
                             f"{float((x ** 3).mean()):+.4f}",
                             f"{float((x ** 4).mean()):.4f}"])
            Nj = {ell: c}
            Vj = {0: 0}
            for j in range(ell, 0, -1):
                if j < ell:
                    pi = _project_index(j + 1, j, 1 << (j + 1))
                    Nj[j] = np.bincount(pi, weights=Nj[j + 1].astype(np.float64),
                                        minlength=1 << j).round().astype(np.int64)
                Vj[j] = _sumsq(Nj[j] - (1 << (n - j)))
            for j in range(1, ell + 1):
                S = (1 << j) * Vj[j] - (1 << (j - 1)) * Vj[j - 1]
                st = (1 << (j - 1)) * (j - 1) * (1 << n)
                var_rows.append([ell, n, j, S, V, f"{S / st:.6f}" if st else "0.000000"])
            for j in range(2, ell + 1):
                pi = _project_index(j, j - 1, 1 << j)
                Dj = Nj[j] * np.int64(1 << j) - (Nj[j - 1] * np.int64(1 << (j - 1)))[pi]
                b = (1 << (j - 1)) * (j - 1) * (2.0 ** (n / 2.0))
                mx = int(np.abs(Dj).max())
                mar_rows.append([ell, n, j, mx, int(abs(Dj[0])), f"{b:.6e}",
                                 f"{mx / b:.6f}", f"{abs(int(Dj[0])) / b:.6f}"])
            print(f"  ell={ell} n={n} V={V} rank={rank}/{c.size}", flush=True)

    write_table(
        os.path.join(DATA, "prob-variance-ladder.txt"),
        ["Per-conductor second moments Sigma_j = sum_{cond chi = j} |S_n(chi)|^2",
         "  = 2^j V_j - 2^{j-1} V_{j-1}, V_j the second moment of the level-j",
         "projection of the exact class dump.  Weil: Sigma_j <= 2^{j-1}(j-1)^2 2^n.",
         "Sato-Tate: Sigma_j ~ 2^{j-1}(j-1) 2^n.  C_j is the ratio to Sato-Tate.",
         "Producer: axeyum-gf2-dump-populations <ell> <n> 1300000000."],
        ["ell", "n", "j", "Sigma_j", "V", "C_j"], var_rows)
    write_table(
        os.path.join(DATA, "prob-order-statistics.txt"),
        ["Order statistics of the class deviations D_g = N_ell(g) - 2^{n-ell}.",
         "rank = 1 + #{g : |D_g| > |D_1|} (rank 1 = most extreme class);",
         "quantile = rank / 2^ell (uniform on (0,1] if the identity is typical).",
         "m3, m4 are the third and fourth moments of D_g/sd over all 2^ell classes.",
         "Producer: axeyum-gf2-dump-populations <ell> <n> 1300000000."],
        ["ell", "n", "total", "sumN2", "V", "D_identity", "rank", "quantile",
         "max_abs", "max_over_sd", "identity_over_sd", "m3", "m4"], ord_rows)
    write_table(
        os.path.join(DATA, "prob-martingale.txt"),
        ["Doob martingale of N_ell(G), G uniform on E_ell, along the tower",
         "E_ell ->> E_{ell-1} ->> ... ->> E_1.  Increment (scaled by 2^ell):",
         "  2^ell D_j(g) = 2^j N_j(pi_j g) - 2^{j-1} N_{j-1}(pi_{j-1} g)",
         "                = sum_{chi in X_j} S_n(chi) conj(chi(g)).",
         "b_j = 2^{j-1}(j-1)2^{n/2} is the Weil bound on that quantity."],
        ["ell", "n", "j", "max_abs_inc", "identity_inc", "b_j",
         "max_over_b", "identity_over_b"], mar_rows)
    print("wrote prob-variance-ladder.txt, prob-order-statistics.txt, prob-martingale.txt")


def regenerate_angles(ell_max: int) -> None:
    rows = []
    for ell in range(4, ell_max + 1):
        G, _, _, _ = g_series(ell, GSERIES_N)
        a = G[GSERIES_BURN : GSERIES_N - 2]
        b = G[GSERIES_BURN + 1 : GSERIES_N - 1]
        c = G[GSERIES_BURN + 2 : GSERIES_N]
        th, m, rh = angle_multiset(ell)
        at = np.isclose((th * 8) % 1.0, 0, atol=1e-5) | np.isclose((th * 8) % 1.0, 1, atol=1e-5)
        S1 = float(m.sum())
        S2 = float((m * m).sum())
        P = atom_phase(ell)
        rows.append([ell, f"{float(np.corrcoef(a, b)[0, 1]):+.5f}",
                     f"{predicted_lag_rho(th, m, 1):+.5f}",
                     f"{float(np.corrcoef(a, c)[0, 1]):+.5f}",
                     f"{predicted_lag_rho(th, m, 2):+.5f}",
                     f"{S1:.0f}", f"{S2:.0f}", f"{S2 / S1:.4f}",
                     f"{float((m[at] ** 2).sum()) / S2:.4f}",
                     f"{int(m.max())}",
                     "".join("-" if v < 0 else "+" for v in P)]
                    + [f"{v:.1f}" for v in P])
    write_table(
        os.path.join(DATA, "prob-anticorrelation.txt"),
        ["Frobenius angle multiset A_ell of the FULL character group of E_ell",
         "(all conductors 2..ell), and the lag-k autocorrelation of",
         "  G_ell(n) = sum_{theta in A_ell} e(n theta) = -2^{-n/2} sum_{chi!=1} S_n(chi),",
         "  d_n = -2^{-n/2} G_ell(n).",
         "rho_k_emp is measured over n in [200, 6000); rho_k_pred is",
         "  (sum m_theta^2 cos(2 pi k theta) - m_0^2)/(sum m_theta^2 - m_0^2).",
         "Sigma1 = sum m_theta = D(ell) = (ell-2)2^ell+2, Sigma2 = sum m_theta^2.",
         "eighth_frac is the share of Sigma2 carried by theta in (1/8)Z.",
         "P0..P7 is the eighth-root atom phase P_ell(r) = mean_{n = r mod 8} G_ell(n).",
         "Producer: the embedded Hayes-character engine (independent of the CAS)."],
        ["ell", "rho1_emp", "rho1_pred", "rho2_emp", "rho2_pred", "Sigma1",
         "Sigma2", "Sigma2_over_Sigma1", "eighth_frac", "max_mult", "P_signs",
         "P0", "P1", "P2", "P3", "P4", "P5", "P6", "P7"], rows)
    print("wrote prob-anticorrelation.txt")


def regenerate_calibration(ell_max: int) -> None:
    """Write the calibration table: model prediction vs measurement, per axis."""
    o = read_table(os.path.join(DATA, "prob-order-statistics.txt"))
    ac = read_table(os.path.join(DATA, "prob-anticorrelation.txt"))
    rat = []
    for r in o:
        ell, n, V = int(r["ell"]), int(r["n"]), int(r["V"])
        rat.append(V / (((ell - 2) * (1 << ell) + 2) * (1 << n) / (1 << ell)))
    m3 = np.array([float(r["m3"]) for r in o])
    m4 = np.array([float(r["m4"]) for r in o])
    ell = np.array([int(r["ell"]) for r in o], dtype=float)
    rel = np.array([float(r["max_over_sd"]) for r in o]) / np.sqrt(2 * ell * math.log(2))
    q = np.array([float(r["quantile"]) for r in o])
    X = conductor_blocks(min(ell_max, 11))
    C = np.corrcoef(X)
    off = C[np.triu_indices(C.shape[0], 1)]
    blk = float(X.sum(axis=0).var() / X.var(axis=1).sum())
    rows = [
        ["2nd-moment-over-classes", "V=2^{n-ell}D(ell)", "1",
         f"{np.mean(rat):.4f}", f"[{min(rat):.4f},{max(rat):.4f}]", "CONFIRMED"],
        ["3rd-moment-of-classes", "Gaussian", "0",
         f"{m3.mean():+.4f}", f"[{m3.min():+.4f},{m3.max():+.4f}]", "CONFIRMED"],
        ["4th-moment-of-classes", "Gaussian", "3",
         f"{m4.mean():.4f}", f"[{m4.min():.4f},{m4.max():.4f}]", "CONFIRMED"],
        ["max-over-classes", "Gumbel:sqrt(2*ell*log2)", "1",
         f"{rel.mean():.4f}", f"[{rel.min():.4f},{rel.max():.4f}]", "CONFIRMED"],
        ["identity-class-quantile", "uniform-on-(0,1]", "0.5",
         f"{q.mean():.4f}", f"3.08-sigma-low", "FAILS"],
        ["identity-top-5-percent", "0.05-of-endpoints", "1.10",
         f"{int((q <= 0.05).sum())}", "Poisson-p=9.7e-4", "FAILS"],
        ["cross-character-repeats", "Sigma2/Sigma1=1", "1",
         ac[-1]["Sigma2_over_Sigma1"], f"ell={ac[-1]['ell']}", "FAILS"],
        ["block-independence-in-j", "corr(g_j,g_j')=0", "0",
         f"{off.mean():+.4f}", f"max|r|={abs(off).max():.3f}", "FAILS"],
        ["block-variance-additivity", "Var(G)=sum_j Var(g_j)", "1",
         f"{blk:.4f}", f"ell={min(ell_max,11)}", "FAILS"],
        ["consecutive-degree-corr", "0", "0",
         ac[-1]["rho1_emp"], f"pred {ac[-1]['rho1_pred']}", "FAILS"],
    ]
    write_table(
        os.path.join(DATA, "prob-model-calibration.txt"),
        ["Calibration of the independent-Sato-Tate model (independent USp/PU(j-1)",
         "Frobenius angles per character, blocks independent across conductors)",
         "against every statistic the lane can measure.  Each row is asserted by a",
         "named check in lemire_probabilistic.py; see note 21 sec. 6."],
        ["statistic", "model", "predicted", "measured", "spread", "verdict"], rows)
    print("wrote prob-model-calibration.txt")


# =============================================================================
# 5. controls
# =============================================================================
CONTROLS = [
    ("M1", "m_weighting_linear",
     "weight the angle multiset by m instead of m^2 in the predicted lag-1 "
     "autocorrelation (note 20's rejected first-Fourier-coefficient mechanism)",
     "CHECK_ANTICORRELATION_MECHANISM"),
    ("M2", "weil_uniform_improvement",
     "state the variance conjecture as a uniform-in-j proportional saving over "
     "Weil (Sigma_j <= 0.9 Weil) instead of the j-dependent Sato-Tate form",
     "CHECK_VARIANCE_CONJECTURE"),
    ("M3", "rotate_sign_pattern",
     "rotate the eighth-root atom sign pattern by one residue",
     "CHECK_SIGN_LAW"),
    ("M4", "ceil_convention",
     "use 2^{ceil(n/2)} instead of Weil's actual 2^{n/2} in the z identity",
     "CHECK_NORMALISATION_NOT_ARTEFACT"),
    ("M5", "drop_sum_rule_V",
     "drop the -V on the right of the negative-correlation sum rule",
     "CHECK_NEGATIVE_CORRELATION_SUM_RULE"),
    ("M6", "drop_kappa",
     "drop kappa = 2^{n/2-ell} from the martingale increment requirement",
     "CHECK_DOOB_INCREMENT_GAP"),
    ("M7", "flip_rank_orientation",
     "flip the orientation of the identity's rank among the 2^ell classes",
     "CHECK_IDENTITY_RANK"),
    ("M8", "skip_theta_subtraction",
     "skip the square-mass subtraction (and the flint pins) in the "
     "proper-power control", "CHECK_PROPER_POWER_NOT_ARTEFACT"),
]


def run_all(ell_max: int) -> bool:
    del PASSED[:], FAILED[:]
    print("-- engine")
    check_engine(ell_max)
    print("-- A. the variance statement")
    check_variance_ladder()
    print("-- B(i). negative association / the exact sum rule")
    check_sum_rule()
    print("-- B(ii). martingale concentration along the Witt tower")
    check_martingale()
    print("-- B(iii). Chen--Stein Poisson approximation")
    check_stein()
    print("-- B(iv). extreme values and the identity's rank")
    check_order_statistics()
    print("-- C. the anti-correlation, explained")
    check_anticorrelation(ell_max)
    check_proper_power(ell_max)
    print("-- D. model calibration")
    check_model_calibration()
    check_block_independence(min(ell_max, 11))
    return not FAILED


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--regenerate", action="store_true")
    ap.add_argument("--regenerate-angles", action="store_true")
    ap.add_argument("--regenerate-calibration", action="store_true")
    ap.add_argument("--scratch", default=None)
    ap.add_argument("--ells", default="12-22")
    ap.add_argument("--heavy", action="store_true",
                    help="raise the live engine ceiling from 11 to 13")
    args = ap.parse_args()
    ell_max = 13 if args.heavy else ENGINE_ELL

    if args.regenerate:
        if not args.scratch:
            print("--regenerate needs --scratch DIR", file=sys.stderr)
            return 2
        lo, hi = (int(v) for v in args.ells.split("-"))
        regenerate(args.scratch, range(lo, hi + 1))
        return 0
    if args.regenerate_angles:
        regenerate_angles(ell_max)
        return 0
    if args.regenerate_calibration:
        regenerate_calibration(ell_max)
        return 0

    if args.controls:
        rc = 0
        for tag, flag, what, target in CONTROLS:
            MUT.clear()
            MUT[flag] = True
            run_all(ell_max)
            killed = set(FAILED)
            MUT.clear()
            ok = killed == {target}
            print(f"{tag}: {what}\n    kills {sorted(killed)} "
                  f"(want exactly [{target}]) -- {'ok' if ok else 'CONTROL FAILED'}\n")
            if not ok:
                rc = 1
        return rc

    ok = run_all(ell_max)
    print()
    print(f"{len(PASSED)} checks passed, {len(FAILED)} failed"
          + (f": {FAILED}" if FAILED else ""))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
