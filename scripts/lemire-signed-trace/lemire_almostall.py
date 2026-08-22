#!/usr/bin/env python3
"""lemire-signed-trace.almostall -- numerical control for the "almost all top halves" theorem.

For each exact class-population dump `lemire-signed-trace.dump-<ell>-<n>.txt`
(N_ell(g) = Mangoldt mass of monic degree-n F with <F>_ell = g, mixed-radix Witt
class order) this script checks, with exact integer arithmetic:

  (C1) total mass  sum_g N_ell(g) = 2^n;
  (C2) the Weil/Parseval second-moment inequality
         V := sum_g (N_ell(g) - 2^{n-ell})^2
            = 2^{-ell} sum_{chi != 1} |S_n(chi)|^2
            <= 2^{2*ceil(n/2)} * ( (ell^2-4ell+6) - 6*2^{-ell} )  =: Vbound;
  (C3) the Chebyshev exceptional-set bound
         #{g : |N_ell(g)-2^{n-ell}| >= t 2^{n-ell}} <= Vbound / (t 2^{n-ell})^2
       for t in {1/4, 1/2, 3/4}, against the exact count;
  (C4) per-conductor exact second moments Sigma_j = sum_{cond(chi)=j} |S_n(chi)|^2
       = 2^j V_j - 2^{j-1} V_{j-1} (V_j the second moment of the level-j
       projection) satisfy 0 <= Sigma_j <= 2^{j-1} (j-1)^2 2^{2 ceil(n/2)};
       in particular Sigma_1 = 0 (the conductor-1 character has L = 1);
  (C5) the proper-power bookkeeping: Theta_n = 2^n - n I_n is the total mass of
       proper prime powers of degree n, and #{g : Theta(g) >= 2^{n-ell}/2}
       <= 2 Theta_n 2^{ell-n} must be < 2 (the theorem's "+1");
  (C6) the stronger empirical statement min_g N_ell(g) > Theta_n, which certifies
       that EVERY class contains an irreducible of degree n.

Exit status 0 iff every check passes; 1 on any violation.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys

import numpy as np

DEFAULT_DUMPS = os.path.dirname(os.path.abspath(__file__))
PREFIX = "lemire-signed-trace.dump-"


# ---------------------------------------------------------------- exact helpers
def exact_sumsq(d: np.ndarray) -> int:
    """Exact sum of squares of an int64 array, via a 2^20 hi/lo split."""
    a = np.abs(d.astype(np.int64))
    if a.size == 0:
        return 0
    shift = 20
    hi = (a >> shift).astype(np.int64)
    lo = (a & ((1 << shift) - 1)).astype(np.int64)
    hmax, lmax = int(hi.max()), int(lo.max())
    step = 1 << 20
    assert hmax * hmax * step < (1 << 62), "hi accumulator would overflow"
    assert hmax * lmax * step < (1 << 62), "cross accumulator would overflow"
    assert lmax * lmax * step < (1 << 62), "lo accumulator would overflow"
    s_hh = s_hl = s_ll = 0
    for i in range(0, a.size, step):
        h, l = hi[i : i + step], lo[i : i + step]
        s_hh += int(np.dot(h, h))
        s_hl += int(np.dot(h, l))
        s_ll += int(np.dot(l, l))
    return (s_hh << (2 * shift)) + (s_hl << (shift + 1)) + s_ll


def _mobius(m: int) -> int:
    mu, p = 1, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            mu = -mu
        p += 1
    if m > 1:
        mu = -mu
    return mu


def n_irreducible(n: int) -> int:
    """I_n over F_2 by Moebius inversion."""
    tot = sum(_mobius(n // d) * (1 << d) for d in range(1, n + 1) if n % d == 0)
    assert tot % n == 0
    return tot // n


def theta_n(n: int) -> int:
    """Total Mangoldt mass of PROPER prime powers of degree n: 2^n - n I_n."""
    return (1 << n) - n * n_irreducible(n)


def ek(j: int, k: int) -> int:
    e = 0
    while k << e <= j:
        e += 1
    return e


# ---------------------------------------------------------------- dump loading
def load_dump(path: str):
    with open(path) as fh:
        header = fh.readline().strip()
        fh.readline()  # STRUCTURE line
        rest = fh.read().split()
    kv = dict(item.split("=") for item in header.split("|")[1:])
    ell, n = int(kv["ell"]), int(kv["degree"])
    counts = np.array(rest, dtype=np.int64)
    assert counts.size == 1 << ell, (counts.size, ell)
    return ell, n, counts


def decode_coords(ell: int, size: int) -> np.ndarray:
    """Mixed-radix Witt coordinates (first factor fastest), uint8."""
    factors = [(k, 1 << ek(ell, k)) for k in range(1, ell + 1, 2)]
    coords = np.empty((size, len(factors)), dtype=np.uint8)
    rem = np.arange(size, dtype=np.int64)
    for i, (_, o) in enumerate(factors):
        coords[:, i] = (rem % o).astype(np.uint8)
        rem //= o
    assert not rem.any()
    return coords


def level_second_moments(ell: int, n: int, counts: np.ndarray) -> list[int]:
    """V_j = sum_{g in E_j} (N_j(g) - 2^{n-j})^2 for j = 0..ell (exact)."""
    coords = decode_coords(ell, counts.size)
    w = counts.astype(np.float64)
    vs = [0]  # V_0 = 0
    for j in range(1, ell + 1):
        proj = np.zeros(counts.size, dtype=np.int64)
        stride = 1
        for i, k in enumerate(range(1, j + 1, 2)):
            o = 1 << ek(j, k)
            proj += (coords[:, i].astype(np.int64) % o) * stride
            stride *= o
        assert stride == 1 << j
        nj = np.rint(np.bincount(proj, weights=w, minlength=1 << j)).astype(np.int64)
        assert int(nj.sum()) == (1 << n)
        vs.append(exact_sumsq(nj - (1 << (n - j))))
    return vs


# ---------------------------------------------------------------- the bounds
def eps_ell(ell: int) -> float:
    """(ell^2 - 4 ell + 6) - 6 * 2^-ell, the exact character-sum constant."""
    return (ell * ell - 4 * ell + 6) - 6.0 / (1 << ell)


def char_sum_const(ell: int) -> int:
    """A(ell) = sum_{i=1}^{ell-1} i^2 2^i = 2^ell (ell^2 - 4 ell + 6) - 6."""
    return (1 << ell) * (ell * ell - 4 * ell + 6) - 6


def weil_second_moment_bound(ell: int, n: int, sharp: bool = False) -> int:
    """2^{-ell} A(ell) 2^{2 ceil(n/2)} (or 2^n with the sharp RH form), rounded up."""
    a = char_sum_const(ell)
    num = a << (n if sharp else 2 * ((n + 1) // 2))
    q, r = divmod(num, 1 << ell)
    return q + (1 if r else 0)


# ---------------------------------------------------------------- per-dump work
def analyse(path: str, do_conductors: bool) -> dict:
    ell, n, counts = load_dump(path)
    assert n in (2 * ell + 1, 2 * ell + 2), (ell, n)
    mean = 1 << (n - ell)
    fails: list[str] = []

    total = int(counts.sum())
    if total != 1 << n:
        fails.append(f"C1 total mass {total} != 2^{n}")

    d = counts - mean
    v = exact_sumsq(d)
    vbound = weil_second_moment_bound(ell, n)
    vsharp = weil_second_moment_bound(ell, n, sharp=True)
    if v > vbound:
        fails.append(f"C2 second moment {v} > Weil bound {vbound}")
    if v > vsharp:
        fails.append(f"C2s second moment {v} > sharp-RH bound {vsharp}")

    cheb = {}
    for num, den in ((1, 4), (1, 2), (3, 4)):
        t = num / den
        thr = mean * num  # compare den*|d| >= num*mean
        actual = int(np.count_nonzero(np.abs(d) * den >= thr))
        bound = vbound * den * den / (num * num * mean * mean)
        if actual > math.floor(bound + 1e-9):
            fails.append(f"C3 t={num}/{den}: actual {actual} > bound {bound:.3f}")
        cheb[f"{num}/{den}"] = {"actual": actual, "bound": bound}
        # C3c: the numeric bound must agree with the closed form published in the
        # note, kappa_n 2^{2ell-n} eps(ell) / t^2 with kappa_n = 2^{2 ceil(n/2)-n}.
        closed = (2 ** (2 * ((n + 1) // 2) - n)) * (2.0 ** (2 * ell - n)) * eps_ell(ell) * (den / num) ** 2
        if abs(bound - closed) > 1e-6 * max(1.0, closed):
            fails.append(f"C3c t={num}/{den}: script bound {bound} != closed form {closed}")

    # C3b: the Chebyshev inequality at nine data-driven thresholds.  These fire
    # (unlike C3, whose exact counts are 0 at t >= 1/4) and bind BOTH the exact
    # second moment V and the Weil bound Vbound to the observed tail.
    ad = np.abs(d)
    dmax = int(ad.max())
    tail = []
    for i in range(1, 10):
        u = (dmax * i) // 10
        if u == 0:
            continue
        cnt = int(np.count_nonzero(ad >= u))
        tail.append({"u": u, "u_rel": u / mean, "count": cnt})
        if cnt * u * u > v:
            fails.append(f"C3b exact Chebyshev: {cnt} classes with |D|>={u} but V={v}")
        if cnt * u * u > vbound:
            fails.append(f"C3b Weil Chebyshev: {cnt} classes with |D|>={u} but Vbound={vbound}")
    if not tail or tail[-1]["count"] < 1:
        fails.append("C3b produced no live threshold (check is inert)")

    th = theta_n(n)
    pp_bound = 2.0 * th / mean  # #{g : Theta(g) >= mean/2}
    if pp_bound >= 2.0:
        fails.append(f"C5 proper-power Markov count {pp_bound:.4f} >= 2")

    minn = int(counts.min())
    all_irr = minn > th
    if not all_irr:
        fails.append(f"C6 min N {minn} <= Theta_n {th} (cannot certify all classes)")

    sigmas = None
    if do_conductors:
        vs = level_second_moments(ell, n, counts)
        if vs[ell] != v:
            fails.append(f"C4 level-ell second moment mismatch {vs[ell]} != {v}")
        sigmas = []
        for j in range(1, ell + 1):
            sig = (vs[j] << j) - (vs[j - 1] << (j - 1))
            wb = ((j - 1) ** 2) << (j - 1 + 2 * ((n + 1) // 2))
            sigmas.append(sig)
            if sig < 0:
                fails.append(f"C4 Sigma_{j} = {sig} < 0")
            if sig > wb:
                fails.append(f"C4 Sigma_{j} = {sig} > per-conductor Weil {wb}")
        if sigmas[0] != 0:
            fails.append(f"C4 Sigma_1 = {sigmas[0]} != 0")

    # Sato--Tate (Keating--Rudnick) heuristic second moment: sum of L-degrees * 2^n / 2^ell
    v_st = (((1 << ell) * (ell - 2) + 2) * (1 << n)) / (1 << ell)

    return {
        "ell": ell,
        "n": n,
        "mean": mean,
        "identity": int(counts[0]),
        "min": minn,
        "max": int(counts.max()),
        "maxdev_rel": float(np.abs(d).max()) / mean,
        "V": v,
        "Vbound": vbound,
        "Vsharp": vsharp,
        "V_over_bound": v / vbound,
        "V_over_sharp": v / vsharp,
        "V_over_satotate": v / v_st,
        "cheb": cheb,
        "tail": tail,
        "theta": th,
        "theta_over_mean": th / mean,
        "pp_markov": pp_bound,
        "all_classes_irreducible": bool(all_irr),
        "sigmas": sigmas,
        "fails": fails,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dumps", default=DEFAULT_DUMPS)
    ap.add_argument("--conductor-ell-max", type=int, default=18)
    ap.add_argument("--json", default=None)
    ap.add_argument("--detail", default=None, help="ell,n -- print the per-conductor table")
    args = ap.parse_args()

    files = []
    for fn in sorted(os.listdir(args.dumps)):
        m = re.fullmatch(re.escape(PREFIX) + r"(\d+)-(\d+)\.txt", fn)
        if m:
            files.append((int(m.group(1)), int(m.group(2)), os.path.join(args.dumps, fn)))
    files.sort()
    if not files:
        print("no dumps found", file=sys.stderr)
        return 1

    rows, bad = [], 0
    for ell, n, path in files:
        r = analyse(path, do_conductors=(ell <= args.conductor_ell_max))
        rows.append(r)
        bad += len(r["fails"])
        for f in r["fails"]:
            print(f"FAIL ell={ell} n={n}: {f}", file=sys.stderr)

    if args.detail:
        de, dn = (int(x) for x in args.detail.split(","))
        for r in rows:
            if r["ell"] == de and r["n"] == dn and r["sigmas"]:
                print(f"per-conductor second moments, ell={de} n={dn}")
                print(f"{'j':>3} {'#chi':>10} {'Sigma_j':>22} {'/sharp Weil':>12} {'rms|S|/(j-1)2^(n/2)':>21}")
                for j, sig in enumerate(r["sigmas"], start=1):
                    wb = ((j - 1) ** 2) << (j - 1 + dn)  # sharp: (j-1)^2 2^n per character
                    rat = int(sig) / wb if wb else 0.0
                    print(f"{j:>3} {1 << (j-1):>10} {int(sig):>22} {rat:>12.5f} {math.sqrt(rat) if rat else 0.0:>21.5f}")
                print()

    hdr = (
        f"{'ell':>3} {'n':>3} {'2^(n-ell)':>12} {'minN/mean':>9} {'max|D|/mean':>11} "
        f"{'V/Weil':>8} {'V/RH':>6} {'V/ST':>6} {'#|D|>=m/2':>9} {'bound':>9} {'Th/mean':>8} {'allirr':>6}"
    )
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        c = r["cheb"]["1/2"]
        print(
            f"{r['ell']:>3} {r['n']:>3} {r['mean']:>12} {r['min']/r['mean']:>9.4f} "
            f"{r['maxdev_rel']:>11.4f} {r['V_over_bound']:>8.5f} {r['V_over_sharp']:>6.4f} {r['V_over_satotate']:>6.3f} "
            f"{c['actual']:>9} {c['bound']:>9.1f} {r['theta_over_mean']:>8.5f} "
            f"{'yes' if r['all_classes_irreducible'] else 'NO':>6}"
        )

    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rows, fh, indent=1, default=str)
    print(f"\nchecks: {len(rows)} dumps, {bad} violations")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
