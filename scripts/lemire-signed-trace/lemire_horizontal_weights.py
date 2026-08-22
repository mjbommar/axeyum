#!/usr/bin/env python3
"""Horizontal (conductor-aspect) character sums for the Kaser--Lemire lane.

This is the computational half of
`docs/research/10-cas/lemire-signed-trace/12-horizontal-deligne-budget.md`.

Setting.  `q = 2^r`, `E_j = (1 + x F_q[x])/x^{j+1}` (order `q^j`),
`<F>_j = x^{deg F} F(1/x) mod x^{j+1}` for monic `F`, and

    N_j(1) = sum_{F monic, deg F = n, <F>_j = 1} Lambda(F)

the Mangoldt mass of the monic degree-`n` polynomials whose top `j`
non-leading coefficients vanish.  Orthogonality on `E_j` gives the *signed*
sum of `S_n(chi)` over the characters of exact conductor `j`, i.e. over the
`F_q`-points of Katz's `Prim_j`:

    A_r(n,j) := sum_{chi in Prim_j(F_q)} S_n(chi) = q^j N_j(1) - q^{j-1} N_{j-1}(1).

The means cancel, so `A_r` is pure fluctuation.  By Grothendieck--Lefschetz
`A_r(n,j) = -sum_i (-1)^i Tr(Frob_{2}^r | H^i_c(Prim_j (x) F_2bar, Xi_n L_univ))`,
so the growth of `|A_r|` in `r` at FIXED `(n,j)` measures the largest Frobenius
weight `w` present, hence a lower bound `i_max >= w - n` on the top
cohomological degree.  That is the discriminating quantity of note 12:
`w = n + j` is middle concentration, `w = n + j + 1` is one above middle,
`w = n + 2j - 1` is "top minus one" (the shape of Katz's own Thm. 8.2), and
`w = n + 2j` is no cancellation at all.

Engines (never sharing an implementation):

* `witt`   -- exact, `j = 2` only, all `n`, `r` up to ~16.  Uses the
  Artin--Hasse identification `E_2 = W_2(F_q)`, the explicit order-4 character
  `chi_c((a,0)) = i^{Tr(c_0 a) + 2(Tr(c_1 a^2) + e_2(c_0 a))}`, and a
  Walsh--Hadamard transform.  Produces the `L`-polynomial root `alpha` of every
  primitive character, exactly, in `Z[i]`.
Mutation controls (each must make the run exit nonzero, through a NAMED check):
`1` drops the Witt carry `e_2` (dies on the Weil norm `|alpha|^2 = q`);
`2` sums over `q` rather than `q-1` characters per `G_m`-orbit (dies on the
`(q-1) | A_r` divisibility and on witt-vs-flint);
`3` drops the proper prime powers (dies on `N_1(1) = q^{n-1}`);
`4` uses `q^j N_{j-1}` in place of `q^{j-1} N_{j-1}` (dies on `A_r(n,1) = 0`);
`5` shifts the window depth by one (dies on witt-vs-flint and on the `q = 2`
anchor).

* `flint`  -- independent: enumerates the window with `python-flint`'s
  `is_irreducible` and adds the proper prime powers by hand.
* `rust`   -- the lane's bulk engine, `axeyum-lemire-horizontal` in a snapshot of
  branch `agent/gf2/lemire-proof` (source mirrored as
  `axeyum-lemire-horizontal.rs.txt` beside this file).  Same algorithm as
  `flint`, 24-threaded, own `F_{2^r}` arithmetic.

Every assertion below is checked; a zero exit status means they all held.
Mutation controls: `--mutate <k>` breaks one hypothesis and the run MUST fail.
"""

from __future__ import annotations

import argparse
import math
import os
import re
import subprocess
import sys
from fractions import Fraction

import numpy as np

# ---------------------------------------------------------------- mutations --
# Set by --mutate; each value deliberately breaks one thing.  A control run is
# expected to EXIT NONZERO.
MUTATE = 0

# Irreducible (not necessarily primitive) polynomials over F_2, bit i = coeff of x^i.
MODULI = {
    1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011,
    7: 0b10000011, 8: 0b100011011, 9: 0b1000010001, 10: 0b10000001001,
    11: 0b100000000101, 12: 0b1000001010011, 13: 0b10000000011011,
    14: 0b100010001000011, 15: 0b1000000000000011, 16: 0b10001000000001011,
    17: 0b100000000000001001, 18: 0b1000000000000001001,
    19: 0b10000000000000100111, 20: 0b100000000000000001001,
}

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    if not cond:
        FAILURES.append(msg)
        print(f"FAIL: {msg}", file=sys.stderr)


# ------------------------------------------------------------- witt engine --
def witt_alphas(r: int):
    """Exact inverse roots `alpha(chi)` of `L(chi,T)` for every `chi` of exact
    conductor 2 over `F_{2^r}`, as Gaussian integers.

    `E_2 = W_2(F_q)` by `1 + u_1 x + u_2 x^2 <-> (u_1, u_2)` (checked: the
    truncated-polynomial product and the length-2 Witt sum agree identically).
    Characters are `chi_c(w) = i^{tr_W(c . w)}`, `tr_W` the Witt trace to
    `W_2(F_2) = Z/4`; `chi_c` has exact conductor 2 iff `c_0 != 0`.  With
    `L(chi,T) = 1 - alpha T` and `alpha = -sum_{b in F_q} chi(1 + b x)`, the
    substitution `u = c_0 b` shows `alpha` depends on `c` only through
    `d = c_1 / c_0^2`, so there are exactly `q` values, each taken `q-1` times:

        alpha_d = - sum_{u in F_q} i^{Tr(u)} (-1)^{Tr(d u^2) + e_2(u)},

    `e_2(u) = sum_{i<k} u^{2^i + 2^k}` the second elementary symmetric function
    of the Frobenius orbit (the Witt carry).  Returns `(re, im)` arrays indexed
    by an arbitrary bijective relabelling of `d` (only the multiset matters).
    """
    q = 1 << r
    m = MODULI[r]
    idx = np.arange(q, dtype=np.int64)

    def mul(a, b):
        res = np.zeros_like(a)
        x = a.copy()
        for k in range(r):
            res = res ^ np.where((b >> k) & 1 == 1, x, 0)
            x = x << 1
            x = np.where((x & q) != 0, x ^ m, x)
        return res

    def sqr(a):
        return mul(a, a)

    s = np.zeros(q, dtype=np.int64)
    c = np.zeros(q, dtype=np.int64)
    x = idx.copy()
    for _ in range(r):
        c = c ^ mul(x, s)
        s = s ^ x
        x = sqr(x)
    tr, e2 = s, c
    check(set(np.unique(tr).tolist()) <= {0, 1}, f"witt: trace not in F_2 (r={r})")
    check(set(np.unique(e2).tolist()) <= {0, 1}, f"witt: e_2 not in F_2 (r={r})")
    if MUTATE == 1:
        e2 = np.zeros_like(e2)          # drop the Witt carry
    re = np.where(tr == 0, 1, 0) * np.where(e2 == 0, 1, -1)
    im = np.where(tr == 1, 1, 0) * np.where(e2 == 0, 1, -1)
    root = idx.copy()
    for _ in range(r - 1):
        root = sqr(root)                 # root[v] = sqrt(v)
    gre, gim = re[root], im[root]

    def wht(a):
        a = a.copy().astype(np.int64)
        h = 1
        while h < q:
            a = a.reshape(-1, 2 * h)
            lo = a[:, :h].copy()
            hi = a[:, h:].copy()
            a[:, :h] = lo + hi
            a[:, h:] = lo - hi
            a = a.reshape(-1)
            h *= 2
        return a

    return -wht(gre), -wht(gim), q


def witt_A(r: int, nmax: int) -> dict[int, int]:
    """`A_r(n,2)` for `n = 1..nmax`, exactly."""
    ar, ai, q = witt_alphas(r)
    norms = ar * ar + ai * ai
    check(bool(np.all(norms == q)),
          f"witt: Weil |alpha|^2 = q fails at r={r} (saw {sorted(set(norms.tolist()))[:4]})")
    vals, mult = np.unique(np.stack([ar, ai], 1), axis=0, return_counts=True)
    check(len(vals) <= 4,
          f"witt: more than 4 Gaussian integers of norm 2^{r} at r={r}: {len(vals)}")
    out = {}
    for n in range(1, nmax + 1):
        tr_, ti_ = 0, 0
        for (a, b), mm in zip(vals.tolist(), mult.tolist()):
            zr, zi = 1, 0
            for _ in range(n):
                zr, zi = zr * a - zi * b, zr * b + zi * a
            tr_ += mm * zr
            ti_ += mm * zi
        check(ti_ == 0, f"witt: A_r({n},2) not real at r={r} (imag {ti_})")
        # each alpha value is shared by the q-1 characters in one G_m-orbit
        orbit = q if MUTATE == 2 else q - 1
        out[n] = -orbit * tr_
    return out


# ------------------------------------------------------------ flint engine --
def _flint():
    try:
        from flint import fq_default_ctx, fq_default_poly_ctx
    except ImportError:  # pragma: no cover - environment dependent
        return None
    return fq_default_ctx, fq_default_poly_ctx


def flint_N(n: int, r: int, jstart: int) -> dict[int, int]:
    """`N_j(1)` for `j >= jstart` by direct enumeration; independent of `witt`."""
    mods = _flint()
    check(mods is not None, "flint: python-flint not importable")
    if mods is None:
        return {}
    fq_default_ctx, fq_default_poly_ctx = mods
    ctx = fq_default_ctx(2, r)
    pctx = fq_default_poly_ctx(ctx)
    q = 1 << r
    g = ctx.gen()
    els = []
    for value in range(q):
        e = ctx(0)
        i, t = 0, value
        while t:
            if t & 1:
                e = e + g**i
            t >>= 1
            i += 1
        els.append(e)
    zero, one = ctx(0), ctx(1)
    nvals = {j: 0 for j in range(0, n + 1)}
    width = n - jstart
    for idx in range(q**width):
        coef = []
        t = idx
        for _ in range(width):
            coef.append(t % q)
            t //= q
        # coef[k] is the coefficient of x^{n-jstart-1-k}
        low = [zero] * n
        for k in range(width):
            low[n - jstart - 1 - k] = els[coef[k]]
        depth = 0
        while depth < n and low[n - 1 - depth] == zero:
            depth += 1
        if MUTATE == 5:
            depth += 1                    # off-by-one in the window depth
        f = pctx(low + [one])
        if f.is_irreducible():
            for j in range(jstart, min(depth, n) + 1):
                nvals[j] += n
    if MUTATE != 3:
        for d in range(1, n):
            if n % d:
                continue
            k = n // d
            for idx in range(q**d):
                coef = []
                t = idx
                for _ in range(d):
                    coef.append(t % q)
                    t //= q
                p = pctx([els[c] for c in coef] + [one])
                if not p.is_irreducible():
                    continue
                cf = list((p**k).coeffs())
                cf += [zero] * (n + 1 - len(cf))
                depth = 0
                while depth < n and cf[n - 1 - depth] == zero:
                    depth += 1
                for j in range(jstart, min(depth, n) + 1):
                    nvals[j] += d
    return {j: nvals[j] for j in range(jstart, n + 1)}


# ------------------------------------------------------------- rust engine --
def rust_run(binary: str, n: int, r: int, jstart: int, threads: int) -> dict[int, int]:
    out = subprocess.run([binary, str(n), str(r), str(jstart), str(threads)],
                         capture_output=True, text=True, check=True).stdout
    nvals = {}
    for line in out.splitlines():
        if line.startswith("N|"):
            _, j, v = line.split("|")
            nvals[int(j)] = int(v)
    return nvals


# ------------------------------------------------------------------ shared --
def A_from_N(nvals: dict[int, int], n: int, r: int, jstart: int) -> dict[int, int]:
    q = 1 << r
    lo = max(jstart, 1)
    out = {}
    for j in range(lo + 1, n + 1):
        if j not in nvals or j - 1 not in nvals:
            continue
        coef = q ** (j - 1) if MUTATE != 4 else q**j
        out[j] = q**j * nvals[j] - coef * nvals[j - 1]
    return out


def berlekamp_massey(seq: list[int]):
    """Minimal linear recurrence `a_k = sum_i c_i a_{k-i}` over `Q`, or `None`."""
    N = len(seq)
    for L in range(1, N // 2 + 1):
        rows = [[Fraction(seq[k - i]) for i in range(1, L + 1)] + [Fraction(seq[k])]
                for k in range(L, N)]
        if len(rows) < L:
            break
        mat = [row[:] for row in rows]
        piv, rr = [], 0
        for col in range(L):
            p = next((i for i in range(rr, len(mat)) if mat[i][col] != 0), None)
            if p is None:
                continue
            mat[rr], mat[p] = mat[p], mat[rr]
            f = mat[rr][col]
            mat[rr] = [v / f for v in mat[rr]]
            for i in range(len(mat)):
                if i != rr and mat[i][col] != 0:
                    gg = mat[i][col]
                    mat[i] = [a - gg * b for a, b in zip(mat[i], mat[rr])]
            piv.append(col)
            rr += 1
        sol = [Fraction(0)] * L
        for i, col in enumerate(piv):
            sol[col] = mat[i][L]
        if all(seq[k] == sum(sol[i - 1] * seq[k - i] for i in range(1, L + 1))
               for k in range(L, N)):
            return sol
    return None


def weights_from_recurrence(coeffs):
    poly = [1.0] + [-float(c) for c in coeffs]
    roots = np.roots(poly)
    roots = [z for z in roots if abs(z) > 1e-9]
    return sorted(2 * math.log(abs(z), 2) for z in roots), roots


def gamma_row(rows: dict[int, int], n: int) -> list[float | None]:
    out = []
    for r in sorted(rows):
        a = rows[r]
        out.append(None if a == 0 else math.log(abs(a), 1 << r) - n / 2)
    return out


# -------------------------------------------------------------- q=2 anchor --
def anchor_q2(path: str, nmax: int) -> None:
    """`I_n(1)` from our own `q = 2` computation against the lane's pinned table."""
    if not os.path.exists(path):
        check(False, f"anchor: missing data file {path}")
        return
    pinned = {}
    for line in open(path):
        m = re.match(r"n=\s*(\d+)\s+floor\(n/2\)=\s*(\d+)\s+I_n\(1\)=\s*(\d+)", line)
        if m:
            pinned[int(m.group(1))] = (int(m.group(2)), int(m.group(3)))
    check(len(pinned) > 20, f"anchor: parsed only {len(pinned)} rows from {path}")
    tested = 0
    for n in sorted(pinned):
        if n > nmax or n < 3:
            continue
        _gdeg, i_n = pinned[n]
        # the file's I_n(1) counts irreducible x^n + g with deg g <= floor(n/2),
        # i.e. the identity class of E_j for j = ceil(n/2) - 1 (the top of the
        # Lemire range), NOT for j = floor(n/2).
        j = (n + 1) // 2 - 1
        if j < 1:
            continue
        nvals = flint_N(n, 1, max(j - 1, 1))
        if j not in nvals:
            continue
        theta = proper_power_mass_q2(n, j)
        got = Fraction(nvals[j] - theta, n)
        check(got == i_n, f"anchor: I_{n}(1) computed {got} != pinned {i_n} (j={j})")
        tested += 1
    check(tested >= 8, f"anchor: only {tested} rows tested against {path}")
    print(f"[anchor] q=2: I_n(1) reproduced for {tested} degrees from {os.path.basename(path)}")


def proper_power_mass_q2(n: int, ell: int) -> int:
    """`Theta(1)` at `q = 2`: Mangoldt mass of the PROPER prime powers in the
    identity class of `E_ell` among monic degree-`n` polynomials."""
    mods = _flint()
    if mods is None:
        return 0
    fq_default_ctx, fq_default_poly_ctx = mods
    ctx = fq_default_ctx(2, 1)
    pctx = fq_default_poly_ctx(ctx)
    zero, one = ctx(0), ctx(1)
    total = 0
    for d in range(1, n):
        if n % d:
            continue
        k = n // d
        for idx in range(1 << d):
            p = pctx([one if (idx >> i) & 1 else zero for i in range(d)] + [one])
            if not p.is_irreducible():
                continue
            cf = list((p**k).coeffs())
            cf += [zero] * (n + 1 - len(cf))
            depth = 0
            while depth < n and cf[n - 1 - depth] == zero:
                depth += 1
            if depth >= ell:
                total += d
    return total


# ---------------------------------------------------------------- main run --
def main() -> int:
    global MUTATE
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rmax-witt", type=int, default=14)
    ap.add_argument("--nmax-witt", type=int, default=12)
    ap.add_argument("--anchor-nmax", type=int, default=28)
    ap.add_argument("--rust-binary", default=os.environ.get("AXEYUM_LEMIRE_HORIZONTAL", ""))
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--grid", default="",
                    help="extra Rust rows, 'n:r:jstart,n:r:jstart,...'")
    ap.add_argument("--grid-file", default="",
                    help="comma-separated list of Rust grid dumps produced earlier")
    ap.add_argument("--out", default="")
    ap.add_argument("--mutate", type=int, default=0)
    args = ap.parse_args()
    MUTATE = args.mutate
    check(args.nmax_witt >= 7, "harness: --nmax-witt must be at least 7")
    if FAILURES:
        return 2
    if MUTATE:
        print(f"[mutation control {MUTATE}] this run MUST fail")

    lines: list[str] = []

    def emit(text: str = "") -> None:
        print(text)
        lines.append(text)

    # --- engine `witt`: j = 2, exact, all n --------------------------------
    witt: dict[int, dict[int, int]] = {}
    for r in range(1, args.rmax_witt + 1):
        witt[r] = witt_A(r, args.nmax_witt)
    emit("== engine witt (exact, j = 2, E_2 = W_2(F_q), Walsh--Hadamard) ==")
    emit("   |A_r(n,2)| = C q^{n/2 + gamma};  gamma -> 3/2 means top weight n + 2j - 1")
    emit(f"{'n':>3}  " + "  ".join(f"r={r}" for r in range(1, min(4, args.rmax_witt) + 1))
         + "   gamma(r=" + ",".join(str(r) for r in range(4, args.rmax_witt + 1)) + ")")
    for n in range(1, args.nmax_witt + 1):
        head = "  ".join(f"{witt[r][n]}" for r in range(1, min(4, args.rmax_witt) + 1))
        tail = []
        for r in range(4, args.rmax_witt + 1):
            a = witt[r][n]
            tail.append("0" if a == 0 else f"{math.log(abs(a), 1 << r) - n / 2:.4f}")
        emit(f"{n:>3}  {head}   " + " ".join(tail))
    emit()

    # closed form check for j = 2
    for n in range(1, args.nmax_witt + 1):
        seq = [witt[r][n] for r in range(1, args.rmax_witt + 1)]
        if all(v == 0 for v in seq):
            check(n % 4 == 2, f"witt: A_r({n},2) vanishes but n % 4 != 2")
            continue
        coeffs = berlekamp_massey(seq)
        check(coeffs is not None and len(coeffs) == 2,
              f"witt: A_r({n},2) is not a 2-term Frobenius trace (order "
              f"{None if coeffs is None else len(coeffs)})")
        if coeffs is None or len(coeffs) != 2:
            continue
        ws, roots = weights_from_recurrence(coeffs)
        for w in ws:
            check(abs(w - round(w)) < 1e-6, f"witt: non-integral weight {w} at n={n}")
        want = n + 4 if n % 4 == 0 else n + 3
        check(abs(max(ws) - want) < 1e-6,
              f"witt: top weight {max(ws):.4f} != {want} at n={n} (j=2)")
        check(abs(min(ws) - (want - 2)) < 1e-6,
              f"witt: second weight {min(ws):.4f} != {want - 2} at n={n} (j=2)")

    # --- engine `flint`: independent, all j -------------------------------
    emit("== engine flint (independent window enumeration) ==")
    rows: dict[tuple[int, int], dict[int, int]] = {}
    for n in (5, 6, 7):
        for r in (1, 2, 3):
            nvals = flint_N(n, r, 1)
            check(nvals[1] == (1 << r) ** (n - 1),
                  f"control C1: N_1(1) = {nvals[1]} != q^(n-1) at n={n}, r={r}")
            avals = A_from_N(nvals, n, r, 1)
            a1 = (1 << r) * nvals[1] - ((1 << r) ** n)
            check(a1 == 0, f"control C1: A_r({n},1) = {a1} != 0 at r={r}")
            for j, v in avals.items():
                rows.setdefault((n, j), {})[r] = v
            if 2 in avals and n in witt[r]:
                check(avals[2] == witt[r][n],
                      f"control C3: flint A_{r}({n},2) = {avals[2]} != witt {witt[r][n]}")
    emit("   C1 (A_r(n,1) = 0 identically) and C3 (flint == witt at j = 2) hold")
    emit()
    # the exact witt engine supersedes the grid at j = 2 (it reaches r = 16)
    for n in range(2, args.nmax_witt + 1):
        rows[(n, 2)] = {r: witt[r][n] for r in sorted(witt)}

    # --- engine `rust`: bulk ----------------------------------------------
    grid: list[tuple[int, int, int]] = []
    if args.grid:
        for spec in args.grid.split(","):
            n, r, js = (int(v) for v in spec.split(":"))
            grid.append((n, r, js))
    if args.rust_binary and os.path.exists(args.rust_binary):
        emit("== engine rust (bulk; cross-checked against flint) ==")
        for n, r in ((5, 3), (7, 3), (7, 4), (9, 3)):
            rn = rust_run(args.rust_binary, n, r, 1, args.threads)
            fn = flint_N(n, r, 1) if (1 << r) ** (n - 1) <= 3_000_000 else None
            if fn:
                for j in sorted(set(rn) & set(fn)):
                    check(rn[j] == fn[j],
                          f"control C4: rust N_{j} = {rn[j]} != flint {fn[j]} at n={n}, r={r}")
            for j, v in A_from_N(rn, n, r, 1).items():
                rows.setdefault((n, j), {})[r] = v
        emit("   C4 (rust == flint) holds on the overlap")
        for n, r, js in grid:
            rn = rust_run(args.rust_binary, n, r, js, args.threads)
            for j, v in A_from_N(rn, n, r, js).items():
                rows.setdefault((n, j), {})[r] = v
        emit()
    elif grid:
        check(False, "grid requested but no --rust-binary; refusing to fall back silently")

    for gpath in [g for g in args.grid_file.split(",") if g]:
        cur = None
        for line in open(gpath):
            line = line.strip()
            m = re.match(r"### n=(\d+) r=(\d+) jstart=(\d+)", line)
            if m:
                cur = tuple(int(v) for v in m.groups())
            elif line.startswith("A|") and cur:
                _, j, v = line.split("|")
                rows.setdefault((cur[0], int(j)), {})[cur[1]] = int(v)

    # --- controls over every row -------------------------------------------
    for (n, j), byr in sorted(rows.items()):
        for r, v in byr.items():
            check(v % ((1 << r) - 1) == 0 if r > 1 else True,
                  f"control C5: (q-1) does not divide A_{r}({n},{j}) = {v}")

    # --- the weight table ---------------------------------------------------
    emit("== measured top weight w (|A_r| ~ C q^{(n+w)/2}), Lemire range j <= ceil(n/2)-1 ==")
    emit("   w_loc(r) = 2(log2|A_{r+1}| - log2|A_r|) - n;  RESOLVED means the")
    emit("   Berlekamp--Massey recurrence closes on the data with integral weights.")
    emit("   sav(q=2) = 2^{j-1}(j-1)2^{n/2}/|A_1| is the saving over the trivial")
    emit("   bound actually achieved at q = 2; (HWO) needs 4*ell = 4*(ceil(n/2)-1).")
    emit("   shape names w against the four candidates j, j+1, 2j-1, 2j;")
    emit("   only j and j+1 leave room for a Betti bound at large j (Prop. 1).")
    emit(f"{'n':>3} {'j':>3} {'R':>3} {'rng':>4} {'w_meas':>8} {'i_max>=':>8} "
         f"{'C':>4} {'shape':>7} {'sav(q=2)':>9} {'4ell':>5}  w_loc tail")
    for (n, j), byr in sorted(rows.items()):
        rs = sorted(byr)
        if rs != list(range(1, len(rs) + 1)) or j < 2:
            continue
        seq = [byr[r] for r in rs]
        inr = "yes" if j <= (n + 1) // 2 - 1 else "no"
        ell = (n + 1) // 2 - 1
        if all(v == 0 for v in seq):
            emit(f"{n:>3} {j:>3} {len(rs):>3} {inr:>4}   A == 0 identically "
                 f"(H^*_c vanishes; nothing to bound)")
            continue
        wloc = []
        for k in range(1, len(rs)):
            if seq[k] == 0 or seq[k - 1] == 0:
                wloc.append(None)
                continue
            wloc.append(2 * (math.log2(abs(seq[k])) - math.log2(abs(seq[k - 1]))) - n)
        coeffs = berlekamp_massey(seq)
        resolved, w_meas, csum = False, None, None
        if coeffs is not None and 2 * len(coeffs) <= len(seq):
            ws, _ = weights_from_recurrence(coeffs)
            if ws and all(abs(w - round(w)) < 1e-6 for w in ws):
                resolved, w_meas, csum = True, round(max(ws)) - n, len(coeffs)
        sav = (2 ** (j - 1)) * (j - 1) * 2 ** (n / 2) / abs(seq[0]) if seq[0] else float("inf")
        if resolved:
            names = {j: "j", j + 1: "j+1", 2 * j - 2: "2j-2", 2 * j - 1: "2j-1",
                     2 * j: "2j"}
            shape = names.get(w_meas, "other")
            emit(f"{n:>3} {j:>3} {len(rs):>3} {inr:>4} {w_meas:>8} {w_meas:>8} "
                 f"{csum:>4} {shape:>7} {sav:>9.2f} {4 * ell:>5}  "
                 + " ".join("  --  " if w is None else f"{w:6.2f}" for w in wloc[-3:]))
        else:
            emit(f"{n:>3} {j:>3} {len(rs):>3} {inr:>4} {'unres.':>8} {'-':>8} "
                 f"{'-':>4} {'-':>7} {sav:>9.2f} {4 * ell:>5}  "
                 + " ".join("  --  " if w is None else f"{w:6.2f}" for w in wloc[-3:]))
    emit()

    # --- q = 2 anchor -------------------------------------------------------
    here = os.path.dirname(os.path.abspath(__file__))
    anchor_q2(os.path.join(here, "data", "irreducible-counts-n2-38.txt"), args.anchor_nmax)

    if args.out:
        with open(args.out, "w") as fh:
            fh.write("\n".join(lines) + "\n")
        print(f"[wrote] {args.out}")

    if MUTATE:
        if FAILURES:
            print(f"mutation control {MUTATE}: died as required "
                  f"({len(FAILURES)} assertion(s))")
            return 1
        print(f"mutation control {MUTATE}: SURVIVED -- the suite is blind to it",
              file=sys.stderr)
        return 3
    if FAILURES:
        print(f"{len(FAILURES)} assertion(s) failed", file=sys.stderr)
        return 1
    print("all assertions held")
    return 0


if __name__ == "__main__":
    sys.exit(main())
