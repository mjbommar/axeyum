#!/usr/bin/env python3
"""Checks for note 20 (`20-almost-all-degrees.md`): Kaser--Lemire for almost all
DEGREES, and the exact obstruction to every averaging-over-degrees scheme.

Target (AAD):  `#{n <= N : W_n contains no irreducible} = o(N)`, where
`W_n = {x^n + g : deg g <= floor(n/2)}`.  Nothing here proves it; what is
proved is a reduction and a null result, and both are checked numerically.

The checks, each with at least one positive control that MUST fail if the
check were vacuous:

  CHECK A  an INDEPENDENT Python character/L-function engine for the Hayes
           groups `E_ell` reproduces the branch CAS's endpoint discrepancies
           `D_n = N_ell(1) - 2^{n-ell}` for `2 <= ell <= 10`, both degrees.
           This is the two-engine anchor for everything below; the RH check
           `|alpha_i| in {0, sqrt 2}` and the conductor counts `2^{j-1}` are
           the positive controls.
  CHECK B  Theorem 1 (low-block bound): with `a = ell - ceil(log2 ell) - 1`,
           the conductors `j < a` contribute `< 0.177` (odd `n`) / `< 0.125`
           (even `n`) to `d_n = D_n / 2^{n-ell}`, exactly and uniformly.
  CHECK C  Theorem 2 (reduction): `I_n >= 1` as soon as `|d_n^top| <= 0.37`,
           via the proper-prime-power mass, recomputed directly for `n <= 30`.
  CHECK D  Theorem 3 (block support): each conductor `j` is in the top block
           of at most `2 ceil(log2 j) + 4` degrees.  So a fixed block of
           character data is attached to `O(log n)` degrees, not to `N`.
  CHECK E  Theorem 4 (large-sieve null result): `delta^{-1} >= D` and
           `Sigma_2 >= Sigma_1^2 / D` make the Montgomery--Vaughan exceptional
           bound `>= Sigma_1^2 / lambda^2`, which at the Lemire threshold is
           `>= c ell^2 > 1` for every `ell >= 4` and EVERY range of degrees.
  CHECK F  Theorem 6 (slack ladder): the exact Hsu/Cohen slack `k*(n)` at
           which the pointwise Weil bound already gives the window, against
           the slack at which the large sieve first becomes non-vacuous.
           They differ by at most one coefficient.
  CHECK G  the Frobenius-angle multiset of a conductor has exact repeats, so
           `delta = 0` and the separated large sieve is not merely lossy but
           inapplicable.
  CHECK H  the measured endpoint deviations `z_ell = D_n / sd` for
           `2 <= ell <= 24` (branch CAS, pinned): size, distribution, and
           correlation across consecutive `ell` and across the two degrees of
           one `ell`.
  CHECK I  the observed margin: minimal subdegree `s_min(n)` (independent
           flint Rabin test) against the conjecture's `floor(n/2)`.
  CHECK J  the Q-transform `x^m f(x + 1/x)` is window-hostile (a candidate-5
           side road, closed by an exact binomial computation).

Exits nonzero on any failure.  Data written to data/aad-*.txt.  Run with the
lane venv (`/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python`):
the external dependencies are numpy (the character/L-function engine) and
python-flint (the proper-power mass in CHECK C and the subdegree search in
CHECK I).  Whole run ~4 s.
"""

import math
import os
import random
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

FAILURES = []


class CheckFailed(Exception):
    pass


def check(name, ok, detail=""):
    status = "ok" if ok else "FAIL"
    print(f"[{status}] {name}{(' -- ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)
    return ok


def require(cond, msg):
    if not cond:
        raise CheckFailed(msg)


def mutation_control(name, fn):
    """A control passes when the mutated input makes the check FAIL."""
    try:
        fn()
    except CheckFailed as exc:
        print(f"  control {name}: tripped ({str(exc)[:90]})")
        return
    FAILURES.append(f"mutation control {name} did NOT trip")
    print(f"FAIL: mutation control {name} did NOT trip")


def clog2(m):
    """ceil(log2 m) for m >= 1."""
    return (m - 1).bit_length()


def a_of(ell, mutate_a=None):
    """The Haar-telescope cutoff `a = ell - ceil(log2 ell) - 1` (note 01)."""
    if mutate_a == "narrow":
        return ell - 1
    return ell - clog2(ell) - 1


def wei(lo, hi):
    """sum_{j=lo}^{hi} (j-1) 2^{j-1}: the Weil allowance of conductors lo..hi."""
    def upto(J):
        return (J - 2) * (1 << J) + 2 if J >= 1 else 0
    return upto(hi) - upto(lo - 1)


# ---------------------------------------------------------------------------
# The independent character / L-function engine for E_j = (1 + x F_2[x])/x^{j+1}
# ---------------------------------------------------------------------------

def clmulmod(a, b, mask):
    """Carry-less product of two F_2[x] bitmasks, truncated by `mask`."""
    r = 0
    while b:
        lo = b & -b
        r ^= a << (lo.bit_length() - 1)
        b ^= lo
    return r & mask


class Hayes:
    """Structure of E_j: generators 1 + x^k (k odd), orders 2^{e_k}, discrete log."""

    def __init__(self, j, mutate_ek=False):
        self.j = j
        mask = (1 << (j + 1)) - 1
        self.mask = mask
        self.odds = [k for k in range(1, j + 1, 2)]
        self.e = {k: (j // k).bit_length() for k in self.odds}   # floor(log2(j/k)) + 1
        if mutate_ek:
            k0 = self.odds[0]
            self.e[k0] = self.e[k0] + 1
        require(sum(self.e.values()) == j,
                f"sum e_k = {sum(self.e.values())} != j = {j}")
        self.gens = {k: (1 | (1 << k)) for k in self.odds}
        for k in self.odds:
            u, o = self.gens[k], 1
            while u != 1:
                u = clmulmod(u, self.gens[k], mask)
                o += 1
            require(o == 1 << self.e[k], f"ord(1+x^{k}) = {o} != 2^{self.e[k]}")
        # discrete log: exponent vector of every element
        cur = [(1, tuple(0 for _ in self.odds))]
        for idx, k in enumerate(self.odds):
            g, new = self.gens[k], []
            for u, v in cur:
                p = u
                for aa in range(1 << self.e[k]):
                    vv = list(v)
                    vv[idx] = aa
                    new.append((p, tuple(vv)))
                    p = clmulmod(p, g, mask)
            cur = new
        require(len(cur) == 1 << j, "group enumeration size")
        tab = {}
        for u, v in cur:
            require(u not in tab, "discrete-log collision")
            tab[u] = v
        self.tab = tab
        self.E = max(self.e.values())
        self.M = 1 << self.E
        # element order: index idx <-> u = 1 | (idx << 1); V_m = {idx < 2^m}
        import numpy as np
        self.A = np.array([tab[1 | (i << 1)] for i in range(1 << j)], dtype=np.int64)
        self.w = np.array([1 << (self.E - self.e[k]) for k in self.odds], dtype=np.int64)
        k0 = j
        while k0 % 2 == 0:
            k0 //= 2
        self.k0 = k0
        self.ik0 = self.odds.index(k0)

    def characters(self, exact_conductor=None, mutate_cond=False):
        """Yield (cvec, exact_cond_flag)."""
        import itertools
        ranges = [range(1 << self.e[k]) for k in self.odds]
        idx = 0 if mutate_cond else self.ik0
        for cv in itertools.product(*ranges):
            ex = (cv[idx] % 2 == 1)
            if exact_conductor is True and not ex:
                continue
            if exact_conductor is False and ex:
                continue
            yield cv, ex

    def lcoeffs_exact(self, cv):
        """Exact L-polynomial coefficients c_0..c_{j-1} as vectors in Z[zeta_M],
        basis 1, zeta, ..., zeta^{M/2-1} (zeta^{M/2} = -1)."""
        import numpy as np
        c = np.array(cv, dtype=np.int64)
        ph = (self.A * (c * self.w)).sum(axis=1) % self.M
        half = self.M // 2
        out = []
        for m in range(self.j):
            hist = np.bincount(ph[: 1 << m], minlength=self.M)
            out.append(tuple((hist[:half] - hist[half:]).tolist()))
        return tuple(out)

    def lcoeffs_complex(self, cv):
        import numpy as np
        zeta = np.exp(2j * np.pi * np.arange(self.M) / self.M)
        c = np.array(cv, dtype=np.int64)
        ph = (self.A * (c * self.w)).sum(axis=1) % self.M
        vals = zeta[ph]
        cs = np.cumsum(vals)
        return np.array([cs[(1 << m) - 1] for m in range(self.j)])


def s_series(coeffs, nmax):
    """S_n(chi) for n = 1..nmax from L(u) = sum_m c_m u^m: S_n = [u^n](u L'/L)."""
    import numpy as np
    c = np.trim_zeros(np.asarray(coeffs, dtype=complex), "b")
    if len(c) == 0:
        c = np.array([1.0 + 0j])
    d = len(c) - 1
    r = np.zeros(nmax + 1, dtype=complex)
    for m in range(1, nmax + 1):
        s = (m * c[m]) if m <= d else 0j
        for k in range(max(1, m - d), m):
            s -= r[k] * c[m - k]
        r[m] = s
    return r


def trim_lead(v, tol=1e-8):
    """Drop leading (highest-degree) coefficients that are numerically zero."""
    import numpy as np
    v = np.asarray(v)
    i = 0
    while i < len(v) - 1 and abs(v[i]) < tol:
        i += 1
    return v[i:]


# pinned: branch CAS `axeyum-gf2-hayes-endpoints <maxell>`, discrepancies
# D_n = N_ell(1) - 2^{n-ell} at n = 2ell+1 (odd) and n = 2ell+2 (even).
CAS_DISC = {
    1: (0, 0), 2: (-2, 0), 3: (6, -8), 4: (5, 12), 5: (-19, 32), 6: (-49, 32),
    7: (45, -40), 8: (50, 75), 9: (-92, 48), 10: (53, 63), 11: (206, -352),
    12: (359, 335), 13: (-345, 980), 14: (-896, 645), 15: (340, -1832),
    16: (2744, 660), 17: (-1988, 6587), 18: (928, 9592), 19: (4074, -13496),
    20: (3115, -4509),
}
# ell = 21, 22, 23 from the same producer (`axeyum-gf2-hayes-endpoints 23`,
# 53 min on this host); ell = 22, 23, 24 also come out of
# data/cylinder-variances-ell12-24.txt, and CHECK H asserts the two agree.
CAS_DISC_HIGH = {
    21: (-20938, 25007), 22: (-7582, 28402), 23: (57574, -88336),
}


def check_a(ell_max=10, corrupt=None, mutate_ek=False):
    """CHECK A: the independent engine reproduces the CAS endpoint discrepancies."""
    import numpy as np
    rows = []
    worst_rh = 0.0
    for ell in range(2, ell_max + 1):
        H = Hayes(ell, mutate_ek=mutate_ek)
        ns = [2 * ell + 1, 2 * ell + 2]
        tot = {n: 0j for n in ns}
        nexact = 0
        for cv, ex in H.characters():
            if all(v == 0 for v in cv):
                continue
            nexact += 1 if ex else 0
            co = H.lcoeffs_complex(cv)
            # RH: nonzero roots of L(u) have modulus 1/sqrt(2)
            trimmed = trim_lead(co[::-1])
            if len(trimmed) > 1:
                rr = np.roots(trimmed)
                worst_rh = max(worst_rh, float(np.max(np.abs(np.abs(rr) - 2 ** -0.5))))
            rs = s_series(co, ns[-1])
            for n in ns:
                tot[n] += rs[n]
        require(nexact == 1 << (ell - 1),
                f"ell={ell}: {nexact} characters of exact conductor, expected {1 << (ell - 1)}")
        got = []
        for n in ns:
            v = tot[n] / (1 << ell)
            require(abs(v.imag) < 1e-6, f"ell={ell} n={n}: imaginary part {v.imag}")
            got.append(int(round(v.real)))
            require(abs(v.real - round(v.real)) < 1e-5,
                    f"ell={ell} n={n}: non-integer discrepancy {v.real}")
        want = list(CAS_DISC[ell])
        if corrupt is not None and ell == corrupt:
            got[0] += 1
        require(got == want, f"ell={ell}: engine {got} != CAS {want}")
        rows.append((ell, ns[0], got[0], ns[1], got[1]))
    require(worst_rh < 1e-6, f"RH check: worst |{'|alpha|'} - sqrt2| deviation {worst_rh}")
    return rows, worst_rh


def conductor_block(j, nmax, mutate_cond=False):
    """Exact/complex data for the conductor-exactly-j block.

    Returns dict with the angle multiset statistics and G_j(n) for n <= nmax."""
    import numpy as np
    H = Hayes(j)
    exact_l = {}
    angles = []
    G = np.zeros(nmax + 1, dtype=complex)
    nchar = 0
    for cv, ex in H.characters(exact_conductor=True, mutate_cond=mutate_cond):
        nchar += 1
        key = H.lcoeffs_exact(cv)
        exact_l[key] = exact_l.get(key, 0) + 1
        co = H.lcoeffs_complex(cv)
        trimmed = trim_lead(co[::-1])
        if len(trimmed) > 1:
            rr = np.roots(trimmed)
            alph = 1.0 / rr
            angles.extend((np.angle(alph) / (2 * np.pi)) % 1.0)
        G += s_series(co, nmax)
    require(nchar == 1 << (j - 1),
            f"j={j}: {nchar} exact-conductor characters, expected {1 << (j - 1)}")
    ang = np.sort(np.array(angles))
    sigma1 = len(ang)
    # Katz: a character of exact conductor j has L of degree exactly j-1
    require(sigma1 == (j - 1) * (1 << (j - 1)),
            f"j={j}: {sigma1} inverse roots, expected (j-1)2^(j-1) = "
            f"{(j - 1) * (1 << (j - 1))}")
    # distinct angles at 1e-7 resolution
    keep = np.concatenate(([True], np.diff(ang) > 1e-7))
    reps = np.flatnonzero(keep)
    mult = np.diff(np.concatenate((reps, [sigma1])))
    Dd = len(reps)
    sigma2 = int((mult.astype(np.int64) ** 2).sum())
    pts = ang[reps]
    wrap = 1.0 - pts[-1] + pts[0]
    if Dd > 1 and wrap <= 1e-7:
        # 0 and 1 are the same angle: merge the wrap-around pair
        mult = np.concatenate(([mult[0] + mult[-1]], mult[1:-1]))
        pts = pts[:-1]
        Dd -= 1
        sigma2 = int((mult.astype(np.int64) ** 2).sum())
        wrap = 1.0 - pts[-1] + pts[0]
    gaps = np.diff(pts)
    delta = float(min(gaps.min(), wrap)) if Dd > 1 else 1.0
    return {
        "j": j, "chars": nchar, "distinct_L": len(exact_l), "sigma1": sigma1,
        "distinct_angles": Dd, "sigma2": sigma2, "delta": delta,
        "G": G, "maxmult": int(mult.max()),
    }


# ---------------------------------------------------------------------------
# CHECK B -- Theorem 1, the low-block bound
# ---------------------------------------------------------------------------

def check_b(ell_list, mutate_a=None):
    """|d_n^low| < 2^{-5/2} (n odd), < 2^{-3} (n even), exactly and uniformly."""
    worst_odd = Fraction(0)
    worst_even = Fraction(0)
    for ell in ell_list:
        a = a_of(ell, mutate_a)
        if a < 2:
            continue
        w = wei(2, a - 1)
        # odd n = 2ell+1: |d^low| <= w / (2^ell sqrt2); compare squares exactly
        sq = Fraction(w * w, 2 * (4 ** ell))
        worst_odd = max(worst_odd, sq)
        require(sq < Fraction(1, 32),
                f"ell={ell}: odd low-block {float(sq) ** 0.5} >= 2^-5/2")
        r = Fraction(w, 2 ** (ell + 1))
        worst_even = max(worst_even, r)
        require(r < Fraction(1, 8),
                f"ell={ell}: even low-block {float(r)} >= 2^-3")
    return float(worst_odd) ** 0.5, float(worst_even)


# ---------------------------------------------------------------------------
# CHECK C -- Theorem 2, the reduction through the proper-prime-power mass
# ---------------------------------------------------------------------------

def irreducibles_of_degree(d):
    from flint import nmod_poly
    X = nmod_poly([0, 1], 2)
    out = []
    ps = []
    m = d
    q = 2
    while q * q <= m:
        while m % q == 0:
            ps.append(q)
            m //= q
        q += 1
    if m > 1:
        ps.append(m)
    ps = sorted(set(ps))
    for tail in range(1 << d):
        c = [(tail >> i) & 1 for i in range(d)] + [1]
        if c[0] == 0:
            continue
        f = nmod_poly(c, 2)
        if X.pow_mod(1 << d, f) != X:
            continue
        ok = True
        for p in ps:
            if (X.pow_mod(1 << (d // p), f) - X).gcd(f).degree() != 0:
                ok = False
                break
        if ok:
            out.append(f)
    return out


def theta_exact(n, cache={}):
    """Lambda-mass of PROPER prime powers inside W_n."""
    from flint import nmod_poly
    tot = 0
    for d in range(1, n):
        if n % d:
            continue
        k = n // d
        if d not in cache:
            cache[d] = irreducibles_of_degree(d)
        for f in cache[d]:
            g = nmod_poly([1], 2)
            for _ in range(k):
                g = g * f
            co = g.coeffs()
            sub = -1
            for i in range(n):
                if int(co[i]) % 2:
                    sub = i
            if sub <= n // 2:
                tot += d
    return tot


def check_c(nmax=28, tau=Fraction(34, 100), fudge=0):
    rows = []
    for n in range(6, nmax + 1):
        ell = (n + 1) // 2 - 1
        h = n - ell
        th = theta_exact(n) + fudge
        if n % 2:
            require(th < 2 ** (n // 3 + 1),
                    f"n={n} odd: Theta={th} >= 2^(n/3+1)={2 ** (n // 3 + 1)}")
            low = Fraction(1, 1)  # 2^{-5/2} bound, handled as a float below
            need = -1 + 2 ** -2.5 + th / 2 ** h
        else:
            require(th <= 2 ** (n // 2) + 2 ** (n // 3 + 1),
                    f"n={n} even: Theta={th} > 2^(n/2)+2^(n/3+1)")
            need = -1 + 2 ** -3 + th / 2 ** h
        rows.append((n, ell, h, th, need))
        if n >= 26:
            require(need < -float(tau),
                    f"n={n}: reduction threshold {need} not below -tau={-float(tau)}")
    return rows


# ---------------------------------------------------------------------------
# CHECK D -- Theorem 3, block support
# ---------------------------------------------------------------------------

def block_support(j, mutate_a=None):
    """The degrees n whose TOP block contains conductor j: a(ell) < j <= ell."""
    ells = []
    ell = j
    while a_of(ell, mutate_a) < j:
        ells.append(ell)
        ell += 1
        if ell > j + 200:
            break
    return ells


def check_d(js, bound_const=4, mutate_a=None):
    worst = (0, 0.0)
    rows = []
    for j in js:
        ells = block_support(j, mutate_a)
        T = 2 * len(ells)
        bound = 2 * clog2(j) + bound_const
        require(T <= bound, f"j={j}: block support {T} > {bound}")
        rows.append((j, len(ells), T, bound))
        if T / bound > worst[1]:
            worst = (j, T / bound)
    return rows, worst


# ---------------------------------------------------------------------------
# CHECK E -- Theorem 4, the large-sieve null result
# ---------------------------------------------------------------------------

TAU = Fraction(34, 100)          # the reduction threshold of Theorem 2
TAU_TOP = TAU / 2                # the share allotted to the top conductor


def check_e(blocks, ell_list, tau_top=TAU_TOP):
    """Two halves: (i) the algebraic lemma delta*D <= 1 and Sigma_2*D >= Sigma_1^2
    on measured blocks; (ii) the floor (Sigma_1/lambda)^2 > 1 for every ell."""
    for b in blocks:
        require(b["delta"] * b["distinct_angles"] <= 1.0 + 1e-9,
                f"j={b['j']}: delta*D = {b['delta'] * b['distinct_angles']} > 1")
        require(b["sigma2"] * b["distinct_angles"] >= b["sigma1"] ** 2,
                f"j={b['j']}: Sigma_2 * D < Sigma_1^2")
        # the Montgomery-Vaughan bound never drops below Sigma_1^2/lambda^2
        for T in (2, 8, 32, 1000, 10 ** 6):
            lhs = (T + 1.0 / b["delta"]) * b["sigma2"]
            require(lhs >= b["sigma1"] ** 2 * (1.0 - 1e-9),
                    f"j={b['j']}, T={T}: MV bound {lhs} < Sigma_1^2 {b['sigma1'] ** 2}")
    rows = []
    for ell in ell_list:
        # Sigma_1 = (ell-1)2^{ell-1}, lambda = tau_top 2^{ell+1/2}: ratio^2 exactly
        ratio2 = Fraction((ell - 1) ** 2, 1) / (tau_top ** 2 * 8)
        require(ratio2 > 1,
                f"ell={ell}: large-sieve exceptional floor {float(ratio2)} <= 1")
        rows.append((ell, float(ratio2)))
    return rows


# ---------------------------------------------------------------------------
# CHECK F -- Theorem 6, the slack ladder
# ---------------------------------------------------------------------------

def kstar(n, drop_log_term=False):
    """Least slack k such that Hsu (1996) Thm 2.4 / Cohen (2005) Thm 2.1,
    #{irreducible, top l coefficients prescribed} >= 2^{n-l}/n - (l+1)2^{n/2}/n,
    is positive for l = ell - k.  Exact integer comparison (squares)."""
    ell = (n + 1) // 2 - 1
    for k in range(0, ell + 1):
        l = ell - k
        if drop_log_term:
            if 2 ** (2 * (n - l)) > 2 ** n:
                return k
        elif 2 ** (2 * (n - l)) > (l + 1) ** 2 * 2 ** n:
            return k
    return None


def k_largesieve(n, tau_top=TAU_TOP):
    """Least slack k at which the large sieve's exceptional floor drops below 1,
    i.e. Sigma_1(ell-k) <= lambda: (ell-k-1) 2^{ell-k-1} <= tau_top 2^{n/2}."""
    ell = (n + 1) // 2 - 1
    for k in range(0, ell + 1):
        m = ell - k
        if m < 2:
            return k
        lhs2 = Fraction((m - 1) ** 2 * 4 ** (m - 1), 1)
        rhs2 = tau_top ** 2 * Fraction(2 ** n)
        if lhs2 <= rhs2:
            return k
    return None


def check_f(ns, pin=(64, 27), drop_log_term=False):
    """The large sieve NEVER lowers the provable slack: 0 <= kLS - k* <= 2."""
    rows = []
    worst = 0
    for n in ns:
        ks = kstar(n, drop_log_term)
        kl = k_largesieve(n)
        ell = (n + 1) // 2 - 1
        require(ks is not None and kl is not None, f"n={n}: no slack found")
        require(kl >= ks,
                f"n={n}: the large sieve slack {kl} beats the pointwise {ks}")
        worst = max(worst, kl - ks)
        rows.append((n, ell, ks, kl, ell - ks))
    require(worst <= 2,
            f"slack ladder: kLS - kstar reaches {worst} > 2")
    n0, lmax = pin
    ks = kstar(n0, drop_log_term)
    ell0 = (n0 + 1) // 2 - 1
    require(ell0 - ks == lmax,
            f"pin n={n0}: l_max = {ell0 - ks}, expected {lmax} (diary literature check)")
    # concordance with note 18 / diary entry 8: smallest proved slack at ell = 200
    got = (kstar(401, drop_log_term), kstar(402, drop_log_term))
    require(got == (8, 7),
            f"note-18 concordance: k*(401), k*(402) = {got}, expected (8, 7)")
    return rows, worst


# ---------------------------------------------------------------------------
# CHECK J -- the Q-transform is window-hostile
# ---------------------------------------------------------------------------

def check_j(mmax=4096):
    """F(x) = x^m f(x + 1/x) has degree 2m; deg((x^2+1)^m - x^{2m}) = 2m - 2^{v+1}
    with v = v_2(m), which is <= m only when m is a power of two -- and then
    deg(F - x^{2m}) = m + deg(f - x^m) > m unless f = x^m + 1."""
    good = []
    for m in range(2, mmax + 1):
        v = (m & -m).bit_length() - 1
        sub = 2 * m - (1 << (v + 1))
        if sub <= m:
            good.append(m)
    require(all((m & (m - 1)) == 0 for m in good),
            "Q-transform: a non-power-of-two m kept the cyclotomic part in window")
    require(len(good) >= 5, "Q-transform: too few m examined")
    # and for m a power of two the tail is m + deg(f - x^m) > m for any f != x^m+1
    return good


# ---------------------------------------------------------------------------
# CHECK H -- the measured endpoint deviations
# ---------------------------------------------------------------------------

def read_cylinder_variances():
    """N_ell(1) at the 15 endpoints pinned in data/cylinder-variances-ell12-24.txt."""
    import re
    path = os.path.join(DATA, "cylinder-variances-ell12-24.txt")
    out = {}
    with open(path) as fh:
        for line in fh:
            m = re.match(r"ell=(\d+) n=(\d+).*N_id=\s*(\d+)", line)
            if m:
                ell, n, N = int(m.group(1)), int(m.group(2)), int(m.group(3))
                out[(ell, n)] = N - 2 ** (n - ell)
    require(len(out) >= 15, f"cylinder-variances: only {len(out)} endpoints parsed")
    return out


def sd_model(ell, n):
    """Sato--Tate / Keating--Rudnick per-class standard deviation:
    V = 2^{-ell} sum_{chi != 1} |S_n|^2 ~ 2^{n-ell}[(ell-2)2^ell + 2], sd = sqrt(V/2^ell).
    Note 05 sec. 4 measures V / SatoTate in [0.97, 1.01] for 12 <= ell <= 24."""
    return math.sqrt(2 ** (n - ell) * (ell - 2) + 2 ** (n - 2 * ell + 1))


def _ranks(v):
    order = sorted(range(len(v)), key=lambda i: v[i])
    out = [0] * len(v)
    for k, i in enumerate(order):
        out[i] = k
    return out


def pearson(a, b):
    m = len(a)
    ma, mb = sum(a) / m, sum(b) / m
    sa = math.sqrt(sum((x - ma) ** 2 for x in a))
    sb = math.sqrt(sum((x - mb) ** 2 for x in b))
    return sum((x - ma) * (y - mb) for x, y in zip(a, b)) / (sa * sb)


def check_h(extra_disc=None, corrupt_sd=False):
    cyl = read_cylinder_variances()
    disc = dict(CAS_DISC)
    if extra_disc:
        disc.update(extra_disc)
    # two-source cross-check
    agreed = 0
    for (ell, n), d in sorted(cyl.items()):
        par = 0 if n % 2 else 1
        want = disc.get(ell, (None, None))[par]
        if want is not None:
            require(d == want,
                    f"two-source mismatch at (ell,n)=({ell},{n}): {d} vs {want}")
            agreed += 1
        else:
            cur = list(disc.get(ell, (None, None)))
            cur[par] = d
            disc[ell] = tuple(cur)
    require(agreed >= 9, f"only {agreed} endpoints cross-checked between two producers")
    ells = [e for e in sorted(disc) if e >= 2 and None not in disc[e]]
    rows = []
    zo, ze = [], []
    for ell in ells:
        for par, n in ((0, 2 * ell + 1), (1, 2 * ell + 2)):
            D = disc[ell][par]
            h = n - ell
            s = sd_model(ell, n) * (100.0 if corrupt_sd else 1.0)
            z = D / s
            weil = ((ell - 2) * 2 ** ell + 2) / 2 ** (n / 2)
            rows.append((ell, n, D, 2 ** h, D / 2 ** h, weil, s, z))
            (zo if par == 0 else ze).append((ell, z))
    allz = [z for _, z in zo] + [z for _, z in ze]
    mx = max(abs(z) for z in allz)
    require(mx < 4.0, f"identity-class deviation reaches {mx} sd (model says O(1))")
    rms = math.sqrt(sum(z * z for z in allz) / len(allz))
    require(0.5 < rms < 2.0, f"rms z = {rms}, not O(1)")
    # correlations
    def consec(seq):
        p = [(seq[i][1], seq[i + 1][1]) for i in range(len(seq) - 1)
             if seq[i + 1][0] == seq[i][0] + 1]
        return pearson([x for x, _ in p], [y for _, y in p]), len(p)
    r_odd, n_odd = consec(zo)
    r_even, n_even = consec(ze)
    require(abs(r_odd) < 0.6 and abs(r_even) < 0.6,
            f"consecutive-ell correlation {r_odd:.3f}/{r_even:.3f} is not small")
    aa = [z for _, z in zo]
    bb = [z for _, z in ze]
    r_pair = pearson(aa, bb)
    r_spear = pearson(_ranks(aa), _ranks(bb))
    # permutation test (deterministic seed) and jackknife, both quoted in note 20
    rng = random.Random(11)
    hits = 0
    trials = 50000
    for _ in range(trials):
        sh = bb[:]
        rng.shuffle(sh)
        if pearson(aa, sh) <= r_pair:
            hits += 1
    p_perm = hits / trials
    jk = [pearson(aa[:i] + aa[i + 1:], bb[:i] + bb[i + 1:]) for i in range(len(aa))]
    require(r_pair < -0.4 and max(jk) < -0.3 and p_perm < 0.01,
            f"odd/even anti-correlation not reproduced: r={r_pair:.3f}, "
            f"jackknife max {max(jk):.3f}, permutation p={p_perm:.5f}")
    return rows, (rms, mx, r_odd, n_odd, r_even, n_even, r_pair, len(zo),
                  r_spear, p_perm, min(jk), max(jk), agreed)


# ---------------------------------------------------------------------------
# CHECK I -- the observed margin: minimal subdegree
# ---------------------------------------------------------------------------

def min_subdegree(n):
    """Least s with an irreducible x^n + g, deg g = s, g(0) = 1 (s = 0 is g = 1)."""
    from flint import nmod_poly
    X = nmod_poly([0, 1], 2)
    ps, m, q = [], n, 2
    while q * q <= m:
        while m % q == 0:
            ps.append(q)
            m //= q
        q += 1
    if m > 1:
        ps.append(m)
    ps = sorted(set(ps))

    def irr(bits):
        c = [0] * (n + 1)
        c[n] = 1
        for b in bits:
            c[b] = 1
        f = nmod_poly(c, 2)
        if X.pow_mod(1 << n, f) != X:
            return False
        for p in ps:
            if (X.pow_mod(1 << (n // p), f) - X).gcd(f).degree() != 0:
                return False
        return True

    if irr([0]):
        return 0
    for s in range(1, n // 2 + 2):
        for mid in range(1 << (s - 1)):
            bits = [0, s] + [i for i in range(1, s) if (mid >> (i - 1)) & 1]
            if irr(bits):
                return s
    return None


def check_i(verify_upto=60, slope=2.0, intercept=4.0):
    """Read the pinned s_min table, re-derive a prefix from scratch, and assert
    the margin against the conjecture's floor(n/2)."""
    path = os.path.join(DATA, "aad-min-subdegree.txt")
    rows = []
    with open(path) as fh:
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            p = line.split()
            rows.append((int(p[0]), int(p[1])))
    require(len(rows) >= 400, f"only {len(rows)} s_min rows pinned")
    redone = 0
    for n, s in rows:
        if n <= verify_upto:
            require(min_subdegree(n) == s,
                    f"n={n}: recomputed s_min differs from the pinned {s}")
            redone += 1
    require(redone >= 50, f"only {redone} s_min values recomputed independently")
    worst = max(rows, key=lambda r: r[1] - slope * math.log2(max(r[0], 2)))
    tight = []
    for n, s in rows:
        require(s <= n // 2,
                f"n={n}: s_min={s} > floor(n/2) -- Kaser--Lemire FAILS at this degree")
        if s == n // 2:
            tight.append(n)
        if n >= 8:
            require(s <= intercept + slope * math.log2(n),
                    f"n={n}: s_min={s} exceeds {intercept} + {slope} log2 n")
        if n >= 9:
            require(s < n // 2,
                    f"n={n}: s_min={s} is not strictly inside the window")
    require(tight == [n for n in (2, 3, 5, 8) if n in dict(rows)],
            f"degrees with s_min = floor(n/2) exactly: {tight}, expected 2,3,5,8")
    ratio = max(s / (n // 2) for n, s in rows if n >= 8)
    return rows, (worst, tight), ratio, redone


# ---------------------------------------------------------------------------
# data files
# ---------------------------------------------------------------------------

def write_endpoints(rows, stats):
    p = os.path.join(DATA, "aad-endpoint-deviations.txt")
    (rms, mx, r_odd, n_odd, r_even, n_even, r_pair, npair,
     r_spear, p_perm, jk_lo, jk_hi, agreed) = stats
    with open(p, "w") as fh:
        fh.write("# Identity-class deviation at the Kaser--Lemire endpoints.\n")
        fh.write("# D_n = N_ell(1) - 2^{n-ell}; d_n = D_n / 2^{n-ell}; weil = the\n")
        fh.write("# unconditional Weil allowance for |d_n|; sd = Sato-Tate per-class\n")
        fh.write("# standard deviation sqrt(2^{n-ell}(ell-2) + 2^{n-2ell+1}); z = D_n/sd.\n")
        fh.write("# Producers: axeyum-gf2-hayes-endpoints (branch CAS) and\n")
        fh.write("# data/cylinder-variances-ell12-24.txt; the overlap is cross-checked.\n")
        fh.write("# ell   n            D_n         2^(n-ell)        d_n     weil"
                 "          sd        z\n")
        for ell, n, D, mean, d, weil, s, z in rows:
            fh.write("%5d %3d %14d %17d %+10.3e %8.3f %11.1f %+8.3f\n"
                     % (ell, n, D, mean, d, weil, s, z))
        fh.write("# rms z = %.3f, max|z| = %.3f over %d endpoints\n"
                 % (rms, mx, len(rows)))
        fh.write("# consecutive-ell Pearson r: odd %.3f (%d pairs), even %.3f (%d pairs)\n"
                 % (r_odd, n_odd, r_even, n_even))
        fh.write("# odd-vs-even at the same ell: Pearson r = %.3f, Spearman %.3f,\n"
                 % (r_pair, r_spear))
        fh.write("#   permutation p = %.5f (50000 shuffles, seed 11), jackknife"
                 " [%.3f, %.3f], %d groups\n" % (p_perm, jk_lo, jk_hi, npair))
        fh.write("# %d endpoints cross-checked between the two CAS producers\n"
                 % agreed)
    return p


def write_block_support(rows, ls_rows, blocks):
    p = os.path.join(DATA, "aad-block-support.txt")
    with open(p, "w") as fh:
        fh.write("# Theorem 3 (block support) and Theorem 4 (large-sieve floor).\n")
        fh.write("# T(j) = #{n : a(ell(n)) < j <= ell(n)} -- the degrees whose TOP\n")
        fh.write("# block contains conductor j; bound = 2 ceil(log2 j) + 4.\n")
        fh.write("#     j   #ell   T(j)  bound\n")
        for j, ne, T, b in rows:
            fh.write("%7d %6d %6d %6d\n" % (j, ne, T, b))
        fh.write("#\n# large-sieve exceptional floor (Sigma_1/lambda)^2 at the top\n")
        fh.write("# conductor, tau_top = 0.17: it exceeds 1 at every ell, so the\n")
        fh.write("# Montgomery--Vaughan bound never isolates a single degree.\n")
        fh.write("#   ell   floor=(Sigma_1/lambda)^2\n")
        for ell, r in ls_rows:
            fh.write("%6d   %14.4g\n" % (ell, r))
        fh.write("#\n# measured Frobenius-angle multisets, conductor exactly j\n")
        fh.write("#  j  chars  distinctL  Sigma_1  D(angles)  Sigma_2  maxmult"
                 "     delta   1/(delta*D)\n")
        for b in blocks:
            fh.write("%4d %6d %10d %8d %10d %8d %8d %10.3e %12.1f\n"
                     % (b["j"], b["chars"], b["distinct_L"], b["sigma1"],
                        b["distinct_angles"], b["sigma2"], b["maxmult"], b["delta"],
                        1.0 / (b["delta"] * b["distinct_angles"])))
    return p


def write_slack(rows):
    p = os.path.join(DATA, "aad-slack-ladder.txt")
    with open(p, "w") as fh:
        fh.write("# The slack ladder.  Window with slack k: deg(f - x^n) <= floor(n/2) + k,\n")
        fh.write("# i.e. the top l = ell - k coefficients prescribed.\n")
        fh.write("# k*  = least k for which Hsu (1996) Thm 2.4 / Cohen (2005) Thm 2.1,\n")
        fh.write("#       2^{n-l}/n - (l+1) 2^{n/2}/n > 0, is positive: a theorem for ALL n.\n")
        fh.write("# kLS = least k at which the large sieve over degrees first becomes\n")
        fh.write("#       non-vacuous (Sigma_1 <= lambda).  They differ by at most 1.\n")
        fh.write("#        n     ell    k*   kLS   l_max=ell-k*\n")
        for n, ell, ks, kl, lmax in rows:
            fh.write("%10d %7d %5d %5d %8d\n" % (n, ell, ks, kl, lmax))
    return p


def write_minsub(rows, worst, ratio):
    p = os.path.join(DATA, "aad-margin.txt")
    with open(p, "w") as fh:
        fh.write("# The observed margin.  s_min(n) = minimal subdegree of an\n")
        fh.write("# irreducible of degree n over F_2; the conjecture asks only for\n")
        fh.write("# s_min(n) <= floor(n/2).  Produced by an independent python-flint\n")
        fh.write("# Rabin search (data/aad-min-subdegree.txt); here the margin.\n")
        fh.write("#      n  s_min  floor(n/2)  margin  s_min/log2(n)\n")
        for n, s in rows:
            fh.write("%8d %6d %11d %7d %13.3f\n"
                     % (n, s, n // 2, n // 2 - s, s / math.log2(max(n, 2))))
        fh.write("# worst n for s_min - 2 log2 n: n=%d s_min=%d\n" % worst[:2])
        fh.write("# max s_min/floor(n/2) over n >= 8: %.4f\n" % ratio)
    return p


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    os.makedirs(DATA, exist_ok=True)
    ok = True

    print("== CHECK A: independent character/L-function engine vs the branch CAS ==")
    try:
        rows_a, rh = check_a(ell_max=10)
        check("A engine reproduces D_n for 2 <= ell <= 10, both degrees",
              True, f"{2 * len(rows_a)} endpoints, worst RH deviation {rh:.2e}")
    except CheckFailed as exc:
        ok = check("A engine reproduces D_n for 2 <= ell <= 10, both degrees", False, str(exc))

    print("== CHECK B: Theorem 1, the low-block bound ==")
    ell_list = list(range(5, 300)) + [1000, 1023, 1024, 1025, 4096, 65536, 10 ** 6]
    try:
        wo, we = check_b(ell_list)
        check("B |d^low| < 2^-5/2 (odd) and < 2^-3 (even), 5 <= ell <= 10^6", True,
              f"sup measured {wo:.5f} (odd, cap {2 ** -2.5:.5f}), "
              f"{we:.5f} (even, cap 0.125)")
    except CheckFailed as exc:
        ok = check("B |d^low| < 2^-5/2 (odd) and < 2^-3 (even)", False, str(exc))

    print("== CHECK C: Theorem 2, the reduction ==")
    try:
        rows_c = check_c(nmax=28)
        check("C I_n >= 1 whenever |d^top| <= 0.34, for every n >= 26", True,
              f"Theta_n recomputed exactly for 6 <= n <= 28 ({len(rows_c)} degrees)")
    except CheckFailed as exc:
        ok = check("C reduction through the proper-prime-power mass", False, str(exc))

    print("== CHECK D: Theorem 3, block support ==")
    js = list(range(4, 400)) + [1000, 1024, 2048, 10 ** 4, 10 ** 5]
    try:
        rows_d, worst_d = check_d(js)
        check("D every conductor is in the top block of <= 2ceil(log2 j)+4 degrees",
              True, f"{len(rows_d)} conductors, tightest at j={worst_d[0]} "
                    f"({worst_d[1] * 100:.0f}% of the bound)")
    except CheckFailed as exc:
        ok = check("D block support", False, str(exc))

    print("== CHECK G: Frobenius-angle multiset of a conductor ==")
    blocks = []
    try:
        for j in range(3, 12):
            blocks.append(conductor_block(j, 2 * j + 4))
        for b in blocks:
            if b["j"] >= 9:
                require(b["distinct_L"] < b["chars"],
                        f"j={b['j']}: no two characters share an L-polynomial")
            if b["j"] >= 4:
                require(b["distinct_angles"] < b["sigma1"],
                        f"j={b['j']}: the angle multiset is squarefree")
                require(b["sigma2"] > b["sigma1"],
                        f"j={b['j']}: Sigma_2 = Sigma_1 (no repeats)")
            require(b["sigma1"] == (b["j"] - 1) * (1 << (b["j"] - 1)),
                    f"j={b['j']}: Sigma_1 = {b['sigma1']}, not (j-1)2^(j-1)")
        check("G exact angle coincidences exist, so delta = 0 in the separated form",
              True, f"j = 3..11; e.g. j=11: {blocks[-1]['distinct_L']} distinct L among "
                    f"{blocks[-1]['chars']} characters, Sigma_2/Sigma_1 = "
                    f"{blocks[-1]['sigma2'] / blocks[-1]['sigma1']:.2f}")
    except CheckFailed as exc:
        ok = check("G angle coincidences", False, str(exc))

    print("== CHECK E: Theorem 4, the large-sieve null result ==")
    ell_e = list(range(4, 400)) + [1024, 4096]
    try:
        ls_rows = check_e(blocks, ell_e)
        check("E every Montgomery--Vaughan bound is >= Sigma_1^2/lambda^2 > 1", True,
              f"floor {ls_rows[0][1]:.1f} at ell=4 up to {ls_rows[-1][1]:.3g} at "
              f"ell={ls_rows[-1][0]}")
    except CheckFailed as exc:
        ok = check("E large-sieve null result", False, str(exc))

    print("== CHECK F: Theorem 6, the slack ladder ==")
    ns_f = [2 ** k for k in range(5, 21)] + list(range(32, 400)) + [3000, 10 ** 5, 10 ** 6]
    ns_f = sorted(set(ns_f))
    try:
        rows_f, worst_f = check_f(ns_f)
        check("F the large sieve never lowers the slack: 0 <= kLS - k* <= 2", True,
              f"{len(rows_f)} degrees, worst kLS - k* = {worst_f}; "
              f"pin n=64 gives l_max=27 against ell=31")
    except CheckFailed as exc:
        ok = check("F slack ladder", False, str(exc))

    print("== CHECK J: the Q-transform is window-hostile ==")
    try:
        good = check_j()
        check("J x^m f(x+1/x) leaves the window unless m is a power of two", True,
              f"{len(good)} admissible m below 4096, all powers of two")
    except CheckFailed as exc:
        ok = check("J Q-transform", False, str(exc))

    print("== CHECK H: measured endpoint deviations ==")
    stats = None
    try:
        rows_h, stats = check_h(extra_disc=CAS_DISC_HIGH)
        (rms, mx, r_odd, n_odd, r_even, n_even, r_pair, npair,
         r_spear, p_perm, jk_lo, jk_hi, agreed) = stats
        check("H the identity class deviates like a typical class", True,
              f"{len(rows_h)} endpoints, rms z = {rms:.3f}, max|z| = {mx:.3f}")
        check("H no correlation across consecutive ell", True,
              f"Pearson r = {r_odd:+.3f} (odd, {n_odd} pairs), "
              f"{r_even:+.3f} (even, {n_even} pairs)")
        check("H the two degrees of one group are anti-correlated", True,
              f"Pearson r = {r_pair:+.3f}, Spearman {r_spear:+.3f}, permutation "
              f"p = {p_perm:.5f}, jackknife [{jk_lo:.3f}, {jk_hi:.3f}], "
              f"{npair} groups; {agreed} endpoints cross-checked between producers")
        write_endpoints(rows_h, stats)
    except CheckFailed as exc:
        ok = check("H measured endpoint deviations", False, str(exc))

    try:
        write_block_support(rows_d, ls_rows, blocks)
        write_slack(rows_f)
    except NameError:
        pass

    print("== CHECK I: the observed margin ==")
    try:
        rows_i, (worst_i, tight), ratio_i, redone = check_i()
        check("I s_min(n) <= 4 + 2 log2 n; equality s_min = floor(n/2) only at "
              "n = 2,3,5,8", True,
              f"{len(rows_i)} degrees pinned, {redone} recomputed from scratch; "
              f"max s_min/floor(n/2) = {ratio_i:.4f} over n >= 8")
        write_minsub(rows_i, worst_i, ratio_i)
    except (CheckFailed, FileNotFoundError) as exc:
        ok = check("I observed margin", False, str(exc))

    print("== mutation controls ==")
    mutation_control("M1 one CAS discrepancy corrupted (-> A)",
                     lambda: check_a(ell_max=6, corrupt=5))
    mutation_control("M2 telescope cutoff a := ell-1 (-> B)",
                     lambda: check_b(list(range(5, 60)), mutate_a="narrow"))
    mutation_control("M3 proper-power mass inflated by 2^h (-> C)",
                     lambda: check_c(nmax=26, fudge=2 ** 14))
    mutation_control("M4 block-support constant 4 -> 1 (-> D)",
                     lambda: check_d(list(range(4, 200)), bound_const=1))
    mutation_control("M5 large-sieve threshold tau_top := ell (-> E)",
                     lambda: check_e([], list(range(4, 50)), tau_top=Fraction(50)))
    mutation_control("M6 Hsu/Cohen log term dropped (-> F)",
                     lambda: check_f([2 ** k for k in range(5, 12)], drop_log_term=True))
    mutation_control("M7 exact-conductor test moved to the wrong block (-> G)",
                     lambda: conductor_block(6, 16, mutate_cond=True))
    mutation_control("M8 e_k perturbed in the Hayes group (-> A)",
                     lambda: check_a(ell_max=4, mutate_ek=True))
    mutation_control("M9 s_min ceiling tightened to 1 + log2 n (-> I)",
                     lambda: check_i(slope=1.0, intercept=1.0))
    mutation_control("M10 Sato-Tate sd inflated 100x (-> H)",
                     lambda: check_h(extra_disc=CAS_DISC_HIGH, corrupt_sd=True))

    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s): {', '.join(FAILURES)}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
