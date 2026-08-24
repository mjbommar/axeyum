#!/usr/bin/env python3
"""Checks for note 19 (`19-effective-large-q.md`): effectivising the large-`q`
Kaser--Lemire theorem of note 16.

Note 16 established: for `p` odd and `q = p^l > 961 e^2 p^2`, Bagshaw
arXiv:2401.10399 Cor. 2.5 plus the reversal duality `r = ceil(n/2)` gives
Kaser--Lemire over `F_q` for all `n >= n_0(q)`, with `n_0` ineffective; and
Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1 gives it unconditionally for small `n`.
This script pins the arithmetic on both ends of the resulting gap and the
effectivity audit in between.

  CHECK 1  the Hsu/Cohen end.  `I_q(n; L) >= q^{n-L}/n - (L+1) q^{n/2}/n` with
           `L = ceil(n/2)-1` prescribed top coefficients is positive exactly
           when `q^{n-2L} > (L+1)^2`; at `q = 3^11` that is odd `n <= 839` and
           even `n <= 354292`.  Also the slack-`k` reach, which shows the gap
           lives ONLY at the exact endpoint.
  CHECK 2  the savings exponent `delta` in Bagshaw Cor. 2.5.  Reconstructed
           from his proof as `delta = min(theta, eps*beta/p)` subject to his
           own `q`-condition, optimised, and turned into the trade-off curve.
           `n_0 = 2 log_q(C) / delta` where `C` is the implied constant.
  CHECK 3  the divisor-bound audit.  `sum_{deg x = m} tau(x) = (m+1) q^m` is
           EXACT over `F_q[T]`, but the pointwise bound `tau(x) <<_g q^{g deg x}`
           that Bagshaw and Sawin--Shusterman actually invoke has an extremal
           constant of size `q^{10^{341}}` at `g = delta(3^11)`.  That single
           step, not any Siegel-type mechanism, is what makes `n_0` useless.
  CHECK 4  the one input Sawin--Shusterman do not prove (`BounNumSqArithProgProp`,
           quoted from the integer "squares in arithmetic progressions"
           literature) has an elementary function-field substitute; its count
           is verified by brute force against an explicit bound.
  CHECK 5  the computational witnesses: in-window irreducibles of odd degree
           over `F_{3^11}` for `n` above the Hsu/Cohen reach, each re-verified
           by two independent irreducibility routines.

Exits nonzero on any failure.  Data written to data/effq-*.txt.

Usage:
    lemire_effective_largeq.py                 run the checks (default)
    lemire_effective_largeq.py --search LO HI BUDGET [PROCS [FLAGS]]
                                               regenerate the witness table.
                                               FLAGS is a comma list of
                                               `skip11` (leave 11 | n alone)
                                               and `onlymiss` (retry only the
                                               n that have no witness yet).
"""

import math
import os
import random
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

P_CHAR = 3
L_EXT = 11
Q_MAIN = P_CHAR ** L_EXT          # 177147
WITNESS_FILE = os.path.join(DATA, "effq-witnesses-3p11.txt")

FAILURES = []


def check(name, ok, detail=""):
    status = "ok" if ok else "FAIL"
    print(f"[{status}] {name}{(' -- ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)
    return ok


# ==========================================================================
# CHECK 1 -- the Hsu/Cohen end
# ==========================================================================

def hsu_cohen_positive(q, n, slack=0):
    """Is the Hsu 1996 / Cohen 2005 lower bound for the number of monic
    irreducibles of degree `n` over `F_q` with the top `L` coefficients
    prescribed strictly positive?  `L = ceil(n/2) - 1 - slack`, i.e. window
    `deg(f - T^n) <= floor(n/2) + slack`.

    Bound: `q^{n-L}/n - (L+1) q^{n/2}/n > 0`  <=>  `q^{n-2L} > (L+1)^2`
    (square both sides of `q^{n-L} > (L+1) q^{n/2}`; all quantities positive).
    Exact integer arithmetic -- no floats, no `q^{n/2}` for odd `n`.
    """
    L = (n + 1) // 2 - 1 - slack
    if L < 0:
        return True
    return q ** (n - 2 * L) > (L + 1) ** 2


def hsu_cohen_reach(q, parity, slack=0):
    """Largest `n` of the given parity for which the bound is positive.
    Closed forms (slack 0): even `n < 2q`, odd `((n+1)/2)^2 < q`."""
    def nth(i):
        return 2 * i if parity == "even" else 2 * i - 1
    if not hsu_cohen_positive(q, nth(1), slack):
        return None
    hi_i = 1
    while hsu_cohen_positive(q, nth(hi_i), slack):
        hi_i *= 2
        if hi_i > 10 ** 30:
            return None
    lo_i = hi_i // 2
    while lo_i + 1 < hi_i:
        mid = (lo_i + hi_i) // 2
        if hsu_cohen_positive(q, nth(mid), slack):
            lo_i = mid
        else:
            hi_i = mid
    return nth(lo_i)


def brute_window_irreducible(q, n):
    """Exhaustive: does an in-window monic irreducible of degree `n` exist
    over `F_q`?  Only for tiny `(q, n)` -- this is the positive control that
    the Hsu/Cohen bound is a statement about a nonempty set."""
    ctx = flint.fq_default_poly_ctx(*_pd(q))
    K = ctx.base_field()
    els = _field_elements(K, q)
    h = n // 2
    for code in range(q ** (h + 1)):
        c, coeffs = code, []
        for _ in range(h + 1):
            coeffs.append(els[c % q])
            c //= q
        f = ctx(coeffs + [K.zero()] * (n - h - 1) + [K.one()])
        if f.degree() == n and f.is_irreducible():
            return True
    return False


def _pd(q):
    p = None
    for cand in range(2, q + 1):
        if q % cand == 0:
            p = cand
            break
    d = round(math.log(q, p))
    assert p ** d == q, (p, d, q)
    return p, d


def _field_elements(K, q):
    p, d = _pd(q)
    z = K.gen()
    out = []
    for code in range(q):
        e, c, zp = K.zero(), code, K.one()
        for _ in range(d):
            e = e + K(c % p) * zp
            c //= p
            zp = zp * z
        out.append(e)
    return out


def admissible_q(limit_p=100, cutoff=None):
    """`{p^l : p odd, p^{l-2} > 961 e^2}` -- note 16 sec. 5, re-derived."""
    if cutoff is None:
        cutoff = 961 * math.e ** 2
    out = []
    for p in _odd_primes(limit_p):
        for l in range(3, 60):
            if p ** (l - 2) > cutoff:
                out.append((p, l, p ** l))
                break
    out.sort(key=lambda t: t[2])
    return out


def _odd_primes(limit):
    ps = []
    for n in range(3, limit + 1):
        if all(n % d for d in range(2, int(n ** 0.5) + 1)):
            ps.append(n)
    return ps


def check1():
    print("\n--- CHECK 1: the Hsu/Cohen end (exact integer arithmetic) ---")

    # C1.1  three independent evaluations of the same positivity condition
    #       agree on a sweep: the squared integer test used everywhere below,
    #       the closed forms, and -- for EVEN n only, where `q^{n/2}` is an
    #       integer -- the raw inequality `q^{n-L} > (L+1) q^{n/2}` as Hsu and
    #       Cohen state it.  The raw form is the one that is not a rearrangement
    #       of the others, so it is the one that could catch a squaring error.
    agree = True
    for q in (9, 27, 81, 3 ** 7, 5 ** 5):
        for n in range(2, 260):
            L = (n + 1) // 2 - 1
            closed = (n // 2 < q) if n % 2 == 0 else (((n + 1) // 2) ** 2 < q)
            sq = hsu_cohen_positive(q, n)
            if sq != closed:
                agree = False
            if n % 2 == 0:
                raw = q ** (n - L) > (L + 1) * q ** (n // 2)
                if raw != sq:
                    agree = False
    check("C1.1 raw `q^{n-L} > (L+1) q^{n/2}` == squared test == closed forms",
          agree)

    # C1.2  exact reach at q = 3^11
    odd_reach = hsu_cohen_reach(Q_MAIN, "odd")
    even_reach = hsu_cohen_reach(Q_MAIN, "even")
    ok = (odd_reach == 839 and even_reach == 354292
          and hsu_cohen_positive(Q_MAIN, 839)
          and not hsu_cohen_positive(Q_MAIN, 841)
          and hsu_cohen_positive(Q_MAIN, 354292)
          and not hsu_cohen_positive(Q_MAIN, 354294))
    check("C1.2 q=3^11 reach: odd n<=839, even n<=354292 (and n+2 fails)",
          ok, f"odd={odd_reach} even={even_reach}")

    # C1.3  POSITIVE CONTROL: the bound is about a nonempty set.  For tiny
    #       (q, n) where the bound is positive, brute force finds a witness.
    pc = True
    for q, n in ((9, 3), (9, 5), (27, 5), (25, 7)):
        if hsu_cohen_positive(q, n):
            if not brute_window_irreducible(q, n):
                pc = False
    # and the converse direction is NOT claimed: at q=3, n=5 the bound is
    # negative yet a witness exists -- so a failure of the bound is not a
    # failure of the conjecture.
    bound_neg_but_exists = (not hsu_cohen_positive(3, 5)) and brute_window_irreducible(3, 5)
    check("C1.3 POSITIVE CONTROL: bound positive => brute-force witness exists",
          pc and bound_neg_but_exists,
          "and q=3,n=5: bound negative, witness exists (bound is sufficient only)")

    # C1.4  slack-k reach: one coefficient of slack moves the odd reach from
    #       839 to beyond 10^8.  The gap lives ONLY at the exact endpoint.
    r0 = hsu_cohen_reach(Q_MAIN, "odd", slack=0)
    r1 = hsu_cohen_reach(Q_MAIN, "odd", slack=1)
    r2 = hsu_cohen_reach(Q_MAIN, "odd", slack=2)
    ok = r0 == 839 and r1 > 10 ** 8 and r2 > 10 ** 13
    check("C1.4 slack-k odd reach ~ 2 q^{k+1/2}: k=0 -> 839, k=1 -> %d" % r1,
          ok, f"k=2 -> {r2}")

    rows = ["# Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1 at the half-degree window",
            "# bound: #{monic irred, deg n, top L coeffs prescribed} >=",
            "#        q^{n-L}/n - (L+1) q^{n/2}/n,   L = ceil(n/2)-1-slack",
            "# positive  <=>  q^{n-2L} > (L+1)^2   (exact integer test)",
            "#",
            "# p|l|q|odd_reach|even_reach|odd_reach_slack1"]
    for p, l, q in admissible_q(200)[:24]:
        rows.append("%d|%d|%d|%d|%d|%d" % (
            p, l, q, hsu_cohen_reach(q, "odd"), hsu_cohen_reach(q, "even"),
            hsu_cohen_reach(q, "odd", slack=1)))
    rows.append("#")
    rows.append("# slack sweep at q = 3^11 (odd n), showing the endpoint-only gap")
    rows.append("# slack|odd_reach")
    for k in range(0, 6):
        rows.append("%d|%d" % (k, hsu_cohen_reach(Q_MAIN, "odd", slack=k)))
    _write("effq-hsu-cohen-reach.txt", rows)
    return odd_reach, even_reach


# ==========================================================================
# CHECK 2 -- the savings exponent delta, reconstructed from Bagshaw's proof
# ==========================================================================
#
# Bagshaw arXiv:2401.10399, proof of Thm 1.5 (`cor:vonmangoldt`), verbatim
# structure:
#     d = n - r;  omega' = (2 omega - 1)/omega < 1/16;  theta > 0 small;
#     eps = (16/15)(1/16 - omega' - 2 theta);
#     k <= r(1+eps):  S_0 <<_theta q^{15r/16 + 15 r eps/16 + r theta}
#                          = q^{r - r omega' - r theta} <= q^{d - r theta}
#     k >  r(1+eps):  S_0 <<_{theta,beta} q^{d - r beta eps / p},
#                     valid as long as q > (p e (eps+2)/eps)^{2/(1-2 beta)}.
# Hence the theorem's `delta` is  min(theta, eps*beta/p),  and the error is
# `C q^{d - r delta}` against a main term `q^{d+1}/(q-1)`, so positivity of the
# von Mangoldt sum needs `r delta > log_q C`, i.e. `n_0 ~ 2 log_q(C)/delta`.

def beta_max(eps, p, q):
    """Largest `beta` with `q > (p e (2+eps)/eps)^{2/(1-2 beta)}`."""
    B = p * math.e * (2.0 + eps) / eps
    return 0.5 - math.log(B) / math.log(q)


def eps_of(omega, theta):
    wp = (2.0 * omega - 1.0) / omega
    return (16.0 / 15.0) * (1.0 / 16.0 - wp - 2.0 * theta)


def delta_opt(omega, p, q, grid=200000):
    """Maximise `delta = min(theta, eps*beta/p)` over admissible (theta, beta)."""
    wp = (2.0 * omega - 1.0) / omega
    hi = (1.0 / 16.0 - wp) / 2.0
    if hi <= 0:
        return 0.0, None
    best, arg = 0.0, None
    for i in range(1, grid):
        th = hi * i / grid
        eps = eps_of(omega, th)
        if eps <= 0:
            break
        bm = beta_max(eps, p, q)
        if bm <= 0:
            continue
        d = min(th, eps * bm / p)
        if d > best:
            best, arg = d, (th, bm, eps)
    return best, arg


def omega_max(q, p):
    """Largest `omega` allowed by `q > p^2 e^2 ((16-omega)/(16-31 omega))^2`."""
    R = math.sqrt(q) / (p * math.e)
    return min((16 * R - 16) / (31 * R - 1), 0.5 + 1.0 / 62)


def check2():
    print("\n--- CHECK 2: the savings exponent delta and the trade-off ---")

    # C2.1  the two forms of Bagshaw's q-condition coincide at theta = 0.
    #       (16-w)/(16-31w) == 1 + 30/(1-16 w'),  w' = (2w-1)/w
    #       and the corresponding eps is (16/15)(1/16 - w'), so
    #       (2+eps)/eps == 1 + 30/(1-16 w') too.
    ok = True
    for w in (0.5, 0.5005, 0.502, 0.51, 0.515):
        wp = (2 * w - 1) / w
        lhs = (16 - w) / (16 - 31 * w)
        rhs = 1 + 30 / (1 - 16 * wp)
        eps = (16 / 15) * (1 / 16 - wp)
        rhs2 = (2 + eps) / eps
        if abs(lhs - rhs) > 1e-9 * abs(lhs) or abs(lhs - rhs2) > 1e-9 * abs(lhs):
            ok = False
    check("C2.1 (16-w)/(16-31w) == 1+30/(1-16w') == (2+eps)/eps", ok)

    # C2.2  the hard cap delta <= 1/(30 p): eps <= 1/15 and beta < 1/2.
    cap = 1.0 / (30 * P_CHAR)
    caps_ok = True
    for l in range(11, 40, 3):
        d, _ = delta_opt(0.5, P_CHAR, P_CHAR ** l, grid=40000)
        if not (0 < d < cap):
            caps_ok = False
    check("C2.2 delta < 1/(30p) = %.5f for every q = 3^l  => n_0 >= 60p log_q C"
          % cap, caps_ok)

    # C2.3  delta at q = 3^11, and the resulting n_0 formula.
    d11, arg11 = delta_opt(0.5, P_CHAR, Q_MAIN)
    ok = abs(d11 - 8.630e-4) < 2e-6
    check("C2.3 delta(3^11) = %.4e  (theta=%.3e, beta=%.4f, eps=%.5f)"
          % (d11, arg11[0], arg11[1], arg11[2]), ok,
          "n_0(3^11) = %.0f * log_q C" % (2 / d11))

    # C2.4  POSITIVE CONTROL against the task brief's stated premise.  The
    #       brief asserts "constants blow up as omega -> 1/2".  They do NOT:
    #       g(omega) = e^2((16-omega)/(16-31omega))^2 is MINIMISED at 1/2 and
    #       delta is MAXIMISED there.  Both directions are checked, so the
    #       control fails if either monotonicity is reversed.
    g = lambda w: math.e ** 2 * ((16 - w) / (16 - 31 * w)) ** 2
    ws = [0.5 + i * 0.0005 for i in range(0, 25)]
    g_inc = all(g(ws[i]) < g(ws[i + 1]) for i in range(len(ws) - 1))
    ds = [delta_opt(w, P_CHAR, Q_MAIN, grid=20000)[0] for w in ws]
    d_dec = all(ds[i] >= ds[i + 1] for i in range(len(ds) - 1))
    check("C2.4 POSITIVE CONTROL: omega=1/2 is optimal in BOTH directions "
          "(g increasing, delta decreasing)", g_inc and d_dec,
          "the brief's 'constants blow up as omega -> 1/2' is inverted")

    # C2.5  window constraint for odd n: omega = (n+1)/(2n) must be admissible.
    wmax = omega_max(Q_MAIN, P_CHAR)
    n_min_odd = math.ceil(1.0 / (2 * wmax - 1))
    ok = abs(wmax - 0.506445) < 1e-5 and n_min_odd == 78
    check("C2.5 omega_max(3^11) = %.6f  => the window admits every odd n >= %d"
          % (wmax, n_min_odd), ok,
          "so the window is NOT what blocks; the implied constant is")

    rows = ["# Bagshaw arXiv:2401.10399 Cor. 2.5: savings exponent, reconstructed",
            "# delta = min(theta, eps*beta/p),  eps = (16/15)(1/16 - w' - 2 theta),",
            "# w' = (2 omega - 1)/omega,  beta < 1/2 - log(p e (2+eps)/eps)/log q.",
            "# n_0 = 2 log_q(C) / delta  where C is the implied constant.",
            "#",
            "# (a) omega = 1/2 (even n), p = 3, per extension degree l",
            "# l|q|delta|theta|beta|eps|n0_per_log_q_C|hsu_cohen_odd_reach|K_max"]
    for l in range(11, 31):
        q = P_CHAR ** l
        d, a = delta_opt(0.5, P_CHAR, q, grid=100000)
        R = hsu_cohen_reach(q, "odd")
        rows.append("%d|%d|%.6e|%.6e|%.6f|%.6f|%.1f|%d|%.4f"
                    % (l, q, d, a[0], a[1], a[2], 2 / d, R, d * R / 2))
    rows += ["#",
             "# (b) odd n at q = 3^11: omega = (n+1)/(2n) is forced by the window",
             "# n|omega|delta|n0_per_log_q_C"]
    for n in (79, 101, 201, 401, 841, 1601, 3201, 6401, 10001, 100001):
        w = (n + 1) / (2 * n)
        d, _ = delta_opt(w, P_CHAR, Q_MAIN, grid=100000)
        rows.append("%d|%.8f|%.6e|%.1f" % (n, w, d, 2 / d if d else -1))
    rows += ["#",
             "# (d) coefficient slack at q = 3^11, n = 1001: r = ceil(n/2) - k,",
             "#     omega = r/n (which goes BELOW 1/2).  delta improves, but the",
             "#     Hsu/Cohen reach improves far faster -- see effq-hsu-cohen-reach.",
             "# slack|r|omega|delta"]
    for k in (0, 1, 2, 5, 10, 20):
        n = 1001
        r = (n + 1) // 2 - k
        w = r / n
        d, _ = delta_opt(w, P_CHAR, Q_MAIN, grid=100000)
        rows.append("%d|%d|%.6f|%.6e" % (k, r, w, d))
    rows += ["#",
             "# (c) other characteristics at their smallest admissible q",
             "# p|l|q|delta|n0_per_log_q_C"]
    for p, l, q in admissible_q(30)[:8]:
        d, _ = delta_opt(0.5, p, q, grid=100000)
        rows.append("%d|%d|%d|%.6e|%.1f" % (p, l, q, d, 2 / d if d else -1))
    _write("effq-delta-tradeoff.txt", rows)
    return d11


# ==========================================================================
# CHECK 3 -- the divisor-bound audit (where the effectivity actually dies)
# ==========================================================================

def tau_sum_bruteforce(q, m):
    """sum of tau(x) over monic x of degree m over F_q, by enumeration."""
    ctx = flint.fq_default_poly_ctx(*_pd(q))
    K = ctx.base_field()
    els = _field_elements(K, q)
    total = 0
    for code in range(q ** m):
        c, coeffs = code, []
        for _ in range(m):
            coeffs.append(els[c % q])
            c //= q
        f = ctx(coeffs + [K.one()])
        _, fac = f.factor()
        t = 1
        for _, e in fac:
            t *= e + 1
        total += t
    return total


def tau_max_bruteforce(q, m):
    ctx = flint.fq_default_poly_ctx(*_pd(q))
    K = ctx.base_field()
    els = _field_elements(K, q)
    best = 0
    for code in range(q ** m):
        c, coeffs = code, []
        for _ in range(m):
            coeffs.append(els[c % q])
            c //= q
        f = ctx(coeffs + [K.one()])
        _, fac = f.factor()
        t = 1
        for _, e in fac:
            t *= e + 1
        best = max(best, t)
    return best


def pointwise_divisor_constant_logq(q, gamma):
    """`max_m [ log_q(max_{deg x = m} tau(x)) - gamma m ]`.

    The extremal `x` of degree `m` is the product of every monic irreducible of
    degree `<= J` (each to the first power) for the `J` that maximises the
    trade-off: a new irreducible of degree `j` multiplies `tau` by `2` at a
    cost of `j` in degree, so degree class `j` is worth taking while
    `2^{1/j} > q^gamma`.  Returns (value as a Fraction, best J)."""
    L2 = Fraction(int(math.log(2) / math.log(q) * 10 ** 15), 10 ** 15)
    G = Fraction(int(gamma * 10 ** 18), 10 ** 18)
    best, S, m = Fraction(0), Fraction(0), Fraction(0)
    bestJ = 0
    for J in range(1, 200):
        NJ = Fraction(q ** J - q ** (J // 2 + 1), J)   # >= true count, tight
        S += NJ
        m += J * NJ
        v = S * L2 - G * m
        if v > best:
            best, bestJ = v, J
        if J > 5 and v < 0:
            break
    return best, bestJ


def _log10_frac(fr):
    return math.log10(fr.numerator) - math.log10(fr.denominator)


def check3(d11):
    print("\n--- CHECK 3: the divisor-bound audit ---")

    # C3.1  the AVERAGED divisor identity is exact and epsilon-free:
    #       sum_{x monic, deg x = m} tau(x) = (m+1) q^m   (zeta(u)^2).
    ok = True
    for q in (2, 3, 4, 5):
        for m in range(1, 6 if q < 5 else 5):
            if tau_sum_bruteforce(q, m) != (m + 1) * q ** m:
                ok = False
    check("C3.1 sum_{deg x=m} tau(x) = (m+1) q^m exactly (brute force)", ok)

    # C3.2  the POINTWISE extremal is 2^m as long as m <= #{linear monics} = q.
    ok = all(tau_max_bruteforce(q, m) == 2 ** m
             for q, m in ((3, 1), (3, 2), (3, 3), (4, 3), (5, 4), (2, 2)))
    # POSITIVE CONTROL: it is NOT 2^m once m exceeds q (F_2, m = 3 gives 6).
    control = tau_max_bruteforce(2, 3) == 6 and 2 ** 3 == 8
    check("C3.2 max_{deg x=m} tau(x) = 2^m for m <= q; POSITIVE CONTROL: "
          "q=2,m=3 gives 6 != 8", ok and control)

    # C3.3  the constant in the POINTWISE bound `tau(x) <<_g q^{g deg x}` at
    #       g = delta(3^11) is astronomically large, so `n_0` from the argument
    #       AS WRITTEN is astronomically large.  This is where effectivity dies
    #       -- not in any Siegel-type mechanism.
    v, J = pointwise_divisor_constant_logq(Q_MAIN, d11)
    lg = _log10_frac(v)
    n0_written = lg + math.log10(2 / d11)
    ok = lg > 300 and J > 40
    check("C3.3 log_q C_div(3^11, gamma=delta) ~ 10^%.1f at J=%d  =>  "
          "n_0 as written ~ 10^%.1f" % (lg, J, n0_written), ok)

    # C3.4  and this is NOT a small-q artefact: the same catastrophe at every
    #       admissible q = 3^l, because gamma = delta(q) shrinks as fast as
    #       log 2 / log q does.
    rows = ["# divisor-bound audit",
            "# (a) averaged identity sum_{deg x=m} tau(x) = (m+1) q^m is EXACT",
            "# (b) pointwise extremal max tau = 2^m for m <= q",
            "# (c) the constant C_div(q, gamma) in tau(x) <= C_div q^{gamma deg x}",
            "#     at gamma = delta(q), which is what the proofs invoke",
            "# l|q|delta|log10(log_q C_div)|best_J|log10(n0_as_written)|K_max"]
    still_bad = True
    for l in range(11, 31):
        q = P_CHAR ** l
        d, _ = delta_opt(0.5, P_CHAR, q, grid=60000)
        v, J = pointwise_divisor_constant_logq(q, d)
        lg = _log10_frac(v)
        R = hsu_cohen_reach(q, "odd")
        rows.append("%d|%d|%.4e|%.2f|%d|%.2f|%.4f"
                    % (l, q, d, lg, J, lg + math.log10(2 / d), d * R / 2))
        if lg < 5:
            still_bad = False
    check("C3.4 the divisor catastrophe persists at every q = 3^l, l <= 30 "
          "(so it is not a large-q artefact)", still_bad)
    _write("effq-divisor-audit.txt", rows)


# ==========================================================================
# CHECK 4 -- the one unproved Sawin--Shusterman input
# ==========================================================================
#
# SS `BounNumSqArithProgProp`: fix alpha, eps > 0 and a prime power q.  For
# d, m, k >= 0 with d >= eps(m+k), M in M_m, A in M_k, a in F_q[T]:
#   #{g : deg g < d, a + gM = lambda A B^2, lambda in F_q, B in F_q[T]}
#       << q^{(1/2 + alpha) d}.
# SS prove nothing; they cite Bombieri--Granville--Pintz (squares in arithmetic
# progressions over Z) and Cilleruelo--Granville.  Over F_q[T] the count has an
# elementary explicit bound: g is determined by (lambda, B); B is pinned modulo
# M by `lambda A B^2 = a mod M`, which has at most tau(M) q^{m/2} solutions;
# and B has degree at most (d + m - 1 - k)/2, so the number of lifts is
# q^{max(0, deg B + 1 - m)}.  Multiplying gives q^{(d+1)/2} tau(M) when
# deg B + 1 >= m.  This check brute-forces the count and compares.

def bounnumsq_count(q, M, A, a, d, ctx, els):
    """Brute-force #{g : deg g < d, a + gM = lambda A B^2}."""
    cnt = 0
    K = ctx.base_field()
    for code in range(q ** d):
        c, coeffs = code, []
        for _ in range(d):
            coeffs.append(els[c % q])
            c //= q
        g = ctx(coeffs)
        v = a + g * M
        if v.is_zero():
            cnt += 1
            continue
        w = v / A if (v % A).is_zero() else None
        if w is None:
            continue
        lead = w.leading_coefficient()
        w = w.monic()
        _, fac = w.factor()
        if all(e % 2 == 0 for _, e in fac):
            cnt += 1
    return cnt


def bounnumsq_bound(q, tauM, m, DB):
    """The elementary explicit bound of sec. 1.3 of the note:
    `1 + (q-1) * tau(M) * q^{m/2} * q^{max(0, DB+1-m)}`.
    The `q^{m/2}` factor is the allowance for degenerate square roots modulo a
    NON-SQUAREFREE `M` -- `x^2 = 0 mod P^e` has `q^{deg P floor(e/2)}` solutions.
    `T^r`, the modulus the Kaser--Lemire application uses, is the extreme case,
    so that factor is not decoration; check C4.3 is its fixture."""
    return 1 + (q - 1) * tauM * q ** (m // 2 + max(0, DB + 1 - m))


def _tau(poly):
    _, fac = poly.factor()
    t = 1
    for _, e in fac:
        t *= e + 1
    return t


def check4():
    print("\n--- CHECK 4: the unproved Sawin--Shusterman input ---")
    q = 3
    ctx = flint.fq_default_poly_ctx(3, 1)
    K = ctx.base_field()
    els = _field_elements(K, q)
    worst_ratio = 0.0
    rows = ["# BounNumSqArithProgProp (SS, quoted from BGP92/CG07, never proved",
            "# there) -- brute-force count vs the elementary explicit bound",
            "#   bound = 1 + (q-1) * tau(M) * q^{m/2} * q^{max(0, DB+1-m)},",
            "#   DB = floor((d + m - 1 - k)/2)",
            "# q|m|k|d|M|A|count|bound|count/q^{d/2}"]
    ok = True
    # Repeated-factor moduli are included, but note C4.3: even with them this
    # grid never needs the `q^{m/2}` allowance.  That case has its own fixture.
    Ms = [ctx([1, 1]), ctx([0, 1]), ctx([1, 0, 1]), ctx([2, 1, 1]),
          ctx([1, 1, 1, 1]), ctx([0, 0, 1]), ctx([1, 2, 1]), ctx([0, 0, 0, 1])]
    As = [ctx([1]), ctx([1, 1]), ctx([2, 1])]
    for M in Ms:
        m = M.degree()
        for A in As:
            k = A.degree()
            for d in range(1, 5):
              for a in (ctx([1, 2, 1][:max(1, min(3, d + m))]), ctx([0, 1]),
                        M * ctx([1, 1])):
                cnt = bounnumsq_count(q, M, A, a, d, ctx, els)
                tauM = _tau(M)
                DB = (d + m - 1 - k) // 2
                bound = bounnumsq_bound(q, tauM, m, DB)
                if cnt > bound:
                    ok = False
                worst_ratio = max(worst_ratio, cnt / q ** (d / 2))
                rows.append("%d|%d|%d|%d|%s|%s|%d|%d|%.3f"
                            % (q, m, k, d, M.str(), A.str(), cnt, bound,
                               cnt / q ** (d / 2)))
    check("C4.1 brute-force count <= elementary explicit bound on every row",
          ok, "worst count/q^{d/2} = %.3f" % worst_ratio)

    # POSITIVE CONTROL: the exponent 1/2 is not slack -- some row exceeds
    # q^{0.4 d}, so a proposition with exponent 0.4 would be false here.
    control = False
    for M in Ms:
        m = M.degree()
        for d in range(2, 5):
            for a in (ctx([1, 2, 1][:max(1, min(3, d + m))]), ctx([0, 1])):
                cnt = bounnumsq_count(q, M, ctx([1]), a, d, ctx, els)
                if cnt > q ** (0.4 * d):
                    control = True
    check("C4.2 POSITIVE CONTROL: some row exceeds q^{0.4 d}, so the 1/2 in "
          "the proposition is doing work", control)

    # C4.3  ADVERSARIAL FIXTURE for the one case the bound distinguishes.
    #       The grid above is all squarefree or low-power moduli and NEVER
    #       needs the `q^{m/2}` allowance -- measured: deleting that factor
    #       leaves every row of the grid still satisfied.  `M = T^3` with
    #       `A = T`, `a = 0`, `d = 5` does need it: the count is 27 against 25
    #       without the allowance.  Without this fixture the allowance could be
    #       removed from `bounnumsq_bound` with the suite still green.
    fix_ok, fix_rows = True, []
    for d in (5, 6):
        M = ctx([0, 0, 0, 1])          # T^3
        A = ctx([0, 1])                # T
        a = ctx([0])
        m, k = M.degree(), A.degree()
        cnt = bounnumsq_count(q, M, A, a, d, ctx, els)
        DB = (d + m - 1 - k) // 2
        without = 1 + (q - 1) * _tau(M) * q ** max(0, DB + 1 - m)
        with_allowance = bounnumsq_bound(q, _tau(M), m, DB)
        fix_rows.append("fixture|3|%d|%d|%d|T^3|T|%d|%d|%d"
                        % (m, k, d, cnt, without, with_allowance))
        if not (cnt > without and cnt <= with_allowance):
            fix_ok = False
    check("C4.3 ADVERSARIAL FIXTURE: the degenerate-square-root allowance "
          "q^{m/2} is NECESSARY (M = T^3, A = T, a = 0)", fix_ok,
          "; the squarefree grid above never reaches this case")
    rows += ["# adversarial fixture rows (necessity of the q^{m/2} allowance)",
             "# tag|q|m|k|d|M|A|count|bound_without|bound_with"] + fix_rows
    _write("effq-bounnumsq-control.txt", rows)


# ==========================================================================
# CHECK 5 -- the computational witnesses
# ==========================================================================

def _primes_of(n):
    ps, m, d = set(), n, 2
    while d * d <= m:
        if m % d == 0:
            ps.add(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        ps.add(m)
    return ps


def rabin_f3(f, n):
    """Independent Rabin irreducibility test over F_3 (no factor() call)."""
    x = flint.nmod_poly([0, 1], P_CHAR)
    if x.pow_mod(P_CHAR ** n, f) != x:
        return False
    for pr in _primes_of(n):
        if (x.pow_mod(P_CHAR ** (n // pr), f) - x).gcd(f).degree() != 0:
            return False
    return True


def flint_factor_irreducible_f3(f, n):
    _, fac = f.factor()
    return len(fac) == 1 and fac[0][1] == 1 and fac[0][0].degree() == n


def decode_tail(hexstr, ndigits):
    v = int(hexstr, 16)
    digs = []
    for _ in range(ndigits):
        digs.append(v % P_CHAR)
        v //= P_CHAR
    assert v == 0, "tail encoding overflows its declared length"
    return digs


def verify_row(row):
    n_s, carrier, tail_hex, _tries, _sec = row.split("|")
    n = int(n_s)
    h = n // 2
    if carrier == "F3":
        digs = decode_tail(tail_hex, h + 1)
        # round trip: the decode must reproduce the stored string exactly.
        # (The window `deg(f - T^n) <= floor(n/2)` is enforced by the encoding
        # itself -- the tail has exactly floor(n/2)+1 slots -- so checking it
        # on the digit list would be vacuous.  What is NOT vacuous is that the
        # decode is lossless and that the reconstructed f has degree n with
        # the tail in the low positions; both are checked here.)
        if _encode("F3", digs) != tail_hex:
            return (n, False, "encoding round trip")
        f = flint.nmod_poly(digs + [0] * (n - h - 1) + [1], P_CHAR)
        if f.degree() != n:
            return (n, False, "degree")
        tail_poly = flint.nmod_poly(digs, P_CHAR)
        if tail_poly.degree() > h:
            return (n, False, "window")
        if f - flint.nmod_poly([0] * n + [1], P_CHAR) != tail_poly:
            return (n, False, "tail placement")
        if n % L_EXT == 0:
            return (n, False, "F3 carrier invalid when 11 | n")
        a = flint_factor_irreducible_f3(f, n)
        b = rabin_f3(f, n)
        return (n, a and b, "" if a and b else "irreducibility %s/%s" % (a, b))
    ctx = flint.fq_default_poly_ctx(P_CHAR, L_EXT)
    K = ctx.base_field()
    z = K.gen()
    zp = [K.one()]
    for _ in range(L_EXT - 1):
        zp.append(zp[-1] * z)
    digs = decode_tail(tail_hex, L_EXT * (h + 1))
    if _encode("F3^11", [digs[L_EXT * i:L_EXT * (i + 1)] for i in range(h + 1)]) \
            != tail_hex:
        return (n, False, "encoding round trip")
    coeffs = []
    for i in range(h + 1):
        e = K.zero()
        for j in range(L_EXT):
            c = digs[L_EXT * i + j]
            if c:
                e = e + K(c) * zp[j]
        coeffs.append(e)
    f = ctx(coeffs + [K.zero()] * (n - h - 1) + [K.one()])
    if f.degree() != n:
        return (n, False, "degree")
    a = f.is_irreducible()
    x = ctx([0, 1])
    q = P_CHAR ** L_EXT
    b = x.pow_mod(q ** n, f) == x
    if b:
        for pr in _primes_of(n):
            if (x.pow_mod(q ** (n // pr), f) - x).gcd(f).degree() != 0:
                b = False
                break
    return (n, a and b, "" if a and b else "irreducibility %s/%s" % (a, b))


def check5(odd_reach):
    print("\n--- CHECK 5: computational witnesses over F_{3^11} ---")
    if not os.path.exists(WITNESS_FILE):
        check("C5.0 witness file present", False, WITNESS_FILE)
        return

    # C5.1  the subfield lemma the F_3 witnesses rely on: a degree-`n`
    #       irreducible over F_3 stays irreducible over F_{3^11} iff
    #       gcd(n, 11) = 1, and splits into 11 factors when 11 | n.
    ctx = flint.fq_default_poly_ctx(P_CHAR, L_EXT)
    K = ctx.base_field()
    stays, splits = True, True
    rng = random.Random(20260823)
    for n in (5, 7, 9, 13, 21):
        f3 = _random_f3_irreducible(n, rng)
        big = ctx([K(int(c)) for c in f3.coeffs()])
        if not big.is_irreducible():
            stays = False
    for n in (11, 22, 33):
        f3 = _random_f3_irreducible(n, rng)
        big = ctx([K(int(c)) for c in f3.coeffs()])
        _, fac = big.factor()
        if not (sum(e for _, e in fac) == L_EXT
                and all(g.degree() == n // L_EXT for g, _ in fac)):
            splits = False
    check("C5.1 POSITIVE CONTROL: F_3-irreducible of degree n is irreducible "
          "over F_{3^11} iff 11 does not divide n", stays and splits,
          "and splits into 11 equal factors when 11 | n")

    rows = [r.strip() for r in open(WITNESS_FILE) if r.strip()
            and not r.startswith("#")]
    hits = [r for r in rows if r.split("|")[2] != "MISS"]
    misses = [int(r.split("|")[0]) for r in rows if r.split("|")[2] == "MISS"]

    nproc = min(28, max(1, (os.cpu_count() or 4) - 2))
    t0 = time.time()
    with Pool(nproc) as pool:
        res = pool.map(verify_row, hits, chunksize=1)
    bad = [(n, why) for n, ok, why in res if not ok]
    check("C5.2 every witness re-verified by two independent irreducibility "
          "routines (%d rows, %.0f s)" % (len(res), time.time() - t0),
          not bad, str(bad[:5]))

    # C5.3/C5.4 below deliberately test PRESENCE of a row, not its validity:
    # validity is C5.2's job.  Splitting the claim that way makes each guard
    # independently killable -- corrupting a witness kills only C5.2, deleting
    # a row kills only C5.3.  Testing both from the same set would make one
    # mutation kill two checks and hide which guard is doing the work.
    got = set(int(line.split("|")[0]) for line in hits)

    # The two tiers the note claims (sec. 5 / Theorem B).  These are literal
    # numbers, not derived from the data, so removing a row kills a check.
    DENSE_LO, DENSE_HI, SPARSE_HI = 841, 1199, 1601

    dense = [n for n in range(DENSE_LO, DENSE_HI + 1, 2)]
    missing_dense = [n for n in dense if n not in got]
    check("C5.3 EVERY odd n in [%d, %d] has a witness (%d values)"
          % (DENSE_LO, DENSE_HI, len(dense)), not missing_dense,
          "missing: %s" % missing_dense[:12])

    sparse = [n for n in range(DENSE_HI + 2, SPARSE_HI + 1, 2)
              if n % L_EXT != 0]
    missing_sparse = [n for n in sparse if n not in got]
    check("C5.4 every odd n in [%d, %d] with 11 not dividing n has a witness "
          "(%d values)" % (DENSE_HI + 2, SPARSE_HI, len(sparse)),
          not missing_sparse, "missing: %s" % missing_sparse[:12])

    check("C5.5 the dense tier starts immediately above the Hsu/Cohen odd "
          "reach %d" % odd_reach, DENSE_LO == odd_reach + 2)

    carriers = {}
    for line in hits:
        f = line.split("|")
        carriers[int(f[0])] = f[1]
    n_ok = sum(1 for _n, ok, _w in res if ok)
    n_fq = sum(1 for n in got if carriers.get(n) == "F3^11")
    _write("effq-witness-summary.txt",
           ["# witness verification summary (all rows re-verified by two",
            "# independent irreducibility routines; see CHECK 5)",
            "# tier|range|condition|count",
            "dense|[%d, %d]|every odd n|%d" % (DENSE_LO, DENSE_HI, len(dense)),
            "sparse|[%d, %d]|odd n, 11 does not divide n|%d"
            % (DENSE_HI + 2, SPARSE_HI, len(sparse)),
            "#",
            "# total witnesses|%d   verified|%d   of which carrier F_{3^11}|%d"
            % (len(got), n_ok, n_fq),
            "# unresolved (search budget exhausted, NOT proved absent):",
            "|".join(str(m) for m in sorted(misses)) or "(none)"])


def _random_f3_irreducible(n, rng):
    while True:
        f = flint.nmod_poly([rng.randrange(3) for _ in range(n)] + [1], P_CHAR)
        if f.degree() == n and rabin_f3(f, n):
            return f


# ==========================================================================
# search mode
# ==========================================================================

_FQCTX = None


def _fqctx():
    global _FQCTX
    if _FQCTX is None:
        _FQCTX = flint.fq_default_poly_ctx(P_CHAR, L_EXT)
    return _FQCTX


def _search_f3(n, seed, budget):
    rng = random.Random(seed)
    h = n // 2
    x = flint.nmod_poly([0, 1], P_CHAR)
    ps = _primes_of(n)
    t0, tries = time.time(), 0
    while time.time() - t0 < budget:
        tries += 1
        tail = [rng.randrange(P_CHAR) for _ in range(h + 1)]
        f = flint.nmod_poly(tail + [0] * (n - h - 1) + [1], P_CHAR)
        if any(f(a) == 0 for a in range(P_CHAR)):
            continue
        y, ok = x.pow_mod(P_CHAR, f), True
        for _ in range(2, 7):
            y = y.pow_mod(P_CHAR, f)
            if (y - x).gcd(f).degree() != 0:
                ok = False
                break
        if not ok or x.pow_mod(P_CHAR ** n, f) != x:
            continue
        if any((x.pow_mod(P_CHAR ** (n // pr), f) - x).gcd(f).degree() != 0
               for pr in ps):
            continue
        return (n, "F3", tail, tries, time.time() - t0)
    return (n, "F3", None, tries, time.time() - t0)


def _search_fq(n, seed, budget):
    R = _fqctx()
    K = R.base_field()
    z = K.gen()
    zp = [K.one()]
    for _ in range(L_EXT - 1):
        zp.append(zp[-1] * z)
    rng = random.Random(seed)
    h = n // 2
    x = R([0, 1])
    q = P_CHAR ** L_EXT
    t0, tries = time.time(), 0
    while time.time() - t0 < budget:
        tries += 1
        trits = [[rng.randrange(P_CHAR) for _ in range(L_EXT)]
                 for _ in range(h + 1)]
        coeffs = []
        for tr in trits:
            e = K.zero()
            for j, c in enumerate(tr):
                if c:
                    e = e + K(c) * zp[j]
            coeffs.append(e)
        f = R(coeffs + [K.zero()] * (n - h - 1) + [K.one()])
        if f.degree() != n:
            continue
        y1 = x.pow_mod(q, f)
        if (y1 - x).gcd(f).degree() != 0:
            continue
        y, ok = y1, True
        for _ in range(2, 9):
            y = y.compose_mod(y1, f)
            if (y - x).gcd(f).degree() != 0:
                ok = False
                break
        if not ok or not f.is_irreducible():
            continue
        return (n, "F3^11", trits, tries, time.time() - t0)
    return (n, "F3^11", None, tries, time.time() - t0)


def _job(args):
    n, seed, budget = args
    return _search_f3(n, seed, budget) if n % L_EXT else _search_fq(n, seed, budget)


def _encode(carrier, tail):
    digs = tail if carrier == "F3" else [c for tr in tail for c in tr]
    v = 0
    for i, c in enumerate(digs):
        v += c * P_CHAR ** i
    return hex(v)


def _existing_hits():
    have = set()
    if os.path.exists(WITNESS_FILE):
        for line in open(WITNESS_FILE):
            line = line.strip()
            if line and not line.startswith("#") and line.split("|")[2] != "MISS":
                have.add(int(line.split("|")[0]))
    return have


def search_mode(lo, hi, budget, procs, flags=()):
    skip_mult11 = "skip11" in flags
    have = _existing_hits() if "onlymiss" in flags else set()
    tasks = []
    for n in range(lo, hi + 1):
        if n % 2 == 0 or n in have:
            continue
        if n % L_EXT == 0:
            if skip_mult11:
                continue
            # The F_{3^11} route needs ~n trials at ~(n/841)^{2.2} seconds each,
            # so its budget scales as n^{3.2}.  `budget` is the base, calibrated
            # so that base 700 gives n = 841 about 1.2x its expected cost.
            bud = min(3.0 * budget, max(1.3 * budget,
                                        1.4 * budget * (n / 841.0) ** 3.2))
        else:
            bud = budget
        # The seed depends on the budget so that a retry pass (which is run
        # with a different budget) draws a fresh sequence rather than
        # replaying the trials that already failed.
        tasks.append((n, 1000003 + n + int(round(budget)), bud))
    tasks.sort(key=lambda t: -t[2] * t[0])
    res = []
    with Pool(procs) as pool:
        for r in pool.imap_unordered(_job, tasks, chunksize=1):
            res.append(r)
            print("  %d %s %s tries=%d %.1fs [%d/%d]"
                  % (r[0], r[1], "HIT" if r[2] is not None else "MISS",
                     r[3], r[4], len(res), len(tasks)), flush=True)
    keep = {}
    if os.path.exists(WITNESS_FILE):
        for line in open(WITNESS_FILE):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            n_old = int(line.split("|")[0])
            if not (lo <= n_old <= hi) or line.split("|")[2] != "MISS":
                keep[n_old] = line
    for n, carrier, tail, tries, sec in res:
        if tail is None and n in keep:
            continue
        keep[n] = "%d|%s|%s|%d|%.1f" % (n, carrier, "MISS" if tail is None
                                        else _encode(carrier, tail), tries, sec)
    rows = ["# in-window irreducibles of odd degree over F_{3^11}",
            "# f = T^n + g monic irreducible, deg g <= floor(n/2).",
            "# carrier F3 means g has F_3 coefficients; since 11 is prime and",
            "# 11 does not divide n, such an f stays irreducible over F_{3^11}.",
            "# g is stored as the base-3 digit string of its coefficient vector",
            "# (low degree first; 11 trits per F_{3^11} coefficient), packed",
            "# into one integer and printed in hex.",
            "# n|carrier|tail_base3_hex|tries|seconds"]
    rows += [keep[n] for n in sorted(keep)]
    _write("effq-witnesses-3p11.txt", rows)


# ==========================================================================

def _write(name, rows):
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, name), "w") as fh:
        fh.write("\n".join(rows) + "\n")
    print("    wrote data/%s (%d lines)" % (name, len(rows)))


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--search":
        lo, hi, budget = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
        procs = int(sys.argv[5]) if len(sys.argv) > 5 else 28
        flags = tuple(sys.argv[6].split(",")) if len(sys.argv) > 6 else ()
        search_mode(lo, hi, budget, procs, flags)
        return 0
    odd_reach, _ = check1()
    d11 = check2()
    check3(d11)
    check4()
    check5(odd_reach)
    print()
    if FAILURES:
        print("FAILED: " + ", ".join(FAILURES))
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
