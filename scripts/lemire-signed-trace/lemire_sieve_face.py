#!/usr/bin/env python3
"""Checker for note 13 (the sieve face of Kaser--Lemire over F_2).

Every claim in `docs/research/10-cas/lemire-signed-trace/13-sieve-face.md` that
is a finite computation is re-derived here and asserted.  The script exits
nonzero on the first failure and prints `SIEVE-FACE OK` only if every check
passed AND every mutation control tripped the check it is aimed at.

Engines.  The bulk producer is the Rust `GF(2)` CAS binary
`axeyum-lemire-sieve` (source mirrored as `axeyum-lemire-sieve.rs.txt`); its
output is pinned in `data/sieve-typeI-n2-34.txt` and
`data/sieve-window-factorizations-n2-44.txt`.  This script is the INDEPENDENT
cross-check: it recomputes the same quantities from scratch with python-flint
(factorisation) and exact `Fraction`/integer arithmetic, and compares.  The
linear-programming rows in `data/sieve-lp-levels.txt` were produced by
scipy/HiGHS; the ones that assert a value of 0 are re-certified here over Q by
the exact rational populations in `data/sieve-parity-population-n*.txt`, so no
floating-point LP result is load-bearing.

Run with the lane venv:
  /data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python \
      scripts/lemire-signed-trace/lemire_sieve_face.py
"""

from __future__ import annotations

import math
import os
import sys
from collections import defaultdict
from fractions import Fraction

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")

FAILURES: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)
        print(f"FAIL: {message}")


class CheckFailed(Exception):
    pass


def strict(condition: bool, message: str) -> None:
    """Like `check` but raises, for use inside the mutation controls."""
    if not condition:
        raise CheckFailed(message)


# --------------------------------------------------------------- GF(2)[x]

def pmul(a: int, b: int) -> int:
    acc = 0
    while b:
        if b & 1:
            acc ^= a
        a <<= 1
        b >>= 1
    return acc


def pdeg(a: int) -> int:
    return a.bit_length() - 1


def pdivmod(a: int, b: int) -> tuple[int, int]:
    db = pdeg(b)
    if db < 0:
        raise ZeroDivisionError
    q, r = 0, a
    while pdeg(r) >= db:
        s = pdeg(r) - db
        q ^= 1 << s
        r ^= b << s
    return q, r


def reverse(a: int, k: int) -> int:
    """x^k a(1/x) for a of degree <= k."""
    out = 0
    for i in range(k + 1):
        if (a >> i) & 1:
            out |= 1 << (k - i)
    return out


def inverse_mod_xpow(u: int, m: int) -> int:
    """Inverse of a unit u (constant term 1) in F_2[x]/x^m, as a bitmask."""
    assert u & 1 == 1
    inv = 1
    for i in range(1, m):
        # coefficient i of u*inv must vanish
        acc = 0
        for j in range(1, i + 1):
            if (u >> j) & 1 and (inv >> (i - j)) & 1:
                acc ^= 1
        if acc:
            inv |= 1 << i
    return inv


def factor(poly: int):
    """Factorisation of a monic GF(2) polynomial, via python-flint."""
    from flint import nmod_poly

    n = pdeg(poly)
    p = nmod_poly([(poly >> i) & 1 for i in range(n + 1)], 2)
    _, facs = p.factor()
    out = []
    for f, e in facs:
        mask = 0
        for i, c in enumerate(f.coeffs()):
            if int(c) % 2:
                mask |= 1 << i
        out.append((mask, e))
    out.sort(key=lambda t: (pdeg(t[0]), t[0]))
    return out


def divisors_up_to(fac, kmax: int):
    acc = [1]
    for p, e in fac:
        nxt = []
        for d in acc:
            cur = d
            nxt.append(cur)
            for _ in range(e):
                pr = pmul(cur, p)
                if pdeg(pr) > kmax:
                    break
                cur = pr
                nxt.append(cur)
        acc = sorted(set(nxt))
    return acc


def window(n: int):
    h = n // 2 + 1
    return h, n - h, [(1 << n) | g for g in range(1 << h)]


def irreducible_count(m: int) -> int:
    """Number of monic irreducibles of degree m over F_2."""
    from sympy import divisors, mobius

    return sum(mobius(d) * 2 ** (m // d) for d in divisors(m)) // m


# ------------------------------------------------------- data file readers

def read_typei():
    rows = []
    for line in open(os.path.join(DATA, "sieve-typeI-n2-34.txt")):
        if not line.startswith("TYPEI|"):
            continue
        d = dict(kv.split("=") for kv in line.strip().split("|")[1:])
        rows.append({k: int(v) for k, v in d.items()})
    return rows


def read_census():
    joint = defaultdict(dict)
    irred = {}
    for line in open(os.path.join(DATA, "sieve-window-factorizations-n2-44.txt")):
        parts = line.strip().split("|")
        if parts[0] == "JOINT":
            d = dict(kv.split("=") for kv in parts[1:])
            joint[int(d["n"])][(int(d["omega"]), int(d["mindeg"]))] = int(d["count"])
        elif parts[0] == "IRRED":
            d = dict(kv.split("=") for kv in parts[1:])
            irred[int(d["n"])] = int(d["count"])
    return joint, irred


def read_population(n: int):
    path = os.path.join(DATA, f"sieve-parity-population-n{n}.txt")
    w = {}
    meta = {}
    for line in open(path):
        if line.startswith("META|"):
            meta = dict(kv.split("=") for kv in line.strip().split("|")[1:])
        elif line.startswith("W|"):
            _, fhex, frac = line.strip().split("|")
            num, den = frac.split("/")
            w[int(fhex, 16)] = Fraction(int(num), int(den))
    return meta, w


def read_lp_levels():
    lp, kmax, lpw, odd = [], [], [], []
    for line in open(os.path.join(DATA, "sieve-lp-levels.txt")):
        parts = line.strip().split("|")
        if parts[0] == "LP":
            lp.append((int(parts[1]), int(parts[2]), int(parts[3]), float(parts[4]), int(parts[5])))
        elif parts[0] == "KMAX":
            kmax.append((int(parts[1]), int(parts[2]), parts[3], parts[4]))
        elif parts[0] == "LPW":
            lpw.append((int(parts[1]), int(parts[2]), int(parts[3]), float(parts[4]), int(parts[5])))
        elif parts[0] == "ODD":
            odd.append((int(parts[1]), int(parts[2]), float(parts[3]), int(parts[4])))
    return lp, kmax, lpw, odd


# =========================================================== A. Type-I lemma

def type_i_direct(n: int, kextra: int):
    """A_d for every monic d of degree <= h+kextra, from scratch (flint)."""
    h, ell, w = window(n)
    kmax = h + kextra
    counts = defaultdict(int)
    for f in w:
        for d in divisors_up_to(factor(f), kmax):
            counts[d] += 1
    return h, ell, counts


def check_type_i(nmax_direct: int = 18, corrupt: tuple[int, int] | None = None) -> int:
    """Exact Type-I lemma, recomputed independently for 6 <= n <= nmax_direct."""
    examined = 0
    for n in range(6, nmax_direct + 1):
        h, ell, counts = type_i_direct(n, 3)
        if corrupt is not None and corrupt[0] == n:
            # mutation: pretend one d of degree corrupt[1] has one extra multiple
            victim = next(d for d in counts if pdeg(d) == corrupt[1])
            counts[victim] += 1
        for k in range(1, min(h + 3, n) + 1):
            seen = {d: c for d, c in counts.items() if pdeg(d) == k}
            total = sum(seen.values())
            strict(total == 1 << h,
                   f"n={n} k={k}: sum of A_d over deg d = k is {total}, expected 2^h={1 << h}")
            if k <= h:
                strict(len(seen) == 1 << k,
                       f"n={n} k={k}: {len(seen)} distinct divisors, expected 2^k={1 << k}")
                bad = [d for d, c in seen.items() if c != 1 << (h - k)]
                strict(not bad,
                       f"n={n} k={k}: {len(bad)} exceptions to A_d = 2^(h-k) = {1 << (h - k)}")
            else:
                bad = [d for d, c in seen.items() if c != 1]
                strict(not bad, f"n={n} k={k}: {len(bad)} divisors with A_d > 1 above the level")
                strict(len(seen) == 1 << h,
                       f"n={n} k={k}: {len(seen)} divisors with A_d = 1, expected 2^h={1 << h}")
                # the reversal criterion, on every monic d of degree k
                for dlow in range(1 << k):
                    d = (1 << k) | dlow
                    rev = reverse(d, k)
                    inv = inverse_mod_xpow(rev, ell + 1)
                    predicted = 1 if pdeg(inv) <= n - k else 0
                    strict(counts.get(d, 0) == predicted,
                           f"n={n} k={k} d={d:x}: A_d={counts.get(d, 0)} but reversal criterion says {predicted}")
            examined += 1
    return examined


def check_type_i_against_cas(rows) -> None:
    """The pinned CAS table must satisfy the lemma and agree with the direct run."""
    for r in rows:
        n, k, h = r["n"], r["k"], r["n"] // 2 + 1
        check(r["exceptions"] == 0, f"CAS row n={n} k={k} reports {r['exceptions']} exceptions")
        if k > n:
            continue
        check(r["sum"] == 1 << h, f"CAS row n={n} k={k}: sum={r['sum']} != 2^h")
        if k <= h:
            check(r["distinct"] == 1 << k and r["min"] == r["max"] == 1 << (h - k),
                  f"CAS row n={n} k={k} disagrees with A_d = 2^(h-k)")
        else:
            check(r["max"] == 1 and r["distinct"] == 1 << h,
                  f"CAS row n={n} k={k} disagrees with A_d in {{0,1}}, 2^h ones")
    # spot agreement with the independent recomputation
    for n in (12, 15, 18):
        h, ell, counts = type_i_direct(n, 3)
        for k in range(0, h + 4):
            mine = sum(c for d, c in counts.items() if pdeg(d) == k)
            if k == 0:
                mine = 1 << h
            theirs = [r for r in rows if r["n"] == n and r["k"] == k]
            if theirs:
                check(mine == theirs[0]["sum"],
                      f"n={n} k={k}: flint sum {mine} != CAS sum {theirs[0]['sum']}")


def check_interval_transfer(nmax: int = 14) -> None:
    """Every interval {F : deg(F - A0) < h} has the SAME exact Type-I data."""
    for n in range(8, nmax + 1):
        h = n // 2 + 1
        for shift in (0, 1, 3, 5):
            a0 = (1 << n) | (shift << h)  # a monic degree-n centre, arbitrary top half
            elems = [a0 ^ g for g in range(1 << h)]
            counts = defaultdict(int)
            for f in elems:
                for d in divisors_up_to(factor(f), h):
                    counts[d] += 1
            for k in range(1, h + 1):
                seen = {d: c for d, c in counts.items() if pdeg(d) == k}
                check(len(seen) == 1 << k and set(seen.values()) == {1 << (h - k)},
                      f"interval centre {a0:x} (n={n}) fails exact Type-I at k={k}")


# ============================================== B. Mertens over F_2[t]

def mertens_V(y: int) -> float:
    v = 1.0
    for m in range(1, y + 1):
        v *= (1 - 2.0 ** (-m)) ** irreducible_count(m)
    return v


def check_mertens(constant: float = 1.0) -> None:
    """log(1/V(y)) = H_y + R_y with |R_y| <= 2^{-y/2+2}, hence V(y) ~ e^{-gamma}/y."""
    from mpmath import euler, exp, log, mp, mpf

    mp.dps = 60
    harmonic = mpf(0)
    logv = mpf(0)
    worst = 0.0
    for y in range(1, 41):
        harmonic += mpf(1) / y
        logv += irreducible_count(y) * log(1 - mpf(2) ** (-y))
        residual = float(-logv - harmonic)
        bound = 4.0 * 2.0 ** (-y / 2)
        strict(abs(residual) <= bound,
               f"Mertens y={y}: |log(1/V) - H_y| = {residual:.3e} exceeds 2^(-y/2+2) = {bound:.3e}")
        worst = max(worst, abs(residual) * 2 ** (y / 2))
    # the constant is e^{-gamma}, not e^{-gamma} times anything else
    y = 40
    ratio = float(mpf(y) * exp(logv) / exp(-euler)) / constant
    strict(abs(ratio - 1.0) < 0.02,
           f"Mertens: y*V(y)/e^-gamma = {ratio:.6f} at y={y}, expected 1 to within 1/(2y)")


# ================================== C. window census and the P_r statements

def census_direct(n: int):
    h, ell, w = window(n)
    joint = defaultdict(int)
    irred = 0
    for f in w:
        fac = factor(f)
        omega = sum(e for _, e in fac)
        mindeg = min(pdeg(p) for p, _ in fac)
        joint[(omega, mindeg)] += 1
        if omega == 1 and mindeg == n:
            irred += 1
    return joint, irred


def check_census(joint, irred, cross_max: int = 20) -> None:
    for n in sorted(joint):
        h = n // 2 + 1
        check(sum(joint[n].values()) == 1 << h, f"census n={n}: counts do not sum to |W_n|")
    for n in range(8, cross_max + 1):
        j, i = census_direct(n)
        check(dict(j) == joint[n], f"census n={n}: flint disagrees with the CAS histogram")
        check(i == irred[n], f"census n={n}: flint irreducible count {i} != CAS {irred[n]}")
    # against the lane's independently pinned irreducible counts
    pinned = {}
    path = os.path.join(DATA, "irreducible-counts-n2-38.txt")
    for line in open(path):
        parts = line.replace("=", " ").split()
        pinned[int(parts[1])] = int(parts[5])
    for n, v in pinned.items():
        if n in irred:
            check(irred[n] == v, f"n={n}: census {irred[n]} != pinned ledger {v}")


def cnt(joint_n, pred) -> int:
    return sum(c for (om, md), c in joint_n.items() if pred(om, md))


def check_p3(joint, threshold: Fraction = Fraction(1, 4)) -> None:
    """`mindeg > threshold*n` forces omega <= 3, and such an F exists in every W_n."""
    for n in sorted(joint):
        if n < 6:
            continue
        big = cnt(joint[n], lambda om, md: md * 1 > threshold * n)
        big3 = cnt(joint[n], lambda om, md: md * 1 > threshold * n and om <= 3)
        strict(big == big3,
               f"n={n}: {big - big3} elements with every factor of degree > {threshold}*n "
               f"have more than 3 irreducible factors")
        strict(big > 0, f"n={n}: no element of W_n has all factors of degree > {threshold}*n")


def check_sieve_lower_bound(joint) -> None:
    """The Jurkat--Richert MAIN TERM at the largest admissible y, against the truth.

    This is a consistency check on the arithmetic of the main term, not a proof:
    at these y the sieve error term O((log D)^{-1/3}) is larger than f(s).
    """
    egamma = math.exp(0.5772156649015329)

    def f(s: float) -> float:
        if s <= 2:
            return 0.0
        if s <= 4:
            return 2 * egamma * math.log(s - 1) / s
        return 2 * egamma * math.log(3) / 4

    for n in sorted(joint):
        if n < 12:
            continue
        h = n // 2 + 1
        y = (h - 1) // 2
        while y > 0 and h / y <= 2:
            y -= 1
        if y <= 0:
            continue
        main = (1 << h) * mertens_V(y) * f(h / y)
        truth = cnt(joint[n], lambda om, md: md > y)
        check(main <= truth,
              f"n={n}: JR main term {main:.1f} exceeds the true S(W_n,{y}) = {truth}")


def selberg_G(level: int) -> Fraction:
    """G_L = sum over squarefree monic d of degree <= L of prod_{P|d} 1/(|P|-1)."""
    coef = [Fraction(0)] * (level + 1)
    coef[0] = Fraction(1)
    for m in range(1, level + 1):
        weight = Fraction(1, 2 ** m - 1)
        for _ in range(irreducible_count(m)):
            new = coef[:]
            for j in range(level - m, -1, -1):
                if coef[j]:
                    new[j + m] += coef[j] * weight
            coef = new
    return sum(coef)


def check_brun_titchmarsh(irred, level_multiplier: int = 1) -> None:
    """Exact Selberg upper bound: #irreducibles in W_n <= |W_n| / G_{floor(h/2)}.

    The weights are supported on deg d <= L with 2L <= h, so every remainder in
    the quadratic form is EXACTLY zero and the bound carries no error term.
    """
    for n in range(8, 41, 2):
        h = n // 2 + 1
        level = (h // 2) * level_multiplier
        bound = Fraction(1 << h) / selberg_G(level)
        strict(bound >= irred[n],
               f"n={n}: Selberg bound {float(bound):.1f} (L={level}) is below the true "
               f"count {irred[n]}")


# ============================================ E. the parity populations

def check_population(n: int, mutate: str | None = None) -> None:
    """Exact verification of a prime-free population with W_n's Type-I data."""
    meta, w = read_population(n)
    h = n // 2 + 1
    strict(int(meta["h"]) == h, f"population n={n}: h mismatch")

    if mutate == "prime":
        # move a unit of mass onto an irreducible
        target = next(f for f in ((1 << n) | g for g in range(1 << n))
                      if len(factor(f)) == 1 and factor(f)[0][1] == 1)
        w = dict(w)
        w[target] = Fraction(1)
    elif mutate == "perturb":
        w = dict(w)
        key = min(w)
        w[key] = w[key] + Fraction(1, 7)

    # (i) nonnegative
    strict(all(v >= 0 for v in w.values()), f"population n={n}: a value is negative")
    # (ii) vanishes on every irreducible of degree n
    for f in w:
        fac = factor(f)
        if len(fac) == 1 and fac[0][1] == 1:
            strict(w[f] == 0, f"population n={n}: mass {w[f]} sits on the irreducible {f:x}")
    # (iii) exact Type-I data at every level deg d <= h, ambient = all monic degree n
    totals = defaultdict(Fraction)
    for f, v in w.items():
        if v == 0:
            continue
        for d in divisors_up_to(factor(f), h):
            totals[d] += v
    for k in range(0, h + 1):
        for dlow in range(1 << k):
            d = (1 << k) | dlow if k else 1
            want = Fraction(1 << (n - k))
            got = totals.get(d, Fraction(0))
            strict(got == want,
                   f"population n={n}: sum over multiples of d={d:x} (deg {k}) is {got}, "
                   f"expected 2^(n-k) = {want}")
            if k == 0:
                break


def min_window_prime_count(n: int) -> int:
    """min over ALL monic centres A0 of #{irreducible F : deg(F - A0) < h}.

    By the transfer proposition of note 13 sec. 5, no lower-bound sieve at level
    2^h can prove more irreducibles in W_n than this minimum -- so a sieve proof
    of Kaser--Lemire at the window's own level would prove Legendre for F_2[t].
    """
    h = n // 2 + 1
    ell = n - h
    counts = [0] * (1 << ell)
    for low in range(1 << n):
        f = (1 << n) | low
        fac = factor(f)
        if len(fac) == 1 and fac[0][1] == 1:
            counts[low >> h] += 1
    return min(counts)


def check_uniform_windows(nmax: int = 16) -> None:
    for n in range(6, nmax + 1):
        m = min_window_prime_count(n)
        check(m >= 1,
              f"n={n}: some window of length 2^h has no irreducible (min = {m})")
        print(f"  n={n}: every one of the 2^{n - (n // 2 + 1)} windows contains "
              f"an irreducible (min = {m})")


# ============================================ F. the LP ledger, sanity only

def check_lp_ledger(lp, kmax, lpw, irred_all) -> None:
    by_n = defaultdict(dict)
    for n, h, K, value, i_n in lp:
        by_n[n][K] = value
        check(value <= i_n + 1e-6, f"LP(n={n},K={K}) = {value} exceeds the true count {i_n}")
        check(K < n or abs(value - i_n) < 1e-6,
              f"LP(n={n},K=n) should equal the true count")
    for n, values in by_n.items():
        ks = sorted(values)
        for a, b in zip(ks, ks[1:]):
            check(values[a] <= values[b] + 1e-6,
                  f"LP(n={n}) is not nondecreasing in K: LP({a})={values[a]} > LP({b})={values[b]}")
    for n, h, km, delta in kmax:
        if km.startswith(">="):
            floor_k = int(km[2:])
            for K, value in by_n[n].items():
                check(not (K < floor_k and value > 0),
                      f"k_max(n={n}) claimed >= {floor_k} but LP(K={K}) = {value} > 0")
        else:
            k = int(km)
            check(by_n[n].get(k, 1.0) > 0, f"k_max(n={n}) = {k} but LP there is not positive")
            for K, value in by_n[n].items():
                check(not (K < k and value > 0),
                      f"k_max(n={n}) = {k} but LP(K={K}) = {value} > 0")
        check(int(h) == n // 2 + 1, f"k_max row n={n}: wrong h")


# ================================================================= driver

def mutation_control(name: str, fn) -> None:
    """A control passes when the mutated input makes the check FAIL."""
    try:
        fn()
    except CheckFailed as exc:
        print(f"  control {name}: tripped ({str(exc)[:78]})")
        return
    FAILURES.append(f"mutation control {name} did NOT trip")
    print(f"FAIL: mutation control {name} did NOT trip")


def main() -> int:
    print("== A. exact Type-I lemma ==")
    examined = check_type_i(nmax_direct=20)
    check(examined >= 100, f"only {examined} (n,k) pairs were examined directly")
    print(f"  {examined} (n,k) pairs recomputed from scratch with python-flint, 6 <= n <= 20")
    rows = read_typei()
    check_type_i_against_cas(rows)
    print(f"  {len(rows)} pinned CAS rows, zero exceptions; flint agrees on n = 12, 15, 18")
    check_interval_transfer(14)
    print("  every interval of length 2^h has the same exact Type-I data")

    print("== B. Mertens over F_2[t] ==")
    check_mertens()
    print("  log(1/V(y)) = H_y + O(2^{-y/2}), so V(y) = e^{-gamma}/y (1 + O(1/y))")

    print("== C. window census, P_3 threshold, Brun--Titchmarsh ==")
    joint, irred = read_census()
    check_census(joint, irred, cross_max=22)
    check_p3(joint)
    check_sieve_lower_bound(joint)
    check_brun_titchmarsh(irred)
    print(f"  census n = 2..{max(joint)}; 'all factors of degree > n/4' forces omega <= 3 "
          "and is nonempty for every n; exact Selberg bound holds")

    print("== E. prime-free populations with the window's exact Type-I data ==")
    for n in (10, 11, 12, 13, 14, 15):
        check_population(n)
        meta, w = read_population(n)
        print(f"  n={n}: support {len(w)}, all 2^{int(meta['h'])+1}-1 Type-I equalities exact over Q")

    print("== D. the uniform-window transfer bound ==")
    check_uniform_windows(16)

    print("== F. LP ledger ==")
    lp, kmax, lpw, odd = read_lp_levels()
    check_lp_ledger(lp, kmax, lpw, irred)
    for n, h, K, value, i_n in lpw:
        check(value <= i_n + 1e-6,
              f"W-confined LP(n={n},K={K}) = {value} exceeds the window's count {i_n}")
    print("  " + ", ".join(f"k_max({n})={km}" for n, h, km, d in kmax))

    print("== mutation controls ==")
    mutation_control("M1 corrupted A_d", lambda: check_type_i(nmax_direct=10, corrupt=(10, 3)))
    mutation_control("M2 mass on a prime", lambda: check_population(10, mutate="prime"))
    mutation_control("M3 perturbed population value", lambda: check_population(10, mutate="perturb"))
    mutation_control("M4 P_3 threshold lowered to n/5",
                     lambda: check_p3(joint, threshold=Fraction(1, 5)))
    mutation_control("M5 Selberg level tripled (remainders no longer vanish)",
                     lambda: check_brun_titchmarsh(irred, level_multiplier=3))
    mutation_control("M6 Mertens constant doubled",
                     lambda: check_mertens(constant=2.0))

    if FAILURES:
        print(f"\n{len(FAILURES)} FAILURES")
        return 1
    print("\nSIEVE-FACE OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
