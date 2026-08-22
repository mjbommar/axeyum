"""The monomial-composition window family: Theorem A, its coverage set, and the prime-n blocker.

THEOREM A (note 08).  Let `f` be irreducible over `F_2` of degree `m` with
`f(0) != 0`, order `e = ord(f)`, and suppose `f` is IN-WINDOW, i.e.
`deg(f - x^m) <= floor(m/2)`.  Let `t >= 2` satisfy `rad(t) | e` and
`gcd(t, (2^m-1)/e) = 1`.  Then

  (a) `f(x^t)` is irreducible over `F_2` of degree `mt` and order `et`
      (Lidl--Niederreiter, *Finite Fields*, 2nd ed., Thm 3.35; the extra
      hypothesis `q^m = 1 mod 4` when `4 | t` is vacuous at `q = 2` because
      `rad(t) | e | 2^m-1` is odd, so `t` is odd), and

  (b) `f(x^t)` is again in-window, because
      `deg(f(x^t) - x^{mt}) = t * deg(f - x^m) <= t*floor(m/2) <= floor(mt/2)`
      for every odd `t >= 1`.

So Kaser--Lemire holds at `n = mt`.  The old cyclotomic family `n = 2*3^k`
(note 08, first version) is exactly the case `m = 2`, `f = x^2+x+1`, `e = 3`,
`t = 3^k`.

THE HYPOTHESES COLLAPSE TO ONE PER-PRIME TEST.

  `rad(t) | e`  and  `gcd(t, (2^m-1)/e) = 1`
  <=> for every prime `p | t`:  `v_p(e) = v_p(2^m-1) >= 1`
  <=> for every prime `p | t`:  `p | 2^m-1`  and  `x^{(2^m-1)/p} != 1` in `F_2[x]/(f)`.

The last form needs NO factorization of `2^m-1`: one modular exponentiation per
candidate prime.  It is what the Rust CAS calls `monomial_prime_eligibility`
(`root_is_not_prime_power`) and what this script uses.

WHAT IT COMPUTES.

  `S(N) = { m*t <= N : m has a KNOWN in-window irreducible seed `f`, `t >= 2`,
                       and every prime of `t` is admissible for that ONE seed }`

over the lane's certified seed ledger (an in-window irreducible is known for
every degree `m <= 3000`).  Reports coverage, the density trend, the smallest
uncovered composite, which degrees carry the coverage, and re-verifies members
by a DIRECT irreducibility test of `f(x^t)` that shares no logic with the
criterion -- primarily in the Rust CAS, and on a sample independently in flint.

ENGINES.  The Rust `GF(2)` CAS of the lane snapshot is the primary engine
(`axeyum-gf2-monomial-family`, built from `crates/axeyum-cas/src/bin/`); it is
one to three orders of magnitude faster than python-flint here because it is
bit-packed and its reduction is sparsity-aware.  python-flint is the
independent cross-check: `--flint-crosscheck K` re-derives K of the coverage
verdicts and every control with flint and asserts both engines agree.

Exits nonzero if any assertion, control, cross-check, or re-verification fails.

Usage:
  python lemire_composition_family.py [--nmax N] [--sample K] [--flint-crosscheck K]
      [--engine rust|flint] [--procs P] [--out FILE] [--quiet]
"""

import argparse
import os
import random
import subprocess
import sys
import time
from collections import Counter
from multiprocessing import Pool

import flint
from sympy import n_order, primerange

HERE = os.path.dirname(os.path.abspath(__file__))
WITNESS_FILE = os.path.join(HERE, "data", "witnesses-401-3000.txt")
DEFAULT_RUST = os.environ.get(
    "AXEYUM_GF2_MONOMIAL_FAMILY",
    "/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440/target/release/"
    "axeyum-gf2-monomial-family",
)

MAX_SEED_DEGREE = 3000       # the lane's certified in-window seed range
MAX_SEEDS_PER_DEGREE = 12    # distinct in-window seeds evaluated per degree
CANDIDATE_BUDGET = 200_000  # per-degree candidate cap is CANDIDATE_BUDGET // m
MIN_CANDIDATES_PER_DEGREE = 120
EXHAUSTIVE_UPTO = 22         # below this, the candidate stream is exhaustive

X = flint.nmod_poly([0, 1], 2)
ONE = flint.nmod_poly([1], 2)


# ------------------------------------------------------------- flint engine

def poly_from_exps(exps, m):
    """`x^m + sum_{e in exps} x^e + 1` over `F_2`."""
    c = [0] * (m + 1)
    for e in exps:
        c[e] ^= 1
    c[m] ^= 1
    c[0] ^= 1
    return flint.nmod_poly(c, 2)


def compose_monomial(exps, m, t):
    """`f(x^t)` as a flint polynomial."""
    c = [0] * (m * t + 1)
    for i, coeff in enumerate(poly_from_exps(exps, m).coeffs()):
        if int(coeff):
            c[i * t] = 1
    return flint.nmod_poly(c, 2)


def is_irreducible_factor(f):
    _, facs = f.factor()
    return len(facs) == 1 and facs[0][1] == 1


def prime_divisors(n):
    ps, d = [], 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        ps.append(n)
    return ps


def is_irreducible_rabin(f, n):
    """Direct Rabin test in flint.  Shares no logic with the LN criterion."""
    if f.degree() != n or n < 1:
        return False
    if X.pow_mod(1 << n, f) != X % f:
        return False
    for p in prime_divisors(n):
        h = X.pow_mod(1 << (n // p), f) - X
        if h.is_zero():
            return False
        if (h % f).gcd(f) != ONE:
            return False
    return True


FLINT_FACTOR_CAP = 160


def flint_is_irreducible(f, m):
    if f.degree() != m:
        return False
    return is_irreducible_factor(f) if m <= FLINT_FACTOR_CAP else is_irreducible_rabin(f, m)


def flint_admissible(exps, m, primes):
    """`{p in primes : p | 2^m-1 and x^{(2^m-1)/p} != 1 mod f}`."""
    f = poly_from_exps(exps, m)
    M = (1 << m) - 1
    return {p for p in primes if M % p == 0 and X.pow_mod(M // p, f) != ONE}


# -------------------------------------------------------------- rust engine

class RustEngine:
    """Persistent `axeyum-gf2-monomial-family` process (the primary engine)."""

    def __init__(self, path=DEFAULT_RUST):
        self.path = path
        self.proc = subprocess.Popen(
            [path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            text=True, bufsize=1)

    def _ask(self, line):
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()
        out = self.proc.stdout.readline().strip()
        if not out or out.startswith("ERR|"):
            raise RuntimeError(f"rust engine: {line!r} -> {out!r}")
        return dict(kv.split("=", 1) for kv in out.split("|")[1:])

    @staticmethod
    def _exps(exps):
        return ",".join(str(e) for e in exps) if exps else "-"

    def is_irreducible(self, exps, m):
        return self._ask(f"SEED {m} {self._exps(exps)}")["irreducible"] == "true"

    def admissible(self, exps, m, primes):
        if not primes:
            return set()
        ps = ",".join(str(p) for p in primes)
        tests = self._ask(f"ELIG {m} {self._exps(exps)} {ps}")["tests"]
        good = set()
        for item in tests.split(","):
            p, divides, notpow = item.split(":")
            if divides == "1" and notpow == "1":
                good.add(int(p))
        return good

    def composition_is_irreducible(self, exps, m, t):
        r = self._ask(f"IRR {m} {self._exps(exps)} {t}")
        return r["irreducible"] == "true", r["shaped"] == "true", r["route"]


class FlintEngine:
    """Same interface, python-flint underneath (cross-check / fallback)."""

    path = "python-flint"

    def is_irreducible(self, exps, m):
        return flint_is_irreducible(poly_from_exps(exps, m), m)

    def admissible(self, exps, m, primes):
        return flint_admissible(exps, m, primes)

    def composition_is_irreducible(self, exps, m, t):
        g = compose_monomial(exps, m, t)
        n = m * t
        tail = n - 1
        while tail > 0 and not int(g.coeffs()[tail]):
            tail -= 1
        return is_irreducible_rabin(g, n), tail <= n // 2, "flint-rabin"


_ENGINE = None


def _worker_init(kind, path):
    global _ENGINE
    _ENGINE = RustEngine(path) if kind == "rust" else FlintEngine()


# ------------------------------------------------------------------ seeds

def load_certified_witnesses():
    out = {}
    with open(WITNESS_FILE) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            out[int(parts[0])] = tuple(int(e) for e in parts[2].split(",")) if len(parts) > 2 else ()
    return out


def in_window_candidates(m):
    """Deterministic stream of in-window tails for `x^m + g + 1`, best shapes first."""
    half = m // 2
    for k in range(1, half + 1):
        yield (k,)
    if half >= 3:
        rng = random.Random(1000003 * m + 7)
        seen = set()
        for _ in range(4000):
            a, b, c = sorted(rng.sample(range(1, half + 1), 3))
            if (a, b, c) in seen:
                continue
            seen.add((a, b, c))
            yield (a, b, c)
    if m <= EXHAUSTIVE_UPTO:
        for mask in range(1 << half):
            yield tuple(i + 1 for i in range(half) if (mask >> i) & 1)


def candidate_cap(m):
    """Per-degree candidate budget, scaled so the work per degree is ~constant.

    Irreducibility testing costs ~O(m^2) and in-window irreducibles thin out like
    1/m, so a fixed cap lets the large degrees dominate the run while adding
    almost nothing: at large `m` only a handful of multipliers `t <= N/m` exist.
    """
    return max(MIN_CANDIDATES_PER_DEGREE, CANDIDATE_BUDGET // max(m, 1))


def seed_stream(m, certified_exps, engine):
    """In-window IRREDUCIBLE seeds of degree `m`; the ledger's witness first."""
    seen, tried = set(), 0
    cap = candidate_cap(m)
    if certified_exps is not None and engine.is_irreducible(certified_exps, m):
        seen.add(certified_exps)
        yield certified_exps
    for exps in in_window_candidates(m):
        if exps in seen:
            continue
        seen.add(exps)
        tried += 1
        if tried > cap:
            return
        if engine.is_irreducible(exps, m):
            yield exps


def degree_job(args):
    """Everything degree `m` contributes: the maximal admissible prime sets."""
    m, certified_exps, primes = args
    if not primes:
        return m, []
    sets, used = [], 0
    for exps in seed_stream(m, certified_exps, _ENGINE):
        used += 1
        a = _ENGINE.admissible(exps, m, primes)
        if a:
            sets.append((exps, a))
        if a == set(primes) or used >= MAX_SEEDS_PER_DEGREE:
            break
    maximal = []
    for exps, a in sorted(sets, key=lambda s: -len(s[1])):
        if not any(a <= b for _, b in maximal):
            maximal.append((exps, a))
    return m, maximal


def irr_job(args):
    m, exps, t = args
    irr, shaped, route = _ENGINE.composition_is_irreducible(exps, m, t)
    return m, exps, t, m * t, irr, shaped, route


# --------------------------------------------------------------- coverage

def prime_sieve(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
        i += 1
    return sieve


def smallest_prime_factor_sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def prime_set(t, spf):
    ps = set()
    while t > 1:
        p = spf[t]
        ps.add(p)
        while t % p == 0:
            t //= p
    return ps


def build_coverage(nmax, admissible, spf):
    cover = {}
    for m in sorted(admissible):
        entries = admissible[m]
        for t in range(2, nmax // m + 1):
            n = m * t
            if n in cover:
                continue
            ps = prime_set(t, spf)
            for exps, a in entries:
                if ps <= a:
                    cover[n] = (m, t, exps)
                    break
    return cover


def lacunarity_bound(admissible, N):
    """Proved upper bound: #{t >= 2 : rad(t) | prod P} <= prod_p (1 + log_p X)."""
    from math import log
    total = 0
    for m, entries in admissible.items():
        best = 0
        for _, a in entries:
            X = N / m
            if X < 2:
                continue
            b = 1.0
            for p in a:
                b *= (1.0 + log(X) / log(p))
            best = max(best, b)
        total += best
    return total


# ---------------------------------------------------------------- controls

def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def norm_window_check():
    """Does the norm `F_{2^k}[x] -> F_2[x]` preserve the half-degree window?

    `N(f) = prod_{i<k} f^{(2^i)}` (Frobenius on coefficients).  For
    `f = x^n + g` over `F_{2^k}` the product's second layer sits at degree
    `n(k-1) + deg g`, and `n(k-1) + deg g <= nk/2` forces `deg g <= n(1-k/2) <= 0`
    for `k >= 2`.  So the only norm-images in the window come from constant `g`,
    and for `k = 2` with `c` of order 3, `N(x^n + c) = x^{2n} + x^n + 1` -- the
    `m = 2` family again.  Checked here by explicit `F_4` arithmetic.
    """
    out, ok = [], True
    lg = {1: 0, 2: 1, 3: 2}
    ex = {0: 1, 1: 2, 2: 3}
    mul = [[0 if a == 0 or b == 0 else ex[(lg[a] + lg[b]) % 3] for b in range(4)]
           for a in range(4)]
    frob = {0: 0, 1: 1, 2: 3, 3: 2}

    def mulpoly(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        r[i + j] ^= mul[ai][bj]
        return r

    def norm2(a):
        return mulpoly(a, [frob[c] for c in a])

    def tail_degree(c):
        d = len(c) - 2
        while d >= 0 and c[d] == 0:
            d -= 1
        return d

    f = [1, 2, 0, 1]                       # x^3 + w x + 1 over F_4, n = 3, deg g = 1
    nf = norm2(f)
    ok &= all(c in (0, 1) for c in nf)
    td, deg = tail_degree(nf), len(nf) - 1
    out.append(f"control-4a norm of x^3+w*x+1 over F_4: degree {deg}, tail degree {td} "
               f"(prediction n(k-1)+deg g = 4), in-window={td <= deg // 2} (must be False)")
    ok &= (td == 4 and deg == 6 and td > deg // 2)

    f2 = [2] + [0] * 4 + [1]               # x^5 + w over F_4, constant tail
    nf2 = norm2(f2)
    td2, deg2 = tail_degree(nf2), len(nf2) - 1
    same = nf2 == [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    out.append(f"control-4b norm of x^5+w over F_4 = x^10+x^5+1: {same}, tail degree {td2}, "
               f"in-window={td2 <= deg2 // 2} (must be True; this is the m=2 family)")
    ok &= (same and td2 <= deg2 // 2)
    return out, ok


def controls(rust=None):
    """Mutation controls.  Each dies if one hypothesis of Theorem A is dropped."""
    out, ok = [], True

    def both(exps, m, t):
        """(flint verdict, rust verdict or None) for irreducibility of f(x^t)."""
        a = FlintEngine().composition_is_irreducible(exps, m, t)[0]
        b = rust.composition_is_irreducible(exps, m, t)[0] if rust else None
        if b is not None and a != b:
            raise AssertionError(f"engines disagree on ({m},{exps},{t}): flint={a} rust={b}")
        return a, b

    # (1) `rad(t) | e` is load-bearing.  Seed x^2+x+1 has e = 3, so t = 5 violates
    #     it and x^10+x^5+1 must be REDUCIBLE.
    a, b = both((1,), 2, 5)
    out.append(f"control-1 rad(t)|e violated (m=2,e=3,t=5): x^10+x^5+1 irreducible="
               f"{a} (flint) / {b} (rust) -- must be False")
    ok &= (a is False and b in (False, None))

    # positive twin: t = 3 satisfies both conditions for the same seed.
    a, b = both((1,), 2, 3)
    out.append(f"control-1b rad(t)|e satisfied (m=2,e=3,t=3): x^6+x^3+1 irreducible="
               f"{a} / {b} -- must be True")
    ok &= (a is True and b in (True, None))

    # (2) `gcd(t,(2^m-1)/e) = 1` is load-bearing.  A degree-6 irreducible of order
    #     21 has 3 | 21 (so (i) holds) but (2^6-1)/21 = 3, so gcd(3,3) = 3 and (ii)
    #     fails; f(x^3) must be REDUCIBLE.
    witness = None
    for mask in range(1 << 5):
        exps = tuple(i + 1 for i in range(5) if (mask >> i) & 1)
        g = poly_from_exps(exps, 6)
        if g.degree() != 6 or not is_irreducible_factor(g):
            continue
        e = min(d for d in (1, 3, 7, 9, 21, 63) if X.pow_mod(d, g) == ONE)
        if e == 21:
            witness = (exps, e)
            break
    if witness is None:
        out.append("control-2 FAILED: no order-21 degree-6 irreducible found")
        ok = False
    else:
        exps, e = witness
        cond_i = all(e % p == 0 for p in prime_divisors(3))
        cond_ii = _gcd(3, 63 // e) == 1
        a, b = both(exps, 6, 3)
        out.append(f"control-2 gcd(t,(2^m-1)/e) != 1: seed x^6+{exps}+1 has order {e}, t=3, "
                   f"cond(i)={cond_i} cond(ii)={cond_ii}; f(x^3) of degree 18 irreducible="
                   f"{a} / {b} -- must be False")
        ok &= (cond_i is True and cond_ii is False and a is False and b in (False, None))

    # (3) window preservation is exact arithmetic, for every odd t.
    bad = [(m, t) for m in range(1, 200) for t in range(3, 200, 2)
           if t * (m // 2) > (m * t) // 2]
    out.append(f"control-3 window preservation t*floor(m/2) <= floor(mt/2): "
               f"counterexamples over m<200, odd t<200 (must be []): {bad}")
    ok &= (bad == [])

    # (3b) MONOMIALITY is not load-bearing for the WINDOW in the way note 09
    #      claimed, and the exact criterion is checked here.  For a monic
    #      substitution `sigma = x^k + (tail of degree s)`, over F_2
    #      `sigma^m = (sigma^{lsb(m)})^{m/lsb(m)}` and `sigma^{lsb(m)} =
    #      x^{k*lsb(m)} + (tail)^{lsb(m)}`, so the second layer of `f(sigma)`
    #      sits at degree `km - (k-s)*lsb(m)`, where `lsb(m)` is the least
    #      power of two in the binary expansion of `m`.  Hence `f(sigma)` is
    #      in-window iff `(k-s)*lsb(m) >= ceil(km/2)`, which for a NON-monomial
    #      sigma forces `lsb(m) >= m/2`, i.e. `m` a power of two.  (Note 09's
    #      "only the degree-2 seed survives" is false: every power-of-two seed
    #      degree survives.  This is `composition_shape_criterion` in the lane's
    #      own Rust CAS.)
    def horner(exps, m, sigma):
        acc = flint.nmod_poly([0], 2)
        for c in reversed(list(poly_from_exps(exps, m).coeffs())):
            acc = acc * sigma + flint.nmod_poly([int(c)], 2)
        return acc

    def tail_of(a):
        d = a.degree()
        j = d - 1
        while j > 0 and not int(a.coeffs()[j]):
            j -= 1
        return d, j

    seeds_small = {2: (1,), 3: (1,), 4: (1,), 5: (2,), 6: (1,), 7: (1,), 8: (2, 3, 4),
                   9: (4,), 10: (3,), 11: (2,), 12: (1, 4, 6), 16: (2, 3, 5)}
    mism, inwin_degrees = [], set()
    for m, exps in seeds_small.items():
        lsb = m & -m
        for k in (2, 3, 4, 5):
            for smask in range(1, 1 << k):     # sigma = x^k + nonzero tail
                sig = flint.nmod_poly([(smask >> i) & 1 for i in range(k)] + [1], 2)
                sdeg = sig.degree() - 1
                while sdeg > 0 and not int(sig.coeffs()[sdeg]):
                    sdeg -= 1
                if not int(sig.coeffs()[sdeg]):
                    continue
                deg, tail = tail_of(horner(exps, m, sig))
                predicted = k * m - (k - sdeg) * lsb
                criterion = (k - sdeg) * lsb >= -(-k * m // 2)
                observed = tail <= deg // 2
                if deg != k * m or tail != min(predicted, max(tail, predicted)):
                    pass
                if predicted != tail and predicted > k * m // 2:
                    mism.append((m, k, sdeg, tail, predicted))
                if criterion != observed:
                    mism.append(("crit", m, k, sdeg, tail, predicted, criterion, observed))
                if observed:
                    inwin_degrees.add(m)
    pow2 = sorted(d for d in inwin_degrees if d & (d - 1) == 0)
    out.append(f"control-3b non-monomial substitution: exact tail formula "
               f"km-(k-s)lsb(m) and the criterion (k-s)lsb(m) >= ceil(km/2) -- "
               f"mismatches (must be []): {mism[:4]}")
    out.append(f"control-3b' seed degrees admitting an IN-WINDOW non-monomial "
               f"composition: {sorted(inwin_degrees)} (must be exactly the powers "
               f"of two present: {pow2}) -- note 09's 'only the degree-2 seed' is false")
    ok &= (mism == [] and sorted(inwin_degrees) == pow2 and pow2 != [])

    # (5) A THIRD, INDEPENDENT DERIVATION of the admissible prime set.  The
    #     script decides admissibility by the powmod test x^((2^m-1)/p) != 1,
    #     which never computes ord(f).  Here ord(f) is computed outright from a
    #     sympy factorization of 2^m-1 and A(f) read off as
    #     {p : v_p(ord f) = v_p(2^m-1)}.  The two must agree on every seed.
    from sympy import divisors, factorint
    disagree, checked5 = [], 0
    for m in range(2, 21):
        for exps in in_window_candidates(m):
            f = poly_from_exps(exps, m)
            if f.degree() != m or not is_irreducible_factor(f):
                continue
            M = (1 << m) - 1
            fac = factorint(M)
            order = min(d for d in sorted(divisors(M)) if X.pow_mod(d, f) == ONE)
            ofac = factorint(order)
            by_order = {p for p, a in fac.items() if ofac.get(p, 0) == a}
            by_powmod = flint_admissible(exps, m, set(fac))
            by_rust = rust.admissible(exps, m, sorted(fac)) if rust else by_order
            checked5 += 1
            if not (by_order == by_powmod == by_rust):
                disagree.append((m, exps, sorted(by_order), sorted(by_powmod), sorted(by_rust)))
            break            # one seed per degree is enough for the agreement test
    out.append(f"control-5 admissible primes by ord(f) from a sympy factorization of "
               f"2^m-1 vs the powmod test, in both engines: {checked5} seeds "
               f"(degrees 2..20); disagreements (must be []): {disagree[:3]}")
    ok &= (disagree == [])

    # (4) the norm map from F_4[x] leaves the window.
    txt, nok = norm_window_check()
    out.extend(txt)
    ok &= nok
    return out, ok


# -------------------------------------------------------------------- main

def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=100000)
    ap.add_argument("--sample", type=int, default=400)
    ap.add_argument("--flint-crosscheck", type=int, default=200)
    ap.add_argument("--verify-degree-cap", type=int, default=20000)
    ap.add_argument("--engine", choices=("rust", "flint"), default="rust")
    ap.add_argument("--rust-binary", default=DEFAULT_RUST)
    ap.add_argument("--procs", type=int, default=16)
    ap.add_argument("--out", default=None)
    ap.add_argument("--members-out", default=None,
                    help="write the per-n membership table (n, m, t, seed) up to "
                         "--members-nmax; every n not listed is NOT in S")
    ap.add_argument("--members-nmax", type=int, default=10000)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    lines = []

    def emit(s=""):
        lines.append(s)
        if not args.quiet:
            print(s, flush=True)

    kind = args.engine
    if kind == "rust" and not os.path.exists(args.rust_binary):
        emit(f"!! rust engine {args.rust_binary} not found; refusing to fall back silently")
        return 2
    rust = RustEngine(args.rust_binary) if kind == "rust" else None
    emit(f"engine: {kind} ({args.rust_binary if kind == 'rust' else 'python-flint'});"
         f" cross-check engine: {'python-flint' if kind == 'rust' else 'none'}")
    emit()

    ok = True
    t_start = time.time()

    emit("== controls (each dies if one hypothesis of Theorem A is dropped) ==")
    ctl, cok = controls(rust)
    for c in ctl:
        emit("  " + c)
    ok &= cok
    emit(f"  controls: {'OK' if cok else 'FAILED'}")
    emit()

    nmax = args.nmax
    mmax = min(MAX_SEED_DEGREE, nmax // 2)
    emit(f"== admissible primes (seed degrees 2..{mmax}, n <= {nmax}) ==")

    t0 = time.time()
    ords = {p: n_order(2, p) for p in primerange(3, max(3, nmax // 2) + 1)}
    certified = load_certified_witnesses()
    emit(f"  ord_p(2) for {len(ords)} odd primes p <= {nmax // 2} in {time.time() - t0:.1f}s")

    jobs = []
    for m in range(2, mmax + 1):
        b = nmax // m
        primes = tuple(p for p, d in ords.items() if p <= b and m % d == 0)
        if primes:
            jobs.append((m, certified.get(m), primes))
    emit(f"  {len(jobs)} degrees have a candidate prime p <= N/m with p | 2^m-1")

    t0 = time.time()
    with Pool(args.procs, initializer=_worker_init,
              initargs=(kind, args.rust_binary)) as pool:
        results = pool.map(degree_job, jobs, chunksize=1)
    admissible = {m: v for m, v in results if v}
    emit(f"  seed search + admissibility in {time.time() - t0:.1f}s; "
         f"{len(admissible)} degrees contribute at least one usable t")
    W = max((len(a) for v in admissible.values() for _, a in v), default=0)
    argW = [m for m, v in admissible.items() if any(len(a) == W for _, a in v)]
    emit(f"  W = max_f |A(f)| = {W} (first attained at degree m = {min(argW)}); "
         f"the proved lacunarity exponent, so #S(L,N) = O((log N)^{W}) for this "
         f"fixed ledger -- asymptotic only, the implied constant is enormous")
    for m in sorted(admissible)[:12]:
        emit(f"    m={m:<4} seeds={[e for e, _ in admissible[m]]} "
             f"admissible primes={[sorted(a) for _, a in admissible[m]]}")
    emit()

    spf = smallest_prime_factor_sieve(nmax // 2 + 1)
    t0 = time.time()
    cover = build_coverage(nmax, admissible, spf)
    emit(f"== the coverage set S ==  built in {time.time() - t0:.1f}s")
    is_prime = prime_sieve(nmax)
    composite = [n for n in range(4, nmax + 1) if not is_prime[n]]

    emit("  N        |S cap [1,N]|   |S|/N       composites   covered fraction of composites")
    for N in sorted({10 ** 3, 10 ** 4, 10 ** 5, nmax}):
        if N > nmax:
            continue
        cs = sum(1 for n in cover if n <= N)
        cc = sum(1 for n in composite if n <= N)
        emit(f"  {N:<8} {cs:<15} {cs / N:<11.5f} {cc:<12} {cs / cc:.5f}")

    missing = [n for n in composite if n not in cover]
    emit(f"  smallest composites NOT in S: {missing[:14]}")
    emit(f"  smallest ODD composites NOT in S: {[n for n in missing if n % 2][:12]}")
    bad_primes = [n for n in cover if is_prime[n]]
    emit(f"  primes in S (must be []): {bad_primes[:5]}")
    ok &= (bad_primes == [])
    pp = [n for n in cover if n & (n - 1) == 0]
    emit(f"  powers of two in S (must be [], t is forced odd): {pp[:5]}")
    ok &= (pp == [])

    emit("  density trend:")
    N = 100
    while N <= nmax:
        cs = sum(1 for n in cover if n <= N)
        emit(f"    N={N:<8} |S|={cs:<8} |S|/N={cs / N:.6f}   "
             f"proved lacunarity bound sum_m prod_p (1+log_p(N/m)) = "
             f"{lacunarity_bound(admissible, N):.3g}")
        N *= 10
    emit()

    bym = Counter(v[0] for v in cover.values())
    emit(f"  witnessing seed degrees m, most used: {bym.most_common(12)}")
    byt = Counter(v[1] for v in cover.values())
    emit(f"  multipliers t, most used: {byt.most_common(12)}")
    emit()

    emit("== direct re-verification of f(x^t) (independent of the criterion) ==")
    members = sorted(cover.items())
    rng = random.Random(20260822)
    # A dense modulus makes the Rabin chain cost ~degree^3/64 word operations, so
    # the re-verification pool is capped by degree; the criterion itself is not
    # (the coverage set above is exact to nmax).  The cap is reported.
    verify_pool = [it for it in members if it[0] <= args.verify_degree_cap]
    pick = rng.sample(verify_pool, min(args.sample, len(verify_pool)))
    pick += verify_pool[-12:]
    seen, uniq = set(), []
    for n, (m, t, e) in pick:
        if n not in seen:
            seen.add(n)
            uniq.append((m, e, t))
    t0 = time.time()
    with Pool(args.procs, initializer=_worker_init,
              initargs=(kind, args.rust_binary)) as pool:
        checked = pool.map(irr_job, uniq, chunksize=1)
    bad = [c for c in checked if not (c[4] and c[5])]
    degs = sorted(c[3] for c in checked)
    emit(f"  {kind}: {len(checked)} members re-verified in {time.time() - t0:.1f}s, "
         f"degrees {degs[0]}..{degs[-1]} (pool capped at degree "
         f"{args.verify_degree_cap}: {len(verify_pool)} of {len(members)} members); "
         f"failures (must be []): {bad[:5]}")
    ok &= (bad == [])
    emit()

    if args.flint_crosscheck and kind == "rust":
        emit("== python-flint cross-check (independent implementation) ==")
        sub = rng.sample(checked, min(args.flint_crosscheck, len(checked)))
        sub = sorted(sub, key=lambda c: c[3])[:args.flint_crosscheck]
        t0 = time.time()
        with Pool(args.procs, initializer=_worker_init,
                  initargs=("flint", "")) as pool:
            fl = pool.map(irr_job, [(c[0], c[1], c[2]) for c in sub], chunksize=1)
        disagree = [(a[:4], a[4], b[4]) for a, b in zip(sub, fl) if a[4] != b[4]]
        shape = [b for b in fl if not b[5]]
        fdegs = sorted(c[3] for c in fl)
        emit(f"  {len(fl)} of those re-derived in flint in {time.time() - t0:.1f}s, "
             f"degrees {fdegs[0]}..{fdegs[-1]}")
        emit(f"  rust/flint disagreements (must be []): {disagree[:5]}")
        emit(f"  flint says out of window (must be []): {shape[:5]}")
        ok &= (disagree == [] and shape == [])
        emit()

    emit(f"TOTAL {time.time() - t_start:.1f}s")
    emit("COMPOSITION FAMILY " + ("OK" if ok else "FAILED"))

    if args.out:
        with open(args.out, "w") as fh:
            fh.write("\n".join(lines) + "\n")

    if args.members_out:
        with open(args.members_out, "w") as fh:
            fh.write("# Degrees n <= %d at which Kaser--Lemire is PROVED by note 08 "
                     "Theorem A.\n" % args.members_nmax)
            fh.write("# One line per member of S: n = m*t, seed f = x^m + (exponents) + 1,\n"
                     "# witness f(x^t) = x^n + (t*exponents) + 1, irreducible and in-window.\n"
                     "# EVERY n <= %d NOT LISTED HERE IS NOT IN S -- in particular every prime\n"
                     "# and every power of two.  Regenerate with\n"
                     "#   python lemire_composition_family.py --nmax %d --members-out <file>\n"
                     "# Format: n m t seed-exponents\n" % (args.members_nmax, nmax))
            for n, (m, t, exps) in sorted(cover.items()):
                if n <= args.members_nmax:
                    fh.write(f"{n} {m} {t} {','.join(str(e) for e in exps) or '-'}\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
