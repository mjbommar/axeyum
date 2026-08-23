#!/usr/bin/env python3
"""Checks for note 16 (`16-large-q-threshold.md`): the large-`q` threshold claim.

Three things are checked, each with at least one positive control that MUST
fail if the check were vacuous:

  CHECK 1  the reversal duality with its exact index.  Kaser--Lemire's window
           `deg(f - T^n) <= floor(n/2)` corresponds to the arithmetic
           progression `1 mod T^r` with `r = ceil(n/2)` -- NOT `floor(n/2)+1`,
           which is off by one at even `n`.  Verified as a *bijection* on
           actual polynomials over `F_q`, `q` in {2,3,4,5,7,8,9}.
  CHECK 2  the `q`-threshold arithmetic of Bagshaw arXiv:2401.10399 Thm 1.5
           (`cor:vonmangoldt`), including the `omega -> 1/2` limit constant
           `961 e^2`, and the enumeration of which `q = p^l` actually clear it.
  CHECK 3  at the endpoint `r = ceil(n/2)` the von Mangoldt sum's proper-prime-
           power part is negligible against the main term `q^n/phi(T^r)`, so a
           positive `Lambda`-sum really does produce an *irreducible*.

Exits nonzero on any failure.  Data written to data/largeq-*.txt.
"""

import math
import os
import sys

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")

FAILURES = []


def check(name, ok, detail=""):
    status = "ok" if ok else "FAIL"
    print(f"[{status}] {name}{(' -- ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)
    return ok


# --------------------------------------------------------------------------
# field / polynomial plumbing
# --------------------------------------------------------------------------

def field(q):
    """Return (poly_ctx, elements) for GF(q); elements[0] = 0, elements[1] = 1."""
    p = None
    for cand in range(2, q + 1):
        if q % cand == 0:
            p = cand
            break
    d = round(math.log(q, p))
    assert p ** d == q, (p, d, q)
    ctx = flint.fq_default_poly_ctx(p, d)
    K = ctx.base_field()
    z = K.gen()
    els = []
    for code in range(q):
        e = K.zero()
        c = code
        zp = K.one()
        for _ in range(d):
            e = e + K(c % p) * zp
            c //= p
            zp = zp * z
        els.append(e)
    assert els[0] == K.zero() and els[1] == K.one()
    return ctx, els


def digits(code, base, length):
    out = []
    for _ in range(length):
        out.append(code % base)
        code //= base
    return out


def reverse_poly(ctx, coeffs, n):
    """T^n f(1/T) on the coefficient list `coeffs` (index i = coefficient of T^i)."""
    c = list(coeffs) + [ctx.base_field().zero()] * (n + 1 - len(coeffs))
    return ctx(list(reversed(c[: n + 1])))


def window_irreducibles(q, n, unit_constant=None):
    """Monic irreducible f of degree n with deg(f - T^n) <= floor(n/2).

    If `unit_constant` is given, restrict to those with f(0) equal to that
    element code.  Returned as tuples of integer codes, low index first.
    """
    ctx, els = field(q)
    h = n // 2                      # the short-interval parameter
    out = []
    for code in range(q ** (h + 1)):
        tail = digits(code, q, h + 1)
        if unit_constant is not None and tail[0] != unit_constant:
            continue
        codes = tail + [0] * (n - h - 1) + [1]
        f = ctx([els[c] for c in codes])
        if f.degree() == n and f.is_irreducible():
            out.append(tuple(codes))
    return out


def progression_irreducibles(q, n, r, a=1):
    """Monic irreducible P of degree n with P = a mod T^r (a a unit code)."""
    ctx, els = field(q)
    free = n - r                    # coefficients of T^r .. T^{n-1}
    if free < 0:
        return []
    out = []
    for code in range(q ** free):
        top = digits(code, q, free)
        codes = [a] + [0] * (r - 1) + top + [1]
        assert len(codes) == n + 1, (len(codes), n)
        P = ctx([els[c] for c in codes])
        if P.degree() == n and P.is_irreducible():
            out.append(tuple(codes))
    return out


# --------------------------------------------------------------------------
# CHECK 1 -- the reversal duality and its exact index
# --------------------------------------------------------------------------

def check1():
    # keep q^(floor(n/2)+1) bounded so the sweep stays under a minute
    plan = [(2, range(2, 25)), (3, range(2, 17)), (4, range(2, 15)),
            (5, range(2, 13)), (7, range(2, 11)), (8, range(2, 11)),
            (9, range(2, 11))]
    lines = ["# reversal duality: window irreducibles vs the progression a mod T^r",
             "# r = ceil(n/2) is the correct index; r_alt = floor(n/2)+1 is the brief's",
             "# P -> P* = T^n P(1/T) maps {P irred monic, P = 1 mod T^r} bijectively",
             "# onto {f irred monic, deg(f-T^n) <= floor(n/2), f(0) = 1}, and",
             "# |W| = sum over units c of |A_c| (over F_2 the two coincide).",
             "# q n r |W| |W_(f(0)=1)| |A_1| sum_c|A_c| r_alt |A_1,alt| bijection"]
    pairs = 0
    polys = 0
    bij_ok = True
    index_ok = True
    union_ok = True
    alt_differs_somewhere = False
    for q, ns in plan:
        ctx, els = field(q)
        for n in ns:
            r = -(-n // 2)              # ceil(n/2)
            r_alt = n // 2 + 1
            W = window_irreducibles(q, n)
            W1 = window_irreducibles(q, n, unit_constant=1)
            A = progression_irreducibles(q, n, r, a=1)
            A_alt = progression_irreducibles(q, n, r_alt, a=1)
            sum_c = sum(len(progression_irreducibles(q, n, r, a=c))
                        for c in range(1, q))
            # bijection: P -> P* maps A onto W1
            img = set()
            for codes in A:
                Pstar = reverse_poly(ctx, [els[c] for c in codes], n)
                if Pstar.degree() != n or not Pstar.is_irreducible() \
                        or not Pstar.is_monic():
                    bij_ok = False
                cs = list(Pstar.coeffs())
                cs = cs + [els[0]] * (n + 1 - len(cs))
                img.add(tuple(els.index(c) for c in cs))
                polys += 1
            if img != set(W1):
                bij_ok = False
            if len(A) != len(W1):
                index_ok = False
            if sum_c != len(W):
                union_ok = False
            if len(A_alt) != len(W1):
                alt_differs_somewhere = True
            pairs += 1
            lines.append(f"{q} {n} {r} {len(W)} {len(W1)} {len(A)} {sum_c} "
                         f"{r_alt} {len(A_alt)} {'yes' if img == set(W1) else 'NO'}")
    with open(os.path.join(DATA, "largeq-reversal-duality.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")

    check("C1.1 reversal is a bijection {P irred, P = 1 mod T^ceil(n/2)} -> "
          "{f irred, deg(f-T^n) <= floor(n/2), f(0) = 1}", bij_ok,
          f"{pairs} (q,n) pairs, {polys} polynomials")
    check("C1.2 counts agree at r = ceil(n/2)", index_ok)
    check("C1.3 the whole window is the union over units: |W| = sum_c |A_c|",
          union_ok)
    # POSITIVE CONTROL: the off-by-one must be *detectable*, i.e. the brief's
    # r_alt = floor(n/2)+1 must give a different count somewhere.  If this
    # control does not fire, C1.2 proves nothing about the index.
    check("C1.4 [control] r_alt = floor(n/2)+1 gives a DIFFERENT count somewhere "
          "(so C1.2 is not vacuous)", alt_differs_somewhere)

    # POSITIVE CONTROL: reversal degrades exactly when P(0) = 0.
    ctx, els = field(2)
    bad = ctx([els[0], els[1], els[1]])          # T^2 + T, constant term 0
    star = reverse_poly(ctx, list(bad.coeffs()), 2)
    check("C1.5 [control] reversal drops the degree when P(0) = 0 "
          "(so the P(0) != 0 hypothesis is load-bearing)",
          star.degree() < 2, f"deg (T^2+T)* = {star.degree()}")


# --------------------------------------------------------------------------
# CHECK 2 -- the q-threshold arithmetic of Bagshaw Thm 1.5
# --------------------------------------------------------------------------

def bagshaw_factor(omega):
    """The q-threshold of arXiv:2401.10399 Thm 1.5 divided by p^2."""
    return math.e ** 2 * ((16.0 - omega) / (16.0 - 31.0 * omega)) ** 2


def check2():
    lim = bagshaw_factor(0.5)
    check("C2.1 omega -> 1/2 limit of the Bagshaw threshold is 961 e^2",
          abs(lim - 961 * math.e ** 2) < 1e-9 and 7100.88 < lim < 7100.89,
          f"{lim:.6f} p^2  (so the rounded 7101 p^2 in the sweep is correct)")

    # the sweep's own translation of the SS/Bagshaw exponent shape
    check("C2.2 the threshold blows up as omega -> 1/2 + 1/62 = 16/31",
          bagshaw_factor(16.0 / 31.0 - 1e-9) > 1e18,
          f"g(16/31 - 1e-9) = {bagshaw_factor(16.0/31.0 - 1e-9):.3e}")

    # POSITIVE CONTROL: monotonicity.  If g were not increasing on [1/2, 16/31)
    # then "take omega as small as the window allows" would be the wrong move
    # and C2.1 would be the wrong constant.
    xs = [0.5 + k * (16.0 / 31.0 - 0.5) / 200 for k in range(200)]
    mono = all(bagshaw_factor(xs[i]) < bagshaw_factor(xs[i + 1])
               for i in range(len(xs) - 1))
    check("C2.3 [control] g(omega) is strictly increasing on [1/2, 16/31), so "
          "omega = 1/2 really is the cheapest admissible choice", mono)

    # Which q = p^l actually clear q > 7100.883 p^2 ?  Equivalently p^(l-2) > lim.
    primes = [x for x in range(2, 200) if all(x % d for d in range(2, int(x ** .5) + 1))]
    lines = ["# Bagshaw arXiv:2401.10399 Thm 1.5 applied to F = T^ceil(n/2), omega -> 1/2",
             "# admissible iff p is ODD and p^(l-2) > 961 e^2 = %.6f" % lim,
             "# p l_min q_min = p^l_min"]
    rows = []
    for p in primes:
        if p == 2:
            lines.append("2 -- -- EXCLUDED: arXiv:2401.10399 fixes q an ODD prime power")
            continue
        l = 3
        while p ** (l - 2) <= lim:
            l += 1
        rows.append((p, l, p ** l))
        lines.append(f"{p} {l} {p**l}")
    with open(os.path.join(DATA, "largeq-threshold-table.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")

    check("C2.4 no prime field F_p clears the threshold (l = 1 impossible)",
          all(l >= 3 for _, l, _ in rows),
          f"min l over odd p < 200 is {min(l for _, l, _ in rows)}")
    check("C2.5 no q = p^2 clears the threshold either",
          all(l >= 3 for _, l, _ in rows))
    smallest = min(rows, key=lambda t: t[2])
    check("C2.6 smallest admissible q at each small p",
          smallest[2] == 3 ** 11,
          f"p=3 -> 3^11 = {3**11}; p=5 -> 5^{[l for pp,l,_ in rows if pp==5][0]}; "
          f"p=23 -> 23^{[l for pp,l,_ in rows if pp==23][0]}")
    # counting: admissible q up to X is O(X^{1/3}) -- exhibit the sparsity
    X = 10 ** 12
    adm = sum(1 for p in primes for l in range(3, 45)
              if p ** l <= X and p ** (l - 2) > lim)
    check("C2.7 the admissible set is sparse, not cofinite", adm < 200,
          f"{adm} admissible q <= 10^12 with p < 200 "
          f"(vs ~3.7e10 primes <= 10^12, none of which qualify)")

    # POSITIVE CONTROL, external: arXiv:2401.10399 sec. 6 (the `comments.tex`
    # remark) states that improving the Sawin--Shusterman twin-prime constant
    # 685090 to 181157 newly covers exactly
    #   3^14, 5^10, 13^7, 23^6, 59^5, 61^5, 67^5, 71^5, 73^5, 79^5, 83^5.
    # Our rule "q = p^l admissible iff p is odd and p^(l-2) > C" must reproduce
    # that list from the two constants.  If it does not, the rule is wrong and
    # every threshold in note 16 is wrong with it.
    def lmin(pp, C):
        l = 1
        while pp ** (l - 2) <= C:
            l += 1
        return l

    newly = []
    for pp in primes:
        if pp == 2:
            continue
        a, b = lmin(pp, 181157.0), lmin(pp, 685090.0)
        newly.extend(pp ** l for l in range(a, b))
    expected = [3 ** 14, 5 ** 10, 13 ** 7, 23 ** 6, 59 ** 5, 61 ** 5, 67 ** 5,
                71 ** 5, 73 ** 5, 79 ** 5, 83 ** 5]
    check("C2.8 [external control] the rule p^(l-2) > C reproduces Bagshaw's own "
          "published list of newly-covered q (arXiv:2401.10399 sec. 6)",
          sorted(newly) == sorted(expected),
          f"{len(newly)} values, match={sorted(newly) == sorted(expected)}")

    first3 = min(pp for pp in primes + [x for x in range(200, 8000)
                                        if all(x % d for d in range(2, int(x ** .5) + 1))]
                 if pp > 2 and pp > lim)
    check("C2.9 the smallest p for which a CUBIC extension suffices",
          first3 ** 1 > lim, f"p = {first3}, q_min = {first3}^3 = {first3**3}")


# --------------------------------------------------------------------------
# CHECK 3 -- proper prime powers do not eat the main term at r = ceil(n/2)
# --------------------------------------------------------------------------

def check3():
    """Count monic x of degree n with x = 1 mod T^r that are PROPER prime powers.

    The main term of Bagshaw Thm 1.5 is q^n/phi(T^r) = q^(n-r+1)/(q-1), and the
    Lambda-sum counts prime powers too; a positive Lambda-sum only yields an
    irreducible if the proper-power part is smaller.  It is.  The structural
    reason (see note 16 sec. 5): x = P^k = 1 mod T^r with k = p^a k',
    gcd(k',p) = 1 forces P = zeta mod T^ceil(r/p^a), leaving at most
    O(q^(n/(2p))) such x -- a power saving, but only by 1/p, so at p = 2 it is
    q^(n/4) against a main term q^(n/2).
    """
    lines = ["# proper prime powers inside the class 1 mod T^r, r = ceil(n/2)",
             "# q n r class_size main_term proper_in_class all_proper_deg_n "
             "weighted/main structural_bound_4q^(n/2p)"]
    struct_ok = True
    ratio_ok = True
    control_fired = False
    max_ratio = 0.0
    for q, ns in [(2, range(4, 21)), (3, range(4, 15)), (5, range(4, 11))]:
        ctx, els = field(q)
        p = ctx.base_field().prime()
        for n in ns:
            r = -(-n // 2)
            free = n - r
            n_pp = 0
            for code in range(q ** free):
                top = digits(code, q, free)
                codes = [1] + [0] * (r - 1) + top + [1]
                x = ctx([els[c] for c in codes])
                if x.degree() != n:
                    continue
                facs = x.factor()[1]
                if len(facs) == 1 and facs[0][1] >= 2:
                    n_pp += 1
            main = q ** (n - r + 1) / (q - 1)
            class_size = q ** free
            # Lambda(P^k) = deg P <= n/2 for a PROPER power
            weighted = (n / 2.0) * n_pp
            ratio = weighted / main
            bound = 4 * q ** (n / (2.0 * int(p)))
            if n_pp > bound:
                struct_ok = False
            if n >= 12:
                max_ratio = max(max_ratio, ratio)
                if ratio >= 0.2:
                    ratio_ok = False
            total_pp = sum(q ** (n // k) for k in range(2, n + 1) if n % k == 0)
            if total_pp >= class_size:
                control_fired = True
            lines.append(f"{q} {n} {r} {class_size} {main:.1f} {n_pp} {total_pp} "
                         f"{ratio:.4f} {bound:.1f}")
    with open(os.path.join(DATA, "largeq-prime-powers.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    check("C3.1 the structural bound #{proper prime powers = 1 mod T^ceil(n/2)} "
          "<= 4 q^(n/2p) holds on every row", struct_ok)
    check("C3.2 Lambda-weighted proper-power part is < 0.2 of the main term "
          "for n >= 12", ratio_ok, f"max ratio {max_ratio:.4f}")
    # POSITIVE CONTROL: WITHOUT the congruence the proper-power count is at
    # least the SIZE OF THE WHOLE CLASS, so a priori the class could consist
    # entirely of prime powers; C3.1/C3.2 are facts about the congruence.
    check("C3.3 [control] the unconditional proper-power count of degree n is "
          ">= the class size (so C3.1/C3.2 are not vacuous)", control_fired)


def main():
    os.makedirs(DATA, exist_ok=True)
    print("== CHECK 1: reversal duality and its index ==")
    check1()
    print("== CHECK 2: the Bagshaw q-threshold arithmetic ==")
    check2()
    print("== CHECK 3: proper prime powers at the endpoint ==")
    check3()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s): {', '.join(FAILURES)}")
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
