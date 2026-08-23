"""Savings-as-a-dial: the (HWO_k) ladder for Kaser--Lemire over F_2.

Companion checker for `docs/research/10-cas/lemire-signed-trace/18-savings-scale.md`.

The chain of note 01 / the public roadmap states one open estimate as a THRESHOLD
(`prove the factor 4 ell`).  It is really a DIAL: a uniform saving of a factor `F`
over the Weil bound for the whole non-trivial character family of `E_l` yields an
irreducible of degree `n` with `deg(f - x^n) <= floor(n/2) + k`, where `k = ell - l`
and `k` is determined by `F` through the exact criterion

    crit(F, n, l):   F * (2^{n/2} - 2^{l - n/2} Theta^+(n,l))  >  D(l),
    D(l) = sum_{j=1}^{l} (j-1) 2^{j-1} = (l-2) 2^l + 2,

with `Theta^+(n,l)` a rigorous upper bound on the proper-prime-power Lambda-mass in
the identity class of `E_l`.  Everything is tested in exact integer / Fraction
arithmetic (the criterion is squared to remove the irrational `2^{n/2}`).

Checks, all exact and all fatal:

  C1  closed forms          D(m), |E_l[2]| = 2^{l - floor(l/2)}, h_{j,s}
  C2  F = 1 is Gao 2021     the criterion at F = 1 is EXACTLY Gao arXiv:2109.14154
                            Thm 1(b) positivity, and is never weaker than the
                            Hsu 1996 / Cohen 2005 `(l+1)` form
  C3  k = 0 is Kaser--Lemire   F_req(0) = (ell-2)/kappa + o(1), kappa = 2^{n/2-ell},
                            and the roadmap's `4 ell` is a factor 4*kappa stronger
  C4  dumps: k works        at l = ell - k_Weil the exact dump has N_l(1) > Theta,
                            and an irreducible is exhibited in the window
  C5  dumps: k is tight     at k = k_Weil - 1 the F = 1 criterion FAILS
  C6  B1 low-order layers   characters of conductor j and order <= Q are a
                            2^{-floor(j/Q)} fraction; free saving < 1 + 1e-6
  C7  B2 small conductors   Phi(a) is increasing in a, so the W-split only costs;
                            and the j <= 3 layers provably saturate Weil
  C8  B4 aggregate          measured sum_{j,s}|T_{j,s}| clears F_req(0) at every
                            computed endpoint while the worst PER-PAIR layer does not
  C9  B5 trivial crossover  the population route loses to Weil at every layer
  C10 Barrier I ceiling     the moduli-only fake population exists for every
                            k < k_Weil (at most one exception per endpoint)
  C11 Theta bound           Theta^+ >= exact Theta on every computed row, and
                            Theta = 1 exactly at odd n

Usage:
    python3 lemire_savings_scale.py                  # run all checks off committed data
    python3 lemire_savings_scale.py --regenerate     # recompute the data from dumps
    python3 lemire_savings_scale.py --controls       # mutation controls
    python3 lemire_savings_scale.py --mutate <NAME>  # run one mutant (internal)

Exit status is nonzero on any failed check.
"""
from __future__ import annotations

import argparse
import math
import os
import subprocess
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
SNAPSHOT = os.environ.get(
    "AXEYUM_LEMIRE_SNAPSHOT", "/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440"
)
DUMPER = os.path.join(SNAPSHOT, "target", "release", "axeyum-gf2-dump-populations")
TABLE_CELLS = "1300000000"

MUTANT = os.environ.get("LEMIRE_SAVINGS_MUTANT", "")

FAILURES: list[str] = []


def require(name: str, condition: bool, detail: str = "") -> None:
    if not condition:
        FAILURES.append(f"{name}: {detail}")
        print(f"  FAIL {name} {detail}")


# --------------------------------------------------------------------------
# closed forms
# --------------------------------------------------------------------------
def D(m: int) -> int:
    """sum_{j=1}^{m} (j-1) 2^{j-1}: the exact total L-degree of the non-trivial
    characters of E_m over F_2 (conductor j has 2^{j-1} characters of L-degree j-1)."""
    if m < 1:
        return 0
    return (m - 2) * 2**m + 2


def D_by_sum(m: int) -> int:
    return sum((j - 1) << (j - 1) for j in range(1, m + 1))


def two_torsion(l: int) -> int:
    """|E_l[2]| = 2^{l - floor(l/2)}: u^2 = 1 mod x^{l+1} iff u = 1 mod x^{floor(l/2)+1}."""
    return 1 << (l - l // 2)


def hjs(j: int, s: int) -> int:
    """number of characters of E_j of order dividing 2^s."""
    return (1 << (j - (j >> s))) if s >= 0 else 0


def ek(j: int, k: int) -> int:
    e = 0
    while k << e <= j:
        e += 1
    return e


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def v2(r: int) -> int:
    v = 0
    while r % 2 == 0:
        r //= 2
        v += 1
    return v


# --------------------------------------------------------------------------
# the dictionary
# --------------------------------------------------------------------------
def theta_plus(n: int, l: int) -> int:
    """Rigorous upper bound on the proper-prime-power Lambda-mass in the identity
    class of E_l, for monic F of degree n.  Requires 3l >= n.

    F = P^r with r | n, r >= 2, deg P = n/r, and <F>_l = <P>_l^r.  For odd r the
    condition forces <P>_l = 1, hence P = x^{n/r} (not irreducible unless n/r = 1),
    so odd r contributes nothing once l >= n/3.  For r = 2^v r' (r' odd) it is
    <P>_l in E_l[2^v] = ker(E_l -> E_{floor(l/2^v)}), i.e. <P>_{floor(l/2^v)} = 1,
    and the Lambda-mass of degree n/r in one class of E_j is at most
    2^{n/r - j} + j 2^{ceil(n/(2r))} by orthogonality plus Weil."""
    assert 3 * l >= n, (n, l)
    if n % 2 == 1:
        return 1
    total = 0
    for r in divisors(n):
        if r < 2 or r % 2 == 1:
            continue
        m = n // r
        j = l >> v2(r)
        total += (1 << max(0, m - j)) + j * (1 << ((m + 1) // 2))
    return total


def crit(F, n: int, l: int) -> bool:
    """Exact test of  F * (2^{n/2} - 2^{l-n/2} Theta^+) > D(l).

    Multiply by 2^{n/2} > 0:  F * (2^n - 2^l Theta^+) > D(l) * 2^{n/2}; both sides
    are positive once the first factor is, so squaring is an equivalence."""
    F = Fraction(F)
    slack = 2**n - (1 << l) * theta_plus(n, l)
    if slack <= 0 or F <= 0:
        return False
    return F * F * Fraction(slack) ** 2 > Fraction(D(l)) ** 2 * Fraction(2**n)


def k_min(F, n: int, ell: int) -> int | None:
    """smallest window slack k = ell - l for which a saving F suffices."""
    for k in range(0, 200):
        l = ell - k
        if 3 * l < n:
            return None
        if crit(F, n, l):
            return k
    return None


def F_req(n: int, l: int) -> float:
    """the saving needed at level l, as a float (display only)."""
    slack = 2**n - (1 << l) * theta_plus(n, l)
    if slack <= 0:
        return math.inf
    return 2.0 ** (log2_int(D(l)) + n / 2 - log2_int(slack))


def log2_int(x) -> float:
    if isinstance(x, Fraction):
        return log2_int(x.numerator) - log2_int(x.denominator)
    b = x.bit_length()
    return math.log2(x) if b <= 900 else (b - 900) + math.log2(x >> (b - 900))


def gao_correction(n: int, l: int) -> int:
    """Gao arXiv:2109.14154 Thm 1(b)'s `|{eps^{1/2}}| [2 | d]` term at eps = identity.
    It is exactly |E_l[2]| for even n and absent for odd n, and it is exactly the
    proper-prime-power correction: 2^l Theta^+(n,l) ~ 2^{n/2} |E_l[2]|."""
    if n % 2 == 1 or MUTANT == "M2":
        return 0
    return two_torsion(l)


def gao_positive(n: int, l: int) -> bool:
    """Gao arXiv:2109.14154 Thm 1(b) at q = 2, t = 0, epsilon = identity:
    the count is positive as soon as 2^{n/2} > D + |{eps^{1/2}}| [2 | n],
    with D = sum_{chi != 1} deg L(chi) = D(l) and |{1^{1/2}}| = |E_l[2]|.
    (Gao's extra + e_1(q,d) |E| q^{d/2}/d term is nonnegative and dropped.)"""
    rhs = D(l) + gao_correction(n, l)
    return 2**n > rhs * rhs


def cohen_positive(n: int, l: int) -> bool:
    """Cohen 2005 Thm 2.1 / Hsu 1996: I >= q^{n-l}/n - (l+1) q^{n/2}/n."""
    return 2**n > ((l + 1) << l) ** 2


def kappa(n: int, ell: int) -> float:
    return 2.0 ** (n / 2 - ell)


# --------------------------------------------------------------------------
# data file I/O
# --------------------------------------------------------------------------
def read_rows(path: str) -> list[dict]:
    rows = []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            row = {}
            for item in line.split("|"):
                key, _, value = item.partition("=")
                row[key] = value
            rows.append(row)
    return rows


def ints(text: str) -> list[int]:
    return [int(v) for v in text.split(",")] if text else []


# --------------------------------------------------------------------------
# regeneration from exact population dumps
# --------------------------------------------------------------------------
def dump_path(scratch: str, ell: int, n: int) -> str:
    path = os.path.join(scratch, f"ell{ell}-n{n}.txt")
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        if not os.path.exists(DUMPER):
            raise SystemExit(f"missing dumper {DUMPER}; set AXEYUM_LEMIRE_SNAPSHOT")
        with open(path, "w") as fh:
            # the third argument (max_table_cells) is REQUIRED: without it the
            # binary panics and leaves a zero-byte file behind.
            subprocess.run(
                [DUMPER, str(ell), str(n), TABLE_CELLS], stdout=fh, check=True
            )
        if os.path.getsize(path) == 0:
            raise SystemExit(f"zero-byte dump {path}")
    return path


def regenerate(scratch: str, endpoints: list[tuple[int, int]]) -> None:
    sys.path.insert(0, HERE)
    import numpy as np  # noqa: F401
    from lemire_layers import load_dump, level_populations, subgroup_mask

    out = [
        "# exact layer aggregates from axeyum-gf2-dump-populations (branch CAS), one row per endpoint",
        "# Nl1 = N_j(1) for j = 0..ell; aggabs = sum over ALL (j,s) layers of |T_{j,s}|;",
        "# worst_pair_num/den = the layer maximising |T|/(#X (j-1) 2^{n/2}); theta = exact",
        "# proper-prime-power Lambda-mass in the identity class of E_ell.",
    ]
    for ell, n in endpoints:
        path = dump_path(scratch, ell, n)
        ell_, n_, factors, counts = load_dump(path)
        assert (ell_, n_) == (ell, n)
        levels = {j: level_populations(ell, counts, j) for j in range(0, ell + 1)}
        nl1 = [int(levels[j][1][0]) for j in range(0, ell + 1)]
        aggabs = 0
        worst = None
        for j in range(1, ell + 1):
            fj, Nj = levels[j]
            fj1, Nj1 = levels[j - 1]
            smax = ek(j, 1)
            P = {s: int(Nj[subgroup_mask(fj, s)].sum()) for s in range(0, smax + 1)}
            P1 = {s: int(Nj1[subgroup_mask(fj1, s)].sum()) for s in range(0, smax + 1)}
            for s in range(1, smax + 1):
                X = (hjs(j, s) - hjs(j, s - 1)) - (hjs(j - 1, s) - hjs(j - 1, s - 1))
                if X <= 0:
                    continue
                T = (
                    hjs(j, s) * P[s]
                    - hjs(j, s - 1) * P[s - 1]
                    - hjs(j - 1, s) * P1[s]
                    + hjs(j - 1, s - 1) * P1[s - 1]
                )
                aggabs += abs(T)
                if j >= 2 and T != 0:
                    key = Fraction(abs(T), X * (j - 1))
                    if worst is None or key > worst[0]:
                        worst = (key, j, s)
        theta = exact_theta(n, ell)
        out.append(
            f"ell={ell}|n={n}|Nl1={','.join(str(v) for v in nl1)}|aggabs={aggabs}"
            f"|worst_num={worst[0].numerator}|worst_den={worst[0].denominator}"
            f"|worst_j={worst[1]}|worst_s={worst[2]}|theta={theta}"
        )
        print(f"  regenerated ell={ell} n={n}")
    with open(os.path.join(DATA, "savings-layer-aggregates.txt"), "w") as fh:
        fh.write("\n".join(out) + "\n")


def exact_theta(n: int, l: int, maxdeg: int = 19) -> int | None:
    """exact proper-prime-power Lambda-mass in the identity class of E_l (small n only)."""
    try:
        import flint
    except ImportError:
        return None
    total = 0
    for r in divisors(n):
        if r < 2:
            continue
        m = n // r
        if m > maxdeg:
            return None
        for v in range(1 << m):
            coeffs = [(v >> i) & 1 for i in range(m)] + [1]
            factorisation = flint.nmod_poly(coeffs, 2).factor()
            if len(factorisation[1]) != 1 or factorisation[1][0][1] != 1:
                continue
            if class_pow(reversed_class(v, m, l), r, l) == tuple([0] * l):
                total += m
    return total


def reversed_class(poly: int, deg: int, l: int) -> tuple:
    """<P>_l for P = x^deg + sum_{i<deg} b_i x^i, as (c_1, ..., c_l)."""
    return tuple(
        ((poly >> (deg - t)) & 1) if 1 <= t <= deg else 0 for t in range(1, l + 1)
    )


def class_mul(a: tuple, b: tuple, l: int) -> tuple:
    A = [1] + list(a)
    B = [1] + list(b)
    C = [0] * (l + 1)
    for i in range(l + 1):
        if A[i]:
            for j in range(l + 1 - i):
                C[i + j] ^= B[j]
    return tuple(C[1:])


def class_pow(a: tuple, e: int, l: int) -> tuple:
    result = tuple([0] * l)
    base = a
    while e:
        if e & 1:
            result = class_mul(result, base, l)
        base = class_mul(base, base, l)
        e >>= 1
    return result


def window_irreducible(n: int, l: int) -> int | None:
    """exhibit a monic irreducible f of degree n with <f>_l = 1, i.e.
    deg(f - x^n) <= n - l - 1.  Returns the tail as an integer, or None."""
    try:
        import flint
    except ImportError:
        return None
    top = 1 << (n - l)
    for tail in range(top):
        coeffs = [(tail >> i) & 1 for i in range(n - l)] + [0] * l + [1]
        factorisation = flint.nmod_poly(coeffs, 2).factor()
        if len(factorisation[1]) == 1 and factorisation[1][0][1] == 1:
            return tail
    return None


# --------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------
ENDPOINTS = [(ell, n) for ell in range(8, 19) for n in (2 * ell + 1, 2 * ell + 2)]
LARGE = [12, 16, 20, 24, 50, 100, 200, 512, 1024]


def check_closed_forms() -> None:
    print("C1 closed forms")
    for m in [1, 2, 3, 5, 10, 24, 64, 200]:
        require("C1", D(m) == D_by_sum(m), f"D({m})={D(m)} vs {D_by_sum(m)}")
    for l in [1, 2, 7, 8, 12, 13]:
        brute = sum(
            1
            for c in range(1 << l)
            if class_pow(tuple((c >> i) & 1 for i in range(l)), 2, l) == tuple([0] * l)
        )
        require("C1", two_torsion(l) == brute, f"|E_{l}[2]|={two_torsion(l)} vs {brute}")
    for j in (5, 9, 12):
        for s in range(0, 5):
            brute = sum(
                1
                for c in range(1 << j)
                if class_pow(tuple((c >> i) & 1 for i in range(j)), 1 << s, j)
                == tuple([0] * j)
            )
            require("C1", hjs(j, s) == brute, f"h_{{{j},{s}}}={hjs(j,s)} vs {brute}")


def check_F1_is_literature() -> None:
    print("C2 F = 1 reproduces Gao 2021 Thm 1(b) exactly and is never weaker than Cohen 2005")
    for ell in LARGE:
        for n in (2 * ell + 1, 2 * ell + 2):
            for k in range(0, 14):
                l = ell - k
                if 3 * l < n:
                    break
                require(
                    "C2",
                    crit(1, n, l) == gao_positive(n, l),
                    f"ell={ell} n={n} l={l}: crit={crit(1,n,l)} gao={gao_positive(n,l)}",
                )
                if cohen_positive(n, l):
                    require(
                        "C2",
                        crit(1, n, l),
                        f"ell={ell} n={n} l={l}: Cohen positive but our criterion is not",
                    )
                # our Theta^+ correction IS Gao's |{eps^{1/2}}| term: the r = 2
                # summand of theta_plus is 2^{n/2 - floor(l/2)}, and
                # 2^l * 2^{n/2 - floor(l/2)} = 2^{n/2} * |E_l[2]| identically.
                if n % 2 == 0:
                    main = 1 << (n // 2 - l // 2)
                    require(
                        "C2",
                        (1 << l) * main == (1 << (n // 2)) * gao_correction(n, l),
                        f"ell={ell} n={n} l={l}: our main proper-power term is not Gao's "
                        f"|E_l[2]| ({(1<<l)*main} vs {(1 << (n//2)) * gao_correction(n,l)})",
                    )
                    require(
                        "C2",
                        theta_plus(n, l) >= main,
                        f"ell={ell} n={n} l={l}: theta_plus below its own main term",
                    )
                else:
                    require(
                        "C2",
                        gao_correction(n, l) == 0 and (1 << (2 * l)) < 2**n,
                        f"ell={ell} n={n} l={l}: odd-n correction is not the single term x^n",
                    )


def check_k0_is_lemire(report: list[str]) -> None:
    print("C3 k = 0 is Kaser--Lemire; F_req(0) = (ell-2)/kappa; roadmap 4 ell is 4 kappa stronger")
    report.append("# C3: the k=0 requirement against the roadmap's (HWO) constant 4 ell")
    report.append("# ell|n|F_req(0)|(ell-2)/kappa|4*ell|ratio")
    for ell in LARGE:
        for n in (2 * ell + 1, 2 * ell + 2):
            f0 = F_req(n, ell)
            predicted = (ell - 2) / (1.0 if MUTANT == "M6" else kappa(n, ell))
            # F_req(0) = (ell-2)/kappa * (1 + O(2^{-ell/2})): never below, and
            # within 1e-4 relative once ell >= 50.
            require("C3", f0 >= predicted * (1 - 1e-9), f"ell={ell} n={n}: F_req(0)={f0} < {predicted}")
            tolerance = 1e-4 if ell >= 50 else 0.10
            require(
                "C3",
                abs(f0 - predicted) <= tolerance * predicted,
                f"ell={ell} n={n}: F_req(0)={f0} vs (ell-2)/kappa={predicted}",
            )
            ratio = 4 * ell / f0
            target = 4 * kappa(n, ell)
            require(
                "C3",
                0.95 * target <= ratio <= 1.30 * target,
                f"ell={ell} n={n}: 4ell/F_req(0)={ratio} vs 4 kappa={target}",
            )
            require("C3", not crit(1, n, ell), f"ell={ell} n={n}: Weil alone would give k=0")
            require("C3", crit(Fraction(4 * ell), n, ell), f"ell={ell} n={n}: 4 ell insufficient")
            report.append(f"{ell}|{n}|{f0:.4f}|{predicted:.4f}|{4*ell}|{ratio:.4f}")
            # the four steps from 4 ell down to F_req(0), and their product
            c = math.ceil(math.log2(ell))
            a = ell - c - 1
            cn = math.ceil(n / 2)
            hi = Fraction(D(ell) - D(a - 1))
            unit = Fraction(2**cn)
            phi_paper = hi / ((Fraction(2 ** (2 * ell)) - unit * Fraction(D(a - 1))) / unit)
            phi_true = hi / (
                (
                    Fraction(2**n)
                    - Fraction(1 << ell) * Fraction(theta_plus(n, ell))
                    - unit * Fraction(D(a - 1))
                )
                / unit
            )
            phi_a4 = Fraction(D(ell) - D(3), Fraction(2**n, 2**cn) - Fraction(D(3)))
            steps = [
                4 * ell / float(phi_paper),
                float(phi_paper / phi_true),
                float(phi_true / phi_a4),
                float(phi_a4) / f0,
            ]
            product = steps[0] * steps[1] * steps[2] * steps[3]
            require(
                "C3",
                abs(product - ratio) <= 1e-6 * ratio,
                f"ell={ell} n={n}: decomposition {product} != 4ell/F_req(0) = {ratio}",
            )
            # steps 1-3 are exact factors >= 1; step 4 is the 2^{ceil(n/2)} -> 2^{n/2}
            # conversion, which is sqrt(2) at odd n and 1 - O(2^{-ell/2}) at even n.
            require(
                "C3",
                all(step >= 1 - 1e-9 for step in steps[:3]) and steps[3] >= 0.9,
                f"ell={ell} n={n}: decomposition steps {steps}",
            )
            report.append(
                f"# decomposition ell={ell} n={n}: 4ell={4*ell} -> {float(phi_paper):.4f}"
                f" -> {float(phi_true):.4f} -> {float(phi_a4):.4f} -> {f0:.4f}"
                f"  (steps {steps[0]:.4f}, {steps[1]:.4f}, {steps[2]:.4f}, {steps[3]:.4f})"
            )


def check_dumps(rows: list[dict], report: list[str]) -> None:
    print("C4/C5/C8/C11 exact dumps")
    report.append("# C4/C5/C8: measured endpoints.  F_agg = 2^{n/2} D(ell) / sum_{j,s}|T_{j,s}|,")
    report.append("# F_pair = the worst single layer.  k_W = k_min(F=1).")
    report.append("# ell|n|k_W|N_l(1) at l=ell-k_W|theta_exact|theta_bound|F_req(0)|F_agg|F_pair|agg_ok|pair_ok")
    for row in rows:
        ell, n = int(row["ell"]), int(row["n"])
        nl1 = ints(row["Nl1"])
        aggabs = int(row["aggabs"])
        worst = Fraction(int(row["worst_num"]), int(row["worst_den"]))
        theta_exact = row["theta"]
        kw = k_min(1, n, ell)
        require("C4", kw is not None, f"ell={ell} n={n}: no Weil k")
        l = ell - kw
        require("C4", 3 * l >= n, f"ell={ell} n={n}: k_Weil={kw} leaves l={l} < n/3")
        if 3 * l < n:
            continue
        # C11: the rigorous bound dominates the exact value, and odd n has Theta = 1
        if theta_exact not in ("", "None"):
            require(
                "C11",
                theta_plus(n, ell) >= int(theta_exact),
                f"ell={ell} n={n}: theta_plus={theta_plus(n,ell)} < exact={theta_exact}",
            )
            if n % 2 == 1:
                require(
                    "C11",
                    int(theta_exact) == 1,
                    f"ell={ell} n={n} odd: exact Theta={theta_exact}, expected 1 (only x^n)",
                )
        # C4: the criterion's conclusion is TRUE in the exact data
        require(
            "C4",
            nl1[l] > theta_plus(n, l),
            f"ell={ell} n={n}: N_{l}(1)={nl1[l]} <= theta_plus={theta_plus(n,l)}",
        )
        # C5: one step better is out of reach for the F = 1 method
        if kw >= 1:
            require(
                "C5",
                not crit(1, n, ell - kw + 1),
                f"ell={ell} n={n}: F=1 already works at k={kw-1}, so k_W is not the threshold",
            )
        # C8: aggregate clears the requirement, worst per-pair does not
        f_agg = 2.0 ** (n / 2 + log2_int(D(ell)) - log2_int(aggabs))
        f_pair = 2.0 ** (n / 2 - log2_int(worst))
        if MUTANT == "M5":
            # control: bound the total by the worst single layer instead of summing
            f_agg = f_pair
        req = F_req(n, ell)
        agg_ok = f_agg >= req
        pair_ok = f_pair >= req
        require("C8", agg_ok, f"ell={ell} n={n}: aggregate F={f_agg} below F_req(0)={req}")
        require(
            "C8",
            not pair_ok,
            f"ell={ell} n={n}: worst per-layer F={f_pair} already clears F_req(0)={req}",
        )
        report.append(
            f"{ell}|{n}|{kw}|{nl1[l]}|{theta_exact}|{theta_plus(n,ell)}|{req:.4f}"
            f"|{f_agg:.4f}|{f_pair:.4f}|{agg_ok}|{pair_ok}"
        )


def check_window_witnesses(rows: list[dict]) -> None:
    print("C4b independent window witnesses (flint)")
    try:
        import flint  # noqa: F401
    except ImportError:
        print("     flint absent; skipped")
        return
    for row in rows:
        ell, n = int(row["ell"]), int(row["n"])
        if ell > 13:
            continue
        kw = k_min(1, n, ell)
        l = ell - kw
        tail = window_irreducible(n, l)
        require(
            "C4",
            tail is not None,
            f"ell={ell} n={n}: no irreducible with deg(f-x^n) <= {n-l-1}",
        )


def check_low_order_layers(report: list[str]) -> None:
    print("C6 B1: the already-proved low-order layers")
    report.append("# C6 (B1): budget share of the layers the chain already pays by Weil (order <= Q)")
    report.append("# ell|c|a|Q|Sigma_low/Sigma_all|F_eff if those layers were free")
    for ell in [24, 50, 100, 200, 512, 1024]:
        c = math.ceil(math.log2(ell))
        a = ell - c - 1
        Q = 1
        while 3 * c * (2 * Q) <= ell:
            Q *= 2
        t = Q.bit_length() - 1
        low = sum((j - 1) * (hjs(j, t) - hjs(j - 1, t)) for j in range(a, ell + 1))
        allc = sum((j - 1) * (1 << (j - 1)) for j in range(a, ell + 1))
        share = Fraction(low, allc)
        gain = 1 / (1 - float(share))
        require("C6", share < Fraction(1, 10**6), f"ell={ell}: low-order share {float(share)}")
        require("C6", gain < 1 + 1e-6, f"ell={ell}: free gain {gain}")
        # and the per-conductor fraction is exactly 2^{-floor(j/Q)} or zero
        for j in range(a, ell + 1):
            Y = hjs(j, t) - hjs(j - 1, t)
            if j % Q == 0:
                require("C6", Y == 0, f"ell={ell} j={j}: expected empty low-order set, got {Y}")
            else:
                expected = 1 << (j - (0 if MUTANT == "M1" else 1) - j // Q)
                require("C6", Y == expected, f"ell={ell} j={j}: Y={Y} != {expected}")
        report.append(f"{ell}|{c}|{a}|{Q}|{float(share):.6e}|{gain:.12f}")


def check_small_conductors(report: list[str]) -> None:
    print("C7 B2: the small-conductor W term")
    report.append("# C7 (B2): the per-pair constant Phi(a) as a function of the split level a")
    report.append("# ell|n|Phi(a=chain)|Phi(a=4)|cost of the chain's split")
    for ell in [24, 50, 100, 200, 512, 1024]:
        for n in (2 * ell + 1, 2 * ell + 2):
            c = math.ceil(math.log2(ell))
            a_chain = ell - c - 1
            cn = math.ceil(n / 2)
            g = Fraction(2**n, 2**cn)

            def Phi(a: int) -> Fraction:
                if MUTANT == "M3":
                    # control: forget that the W-term also eats the budget
                    return Fraction(D(ell) - D(a - 1)) / g
                return Fraction(D(ell) - D(a - 1), g - Fraction(D(a - 1)))

            a_max = max(a for a in range(2, ell) if Fraction(D(a - 1)) < g / 2)
            values = [Phi(a) for a in range(2, a_max + 1)]
            require("C7", a_chain <= a_max, f"ell={ell} n={n}: a_chain={a_chain} > a_max={a_max}")
            require(
                "C7",
                all(values[i] <= values[i + 1] for i in range(len(values) - 1)),
                f"ell={ell} n={n}: Phi(a) is not monotone increasing in a",
            )
            require(
                "C7",
                Phi(a_chain) > Phi(4),
                f"ell={ell} n={n}: the chain's split does not cost",
            )
            report.append(
                f"{ell}|{n}|{float(Phi(a_chain)):.4f}|{float(Phi(4)):.4f}"
                f"|{float(Phi(a_chain)/Phi(4)):.4f}"
            )


def check_small_conductor_saturation(rows: list[dict]) -> None:
    """the j <= 3 layers saturate Weil, which is why a per-pair (HWO_k) needs a > 3."""
    print("C7b small conductors saturate Weil")
    for row in rows:
        ell, n = int(row["ell"]), int(row["n"])
        worst = Fraction(int(row["worst_num"]), int(row["worst_den"]))
        j = int(row["worst_j"])
        require("C7", j <= 3, f"ell={ell} n={n}: worst layer is j={j}, expected j <= 3")
        # The conductor-2 layer is exactly |T_{2,2}| = 2^{n/2+1} |cos(pi n / 4)|:
        # E_2 = Z/4, its two primitive characters have L(u) = 1 - alpha u with
        # alpha = -(1 +- i), so the layer sum is 2 Re(alpha^n).  Hence
        #   |T|/(#X (j-1)) = 2^{n/2}       (4 | n)   -- Weil saturated exactly
        #                  = 2^{(n-1)/2}   (n odd)   -- 1/sqrt(2) of Weil
        #                  = 0             (n = 2 mod 4), and then j = 3 takes over
        #                                   at 2^{n/2-1}, i.e. 1/2 of Weil.
        if n % 2 == 1:
            target, expect_j = Fraction(2 ** ((n - 1) // 2)), 2
        elif n % 4 == 0:
            target, expect_j = Fraction(2 ** (n // 2)), 2
        else:
            target, expect_j = Fraction(2 ** (n // 2 - 1)), 3
        require("C7", worst == target, f"ell={ell} n={n}: worst numerator {worst} != {target}")
        require("C7", j == expect_j, f"ell={ell} n={n}: worst conductor {j} != {expect_j}")


def check_trivial_crossover(report: list[str]) -> None:
    print("C9 B5: the trivial / population route never beats Weil")
    report.append("# C9 (B5): population route cost, (sum of the four h's)/#X, per layer at ell=200")
    report.append("# j|s|log2(#X)|population/Weil")
    worst_ratio = None
    for ell in [200, 1024]:
        c = math.ceil(math.log2(ell))
        a = ell - c - 1
        for j in range(a, ell + 1):
            for s in range(1, ek(j, 1) + 1):
                X = (hjs(j, s) - hjs(j, s - 1)) - (hjs(j - 1, s) - hjs(j - 1, s - 1))
                if X <= 0:
                    continue
                total = (
                    hjs(j, s) - hjs(j, s - 1) - hjs(j - 1, s) + hjs(j - 1, s - 1)
                    if MUTANT == "M7"
                    else hjs(j, s) + hjs(j, s - 1) + hjs(j - 1, s) + hjs(j - 1, s - 1)
                )
                ratio = Fraction(total, X)
                require("C9", ratio > 1, f"ell={ell} j={j} s={s}: population/Weil = {float(ratio)}")
                if worst_ratio is None or ratio < worst_ratio:
                    worst_ratio = ratio
                if ell == 200:
                    report.append(f"{j}|{s}|{log2_int(X):.4f}|{float(ratio):.4f}")
    # the naive trivial bound |S_n| <= 2^n needs j-1 >= 2^{n/2}
    for ell, n in [(24, 50), (200, 402), (1024, 2050)]:
        require(
            "C9",
            (ell - 1) ** 2 < 2**n,
            f"ell={ell} n={n}: trivial bound would beat Weil",
        )
    report.append(f"# best population/Weil ratio over all layers: {float(worst_ratio):.4f} (> 1 = always loses)")


_ASTAR: dict[int, Fraction] = {}


def astar(l: int) -> Fraction:
    """max over the split level a of (a-1)(1 - 2^{a-1-l}): the strongest moduli-only
    fake population that note 03 sec. 5 admits at level l."""
    if l in _ASTAR:
        return _ASTAR[l]
    best = Fraction(0)
    for a in range(max(2, l - 40), l + 1):
        value = Fraction(a - 1) * (Fraction(1) - Fraction(1, 2 ** (l - a + 1)))
        if value > best:
            best = value
    _ASTAR[l] = best
    return best


def barrier_blocks(n: int, l: int) -> bool:
    """the note-03 construction needs c ~ 2^{n-l} <= A*(l) 2^{n/2}, i.e. 2^{n/2-l} <= A*(l).
    Exact: 2^n <= A*^2 4^l."""
    A = astar(l)
    if MUTANT == "M4":
        return Fraction(2**n) >= A * A * Fraction(4**l)
    return Fraction(2**n) <= A * A * Fraction(4**l)


def check_barrier(report: list[str]) -> None:
    print("C10 Barrier I is the moduli-only ceiling")
    report.append("# C10: moduli-only barrier (note 03 sec. 5) vs the Weil threshold")
    report.append("# ell|n|k_Weil|first k not blocked|verdict")
    gaps = 0
    total = 0
    for ell in LARGE + [30, 64, 128, 256]:
        for n in (2 * ell + 1, 2 * ell + 2):
            kw = k_min(1, n, ell)
            kb = None
            for k in range(0, kw + 1):
                if not barrier_blocks(n, ell - k):
                    kb = k
                    break
            total += 1
            require(
                "C10",
                not barrier_blocks(n, ell - kw),
                f"ell={ell} n={n}: barrier still blocks at the Weil level k={kw}",
            )
            require("C10", kb is not None and kb <= kw, f"ell={ell} n={n}: kb={kb} kw={kw}")
            require(
                "C10",
                kw - kb <= 1,
                f"ell={ell} n={n}: barrier ends {kw-kb} steps below the Weil ceiling",
            )
            if kb != kw:
                gaps += 1
            report.append(
                f"{ell}|{n}|{kw}|{kb}|{'MATCH' if kb == kw else 'one-step gap'}"
            )
    report.append(f"# {total - gaps} of {total} endpoints: barrier ceiling == Weil ceiling")


def check_ladder(report: list[str]) -> None:
    print("C3b the ladder table")
    report.append("# the ladder: saving F vs window slack k = ell - l, at ell = 200 and 1024")
    report.append("# ell|n|F|k_min(F)")
    for ell in [200, 1024]:
        for n in (2 * ell + 1, 2 * ell + 2):
            savings = [
                Fraction(1),
                Fraction(2),
                Fraction(4),
                Fraction(8),
                Fraction(math.isqrt(ell - 2)),
                Fraction(ell - 2, 8),
                Fraction(ell - 2, 4),
                Fraction(ell - 2, 2),
                Fraction(ell - 2),
                Fraction(4 * ell),
                Fraction(ell - 2, 2) + Fraction(1, 100),
                Fraction(ell - 2) * Fraction(71, 100),
                Fraction(ell - 2) + Fraction(1, 100),
            ]
            savings = sorted(savings)
            previous = None
            for F in savings:
                k = k_min(F, n, ell)
                require("C3", k is not None, f"ell={ell} n={n} F={F}: no k")
                if previous is not None:
                    require(
                        "C3",
                        k <= previous,
                        f"ell={ell} n={n}: k is not monotone decreasing in F",
                    )
                previous = k
                report.append(f"{ell}|{n}|{float(F):.4f}|{k}")
            # doubling F buys exactly one step of k while k > 0
            for F in [Fraction(1), Fraction(2), Fraction(4)]:
                k1, k2 = k_min(F, n, ell), k_min(2 * F, n, ell)
                require(
                    "C3",
                    k1 - k2 == 1,
                    f"ell={ell} n={n} F={F}: doubling F moved k by {k1-k2}, expected 1",
                )


def check_dictionary_table(report: list[str]) -> None:
    report.append("# the dictionary across ell: k_Weil (this note, = Gao 2021) vs Hsu/Cohen (l+1) form")
    report.append("# ell|n|k_Weil|k_HsuCohen|F_req(0)|F_req(1)|F_req(2)|F_req(3)")
    for ell in LARGE:
        for n in (2 * ell + 1, 2 * ell + 2):
            kw = k_min(1, n, ell)
            khc = next(k for k in range(0, 60) if cohen_positive(n, ell - k))
            require("C2", kw <= khc, f"ell={ell} n={n}: our k={kw} worse than Cohen's {khc}")
            report.append(
                f"{ell}|{n}|{kw}|{khc}|{F_req(n,ell):.4f}|{F_req(n,ell-1):.4f}"
                f"|{F_req(n,ell-2):.4f}|{F_req(n,ell-3):.4f}"
            )


# --------------------------------------------------------------------------
# mutation controls
# --------------------------------------------------------------------------
CONTROLS = {
    "M1": "C6",  # off-by-one in the low-order character count Y_{j,t}
    "M2": "C2",  # drop Gao's even-n |{eps^{1/2}}| correction
    "M3": "C7",  # let the W-term be free instead of eating the budget
    "M4": "C10",  # flip the moduli-only barrier inequality
    "M5": "C8",  # bound the total by the worst single layer instead of summing
    "M6": "C3",  # drop kappa = 2^{n/2-ell} from the k = 0 requirement
    "M7": "C9",  # price the population route at #X instead of the four h's
}


def run_controls() -> int:
    failures = 0
    for mutant, expected in CONTROLS.items():
        environment = dict(os.environ, LEMIRE_SAVINGS_MUTANT=mutant)
        result = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--quiet"],
            env=environment,
            capture_output=True,
            text=True,
        )
        dead = sorted({line.split()[1] for line in result.stdout.splitlines() if line.strip().startswith("FAIL")})
        status = "OK" if dead == [expected] else "BAD"
        if dead != [expected]:
            failures += 1
        print(f"  control {mutant}: expected {expected}, killed {dead or ['(nothing)']}  {status}")
    return failures


# --------------------------------------------------------------------------
def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--regenerate", action="store_true")
    parser.add_argument("--controls", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--scratch", default=os.environ.get("LEMIRE_SCRATCH", "/tmp"))
    parser.add_argument("--skip-witnesses", action="store_true")
    arguments = parser.parse_args()

    if arguments.controls:
        return 1 if run_controls() else 0

    if arguments.regenerate:
        os.makedirs(arguments.scratch, exist_ok=True)
        regenerate(arguments.scratch, ENDPOINTS)

    rows = read_rows(os.path.join(DATA, "savings-layer-aggregates.txt"))

    report: list[str] = []
    check_closed_forms()
    check_F1_is_literature()
    check_k0_is_lemire(report)
    check_ladder(report)
    check_dictionary_table(report)
    check_dumps(rows, report)
    if not arguments.skip_witnesses and not arguments.quiet:
        check_window_witnesses(rows)
    check_low_order_layers(report)
    check_small_conductors(report)
    check_small_conductor_saturation(rows)
    check_trivial_crossover(report)
    check_barrier(report)

    if not MUTANT:
        with open(os.path.join(DATA, "savings-ladder.txt"), "w") as fh:
            fh.write("\n".join(report) + "\n")

    if FAILURES:
        print(f"\n{len(FAILURES)} FAILED check(s)")
        return 1
    if not arguments.quiet:
        print("\nall checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
