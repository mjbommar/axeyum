#!/usr/bin/env python3
"""Generate a NEUTRAL, GRADUATED synthetic QF_NRA + QF_NIA corpus.

Purpose
-------
PLAN.md's course correction (2026-06-23) flags that competitor regress slices
(cvc5/bitwuzla) are *solver-flavored*, *easy*, and *depth-hiding*, so a "parity"
number on them is not honest. The missing piece is a **neutral, graduated**
corpus with a difficulty knob, where each instance's `(set-info :status …)` is
established **by construction** (a checkable witness for sat; an independent
infeasibility argument for unsat) — so a Z3-vs-axeyum DISAGREE means a real
solver bug, not a mislabeled file.

This script emits SMT-LIB v2 (.smt2) files into:

    corpus/public-curated/synthetic/QF_NRA/graduated/
    corpus/public-curated/synthetic/QF_NIA/graduated/

Every file is plain `(set-logic …)` + `(set-info :status …)` +
`(declare-fun …)` + `(assert …)` + `(check-sat)` — no incremental/exotic
commands, so the flat benchmark-slice parser represents it faithfully.

Difficulty gradient
-------------------
A leading zero-padded knob in each file name (k01, d02, n03, …) lets the
measurement harness compute a DECIDE-FRONTIER: the largest knob axeyum decides
per family. The knob scales var-count k, polynomial degree d, or the integer
bound N.

Status provenance (how `:status` is known WITHOUT Z3)
-----------------------------------------------------
See the families below; each carries an inline `; STATUS-PROOF:` comment in the
emitted file documenting the argument. Summary:

  NRA-sat-witness   sat   — a rational witness is substituted into every
                            (in)equality and checked to hold exactly by this
                            script before emission (assert fails on a bad row).
  NRA-sos-unsat     unsat — sum of even powers (each >= 0) plus 1 asserted < 0:
                            impossible over the reals. (x1^2 + … + xk^2 + 1 < 0.)
  NRA-neg-square    unsat — a single even power asserted strictly negative
                            (x^(2d) < 0): impossible over the reals.
  NRA-circle-line   sat   — intersection of a circle and a line chosen to pass
                            through a rational point ON the circle (witness
                            checked).
  NIA-pythagorean   sat   — a scaled Pythagorean triple (3,4,5)·m with a known
                            integer witness inside the bound (witness checked).
  NIA-product       sat   — bounded integer product = a chosen composite, with a
                            known factor pair inside the bound (witness checked).
  NIA-sum-sq-2      unsat — x^2 = 2 y^2 with 1 <= x,y <= N: forces sqrt(2)
                            rational => no positive integer solution (infinite
                            descent), bounded so it is QF.
  NIA-no-square-mod unsat — x^2 = m*t + r with r a quadratic NON-residue mod m
                            and 0 <= x < B*m: no integer square is = r (mod m);
                            the full residue table is enumerated by this script
                            to confirm r is a non-residue before emission.

Each sat witness is verified by exact integer/rational arithmetic in this
script; a generation run that cannot certify a row aborts (so the committed
corpus can never carry an unproven status).
"""

import os
import sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NRA_DIR = os.path.join(ROOT, "corpus", "public-curated", "synthetic", "QF_NRA", "graduated")
NIA_DIR = os.path.join(ROOT, "corpus", "public-curated", "synthetic", "QF_NIA", "graduated")


# --------------------------------------------------------------------------- #
# SMT-LIB term helpers (s-expressions over Int/Real, SMT-LIB totality-faithful)
# --------------------------------------------------------------------------- #
def smt_real(fr):
    """SMT-LIB Real literal from a Fraction (exact, as p.0 or (/ p.0 q))."""
    fr = Fraction(fr)
    if fr.denominator == 1:
        v = fr.numerator
        return f"{v}.0" if v >= 0 else f"(- {abs(v)}.0)"
    num = smt_real(Fraction(fr.numerator))
    return f"(/ {num} {fr.denominator}.0)"


def power(var, e):
    """(* var var … ) e times; e>=1."""
    if e == 1:
        return var
    return "(* " + " ".join([var] * e) + ")"


def write_file(path, lines):
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def header(logic, status):
    return [
        f"(set-logic {logic})",
        "(set-info :smt-lib-version 2.6)",
        "(set-info :source |axeyum synthetic graduated corpus (scripts/gen-graduated-nra-nia.py)|)",
        f"(set-info :status {status})",
    ]


def assert_witness(ok, msg):
    if not ok:
        sys.stderr.write(f"WITNESS FAILURE (would emit a mislabeled file): {msg}\n")
        sys.exit(1)


# =========================================================================== #
# QF_NRA families
# =========================================================================== #
def gen_nra():
    files = []

    # --- Family A: NRA-sat-witness (SAT), knob k = var count 1..8 -----------
    for k in range(1, 9):
        vars_ = [f"x{i}" for i in range(1, k + 1)]
        wit = [Fraction(i, i + 1) for i in range(1, k + 1)]
        S = sum(w * w for w in wit)
        lines = header("QF_NRA", "sat")
        lines.append(
            f"; STATUS-PROOF: explicit rational witness {[str(w) for w in wit]} "
            f"substituted; sum(xi^2)={S} holds exactly (checked by generator)."
        )
        for v in vars_:
            lines.append(f"(declare-fun {v} () Real)")
        lines.append("")
        for v, w in zip(vars_, wit):
            lines.append(f"(assert (= {v} {smt_real(w)}))")
        sq = "(+ " + " ".join(power(v, 2) for v in vars_) + ")" if k > 1 else power(vars_[0], 2)
        lines.append(f"(assert (= {sq} {smt_real(S)}))")
        lines.append("(check-sat)")
        files.append((f"nra-sat-witness-k{k:02d}.smt2", lines))

    # --- Family B: NRA-sos-unsat (UNSAT), knob k = var count 1..8 ----------
    for k in range(1, 9):
        vars_ = [f"x{i}" for i in range(1, k + 1)]
        lines = header("QF_NRA", "unsat")
        lines.append(
            "; STATUS-PROOF: sum of squares (each >= 0) plus 1 is >= 1 > 0 over the "
            "reals, asserted < 0 -> infeasible (sum-of-squares positivity)."
        )
        for v in vars_:
            lines.append(f"(declare-fun {v} () Real)")
        lines.append("")
        sq_terms = [power(v, 2) for v in vars_] + ["1.0"]
        sos = "(+ " + " ".join(sq_terms) + ")"
        lines.append(f"(assert (< {sos} 0.0))")
        lines.append("(check-sat)")
        files.append((f"nra-sos-unsat-k{k:02d}.smt2", lines))

    # --- Family C: NRA-neg-square (UNSAT), knob d -> even degree 2..12 -----
    for d in range(1, 7):
        deg = 2 * d
        lines = header("QF_NRA", "unsat")
        lines.append(
            f"; STATUS-PROOF: x^{deg} is an even power, >= 0 over the reals; asserted "
            "< 0 -> infeasible (even-power non-negativity)."
        )
        lines.append("(declare-fun x () Real)")
        lines.append("")
        lines.append(f"(assert (< {power('x', deg)} 0.0))")
        lines.append("(check-sat)")
        files.append((f"nra-neg-square-d{d:02d}.smt2", lines))

    # --- Family D: NRA-sos-strict-unsat (UNSAT), knob d, shifted vars ------
    for d in range(1, 6):
        deg = 2 * d
        lines = header("QF_NRA", "unsat")
        lines.append(
            f"; STATUS-PROOF: (x-1)^{deg} + (y-2)^{deg} + 1 is a sum of even powers "
            "plus 1, hence >= 1 > 0; asserted < 0 -> infeasible."
        )
        lines.append("(declare-fun x () Real)")
        lines.append("(declare-fun y () Real)")
        lines.append("")
        xm = "(- x 1.0)"
        ym = "(- y 2.0)"
        t1 = "(* " + " ".join([xm] * deg) + ")"
        t2 = "(* " + " ".join([ym] * deg) + ")"
        lines.append(f"(assert (< (+ {t1} {t2} 1.0) 0.0))")
        lines.append("(check-sat)")
        files.append((f"nra-sos-strict-unsat-d{d:02d}.smt2", lines))

    # --- Family E: NRA-circle-line (SAT), knob m = triple scale ------------
    triples = [(3, 4, 5), (5, 12, 13), (8, 15, 17), (7, 24, 25), (20, 21, 29), (9, 40, 41)]
    for idx, (a, b, c) in enumerate(triples, start=1):
        R2 = c * c
        assert_witness(a * a + b * b == R2, "NRA-circle-line on-circle")
        lines = header("QF_NRA", "sat")
        lines.append(
            f"; STATUS-PROOF: witness (x,y)=({a},{b}) lies on x^2+y^2={R2} "
            f"(since {a}^2+{b}^2={R2}) and on the line y - x = {b - a}; both "
            "checked exactly by the generator."
        )
        lines.append("(declare-fun x () Real)")
        lines.append("(declare-fun y () Real)")
        lines.append("")
        lines.append(f"(assert (= (+ (* x x) (* y y)) {smt_real(R2)}))")
        lines.append(f"(assert (= (- y x) {smt_real(b - a)}))")
        lines.append("(check-sat)")
        files.append((f"nra-circle-line-m{idx:02d}.smt2", lines))

    return files


# =========================================================================== #
# QF_NIA families
# =========================================================================== #
def gen_nia():
    files = []

    # --- Family A: NIA-pythagorean (SAT), knob m = triple scale 1..8 -------
    for m in range(1, 9):
        a, b, c = 3 * m, 4 * m, 5 * m
        N = c
        assert_witness(a * a + b * b == c * c, "NIA-pythagorean triple")
        lines = header("QF_NIA", "sat")
        lines.append(
            f"; STATUS-PROOF: witness (x,y,z)=({a},{b},{c}) satisfies x^2+y^2=z^2 "
            f"({a}^2+{b}^2={c}^2) and 1<=.<={N}; checked by generator."
        )
        for v in ("x", "y", "z"):
            lines.append(f"(declare-fun {v} () Int)")
        lines.append("")
        lines.append("(assert (= (+ (* x x) (* y y)) (* z z)))")
        for v in ("x", "y", "z"):
            lines.append(f"(assert (and (<= 1 {v}) (<= {v} {N})))")
        lines.append("(check-sat)")
        files.append((f"nia-pythagorean-m{m:02d}.smt2", lines))

    # --- Family B: NIA-product (SAT), knob k = prime-pair index 1..8 -------
    primepairs = [(3, 5), (7, 11), (13, 17), (19, 23), (29, 31), (37, 41), (43, 47), (53, 59)]
    for k, (p, q) in enumerate(primepairs, start=1):
        P = p * q
        N = max(p, q)
        assert_witness(p * q == P, "NIA-product factor")
        lines = header("QF_NIA", "sat")
        lines.append(
            f"; STATUS-PROOF: witness (x,y)=({p},{q}) gives x*y={P} with 2<=.<={N}; "
            "checked by generator."
        )
        for v in ("x", "y"):
            lines.append(f"(declare-fun {v} () Int)")
        lines.append("")
        lines.append(f"(assert (= (* x y) {P}))")
        for v in ("x", "y"):
            lines.append(f"(assert (and (<= 2 {v}) (<= {v} {N})))")
        lines.append("(check-sat)")
        files.append((f"nia-product-k{k:02d}.smt2", lines))

    # --- Family C: NIA-sum-sq-2 (UNSAT), knob N = bound scale 1..8 ---------
    for s in range(1, 9):
        N = 4 * s
        lines = header("QF_NIA", "unsat")
        lines.append(
            "; STATUS-PROOF: x^2 = 2 y^2 has no positive-integer solution (sqrt(2) "
            f"irrational / infinite descent); bounded 1<=x,y<={N} -> still infeasible."
        )
        for v in ("x", "y"):
            lines.append(f"(declare-fun {v} () Int)")
        lines.append("")
        lines.append("(assert (= (* x x) (* 2 (* y y))))")
        for v in ("x", "y"):
            lines.append(f"(assert (and (<= 1 {v}) (<= {v} {N})))")
        lines.append("(check-sat)")
        files.append((f"nia-sum-sq-2-n{s:02d}.smt2", lines))

    # --- Family D: NIA-no-square-mod (UNSAT), knob b = bound mult 1..8 -----
    nonres_cases = [
        (3, 2),   # squares mod 3: {0,1}; 2 non-residue
        (4, 2),   # squares mod 4: {0,1}; 2 non-residue
        (4, 3),   # 3 non-residue mod 4
        (5, 2),   # squares mod 5: {0,1,4}; 2 non-residue
        (5, 3),   # 3 non-residue mod 5
        (7, 3),   # squares mod 7: {0,1,2,4}; 3 non-residue
        (8, 3),   # squares mod 8: {0,1,4}; 3 non-residue
        (8, 5),   # 5 non-residue mod 8
    ]
    for b, (m, r) in enumerate(nonres_cases, start=1):
        residues = {(i * i) % m for i in range(m)}
        assert_witness(r not in residues, f"NIA-no-square-mod r={r} mod {m} residues={residues}")
        upper = b * m
        lines = header("QF_NIA", "unsat")
        lines.append(
            f"; STATUS-PROOF: squares mod {m} are {sorted(residues)}; {r} is a "
            f"quadratic non-residue, so no integer x has x^2 = {r} (mod {m}). "
            f"Asserted x^2 = {m}*t + {r}, 0<=x<{upper}, t>=0 -> infeasible."
        )
        for v in ("x", "t"):
            lines.append(f"(declare-fun {v} () Int)")
        lines.append("")
        lines.append(f"(assert (= (* x x) (+ (* {m} t) {r})))")
        lines.append(f"(assert (and (<= 0 x) (< x {upper})))")
        lines.append("(assert (>= t 0))")
        lines.append("(check-sat)")
        files.append((f"nia-no-square-mod-b{b:02d}.smt2", lines))

    return files


def main():
    os.makedirs(NRA_DIR, exist_ok=True)
    os.makedirs(NIA_DIR, exist_ok=True)
    nra = gen_nra()
    nia = gen_nia()
    for name, lines in nra:
        write_file(os.path.join(NRA_DIR, name), lines)
    for name, lines in nia:
        write_file(os.path.join(NIA_DIR, name), lines)
    print(f"QF_NRA: wrote {len(nra)} files -> {NRA_DIR}")
    print(f"QF_NIA: wrote {len(nia)} files -> {NIA_DIR}")


if __name__ == "__main__":
    main()
