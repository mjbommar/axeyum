#!/usr/bin/env python3
"""Attribute the kernel's declaration surface to the 23 `curriculum.toml` nodes.

WHY THIS EXISTS. `docs/curriculum/curriculum.toml` carries a `status` field
whose vocabulary (`covered` / `planned` / `lean-horizon`) is defined in
`crates/axeyum-scenarios/src/mathtour.rs` as *scenario* coverage -- "has a
self-checking exercise family today". It says nothing about what the Lean-core
kernel has PROVED. Measured 2026-08-31: `calculus` is `lean-horizon` with 349
kernel declarations while `linear-algebra` is `covered` with 25 -- the two
axes disagree in opposite directions, and neither value is wrong on its own
axis. ADR-1075.

WHAT IT MEASURES. Input is the TSV emitted by

    cargo run --release -p axeyum-lean-kernel \
      --example kernel_declaration_projection

whose columns are `prelude<TAB>kind<TAB>name<TAB>...`. A declaration is
attributed to the FIRST prelude group that emits it (the projection is emitted
in prelude build order), so nothing is multiply counted -- `complex` and
`cpoint` re-declare every `CReal` name and an unanchored count comes out 3x.

The projection is the right instrument and the theorem inventories are not:
`prelude_theorem_inventory` filters to `Declaration::Theorem`, so
`CReal.integral`, `Nat.add` and every other `Definition` return ZERO rows from
it. This script reports theorem and definition counts separately for exactly
that reason.

WHAT IT DOES NOT MEASURE. Attribution is by declaration NAME against an
ordered pattern table below, not by source module (the projection does not
carry one). The table is therefore a stated, auditable judgement rather than a
derived fact, and the residual is printed so an unattributed namespace cannot
hide. `--verbose` lists every residual row.

EXIT STATUS DEPENDS ON THE FINDING. `--expect-attributed N` fails when the
attributed total moves, and `--require-node <id>` fails when a named node
attributes zero declarations -- so a run that measured nothing cannot exit 0.
An unknown node id is an error, not a silent zero.

    python3 scripts/measure-curriculum-kernel-coverage.py projection.tsv
    python3 scripts/measure-curriculum-kernel-coverage.py projection.tsv \
      --require-node calculus --require-node number-theory
"""

from __future__ import annotations

import argparse
import collections
import re
import sys

# (node_id, pattern). ORDER MATTERS: the first match wins, so a layer-3 topic
# claims a name before the layer-1 carrier bucket (`reals`, `naturals`) sees
# it. Reordering this list changes the numbers; it is the judgement the
# docstring warns about.
BUCKETS: list[tuple[str, str]] = [
    # layer 3 destinations claim their topic names first
    ("calculus",
     r"^CReal\.(HasDerivative|hasDerivative|deriv|antideriv|integral|"
     r"riemannSum|riemannSample|reblock|mesh|fineBlock|fineSample|"
     r"sample(Lower|Upper|Point)|subdivisionPoint|splitPoint|stepFamily|"
     r"ivt|IVT|evt|Evt|mvt|rolle|fermat|"
     r"sup(On|Seq|Level)|lub|"
     r"Uniform|uniform|Continuous|continuous|"
     r"weierstrass|powerSeries|"
     r"exp|Exp|sin|Sin|cos|Cos|trig|e_|two_le_e|"
     r"sqrt|natSqrt|"
     r"monotone|antitone|strict_|order_reflect|lipschitz|inverse_lipschitz|"
     r"constant_of_zero_deriv|clamp|bucket|crossing|"
     r"sumRange|geom|alternating|series|Series|ratio|Ratio|"
     r"scale_cancel|diff_le_of_strict)"),
    ("sequences-and-limits",
     r"^CReal\.(Converges|Cauchy|converges|cauchy|limit|Limit|"
     r"RegularSeq|scaledCauchy|regular_of_scaled|archimedean|density)"),
    ("complex", r"^(Complex|CPoint)\."),
    # The `.*` alternatives are deliberate: a prefix-only pattern leaves
    # `Nat.exists_prime_gt`, `Nat.pow_prime_modeq_self` and
    # `Nat.least_residue_ne_zero_of_coprime` to fall through to the `naturals`
    # carrier bucket, which understates the destination it is measuring.
    ("number-theory",
     r"^(Nat|Int)\.(prime|Prime|totient|fib|Fib|fastFib|perfect|Perfect|"
     r"Squarefree|squarefree|wilson|Wilson|euler|Euler|"
     r"sumOfDivisors|sumDivisors|sigma|nth|minFac|factorization|"
     r"legendre|quadratic|sum_two_squares|"
     r"exists_prime|pow_prime|not_prime|succ_pred_prime|"
     r"dvd_of_forall_prime|coprime_fermatNumber|least_divisor|least_residue|"
     r"pow_mul_prime|pow_two_ne_pow_two_mul_prime|pow_of_pow_add_prime|"
     r"self_inverse_mod_prime|factorial_interior_modeq|factorial_sq_modeq|"
     r"add_pow_modeq_prime|gauss_fold_injective)"),
    # NOT `matrix|determinant|eigen`. That pattern returns ZERO, and the zero
    # is an artefact of the query: this kernel spells its linear algebra
    # `Rat.det2` / `Rat.det3` / `Rat.dotN` (a vector is a finite function plus
    # a dimension, since there is no `List` or product type). A `--name-like
    # matrix` probe reports ABSENT and is correct and useless -- the exact
    # empty-grep-as-negative-result trap. `docs/curriculum/03-destinations/
    # linear-algebra.md` had `det2`/`det3`/`dotN` on 2026-08-30 and this
    # script's first draft did not read it -- and that page in turn says the
    # matrix layer is unbuilt, which was true when written and is not now
    # (`Rat.matMul`, `matMul_assoc`, `matTranspose_mul` are all landed).
    # Two readers, two stale negatives, same direction. Re-measure.
    ("linear-algebra",
     r"^Rat\.(det2|det3|dotN|mat(Id|Mul|Transpose)|cramer|inv2_|mul_adj2_)"),
    # layer 2 structures
    ("divisibility-and-euclid",
     r"^(Nat|Int)\.(gcd|Gcd|lcm|dvd|Dvd|bezout|Bezout|xgcd|"
     r"coprime|Coprime|IsRelPrime|relPrime|euclid|gauss_lemma|"
     r"natAbs_dvd|dvd_)"),
    ("modular-arithmetic",
     r"^(Nat|Int)\.(mod|Mod|modeq|ModEq|crt|Crt|inverseIndex|"
     r"emod|residue|congr_mod)"),
    ("groups",
     r"^Nat\.(isGroupOn|modAdd_isGroup|symmetric_group|group_|perm|Perm|"
     r"bijective_on_perm)"),
    ("polynomials", r"^(Rat|CReal|Int)\.(poly|Poly)"),
    ("counting",
     r"^Nat\.(choose|Choose|factorial|Factorial|ascFactorial|descFactorial|"
     r"multichoose|pigeonhole|prodRange|sumRange|catalan)"),
    ("rings", r"^\x00NO_ABSTRACT_RING_CARRIER$"),
    ("fields", r"^\x00NO_ABSTRACT_FIELD_CARRIER$"),
    # layer 0 foundations -- MUST precede the carrier buckets below
    ("relations-and-functions",
     r"^Nat\.(injectiveOn|injectiveOnP|surjectiveOn|bijectiveOn|"
     r"injective_|surjective_|bijective_|Pair|Fin|restrict_)"),
    ("cardinality", r"^Nat\.countRange"),
    ("sets", r"^Nat\.(Subset|subset_)"),
    ("induction", r"^(Acc|WellFounded)|^Nat\.(Peano|base_induction|strong)"),
    # layer 1 number systems
    ("reals", r"^CReal"),
    ("rationals", r"^Rat\."),
    ("integers", r"^Int\."),
    ("naturals", r"^Nat($|\.)"),
    # remaining layer 0
    ("predicate-logic", r"^Exists"),
    ("propositional-logic",
     r"^(And|Or|Iff|Not|True|False|Bool|Decidable|Eq|absurd|mt|"
     r"noncontradiction|not_not|demorgan|dne_of_em|em_of|peirce|congrFun)"),
]

# Every node id in `docs/curriculum/curriculum.toml`, in layer order. A node
# absent from BUCKETS attributes zero and is reported as such.
NODES = [
    "propositional-logic", "predicate-logic", "proof-methods", "induction",
    "sets", "relations-and-functions", "cardinality",
    "naturals", "integers", "rationals", "reals", "complex",
    "divisibility-and-euclid", "modular-arithmetic", "groups", "rings",
    "fields", "polynomials", "sequences-and-limits", "counting",
    "number-theory", "linear-algebra", "calculus",
]


def load(path: str) -> dict[str, tuple[str, str]]:
    rows: dict[str, tuple[str, str]] = {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            fields = line.rstrip("\n").split("\t")
            if len(fields) < 3:
                continue
            prelude, kind, name = fields[0], fields[1], fields[2]
            rows.setdefault(name, (prelude, kind))
    if not rows:
        sys.exit(f"error: {path} yielded zero declarations -- wrong file?")
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("projection", help="kernel_declaration_projection TSV")
    ap.add_argument("--verbose", action="store_true",
                    help="list every unattributed declaration")
    ap.add_argument("--expect-attributed", type=int, default=None,
                    help="fail unless exactly this many declarations attribute")
    ap.add_argument("--require-node", action="append", default=[],
                    help="fail unless this node attributes at least one "
                         "declaration (repeatable)")
    args = ap.parse_args()

    unknown = [n for n in args.require_node if n not in NODES]
    if unknown:
        sys.exit(f"error: --require-node names no curriculum node: {unknown}")

    rows = load(args.projection)
    compiled = [(nid, re.compile(pat)) for nid, pat in BUCKETS]
    counts: dict[str, collections.Counter] = collections.defaultdict(
        collections.Counter)
    residual: list[tuple[str, str, str]] = []
    for name, (prelude, kind) in sorted(rows.items()):
        for nid, rx in compiled:
            if rx.match(name):
                counts[nid][kind] += 1
                counts[nid]["_total"] += 1
                break
        else:
            residual.append((name, prelude, kind))

    print(f"{'node':26} {'total':>6} {'theorem':>8} {'definition':>11}")
    for nid in NODES:
        c = counts[nid]
        print(f"{nid:26} {c['_total']:>6} {c['theorem']:>8} "
              f"{c['definition']:>11}")
    attributed = sum(counts[n]["_total"] for n in NODES)
    print()
    print(f"declarations={len(rows)} attributed={attributed} "
          f"residual={len(residual)}")
    if args.verbose:
        for name, prelude, kind in residual:
            print(f"  residual {prelude}\t{kind}\t{name}")

    status = 0
    if args.expect_attributed is not None and attributed != args.expect_attributed:
        print(f"FAIL: expected {args.expect_attributed} attributed, "
              f"got {attributed}", file=sys.stderr)
        status = 1
    for nid in args.require_node:
        if counts[nid]["_total"] == 0:
            print(f"FAIL: --require-node {nid} attributed zero declarations",
                  file=sys.stderr)
            status = 1
    return status


if __name__ == "__main__":
    raise SystemExit(main())
