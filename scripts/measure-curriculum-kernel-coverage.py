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
    # `probability` (ADR-1082) must precede the generic `rationals` catch-all
    # below, or these 47 `Rat.*` names fall through to it as they did before
    # the node existed.
    ("probability",
     r"^Rat\.(IsDistribution|expectation|Expectation|variance|Variance|"
     r"covariance|Covariance|markov|Markov|chebyshev|Chebyshev|weak_law|"
     r"bernoulli|Bernoulli|uniform|Uniform|indicator|Indicator|prob_|"
     r"sumVars|PairwiseUncorrelated)"),
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
    #
    # ADR-1205: the N11 quadratic-residue / second-supplementary-law cluster
    # (ADR-1130 Gauss's lemma, ADR-1150 the second supplementary law) landed
    # with camelCase names (`gaussLemmaSignCount`, `gaussSignNeg`, `gaussFold`,
    # `gaussNegCount`, ...) and snake_case ones (`gauss_neg_count_*`,
    # `gauss_fold_*`, `gauss_residue_*`), and NONE of the pre-existing
    # alternatives here matched them -- 32 declarations fell through to the
    # `naturals`/`integers` catch-alls, the exact ADR-1140 failure mode
    # recurring on the very rung (N11) that proposal names as the open
    # frontier. `gauss[A-Z]` deliberately does NOT match bare `gauss_lemma`
    # (`Nat.gauss_lemma`/`Int.gauss_lemma` in `lcm.rs` is a DIFFERENT theorem
    # -- the divisibility one, `gcd x y = 1 -> x|yz -> x|z` -- correctly
    # bucketed to `divisibility-and-euclid` below by the literal `gauss_lemma`
    # alternative there; same colloquial name, unrelated statement).
    ("number-theory",
     r"^(Nat|Int)\.(prime|Prime|totient|fib|Fib|fastFib|perfect|Perfect|"
     r"Squarefree|squarefree|wilson|Wilson|euler|Euler|"
     r"sumOfDivisors|sumDivisors|sigma|nth|minFac|factorization|"
     r"legendre|quadratic|sum_two_squares|"
     r"exists_prime|pow_prime|not_prime|succ_pred_prime|"
     r"dvd_of_forall_prime|coprime_fermatNumber|least_divisor|least_residue|"
     r"pow_mul_prime|pow_two_ne_pow_two_mul_prime|pow_of_pow_add_prime|"
     r"self_inverse_mod_prime|factorial_interior_modeq|factorial_sq_modeq|"
     r"add_pow_modeq_prime|gauss_fold_injective|"
     r"gauss[A-Z]|gauss_neg_count|gauss_fold_|gauss_residue|leastResidue|"
     r"secondSupplementaryLaw|is_quadratic_residue|pow_neg_one_of|"
     r"half_ceil_parity)"),
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
    #
    # `det` (bare, not just `det2|det3`) covers ADR-1120's general-`n`
    # determinant: `Rat.det`, `det_zero`, `det_succ`, `det_one`,
    # `det_eq_det2`, `det_eq_det3`, `det_eval_*`. Landed 2026-08-31 and, until
    # this fix, silently fell through to the `rationals` catch-all below --
    # measured 22 declarations mis-attributed that way (`Rat.det*`,
    # `Rat.matSkip`, `Rat.matMinor`, `Rat.altSign`, `Rat.matInv2*`), the same
    # failure this comment already describes, recurring on the very rung the
    # DEPTH-PROPOSAL named as the keystone.
    # `Rat.sumRange_matSkip` (a Laplace-expansion reindexing lemma in
    # `matrix_det.rs`) doesn't start with any of the `mat(...)` alternatives
    # above -- the `sumRange_` prefix comes first -- so it fell through to
    # `rationals`. One declaration, same anchoring hazard.
    ("linear-algebra",
     r"^Rat\.(det|dotN|mat(Id|Mul|Transpose|Skip|Minor|Inv2)|altSign|"
     r"cramer|inv2_|mul_adj2_|sumRange_matSkip)"),
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
    "number-theory", "linear-algebra", "calculus", "probability",
]


# The carrier and pure-logic buckets. These are the CATCH-ALLS: every pattern
# above them is a topic that claims its names first, and anything unclaimed
# lands here. A mis-attribution is invisible to the residual counter precisely
# because it lands in one of these -- attributed, counted, and wrong.
CATCHALL_NODES = frozenset({
    "naturals", "integers", "rationals", "reals", "complex",
    "propositional-logic", "predicate-logic",
})

# A single-bucket name family must reach this many declarations before the
# family guard asks about it. Below the floor, an ordinary new lemma in a
# carrier bucket is not evidence of anything and must not redden the gate.
FAMILY_FLOOR = 8

DEFAULT_PIN = "artifacts/curriculum/bucket-cohesion-pin.tsv"

_STEM_WORDS = re.compile(r"[A-Z]?[a-z0-9]+|[A-Z]+(?![a-z])")


def name_stem(name: str) -> tuple[str, str]:
    """`Nat.gauss_fold_injective_of_coprime` -> `("Nat", "gauss")`.

    The stem is the FIRST word of the local name, with camelCase and
    snake_case folded into one vocabulary -- `Nat.gaussFold` and
    `Nat.gauss_neg_count_succ` share a stem, which is the whole point: this
    kernel spells one mathematical family both ways (measured over 447 `CReal`
    names: 315 carry an underscore, 225 an internal capital, 117 both), so a
    guard keyed on the raw spelling would see two families where there is one.
    """
    carrier, _, local = name.partition(".")
    if not local:
        carrier, local = "", name
    first = local.split("_", 1)[0]
    words = _STEM_WORDS.findall(first)
    stem = (words[0].lower() if words else first.lower())
    # Trailing digits are stripped so `det2`, `det3` and `det` are ONE family.
    # ADR-1140 is exactly a pattern that named the numbered instances while
    # the general construction grew past them; without this the guard sees
    # three families and never compares them.
    return carrier, (stem.rstrip("0123456789") or stem)


def assign(rows: dict[str, tuple[str, str]],
           buckets: list[tuple[str, str]]) -> dict[str, str]:
    """Declaration name -> node id, for the names some pattern claims."""
    compiled = [(nid, re.compile(pat)) for nid, pat in buckets]
    out: dict[str, str] = {}
    for name in rows:
        for nid, rx in compiled:
            if rx.match(name):
                out[name] = nid
                break
    return out


def stem_groups(attribution: dict[str, str]) -> dict[
        tuple[str, str], dict[str, list[str]]]:
    groups: dict[tuple[str, str], dict[str, list[str]]] = {}
    for name, nid in attribution.items():
        groups.setdefault(name_stem(name), {}).setdefault(nid, []).append(name)
    for by_node in groups.values():
        for names in by_node.values():
            names.sort()
    return groups


def read_pin(path: str) -> tuple[dict[tuple[str, str], tuple[str, ...]],
                                 dict[tuple[str, str], str]]:
    """Return (split pin, family pin). A missing file is an EMPTY pin, not an
    error -- but see `--require-pin`, which the gate passes so a deleted or
    misspelled pin path cannot read as "nothing to report"."""
    splits: dict[tuple[str, str], tuple[str, ...]] = {}
    families: dict[tuple[str, str], str] = {}
    try:
        fh = open(path, encoding="utf-8")
    except FileNotFoundError:
        return splits, families
    with fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) < 4:
                sys.exit(f"error: malformed pin row in {path}: {line!r}")
            kind, carrier, stem, nodes = fields[0], fields[1], fields[2], fields[3]
            if kind == "split":
                splits[(carrier, stem)] = tuple(sorted(nodes.split(",")))
            elif kind == "family":
                families[(carrier, stem)] = nodes
            else:
                sys.exit(f"error: unknown pin row kind {kind!r} in {path}")
    return splits, families


def render_pin(groups) -> str:
    lines = [
        "# Bucket-cohesion pin for scripts/measure-curriculum-kernel-coverage.py.",
        "# ADR-1215. Regenerate with --update-cohesion-pin AFTER deciding the",
        "# attribution is right -- a mechanical refresh of a WRONG attribution",
        "# is how this table stops being evidence.",
        "#",
        "# split\t<carrier>\t<stem>\t<comma-separated node ids>",
        "#   one name family that attributes to more than one node. The node",
        "#   SET is pinned, not the counts, so growth inside known nodes is free.",
        "# family\t<carrier>\t<stem>\t<node>\t<count-when-pinned>",
        "#   one name family of at least " + str(FAMILY_FLOOR) + " declarations sitting",
        "#   entirely in a carrier/logic catch-all. The count is informational.",
    ]
    for (carrier, stem), by_node in sorted(groups.items()):
        if len(by_node) > 1:
            lines.append("split\t{}\t{}\t{}".format(
                carrier, stem, ",".join(sorted(by_node))))
    for (carrier, stem), by_node in sorted(groups.items()):
        if len(by_node) == 1:
            node = next(iter(by_node))
            size = len(by_node[node])
            if node in CATCHALL_NODES and size >= FAMILY_FLOOR:
                lines.append("family\t{}\t{}\t{}\t{}".format(
                    carrier, stem, node, size))
    return "\n".join(lines) + "\n"


def cohesion_findings(groups, splits, families) -> list[str]:
    """Every way the pinned cohesion picture and the measured one disagree.

    G1 SPLIT   a name family attributing to a node set the pin does not carry.
               This is the ADR-1140 / ADR-1205 shape: a pattern that named
               INSTANCES (`det2|det3`, `gauss_fold_injective`) keeps matching
               the instances while the family grows past it, so the family
               splits between its destination node and a catch-all.
    G2 FAMILY  a name family of at least FAMILY_FLOOR declarations landing
               ENTIRELY in a catch-all, unpinned. This is the case G1 cannot
               see: a family with no partial match at all never splits.
    G3 STALE   a pinned row with no measured group. Without it the pin rots
               into a list of things that used to be true, and a rotted pin
               makes G1/G2 progressively weaker with nothing reporting it.
    """
    findings: list[str] = []
    seen_split: set[tuple[str, str]] = set()
    seen_family: set[tuple[str, str]] = set()
    for key, by_node in sorted(groups.items()):
        carrier, stem = key
        nodes = tuple(sorted(by_node))
        if len(by_node) > 1:
            seen_split.add(key)
            if splits.get(key) != nodes:
                was = ",".join(splits[key]) if key in splits else "(unpinned)"
                detail = "; ".join(
                    "{}: {}".format(n, ", ".join(by_node[n][:6])
                                    + (" ..." if len(by_node[n]) > 6 else ""))
                    for n in nodes)
                findings.append(
                    "G1 SPLIT {}.{}* attributes to {} (pinned {}) -- {}".format(
                        carrier, stem, ",".join(nodes), was, detail))
        else:
            node = nodes[0]
            size = len(by_node[node])
            if node in CATCHALL_NODES and size >= FAMILY_FLOOR:
                seen_family.add(key)
                if families.get(key) != node:
                    was = families.get(key, "(unpinned)")
                    findings.append(
                        "G2 FAMILY {}.{}* -- {} declarations, all in the "
                        "catch-all `{}` (pinned {}): {}".format(
                            carrier, stem, size, node, was,
                            ", ".join(by_node[node][:6])
                            + (" ..." if size > 6 else "")))
    for key in sorted(set(splits) - seen_split):
        findings.append(
            "G3 STALE split pin {}.{}* ({}) matches no measured family".format(
                key[0], key[1], ",".join(splits[key])))
    for key in sorted(set(families) - seen_family):
        findings.append(
            "G3 STALE family pin {}.{}* ({}) matches no measured family".format(
                key[0], key[1], families[key]))
    return findings


TOML_NODE_RE = re.compile(
    r'^id\s*=\s*"([a-z0-9-]+)"|^kernel_decls\s*=\s*(\d+)', re.M)


def read_node_counts(path: str) -> dict[str, int]:
    """`docs/curriculum/curriculum.toml`'s pinned per-node `kernel_decls`."""
    text = open(path, encoding="utf-8").read()
    counts: dict[str, int] = {}
    current: str | None = None
    for node_id, decls in TOML_NODE_RE.findall(text):
        if node_id:
            current = node_id
        elif current is not None:
            counts[current] = int(decls)
            current = None
    if not counts:
        sys.exit(f"error: {path} carried no `kernel_decls` pins -- wrong file?")
    return counts


# A projection carrying fewer declarations than this is STALE or truncated, and
# a short index makes a newly-landed family look like it was always in the
# catch-all -- the exact failure these guards exist to catch, arriving through
# the input rather than the table. Same device as
# `check-absence-claims.py`'s `authority_declaration_floor`.
PROJECTION_FLOOR = 2500


def parse_rows(lines, source: str = "<input>") -> dict[str, tuple[str, str]]:
    rows: dict[str, tuple[str, str]] = {}
    for line in lines:
        fields = line.rstrip("\n").split("\t")
        if len(fields) < 3:
            continue
        prelude, kind, name = fields[0], fields[1], fields[2]
        rows.setdefault(name, (prelude, kind))
    if not rows:
        sys.exit(f"error: {source} yielded zero declarations -- wrong file?")
    if len(rows) < PROJECTION_FLOOR:
        sys.exit(f"error: {source} carries {len(rows)} distinct declarations "
                 f"against a floor of {PROJECTION_FLOOR} -- this projection is "
                 "STALE or truncated, and the cohesion guards would report a "
                 "family that has simply not been built yet. Rebuild it, or "
                 "lower PROJECTION_FLOOR deliberately.")
    return rows


def load(path: str) -> dict[str, tuple[str, str]]:
    with open(path, encoding="utf-8") as fh:
        return parse_rows(fh, path)


def run_projection(cargo_bin: str = "cargo") -> str:
    """Run the real tool. `--release` is MANDATORY (debug SIGABRTs)."""
    import subprocess
    cmd = [cargo_bin, "run", "--release", "-q", "-p", "axeyum-lean-kernel",
           "--example", "kernel_declaration_projection"]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=3600,
                          check=False)
    if proc.returncode != 0:
        sys.exit(f"error: `{' '.join(cmd)}` exited {proc.returncode} -- the "
                 "tool itself failed, this is not a finding about any "
                 f"attribution:\n{proc.stderr[-2000:]}")
    return proc.stdout


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("projection", nargs="?",
                    help="kernel_declaration_projection TSV; omit with "
                         "--run-projection")
    ap.add_argument("--verbose", action="store_true",
                    help="list every unattributed declaration")
    ap.add_argument("--expect-attributed", type=int, default=None,
                    help="fail unless exactly this many declarations attribute")
    ap.add_argument("--require-node", action="append", default=[],
                    help="fail unless this node attributes at least one "
                         "declaration (repeatable)")
    ap.add_argument("--cohesion-pin", default=DEFAULT_PIN,
                    help="bucket-cohesion pin TSV (default %(default)s)")
    ap.add_argument("--no-cohesion", action="store_true",
                    help="skip the cohesion guards entirely")
    ap.add_argument("--require-pin", action="store_true",
                    help="fail when the pin file is missing, so a deleted or "
                         "misspelled path cannot read as 'nothing to report'")
    ap.add_argument("--update-cohesion-pin", action="store_true",
                    help="rewrite the pin from this measurement. Do this only "
                         "AFTER deciding the attribution is right")
    ap.add_argument("--expect-node-counts", default=None,
                    help="fail on any per-node drift against this "
                         "curriculum.toml's pinned kernel_decls")
    ap.add_argument("--run-projection", action="store_true",
                    help="ignore the positional path and run "
                         "kernel_declaration_projection --release itself")
    args = ap.parse_args()

    unknown = [n for n in args.require_node if n not in NODES]
    if unknown:
        sys.exit(f"error: --require-node names no curriculum node: {unknown}")

    if args.run_projection:
        rows = parse_rows(run_projection().splitlines())
    else:
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

    if args.expect_node_counts:
        pinned = read_node_counts(args.expect_node_counts)
        for nid in NODES:
            want = pinned.get(nid)
            got = counts[nid]["_total"]
            if want is None:
                print(f"FAIL: {args.expect_node_counts} carries no "
                      f"kernel_decls for node {nid}", file=sys.stderr)
                status = 1
            elif want != got:
                print(f"FAIL: node {nid} pinned at {want}, measured {got}",
                      file=sys.stderr)
                status = 1

    if not args.no_cohesion:
        groups = stem_groups(assign(rows, BUCKETS))
        if args.update_cohesion_pin:
            with open(args.cohesion_pin, "w", encoding="utf-8") as fh:
                fh.write(render_pin(groups))
            print(f"wrote {args.cohesion_pin}")
            return status
        import os
        if args.require_pin and not os.path.isfile(args.cohesion_pin):
            print(f"FAIL: --require-pin and {args.cohesion_pin} does not "
                  "exist -- the cohesion guards examined nothing",
                  file=sys.stderr)
            return 1
        splits, families = read_pin(args.cohesion_pin)
        findings = cohesion_findings(groups, splits, families)
        print(f"cohesion: {len(groups)} name families, "
              f"{len(splits)} split pins, {len(families)} family pins, "
              f"{len(findings)} findings")
        for line in findings:
            print(f"FAIL: {line}", file=sys.stderr)
        if findings:
            print("A finding is not automatically a bug: it says a name "
                  "family moved across bucket boundaries. Decide whether the "
                  "declarations belong in a destination node (widen that "
                  "node's pattern) or in the carrier bucket (then, and only "
                  "then, --update-cohesion-pin).", file=sys.stderr)
            status = 1
    return status


if __name__ == "__main__":
    raise SystemExit(main())
