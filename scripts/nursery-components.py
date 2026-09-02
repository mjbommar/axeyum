#!/usr/bin/env python3
"""The nursery's dependency components, and whether a component-based split is possible.

WHY THIS EXISTS (ADR-1546 option 1, decided in ADR-1551).

ADR-1546 measured the v2 nursery's evaluation partitions being fused by
producers and left three repair options. Lane `partition-edge-gate` took
option 2 (ADR-1550): gate the producer per crossing EDGE, baseline the 198
existing crossings, and let the baseline only shrink. Option 1 -- "make the
draw do component analysis", i.e. re-partition the drawn rows by connected
component of the declared-dependency graph -- was left for a lane to do.

This script is the measurement that option 1 needs and that nobody had run.
ADR-1546 asserted option 1 was "the honest fix and it is expensive"; it did
not measure the graph. The graph refuses it, for reasons that are arithmetic
rather than aesthetic, and the point of a shipped tool rather than a one-off
script is that the refusal stays checkable and stops being true the moment the
ledger changes shape.

WHAT IT MEASURES, in the order the argument needs

  1. THE ASSIGNMENT UNIT IS THE FAMILY, NOT THE FACT. The nursery policy
     declares `family_leakage: no-family-may-cross-evaluation-partitions`
     alongside `split_leakage: no-declared-component-may-cross-evaluation-
     partitions`, and `check-autogenesis-nursery.py` enforces both. So a
     component-based assignment must also be family-respecting, which means
     contracting each family to a single node before taking components.

  2. THE FACT-LEVEL PICTURE LOOKS TRACTABLE AND IS NOT. Over the 716 drawn
     rows the `depends_on` graph has 357 weak components, 352 of them already
     single-partition. Contract the families and that becomes 20 components,
     nineteen of which are a single isolated held-out family -- and one blob
     holding 44 families and 520 of the 716 rows, spanning all four
     partitions.

  3. TWO FAMILIES IN THAT BLOB CANNOT MOVE. `integer-absolute-value` is
     held-out and a held-out row never leaves held-out (ADR-0542).
     `nat-bootstrap` is the longitudinal Autogenesis-1 chain, pinned to
     exactly {F:nat-mul-one, F:nat-zero-add} by
     `check-autogenesis-nursery.py`'s own code, and 45 drawn rows declare a
     dependency on it. Their crossing edges therefore survive ANY
     re-partition.

  4. THE RESIDUAL CANNOT TAKE ONE PARTITION EITHER. Cut the two pinned
     families out and 42 families / 508 rows remain in one component.
     Assigning that one partition would empty one of
     `required_evaluation_partitions: [train, development, held-out]`, which
     `check-autogenesis-nursery.py` reports as `empty-partition:` -- the very
     gate option 1 exists to turn green.

  5. AND THE GRAPH IS NOT OUTCOME-BLIND. `depends_on` on a kernel-route fact
     is DERIVED FROM THE ADMITTED PROOF TERM (`check-fact-depends-derived.py`,
     policy `admission_dependency_authority: proof-derived-kernel-dependency`).
     An unproved row therefore has no edges and is a singleton by
     construction. Measured over the 508 train/development rows: 396 of the
     398 rows that declare any dependency at all are `proved`. Partitioning on
     this graph assigns a row's partition as a function of whether we proved
     it, which is precisely what `split_freeze: before-target-outcomes`
     forbids.

So the tool reports the census, states the ADR-1551 rule, and -- because a
rule nobody can run is not a decision -- computes what the rule WOULD produce
(`--propose`), including the crossing count it would leave and how many rows
would change partition. It never edits a manifest.

MODES
  (default)          print the census
  --propose          also print the ADR-1551 assignment and its cost curve
  --record           write the census artifact (the OWNER for it)
  --remeasure        with --record, re-measure the ledger-derived block
  --check            check the findings that would change ADR-1551's decision
  --json             emit the census as JSON on stdout

WHY --check DOES NOT COMPARE THE LIVE NUMBERS TO THE RECORDED ONES
  The ledger gains `depends_on` edges every time a producer closes a fact, so
  an equality check against a committed snapshot would be red within hours and
  would teach people to re-record rather than to read. What `--check` enforces
  instead is the set of findings ADR-1551's refusal RESTS ON: if any of them
  stops holding, option 1 has become feasible and the next lane must be told.
  Numeric drift from the snapshot is printed as `DRIFT` and is advisory.

EXITS
  0  the findings hold (or, without --check, the report was produced)
  1  a finding that ADR-1551 rests on no longer holds, or --check found the
     recorded artifact internally inconsistent
  2  cannot answer -- no nursery manifest, no fact ledger, or --check with no
     recorded artifact. Distinct from 1 on purpose: a gate that reports a
     disagreement when its subject was unavailable is wrong about its subject.
"""

from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import json
import os
import pathlib
import subprocess
import sys
from typing import Any

# Same device as `AXEYUM_PARTITION_EDGES_ROOT`: point the SHIPPED script at a
# throwaway tree so the control suite can drive every guard to failure without
# re-implementing it and without dirtying the real checkout.
DEFAULT_ROOT = pathlib.Path(__file__).resolve().parents[1]

# NOT a single wide `nursery*.json` glob -- see the identical note in
# `check-partition-edges.py`, whose `MANIFEST_GLOBS` this mirrors exactly.
# A committed decoy matching the wide glob (`nursery-zzz-notes.json`) makes
# `Drawn.__init__` below raise `Unanswerable` the instant it lacks a usable
# `entries` list, taking this tool down over a file with no relation to its
# subject. Two explicit patterns name exactly what a manifest here IS.
MANIFEST_GLOBS = ("artifacts/autogenesis/nursery-v1.json",
                  "artifacts/autogenesis/nursery-v*-extension.json")
FACTS_DIR = "artifacts/facts"
CENSUS_PATH = "artifacts/autogenesis/drawn-population-component-census-v1.json"
ADR = ("docs/research/09-decisions/"
       "adr-1551-the-family-graph-is-one-blob-and-the-dependency-edge-is-"
       "proof-derived.md")

EVALUATION_PARTITIONS = ("train", "development", "held-out")
PARTITIONS = ("longitudinal", "train", "development", "held-out")

# The two families ADR-1551 pins. Named, not derived, because each is pinned
# by a DIFFERENT authority and a reader has to be able to argue with each one
# separately -- deriving them from "whatever cannot move today" would make the
# pin a description of the current ledger instead of a decision.
PINNED_FAMILIES = {
    "integer-absolute-value":
        "held-out; a held-out row never leaves held-out (ADR-0542), so the "
        "family cannot be absorbed into a component's partition",
    "nat-bootstrap":
        "longitudinal; check-autogenesis-nursery.py pins the longitudinal "
        "partition to exactly {F:nat-mul-one, F:nat-zero-add}, so these two "
        "rows cannot be relabelled by any re-partition",
}

# ADR-1551's rule, stated once and quoted into the artifact so the file and
# the ADR cannot drift apart silently.
RULE = (
    "ADR-1551. UNIT: contract each `family` to one node (forced by "
    "`family_leakage: no-family-may-cross-evaluation-partitions`); join two "
    "families when a drawn row of one declares `depends_on` a drawn row of "
    "the other; take weak components. PINS: `integer-absolute-value` "
    "(held-out, ADR-0542) and `nat-bootstrap` (longitudinal, pinned in "
    "check-autogenesis-nursery.py) keep their partition and are removed from "
    "their component; every crossing edge incident to them is a per-edge "
    "amendment. ASSIGNMENT: each residual component takes ONE partition -- "
    "the one its declared dependencies bind it to most strongly, computed by "
    "moving the single family with the largest crossing-weight gain until no "
    "move improves, in lexicographic family order, ties keeping the "
    "incumbent, subject to `train` and `development` each retaining at least "
    "`policy.evaluation_fact_count.minimum` rows. OUTCOME-BLIND ONLY IN ITS "
    "ARITHMETIC: the graph it runs on is proof-derived, which is why "
    "ADR-1551 does not apply it."
)


class Unanswerable(RuntimeError):
    """The tool could not evaluate its subject. Exit 2, never 1."""


def sha256_of(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise Unanswerable(f"{path}: unreadable ({exc})") from exc


def manifest_paths(root: pathlib.Path) -> list[pathlib.Path]:
    """Every path any `MANIFEST_GLOBS` pattern matches, deduplicated and sorted."""
    return sorted({path for pattern in MANIFEST_GLOBS
                   for path in root.glob(pattern)})


# --------------------------------------------------------------------------
# The subject
# --------------------------------------------------------------------------

class Drawn:
    """The drawn population, keyed the three ways the argument needs."""

    def __init__(self, root: pathlib.Path) -> None:
        manifests = manifest_paths(root)
        if not manifests:
            raise Unanswerable(
                f"no nursery manifest matches {MANIFEST_GLOBS} under {root} -- "
                f"there is no drawn population to measure, which is not the "
                f"same as an empty one")
        self.manifest_names: list[str] = []
        self.partition: dict[str, str] = {}
        self.family: dict[str, str] = {}
        self.module: dict[str, str] = {}
        self.manifest: dict[str, str] = {}
        self.minimum_rows = 0
        for path in manifests:
            rel = str(path.relative_to(root))
            self.manifest_names.append(rel)
            document = load_json(path)
            if not isinstance(document, dict):
                raise Unanswerable(f"{rel}: not a JSON object")
            policy = document.get("policy")
            if isinstance(policy, dict):
                counts = policy.get("evaluation_fact_count")
                if isinstance(counts, dict) and isinstance(counts.get("minimum"), int):
                    self.minimum_rows = max(self.minimum_rows, counts["minimum"])
            entries = document.get("entries")
            if not isinstance(entries, list):
                raise Unanswerable(f"{rel}: entries is not a list")
            for index, entry in enumerate(entries):
                if not isinstance(entry, dict):
                    raise Unanswerable(f"{rel}: entries[{index}] is not an object")
                fact_id = entry.get("fact_id")
                partition = entry.get("partition")
                family = entry.get("family")
                if (not isinstance(fact_id, str) or partition not in PARTITIONS
                        or not isinstance(family, str) or not family):
                    raise Unanswerable(
                        f"{rel}: entries[{index}] has no usable "
                        f"fact_id/partition/family")
                self.partition[fact_id] = partition
                self.family[fact_id] = family
                self.manifest[fact_id] = rel
                # v2 rows carry the Mathlib defining module; v1 rows do not,
                # and their `source_group` is a content hash rather than a
                # module path. Reported as given, never invented.
                module = entry.get("module")
                self.module[fact_id] = (module if isinstance(module, str)
                                        else str(entry.get("source_group")))
        if not self.minimum_rows:
            self.minimum_rows = 100

    def rows_of_family(self) -> dict[str, list[str]]:
        out: dict[str, list[str]] = collections.defaultdict(list)
        for fact_id, family in sorted(self.family.items()):
            out[family].append(fact_id)
        return dict(out)


def load_dependencies(root: pathlib.Path) -> dict[str, list[str]]:
    facts_dir = root / FACTS_DIR
    if not facts_dir.is_dir():
        raise Unanswerable(f"{FACTS_DIR} is absent under {root}")
    out: dict[str, list[str]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        fact = load_json(path)
        if not isinstance(fact, dict):
            continue
        fact_id = fact.get("id")
        if not isinstance(fact_id, str):
            continue
        depends_on = fact.get("depends_on") or []
        if not isinstance(depends_on, list):
            raise Unanswerable(f"{path.name}: depends_on is not a list")
        out[fact_id] = [d for d in depends_on if isinstance(d, str)]
    return out


def weak_components(adjacency: dict[str, set[str]],
                    nodes: list[str]) -> list[list[str]]:
    """Weak components, largest first, each sorted, deterministic throughout."""
    seen: set[str] = set()
    out: list[list[str]] = []
    for start in sorted(nodes):
        if start in seen:
            continue
        found: set[str] = set()
        stack = [start]
        while stack:
            current = stack.pop()
            if current in found:
                continue
            found.add(current)
            stack.extend(adjacency.get(current, set()) - found)
        seen |= found
        out.append(sorted(found))
    out.sort(key=lambda members: (-len(members), members[0]))
    return out


# --------------------------------------------------------------------------
# The two graphs
# --------------------------------------------------------------------------

def fact_graph(drawn: Drawn,
               dependencies: dict[str, list[str]]) -> dict[str, set[str]]:
    adjacency: dict[str, set[str]] = {f: set() for f in drawn.partition}
    for fact_id in drawn.partition:
        for dependency in dependencies.get(fact_id, []):
            if dependency in drawn.partition and dependency != fact_id:
                adjacency[fact_id].add(dependency)
                adjacency[dependency].add(fact_id)
    return adjacency


def family_weights(drawn: Drawn,
                   dependencies: dict[str, list[str]]) -> dict[tuple[str, str], int]:
    """Undirected inter-family edge counts over drawn rows.

    Counting EDGES rather than family pairs is what makes the cut cost
    comparable to `check-partition-edges.py`'s crossing count: the two agree
    by construction, and that agreement is the tool's own cross-check.
    """
    weights: collections.Counter[tuple[str, str]] = collections.Counter()
    for fact_id in sorted(drawn.partition):
        for dependency in dependencies.get(fact_id, []):
            if dependency not in drawn.partition:
                continue
            a, b = drawn.family[fact_id], drawn.family[dependency]
            if a != b:
                weights[tuple(sorted((a, b)))] += 1
    return dict(weights)


def crossing_edge_count(drawn: Drawn, dependencies: dict[str, list[str]],
                        partition_of_family: dict[str, str]) -> int:
    """Directed `depends_on` edges whose endpoints differ in partition.

    Computed the same way `check-partition-edges.py` computes it, so the
    `crossings_now` this tool prints can be compared to that gate's
    `crossing=` without either being re-derived from the other's report.
    """
    total = 0
    for fact_id in sorted(drawn.partition):
        source = partition_of_family[drawn.family[fact_id]]
        for dependency in dependencies.get(fact_id, []):
            if dependency not in drawn.partition:
                continue
            if partition_of_family[drawn.family[dependency]] != source:
                total += 1
    return total


# --------------------------------------------------------------------------
# ADR-1551's rule, computed but not applied
# --------------------------------------------------------------------------

def propose(drawn: Drawn, weights: dict[tuple[str, str], int],
            rows_of: dict[str, list[str]]) -> dict[str, Any]:
    """Run ADR-1551's assignment rule and report what it would cost.

    Returns the assignment, the move list, the resulting crossing count and
    the cost curve (crossings after each successive move), so a reader can see
    both the fixed point and how quickly it is reached. NOTHING IS WRITTEN.
    """
    incumbent = {family: drawn.partition[rows[0]]
                 for family, rows in rows_of.items()}
    free = sorted(f for f in rows_of
                  if f not in PINNED_FAMILIES
                  and incumbent[f] in ("train", "development"))
    size = {f: len(rows_of[f]) for f in free}
    inner = {pair: w for pair, w in weights.items()
             if pair[0] in size and pair[1] in size}
    total_rows = sum(size.values())
    floor = drawn.minimum_rows

    def cut(assignment: dict[str, str]) -> int:
        return sum(w for (a, b), w in inner.items()
                   if assignment[a] != assignment[b])

    def development_rows(assignment: dict[str, str]) -> int:
        return sum(size[f] for f in free if assignment[f] == "development")

    assignment = {f: incumbent[f] for f in free}
    curve = [{"moves": 0, "residual_cut": cut(assignment),
              "development_rows": development_rows(assignment),
              "train_rows": total_rows - development_rows(assignment),
              "moved": None}]
    moved: list[str] = []
    while True:
        best: tuple[int, str, dict[str, str]] | None = None
        for family in free:  # lexicographic, so the fixed point is stable
            if family in moved:
                continue
            trial = dict(assignment)
            trial[family] = ("train" if assignment[family] == "development"
                             else "development")
            developed = development_rows(trial)
            if developed < floor or (total_rows - developed) < floor:
                continue
            cost = cut(trial)
            if best is None or cost < best[0]:
                best = (cost, family, trial)
        if best is None or best[0] >= cut(assignment):
            break
        assignment = best[2]
        moved.append(best[1])
        curve.append({"moves": len(moved), "residual_cut": best[0],
                      "development_rows": development_rows(assignment),
                      "train_rows": total_rows - development_rows(assignment),
                      "moved": best[1]})

    final = dict(incumbent)
    final.update(assignment)
    pinned_cut = sum(w for (a, b), w in weights.items()
                     if (a in PINNED_FAMILIES) != (b in PINNED_FAMILIES))
    return {
        "rule": RULE,
        "row_floor_per_partition": floor,
        "families_moved": sorted(moved),
        "rows_moved": sum(size[f] for f in moved),
        "assignment": {f: final[f] for f in sorted(final)},
        "cost_curve": curve,
        "residual_cut_at_fixed_point": cut(assignment),
        "pinned_incident_edges": pinned_cut,
        "partition_counts": dict(sorted(collections.Counter(
            final[drawn.family[f]] for f in drawn.partition).items())),
    }


# --------------------------------------------------------------------------
# The census
# --------------------------------------------------------------------------

def census(root: pathlib.Path) -> dict[str, Any]:
    drawn = Drawn(root)
    dependencies = load_dependencies(root)
    rows_of = drawn.rows_of_family()

    split_families = sorted(
        family for family, rows in rows_of.items()
        if len({drawn.partition[r] for r in rows}) > 1)

    facts = weak_components(fact_graph(drawn, dependencies),
                            sorted(drawn.partition))
    weights = family_weights(drawn, dependencies)
    family_adjacency: dict[str, set[str]] = {f: set() for f in rows_of}
    for a, b in weights:
        family_adjacency[a].add(b)
        family_adjacency[b].add(a)
    family_comps = weak_components(family_adjacency, sorted(rows_of))

    def partition_mix(members: list[str]) -> dict[str, int]:
        return dict(sorted(collections.Counter(
            drawn.partition[m] for m in members).items()))

    def module_mix(members: list[str]) -> list[str]:
        return sorted({drawn.module[m] for m in members})

    fact_component_rows = [
        {"size": len(members),
         "partitions": partition_mix(members),
         "families": sorted({drawn.family[m] for m in members}),
         "modules": module_mix(members)}
        for members in facts]

    family_component_rows = []
    for members in family_comps:
        rows = [r for f in members for r in rows_of[f]]
        family_component_rows.append({
            "families": members,
            "family_count": len(members),
            "rows": len(rows),
            "partitions": partition_mix(rows),
            "modules": module_mix(rows),
            "pinned_families": sorted(set(members) & set(PINNED_FAMILIES)),
        })

    incumbent = {f: drawn.partition[rows_of[f][0]] for f in rows_of}
    pinned_incident = {
        f"{a}--{b}": w for (a, b), w in sorted(weights.items())
        if (a in PINNED_FAMILIES) != (b in PINNED_FAMILIES)}

    ledger_block = {
        "fact_components": {
            "count": len(facts),
            # A LIST, not a dict keyed by size. JSON object keys are strings,
            # so a `{7: 1, 10: 1, 305: 1}` written in numeric order comes back
            # as `{"10": ..., "305": ..., "7": ...}` under `sort_keys=True`,
            # and `--record` stops being idempotent on its own output -- which
            # `check-generated-artifact-ownership.py`'s OWNER arm catches as
            # "did not restore from a perturbed copy". Found that way.
            "size_distribution": [
                {"size": size, "components": count}
                for size, count in sorted(collections.Counter(
                    len(m) for m in facts).items())],
            # Scalars, because `report()` must not index the distribution's
            # SHAPE: the mutant that reverts it to a size-keyed dict is the
            # defect N11 exists to catch, and a printer that crashes on that
            # mutant kills every test instead of the one whose subject it is.
            "largest_component": max((len(m) for m in facts), default=0),
            "singleton_components": sum(1 for m in facts if len(m) == 1),
            "single_partition": sum(
                1 for m in facts if len({drawn.partition[x] for x in m}) == 1),
            "multi_partition": [r for r in fact_component_rows
                                if len(r["partitions"]) > 1],
        },
        "family_components": {
            "count": len(family_comps),
            "single_partition": sum(1 for r in family_component_rows
                                    if len(r["partitions"]) == 1),
            "components": family_component_rows,
        },
        "inter_family_edge_classes": len(weights),
        "inter_family_edges": sum(weights.values()),
        "pinned_incident_edges": pinned_incident,
        "pinned_incident_edge_count": sum(pinned_incident.values()),
        "crossings_now": crossing_edge_count(drawn, dependencies, incumbent),
        "proposal": propose(drawn, weights, rows_of),
        "ledger_sha256": sha256_of(
            [[f, drawn.partition[f], sorted(dependencies.get(f, []))]
             for f in sorted(drawn.partition)]),
    }

    manifest_block = {
        "manifests": drawn.manifest_names,
        "drawn": len(drawn.partition),
        "partition_counts": dict(sorted(collections.Counter(
            drawn.partition.values()).items())),
        "families": [
            {"family": f, "partition": incumbent[f], "rows": len(rows_of[f]),
             "manifest": drawn.manifest[rows_of[f][0]]}
            for f in sorted(rows_of)],
        "families_holding_two_partitions": split_families,
        "pinned_families": {f: why for f, why in sorted(PINNED_FAMILIES.items())},
        "row_floor_per_partition": drawn.minimum_rows,
    }
    return {"manifest_block": manifest_block, "ledger_block": ledger_block}


# --------------------------------------------------------------------------
# The findings --check enforces
# --------------------------------------------------------------------------

def findings(measured: dict[str, Any]) -> list[str]:
    """Every finding ADR-1551's refusal rests on, checked against the tree.

    THE EXIT STATUS DEPENDS ON THESE, and each one is a statement that could
    stop being true: if the blob breaks up, if a pin is lifted, or if a family
    is split, option 1 has become feasible and the next lane needs to know
    that from a gate rather than from re-reading an ADR.
    """
    manifest = measured["manifest_block"]
    ledger = measured["ledger_block"]
    complaints: list[str] = []

    # F1 -- the unit really is the family.
    if manifest["families_holding_two_partitions"]:
        complaints.append(
            "F1 a family now holds two partitions "
            f"({', '.join(manifest['families_holding_two_partitions'])}); "
            "`family_leakage: no-family-may-cross-evaluation-partitions` no "
            "longer describes the manifests, so ADR-1551's contraction of "
            "each family to one node is no longer forced")

    # F2 -- the blob still exists and still spans evaluation partitions.
    blob = max(ledger["family_components"]["components"],
               key=lambda c: c["rows"], default=None)
    if blob is None:
        complaints.append("F2 there are no family components at all")
    else:
        evaluation = [p for p in blob["partitions"] if p in EVALUATION_PARTITIONS]
        if len(evaluation) < 2:
            complaints.append(
                "F2 the largest family component no longer spans two "
                f"evaluation partitions (it holds {blob['partitions']}); a "
                "component-based assignment may now be possible and ADR-1551 "
                "must be re-decided")

    # F3 -- both pins are still pinned, and still inside the blob.
    for family in sorted(PINNED_FAMILIES):
        if family not in manifest["pinned_families"]:
            complaints.append(f"F3 {family} is no longer recorded as pinned")
    if blob is not None and not blob["pinned_families"]:
        complaints.append(
            "F3 the largest family component now contains neither pinned "
            "family; the crossings ADR-1551 called structurally unrepairable "
            "may be repairable now")

    # F4 -- the pinned crossings are still there. A zero here is the good news
    # ADR-1551 says would change the decision, so it must be reported loudly
    # rather than pass silently.
    if ledger["pinned_incident_edge_count"] == 0:
        complaints.append(
            "F4 no drawn row depends across a pinned family any more; the 51 "
            "edges ADR-1551 recorded as unrepairable by re-partition are gone")

    # F5 -- the rule still cannot reach zero. If it can, apply it.
    proposal = ledger["proposal"]
    reachable = (proposal["residual_cut_at_fixed_point"]
                 + proposal["pinned_incident_edges"])
    if reachable == 0:
        complaints.append(
            "F5 ADR-1551's rule now reaches ZERO crossings; the refusal was "
            "conditional on it not doing so and option 1 should be applied")
    return complaints


# --------------------------------------------------------------------------
# The artifact
# --------------------------------------------------------------------------

def head_commit(root: pathlib.Path) -> str:
    try:
        done = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              capture_output=True, text=True, timeout=30,
                              check=False)
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return done.stdout.strip() or "unknown"


def render(root: pathlib.Path, measured: dict[str, Any],
           previous: dict[str, Any] | None, remeasure: bool) -> str:
    """The committed census text.

    THE LEDGER-DERIVED BLOCK IS CARRIED FORWARD unless `--remeasure` asks for
    a new measurement. That is not cosmetic. `depends_on` grows every time a
    producer closes a fact, so a block re-measured on every write would make
    this artifact impossible to own: `check-generated-artifact-ownership.py`'s
    OWNER arm perturbs the committed file and demands the owner restore it
    BYTE-FOR-BYTE, and a live ledger digest cannot survive that. The
    manifest-derived block IS recomputed on every write, because the manifests
    change only when somebody decides to change them -- which is exactly the
    event this artifact should not be able to sleep through.
    """
    ledger = measured["ledger_block"]
    if previous is not None and not remeasure:
        carried = previous.get("ledger_block")
        if isinstance(carried, dict):
            ledger = carried
    document = {
        "kind": "axeyum-nursery-component-census",
        "authority": ADR,
        "produced_by": "scripts/nursery-components.py --record",
        "rule": RULE,
        "note": (
            "The ledger-derived block is a SNAPSHOT and is carried forward by "
            "--record; re-measure it with --record --remeasure. `--check` "
            "enforces the findings ADR-1551 rests on against the live tree, "
            "never equality with this snapshot -- see the module docstring."),
        "measured_date": (previous or {}).get("measured_date")
        if previous is not None and not remeasure
        else datetime.date.today().isoformat(),
        "measured_at_commit": (previous or {}).get("measured_at_commit")
        if previous is not None and not remeasure
        else head_commit(root),
        "ledger_block": ledger,
        "manifest_block": measured["manifest_block"],
        "schema_version": 1,
    }
    if document["measured_date"] is None:
        document["measured_date"] = datetime.date.today().isoformat()
    if document["measured_at_commit"] is None:
        document["measured_at_commit"] = head_commit(root)
    return json.dumps(document, indent=2, sort_keys=True,
                      ensure_ascii=False) + "\n"


def report(measured: dict[str, Any]) -> None:
    manifest = measured["manifest_block"]
    ledger = measured["ledger_block"]
    facts = ledger["fact_components"]
    fams = ledger["family_components"]
    print(f"drawn={manifest['drawn']} "
          f"partitions={manifest['partition_counts']} "
          f"families={len(manifest['families'])}")
    print(f"fact components: {facts['count']} "
          f"({facts['single_partition']} already single-partition); "
          f"largest {facts['largest_component']}, "
          f"{facts['singleton_components']} singletons")
    for row in facts["multi_partition"]:
        print(f"  MULTI size={row['size']} {row['partitions']} "
              f"families={len(row['families'])}")
    print(f"family components: {fams['count']} "
          f"({fams['single_partition']} already single-partition)")
    for row in fams["components"]:
        marker = "BLOB" if len(row["partitions"]) > 1 else "clean"
        print(f"  {marker} families={row['family_count']:2d} "
              f"rows={row['rows']:3d} {row['partitions']}"
              + (f" pinned={row['pinned_families']}"
                 if row["pinned_families"] else ""))
    print(f"inter-family edges: {ledger['inter_family_edges']} in "
          f"{ledger['inter_family_edge_classes']} classes; "
          f"crossings now {ledger['crossings_now']}; "
          f"incident to a pinned family "
          f"{ledger['pinned_incident_edge_count']} (unrepairable by "
          f"re-partition)")


def report_proposal(measured: dict[str, Any]) -> None:
    proposal = measured["ledger_block"]["proposal"]
    print()
    print("ADR-1551 rule, computed and NOT applied:")
    print(f"  row floor per partition: {proposal['row_floor_per_partition']}")
    print(f"  families moved: {len(proposal['families_moved'])} "
          f"({proposal['rows_moved']} rows)")
    print(f"  resulting partition counts: {proposal['partition_counts']}")
    reachable = (proposal["residual_cut_at_fixed_point"]
                 + proposal["pinned_incident_edges"])
    print(f"  crossings after: {reachable} "
          f"({proposal['residual_cut_at_fixed_point']} residual + "
          f"{proposal['pinned_incident_edges']} pinned)")
    print("  cost curve (moves -> total crossings):")
    for step in proposal["cost_curve"]:
        total = step["residual_cut"] + proposal["pinned_incident_edges"]
        print(f"    {step['moves']:2d} -> {total:3d}  "
              f"dev={step['development_rows']:3d} "
              f"train={step['train_rows']:3d}"
              + (f"  moved {step['moved']}" if step["moved"] else ""))
    for family in proposal["families_moved"]:
        was = "train" if proposal["assignment"][family] == "development" else "development"
        print(f"    WOULD MOVE {family}: {was} -> "
              f"{proposal['assignment'][family]}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=None,
                        help="measure this tree instead of the checkout")
    parser.add_argument("--propose", action="store_true",
                        help="also print ADR-1551's assignment and its cost")
    parser.add_argument("--record", action="store_true",
                        help=f"write {CENSUS_PATH}")
    parser.add_argument("--remeasure", action="store_true",
                        help="with --record, re-measure the ledger block")
    parser.add_argument("--check", action="store_true",
                        help="check the findings ADR-1551 rests on")
    parser.add_argument("--json", action="store_true",
                        help="emit the census as JSON")
    args = parser.parse_args(argv)

    root = pathlib.Path(args.root
                        or os.environ.get("AXEYUM_NURSERY_COMPONENTS_ROOT")
                        or DEFAULT_ROOT).resolve()

    try:
        measured = census(root)
        previous: dict[str, Any] | None = None
        path = root / CENSUS_PATH
        if path.is_file():
            candidate = load_json(path)
            if isinstance(candidate, dict):
                previous = candidate
        if args.check and previous is None:
            raise Unanswerable(
                f"{CENSUS_PATH} is absent -- --check reports against the "
                f"recorded census. Record one with --record.")
    except Unanswerable as exc:
        print(f"NURSERY-COMPONENTS|UNANSWERABLE {exc}")
        return 2

    if args.record:
        path.write_text(render(root, measured, previous, args.remeasure))
        print(f"NURSERY-COMPONENTS|RECORDED|{CENSUS_PATH}"
              f"|ledger_block={'remeasured' if args.remeasure or previous is None else 'carried-forward'}")
        return 0

    if args.json:
        print(json.dumps(measured, indent=2, sort_keys=True, ensure_ascii=False))

    report(measured)
    if args.propose:
        report_proposal(measured)

    if not args.check:
        return 0

    complaints = findings(measured)
    recorded = previous.get("ledger_block", {}) if previous else {}
    drift = []
    for key in ("crossings_now", "pinned_incident_edge_count"):
        if recorded.get(key) != measured["ledger_block"][key]:
            drift.append(f"{key} {recorded.get(key)} -> "
                         f"{measured['ledger_block'][key]}")
    # A recorded census whose own summary disagrees with its own component
    # list is a defect in the file, not drift, so it FAILS.
    inconsistent = []
    fams = recorded.get("family_components")
    if isinstance(fams, dict) and isinstance(fams.get("components"), list):
        if fams.get("count") != len(fams["components"]):
            inconsistent.append(
                f"recorded family_components.count={fams.get('count')} but "
                f"{len(fams['components'])} components are listed")
    for line in drift:
        print(f"DRIFT {line} (advisory: the ledger gains edges hourly)")
    for line in inconsistent:
        print(f"FAIL {line}")
    for line in complaints:
        print(f"FAIL {line}")
    verdict = "FAILED" if complaints or inconsistent else "PASS"
    print(f"NURSERY-COMPONENTS|findings={len(complaints)}"
          f"|inconsistent={len(inconsistent)}|drift={len(drift)}|{verdict}")
    return 1 if (complaints or inconsistent) else 0


if __name__ == "__main__":
    sys.exit(main())
