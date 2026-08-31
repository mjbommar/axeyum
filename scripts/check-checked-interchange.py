#!/usr/bin/env python3
"""Gate: validate `artifacts/checked-interchange/census/*.census.json` (L4
phase C2, docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md).

C2 asks, for every headline theorem representable in the pinned Lean slice:
export the exact reachable Axeyum closure, fresh-reimport or replay it through
an independent path, submit it to pinned Lean's kernel, and bind the result to
the fact receipt. `crates/axeyum-lean-import/tests/
checked_interchange_credited_roots.rs` performs that pipeline against real
Lean and writes the committed census this script validates; this script needs
NO Lean toolchain and NO cargo run, matching `check-declaration-graph.py`'s
and `check-graph-join.py`'s own posture toward artifacts a slower producer
writes.

This does NOT recompute the census (that needs pinned Lean and a cargo build,
run by `scripts/gen-checked-interchange.py`). It validates the shape of what
was produced and, critically, that "accepted" credit was actually EARNED --
never a bare-name accept, never a bare-type accept, never a decline that
silently reads as a success.

Credited-root population: the 9 declarations in ADR-0835's graph join
(`artifacts/graph-join/*.join.json`) whose `trust_footprints` dimension
resolved. `artifacts/checked-interchange/populations/*.json` is a committed
SNAPSHOT of that set; this script re-derives the same set from the LIVE join
file (never from the snapshot's own fields) so a name silently dropped from
the join is caught as staleness, not papered over.

Seven guards, seven distinct mutation classes, each mutation-verified to be
killed by exactly one fixture (`scripts/tests/test-checked-interchange-mutations.sh`):

  MISSING              a root named in the population file's expected_roots
                       is absent from the census's own roots list
  STALE_POPULATION     the population file's expected_roots (as a set)
                       disagrees with a FRESH read of the live graph-join's
                       trust_footprints.resolved key set -- the join file is
                       external authority the population snapshot does not
                       control
  ACCOUNTING           len(roots) != expected, or
                       accepted + declined_typed + missing != expected
  MANDATORY_MISSING_ZERO  credited_roots_replay.missing != 0 -- C2's exit
                       criterion is explicit that this is mandatory, not
                       merely reported
  BARE_NAME_ACCEPT     a root record claims status=="accepted" while its own
                       lean_admitted_by_name is not true -- an accept must be
                       evidenced by Lean's OWN kernel holding that name
  BARE_TYPE_ACCEPT     a root record claims status=="accepted" while its own
                       reimport_type_matches is not true -- an accept must be
                       evidenced by independent TYPE identity, never a name
                       match alone (ADR-0716's Nat.multichoose hazard)
  DECLINE_PROBE_VACUOUS  decline_mechanism_probe.status != "declined" --
                       proves the decline path was actually exercised rather
                       than every case reading as a success

Usage:
    python3 scripts/check-checked-interchange.py
    python3 scripts/check-checked-interchange.py --census-dir DIR --population-dir DIR
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CENSUS_DIR = REPO_ROOT / "artifacts" / "checked-interchange" / "census"
DEFAULT_POPULATION_DIR = REPO_ROOT / "artifacts" / "checked-interchange" / "populations"
DEFAULT_GRAPH_JOIN_DIR = REPO_ROOT / "artifacts" / "graph-join"


def load_json(path: Path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def live_join_credited_roots(graph_join_dir: Path) -> set[str] | None:
    """The credited-root name set as the LIVE graph-join files say it is
    right now -- never read from the population snapshot. Returns None if no
    join file has a `trust_footprints` dimension (so staleness cannot be
    judged; callers must not silently pass in that case)."""
    for join_path in sorted(graph_join_dir.glob("*.join.json")):
        join = load_json(join_path)
        dims = join.get("dimensions", {})
        tf = dims.get("trust_footprints")
        if tf is not None:
            return set(tf.get("resolved", {}).keys())
    return None


# GUARD:MISSING begin
def check_missing(population: dict, census: dict) -> list[str]:
    expected_roots = set(population.get("expected_roots", []))
    census_roots = {
        r["name"] for r in census.get("credited_roots_replay", {}).get("roots", [])
    }
    missing = expected_roots - census_roots
    if missing:
        return [
            f"MISSING: population names {sorted(missing)} not present in the "
            "census's own roots list"
        ]
    return []
# GUARD:MISSING end


# GUARD:STALE_POPULATION begin
def check_stale_population(population: dict, live_credited_roots: set[str] | None) -> list[str]:
    if live_credited_roots is None:
        return [
            "STALE_POPULATION: no graph-join artifact carries a trust_footprints "
            "dimension -- cannot verify the population snapshot against a live "
            "authority, so refusing rather than silently trusting the snapshot"
        ]
    expected_roots = set(population.get("expected_roots", []))
    if expected_roots != live_credited_roots:
        added = expected_roots - live_credited_roots
        dropped = live_credited_roots - expected_roots
        return [
            "STALE_POPULATION: the committed population snapshot disagrees "
            f"with the live graph-join's trust_footprints.resolved set "
            f"(snapshot-only={sorted(added)} live-only={sorted(dropped)})"
        ]
    return []
# GUARD:STALE_POPULATION end


# GUARD:ACCOUNTING begin
def check_accounting(census: dict) -> list[str]:
    failures = []
    replay = census.get("credited_roots_replay", {})
    roots = replay.get("roots", [])
    expected = replay.get("expected")
    accepted = replay.get("accepted")
    declined_typed = replay.get("declined_typed")
    missing = replay.get("missing")
    if expected is None or accepted is None or declined_typed is None or missing is None:
        return ["ACCOUNTING: credited_roots_replay is missing a required counter field"]
    if len(roots) != expected:
        failures.append(
            f"ACCOUNTING: {len(roots)} root records present but expected={expected}"
        )
    if accepted + declined_typed + missing != expected:
        failures.append(
            f"ACCOUNTING: accepted({accepted}) + declined_typed({declined_typed}) + "
            f"missing({missing}) != expected({expected})"
        )
    return failures
# GUARD:ACCOUNTING end


# GUARD:MANDATORY_MISSING_ZERO begin
def check_mandatory_missing_zero(census: dict) -> list[str]:
    missing = census.get("credited_roots_replay", {}).get("missing")
    if missing != 0:
        return [
            f"MANDATORY_MISSING_ZERO: credited_roots_replay.missing={missing}, but "
            "C2's exit criterion states missing=0 is mandatory, not merely reported"
        ]
    return []
# GUARD:MANDATORY_MISSING_ZERO end


# GUARD:BARE_NAME_ACCEPT begin
def check_bare_name_accept(census: dict) -> list[str]:
    failures = []
    for root in census.get("credited_roots_replay", {}).get("roots", []):
        if root.get("status") == "accepted" and not root.get("lean_admitted_by_name"):
            failures.append(
                f"BARE_NAME_ACCEPT: {root.get('name')!r} is marked accepted but "
                "pinned Lean's own kernel did not admit a constant of that name"
            )
    return failures
# GUARD:BARE_NAME_ACCEPT end


# GUARD:BARE_TYPE_ACCEPT begin
def check_bare_type_accept(census: dict) -> list[str]:
    failures = []
    for root in census.get("credited_roots_replay", {}).get("roots", []):
        if root.get("status") == "accepted" and not root.get("reimport_type_matches"):
            failures.append(
                f"BARE_TYPE_ACCEPT: {root.get('name')!r} is marked accepted but its "
                "reimported type did not render identically to the source type -- "
                "an accept must never rest on a name match alone"
            )
    return failures
# GUARD:BARE_TYPE_ACCEPT end


# GUARD:DECLINE_PROBE_VACUOUS begin
def check_decline_probe_vacuous(census: dict) -> list[str]:
    probe = census.get("decline_mechanism_probe", {})
    if probe.get("status") != "declined":
        return [
            "DECLINE_PROBE_VACUOUS: decline_mechanism_probe.status is "
            f"{probe.get('status')!r}, not 'declined' -- the census's decline path "
            "must be demonstrated by a real synthetic non-Prop subject, not read "
            "as a success"
        ]
    return []
# GUARD:DECLINE_PROBE_VACUOUS end


def run_all_guards(
    population: dict, census: dict, live_credited_roots: set[str] | None
) -> list[str]:
    failures: list[str] = []
    failures += check_missing(population, census)
    failures += check_stale_population(population, live_credited_roots)
    failures += check_accounting(census)
    failures += check_mandatory_missing_zero(census)
    failures += check_bare_name_accept(census)
    failures += check_bare_type_accept(census)
    failures += check_decline_probe_vacuous(census)
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census-dir", type=Path, default=DEFAULT_CENSUS_DIR)
    parser.add_argument("--population-dir", type=Path, default=DEFAULT_POPULATION_DIR)
    parser.add_argument("--graph-join-dir", type=Path, default=DEFAULT_GRAPH_JOIN_DIR)
    args = parser.parse_args()

    census_files = sorted(args.census_dir.glob("*.census.json"))
    if not census_files:
        print(
            f"NO CENSUS FILES found under {args.census_dir} -- an absent artifact is "
            "a failure, not a clean pass over nothing",
            file=sys.stderr,
        )
        return 1

    live_credited_roots = live_join_credited_roots(args.graph_join_dir)

    total_failures: list[str] = []
    checked = 0
    for census_path in census_files:
        census = load_json(census_path)
        population_id = census.get("population_id")
        if not population_id:
            total_failures.append(f"{census_path}: no population_id field")
            continue
        population_path = args.population_dir / f"{population_id}.json"
        if not population_path.is_file():
            total_failures.append(
                f"{census_path}: population file {population_path} does not exist"
            )
            continue
        population = load_json(population_path)
        failures = run_all_guards(population, census, live_credited_roots)
        if failures:
            total_failures.append(f"{census_path}:")
            total_failures.extend(f"  {f}" for f in failures)
        else:
            replay = census["credited_roots_replay"]
            print(
                f"OK {census_path.name}: expected={replay['expected']} "
                f"attempted={replay['attempted']} accepted={replay['accepted']} "
                f"declined_typed={replay['declined_typed']} missing={replay['missing']} "
                f"extra={replay['extra']}"
            )
        checked += 1

    if checked == 0:
        print("ZERO census files examined -- refusing to report a pass over nothing", file=sys.stderr)
        return 1

    if total_failures:
        print("CHECKED-INTERCHANGE GATE FAILED:", file=sys.stderr)
        for line in total_failures:
            print(line, file=sys.stderr)
        return 1

    print(f"CHECKED-INTERCHANGE GATE PASSED -- {checked} census file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
