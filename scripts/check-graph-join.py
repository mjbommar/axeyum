#!/usr/bin/env python3
"""Gate: validate `artifacts/graph-join/*.join.json` (L1 phase G2,
docs/plan/graph-directed-library-roadmap-2026-08-30.md).

Needs no Lean toolchain and no cargo run -- every input is already-committed
JSON, the same posture `check-declaration-graph.py` takes toward the
declaration graph it reads. This recomputes the ENTIRE join from the same
committed inputs (`scripts/lib/graph_join.py::compute_join`) and requires the
result to match the committed artifact byte-for-byte, then runs guards that
look at different failure shapes.

Six guards, six distinct mutation classes, each mutation-verified to be
killed by exactly one fixture (`scripts/tests/test-graph-join-mutations.sh`):

  EMPTY_POPULATION   the declaration-graph population has zero declarations
  EMPTY_FACTS        the fact ledger has zero facts
  ACCOUNTING         some dimension drops a population member (not resolved,
                     not unresolved -- silently missing from both)
  STALE_ARTIFACT     the committed join.json does not match a fresh
                     recomputation from the same committed inputs
  POSITIVE_CONTROL   the known-good chain (Nat.add_comm -> a real ml430
                     mirror fact -> a real, axiom-free kernel declaration)
                     must still resolve, and against the ACTUAL fact file on
                     disk, not merely against the cached join.json
  BARE_NAME_BASIS    every fact_ids/kernel_declarations resolved row must be
                     independently re-derivable from the fact it names (its
                     title really matches the mirror template; theorem_of
                     really returns the claimed subject) -- catches a
                     resolved link injected without the evidence trail this
                     whole join exists to require

Usage:
    python3 scripts/check-graph-join.py
    python3 scripts/check-graph-join.py --population-id mathlib-group-defs-v1
    python3 scripts/check-graph-join.py --graph-join-dir DIR --facts-dir DIR
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import graph_join as gj  # noqa: E402

DEFAULT_JOIN_DIR = REPO_ROOT / "artifacts" / "graph-join"


def load_json(path: Path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


# GUARD:EMPTY_POPULATION
def check_empty_population(rows: dict) -> list[str]:
    if not rows.get("declarations"):
        return ["EMPTY_POPULATION: declaration graph has zero declarations"]
    return []


# GUARD:EMPTY_FACTS
def check_empty_facts(facts_by_id: dict) -> list[str]:
    if not facts_by_id:
        return ["EMPTY_FACTS: fact ledger has zero facts"]
    return []


# GUARD:ACCOUNTING
def check_accounting(join: dict) -> list[str]:
    failures = []
    for dim_name, dim in join["dimensions"].items():
        resolved = set(dim["resolved"])
        unresolved = set(dim["unresolved"])
        if resolved & unresolved:
            failures.append(
                f"ACCOUNTING: dimension {dim_name!r} has {len(resolved & unresolved)} "
                "member(s) counted as BOTH resolved and unresolved"
            )
        total = len(resolved) + len(unresolved)
        if total != dim["population_count"]:
            failures.append(
                f"ACCOUNTING: dimension {dim_name!r} population={dim['population_count']} "
                f"but resolved+unresolved={total} -- some member was silently dropped"
            )
    return failures


# GUARD:STALE_ARTIFACT
def check_stale_artifact(committed: dict, fresh: dict) -> list[str]:
    if committed != fresh:
        return [
            "STALE_ARTIFACT: committed join.json does not match a fresh recomputation "
            "from the same committed inputs -- regenerate with scripts/gen-graph-join.py"
        ]
    return []


# GUARD:POSITIVE_CONTROL
def check_positive_control(join: dict, facts_by_id: dict) -> list[str]:
    failures = []
    fact_ids = join["dimensions"]["fact_ids"]["resolved"]
    control_name = "Nat.add_comm"
    entry = fact_ids.get(control_name)
    if entry is None:
        failures.append(
            f"POSITIVE_CONTROL: {control_name!r} did not resolve to a fact_id at all"
        )
        return failures
    fid = entry["fact_id"]
    fact = facts_by_id.get(fid)
    if fact is None:
        failures.append(
            f"POSITIVE_CONTROL: {control_name!r} resolved to fact_id {fid!r} which does "
            "not exist as an actual fact file"
        )
        return failures
    expected_title = gj.MIRROR_TITLE_TEMPLATE.format(name=control_name)
    if fact.get("title") != expected_title:
        failures.append(
            f"POSITIVE_CONTROL: fact {fid!r}'s real title {fact.get('title')!r} does not "
            f"match the required mirror template {expected_title!r}"
        )
    kd = join["dimensions"]["kernel_declarations"]["resolved"].get(control_name)
    if kd is None:
        failures.append(f"POSITIVE_CONTROL: {control_name!r} did not resolve to a kernel declaration")
    tf = join["dimensions"]["trust_footprints"]["resolved"].get(control_name)
    if tf is None or tf.get("axiom_footprint") != []:
        failures.append(
            f"POSITIVE_CONTROL: {control_name!r}'s trust footprint is not the expected "
            f"empty list (got {tf.get('axiom_footprint') if tf else 'unresolved'})"
        )
    return failures


# GUARD:BARE_NAME_BASIS
def check_bare_name_basis(join: dict, facts_by_id: dict, depends_derived) -> list[str]:
    failures = []
    fact_ids = join["dimensions"]["fact_ids"]["resolved"]
    for name, entry in fact_ids.items():
        fid = entry["fact_id"]
        fact = facts_by_id.get(fid)
        if fact is None:
            failures.append(
                f"BARE_NAME_BASIS: {name!r} resolved to fact_id {fid!r} which does not "
                "exist -- this resolution has no real evidence backing it"
            )
            continue
        expected_title = gj.MIRROR_TITLE_TEMPLATE.format(name=name)
        if fact.get("title") != expected_title:
            failures.append(
                f"BARE_NAME_BASIS: {name!r} -> {fid!r} was resolved WITHOUT the required "
                f"exact title match (fact title is {fact.get('title')!r}, expected "
                f"{expected_title!r}) -- this looks like an identity injected by name "
                "similarity, not by the mirror-fact evidence trail"
            )

    kernel_decls = join["dimensions"]["kernel_declarations"]["resolved"]
    for name, entry in kernel_decls.items():
        fid = entry["fact_id"]
        fact = facts_by_id.get(fid)
        if fact is None:
            failures.append(
                f"BARE_NAME_BASIS: kernel_declarations[{name!r}] names fact_id {fid!r} "
                "which does not exist"
            )
            continue
        subject = depends_derived.theorem_of(fact)
        if subject != entry.get("kernel_theorem"):
            failures.append(
                f"BARE_NAME_BASIS: kernel_declarations[{name!r}] claims kernel_theorem "
                f"{entry.get('kernel_theorem')!r} but re-deriving theorem_of(fact) from "
                f"{fid!r} gives {subject!r} -- the claimed link is not reproducible from "
                "the fact's own evidence"
            )
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--population-id", default=gj.DEFAULT_POPULATION_ID)
    parser.add_argument("--graph-join-dir", type=Path, default=DEFAULT_JOIN_DIR)
    parser.add_argument("--graph-dir", type=Path, default=gj.DECL_GRAPH_DIR)
    parser.add_argument("--population-dir", type=Path, default=gj.DECL_POP_DIR)
    parser.add_argument("--facts-dir", type=Path, default=gj.FACTS_DIR)
    args = parser.parse_args(argv)

    failures: list[str] = []

    try:
        rows = gj.load_rows(args.population_id, args.graph_dir)
    except FileNotFoundError as exc:
        print(f"check-graph-join: FAILED -- cannot read declaration graph: {exc}", file=sys.stderr)
        return 1
    failures += check_empty_population(rows)
    if failures:
        for f in failures:
            print(f"check-graph-join: FAILED -- {f}", file=sys.stderr)
        return 1

    try:
        facts_by_id = gj.load_facts(args.facts_dir)
    except ValueError as exc:
        print(f"check-graph-join: FAILED -- EMPTY_FACTS: {exc}", file=sys.stderr)
        return 1
    failures += check_empty_facts(facts_by_id)
    if failures:
        for f in failures:
            print(f"check-graph-join: FAILED -- {f}", file=sys.stderr)
        return 1

    join_path = args.graph_join_dir / f"{args.population_id}.join.json"
    if not join_path.exists():
        print(
            f"check-graph-join: FAILED -- no committed join at {join_path}; run "
            "scripts/gen-graph-join.py first",
            file=sys.stderr,
        )
        return 1
    committed = load_json(join_path)

    fresh = gj.compute_join(args.population_id)

    failures += check_accounting(fresh)
    failures += check_stale_artifact(committed, fresh)
    failures += check_positive_control(fresh, facts_by_id)
    depends_derived = gj._load_depends_derived_module()
    failures += check_bare_name_basis(fresh, facts_by_id, depends_derived)

    if failures:
        for f in failures:
            print(f"check-graph-join: FAILED -- {f}", file=sys.stderr)
        return 1

    dims = fresh["dimensions"]
    summary = ", ".join(
        f"{name}={dim['resolved_count']}/{dim['population_count']}" for name, dim in dims.items()
    )
    print(f"check-graph-join: OK -- population={args.population_id} {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
