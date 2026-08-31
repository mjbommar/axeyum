#!/usr/bin/env python3
"""Gate: validate `artifacts/structural-index/*` (L3 phase D2, ADR-0905).

Needs no cargo run and no Lean toolchain -- every input is already-committed
JSON (`theorems.json`, produced once by
`cargo run --release -p axeyum-lean-kernel --example structural_index_extract`,
plus the fact ledger and the two nursery files). This re-derives the
Mathlib goal-feature join and every fixed query result FROM those committed
inputs via `scripts/lib/structural_index.py` and compares against the
committed artifacts, then runs six guards, each isolating one distinct
mutation class (mutation-verified 1:1 in
`scripts/tests/test-structural-index-mutations.sh`):

  EMPTY_INDEX          theorems.json has at least one declaration
  FIXED_QUERIES        every committed query reproduces its committed
                       expected_names exactly, from a FRESH re-run
  HELD_OUT_EXCLUDED    a freshly recomputed held-out fact_id set (from the
                       two nursery files, an authority this artifact does
                       not control) has zero overlap with the fact_ids in
                       the committed mathlib-goal-features.json
  GOAL_FEATURE_NO_LEAK every mathlib-goal-features.json record has EXACTLY
                       the four allowed keys -- no evidence/provenance field
                       can ever appear, even if a future edit adds one to
                       the fact schema
  SIGNAL_SEPARATION    the committed identity-miss / lexical-hit query pair
                       disagrees on the SAME name, proving the two columns
                       are not silently merged into one score
  ABSENCE_UNANSWERABLE a query naming an unknown dependency is reported
                       UNANSWERABLE, never a silent empty match

Each `check_*` guard returns a list of problem strings (empty == pass), the
same shape `check-graph-join.py` uses, so a mutation harness can delete one
guard's body (`return []`) and re-run every fixture without needing to fake
an exit-code path.

Exit 0 all guards pass; exit 1 at least one guard failed (all failures are
printed, not just the first).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import structural_index as si  # noqa: E402

OUT_DIR = si.INDEX_DIR


def load_json(path: Path):
    if not path.exists():
        raise FileNotFoundError(str(path))
    return json.loads(path.read_text(encoding="utf-8"))


# GUARD:EMPTY_INDEX
def check_empty_index(records: list[dict]) -> list[str]:
    if not records:
        return ["EMPTY_INDEX: theorems.json contains zero declarations"]
    return []


# GUARD:FIXED_QUERIES
def check_fixed_queries(records: list[dict], dep_index: dict, queries: list[dict]) -> list[str]:
    if not queries:
        return ["FIXED_QUERIES: queries.json is empty"]
    problems = []
    for spec in queries:
        qid = spec["id"]
        query = spec["query"]
        if spec.get("expect_unanswerable"):
            try:
                si.run_query(records, dep_index, query)
                problems.append(f"FIXED_QUERIES: query {qid!r} was expected UNANSWERABLE but answered")
            except si.Unanswerable:
                pass
            continue
        try:
            rows = si.run_query(records, dep_index, query)
        except si.Unanswerable as exc:
            problems.append(f"FIXED_QUERIES: query {qid!r} unexpectedly unanswerable: {exc}")
            continue
        got = sorted(r["name"] for r in rows)
        expected = spec.get("expected_names")
        if expected is None:
            problems.append(f"FIXED_QUERIES: query {qid!r} has no committed expected_names")
        elif got != expected:
            problems.append(f"FIXED_QUERIES: query {qid!r} expected {expected} got {got}")
    return problems


# GUARD:HELD_OUT_EXCLUDED
def check_held_out_excluded(features: list[dict]) -> list[str]:
    # Freshly recomputed from the nursery files -- an authority this
    # artifact does not control -- never from the manifest's own recorded
    # count, for the reason ADR-0800's MISSING guard reads an external
    # population registry rather than the pack's own metadata.
    held_out = si.held_out_fact_ids()
    if not held_out:
        return ["HELD_OUT_EXCLUDED: recomputed held-out set is empty -- unanswerable"]
    leaked = [f["fact_id"] for f in features if f["fact_id"] in held_out]
    if leaked:
        return [
            f"HELD_OUT_EXCLUDED: {len(leaked)} held-out fact_id(s) present in "
            f"mathlib-goal-features.json: {leaked[:5]}"
        ]
    return []


# GUARD:GOAL_FEATURE_NO_LEAK
def check_goal_feature_no_leak(features: list[dict]) -> list[str]:
    if not features:
        return ["GOAL_FEATURE_NO_LEAK: mathlib-goal-features.json is empty"]
    problems = []
    for record in features:
        keys = set(record.keys())
        if keys != si.GOAL_FEATURE_KEYS:
            problems.append(
                f"GOAL_FEATURE_NO_LEAK: record for {record.get('fact_id')!r} has keys "
                f"{sorted(keys)}, expected exactly {sorted(si.GOAL_FEATURE_KEYS)}"
            )
    return problems


# GUARD:SIGNAL_SEPARATION
def check_signal_separation(records: list[dict], dep_index: dict, queries: list[dict]) -> list[str]:
    by_id = {q["id"]: q for q in queries}
    identity_q = by_id.get("identity-miss-on-plausible-guess")
    lexical_q = by_id.get("lexical-hit-on-same-guess")
    if identity_q is None or lexical_q is None:
        return ["SIGNAL_SEPARATION: committed queries.json is missing the identity/lexical pair"]
    identity_rows = si.run_query(records, dep_index, identity_q["query"])
    lexical_rows = si.run_query(records, dep_index, lexical_q["query"])
    problems = []
    if identity_rows:
        problems.append("SIGNAL_SEPARATION: identity query unexpectedly matched")
    if not lexical_rows:
        problems.append("SIGNAL_SEPARATION: lexical query unexpectedly found nothing")
    for row in lexical_rows:
        if row["identity_match"]:
            problems.append(
                f"SIGNAL_SEPARATION: lexical row for {row['name']!r} claims "
                "identity_match=True; the two columns must never be conflated"
            )
    return problems


# GUARD:ABSENCE_UNANSWERABLE
def check_absence_unanswerable(records: list[dict], dep_index: dict, queries: list[dict]) -> list[str]:
    unanswerable_specs = [q for q in queries if q.get("expect_unanswerable")]
    if not unanswerable_specs:
        return ["ABSENCE_UNANSWERABLE: no committed query is marked expect_unanswerable"]
    problems = []
    for spec in unanswerable_specs:
        try:
            si.run_query(records, dep_index, spec["query"])
            problems.append(
                f"ABSENCE_UNANSWERABLE: query {spec['id']!r} was expected UNANSWERABLE "
                "but returned a result"
            )
        except si.Unanswerable:
            pass
    return problems


def main() -> int:
    try:
        records = si.load_theorems(OUT_DIR / "theorems.json")
        features = load_json(OUT_DIR / "mathlib-goal-features.json")
        queries = load_json(OUT_DIR / "queries.json")
    except FileNotFoundError as exc:
        print(f"CHECK_STRUCTURAL_INDEX_FAIL|guard=MISSING_ARTIFACT|{exc}", file=sys.stderr)
        return 1

    dep_index = si.build_dependency_index(records)

    problems: list[str] = []
    problems += check_empty_index(records)
    problems += check_fixed_queries(records, dep_index, queries)
    problems += check_held_out_excluded(features)
    problems += check_goal_feature_no_leak(features)
    problems += check_signal_separation(records, dep_index, queries)
    problems += check_absence_unanswerable(records, dep_index, queries)

    if problems:
        for p in problems:
            print(f"CHECK_STRUCTURAL_INDEX_FAIL|{p}", file=sys.stderr)
        return 1

    print(
        "CHECK_STRUCTURAL_INDEX_PASS|"
        f"records={len(records)}|goal_features={len(features)}|queries={len(queries)}|"
        "guards=6"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
