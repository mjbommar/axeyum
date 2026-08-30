#!/usr/bin/env python3
"""Gate: validate `artifacts/infrastructure-frontier/<population>.frontier.json`
(L2 phase G3, docs/plan/graph-directed-library-roadmap-2026-08-30.md;
ADR-0845).

Recomputes the frontier from the same committed inputs
(`scripts/lib/infrastructure_frontier.py::build_frontier`) and requires the
result to match the committed artifact byte-for-byte, then runs guards that
each look at a different failure shape. Seven guards, seven distinct
mutation classes, each mutation-verified to be killed by exactly one
fixture (`scripts/tests/test-infrastructure-frontier-mutations.sh`):

  MISSING_JOIN          the graph-join artifact this frontier depends on is
                         absent -- "fail on absence" for the whole pipeline
  STALE_ARTIFACT         the committed frontier.json/dashboard.md do not
                         match a fresh recomputation from the same inputs
  ROW_ID_UNIQUE          two rows (in the same or different queues) share a
                         row_id
  ROW_ID_PURITY          a row's row_id does not equal the hash recomputed
                         from ONLY {queue, population_id, subject, gain_kind}
                         -- catches a volatile field (degree, a count)
                         leaking into the "stable" identifier
  EMPTY_QUEUE_REASON     a queue with zero rows has no non-trivial declared
                         empty_reason (the "fail if every queue is empty for
                         a reason you did not declare" requirement)
  ROW_EVIDENCE_COMPLETE  a row is missing current_blockers, a valid
                         gain_kind, a preregistered_metric.command, or both
                         destination_paths and destination_note
  CROSS_CHECK_PRESENT    the artifact's cross_check section is missing or
                         has no population_overlap_note (the "cross-check
                         against what the ledger already knows" requirement)

Usage:
    python3 scripts/check-infrastructure-frontier.py
    python3 scripts/check-infrastructure-frontier.py --population-id mathlib-group-defs-v1
    python3 scripts/check-infrastructure-frontier.py --frontier-dir DIR
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import infrastructure_frontier as inf  # noqa: E402

DEFAULT_FRONTIER_DIR = REPO_ROOT / "artifacts" / "infrastructure-frontier"
DEFAULT_JOIN_DIR = REPO_ROOT / "artifacts" / "graph-join"
DEFAULT_POPULATION = "mathlib-group-defs-v1"


def load_json(path: Path):
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


# GUARD:MISSING_JOIN begin
def check_missing_join(join_path: Path) -> list[str]:
    if not join_path.is_file():
        return [f"MISSING_JOIN: {join_path} does not exist"]
    try:
        doc = load_json(join_path)
    except (OSError, json.JSONDecodeError) as ex:
        return [f"MISSING_JOIN: {join_path} unreadable: {ex}"]
    if not doc.get("dimensions"):
        return [f"MISSING_JOIN: {join_path} has no dimensions"]
    return []
# GUARD:MISSING_JOIN end


# GUARD:STALE_ARTIFACT begin
def check_stale_artifact(committed_json: str, fresh_json: str, committed_md: str, fresh_md: str) -> list[str]:
    failures = []
    if committed_json != fresh_json:
        failures.append("STALE_ARTIFACT: frontier.json does not match a fresh recomputation")
    if committed_md != fresh_md:
        failures.append("STALE_ARTIFACT: dashboard.md does not match a fresh recomputation")
    return failures
# GUARD:STALE_ARTIFACT end


# GUARD:ROW_ID_UNIQUE begin
def check_row_id_unique(frontier: dict) -> list[str]:
    seen: dict[str, str] = {}
    failures = []
    for q, qd in frontier["queues"].items():
        for row in qd["rows"]:
            rid = row["row_id"]
            if rid in seen:
                failures.append(
                    f"ROW_ID_UNIQUE: row_id {rid!r} used by both {seen[rid]!r} and {q!r}"
                )
            seen[rid] = q
    return failures
# GUARD:ROW_ID_UNIQUE end


# GUARD:ROW_ID_PURITY begin
def check_row_id_purity(frontier: dict) -> list[str]:
    failures = []
    pop = frontier["population_id"]
    for q, qd in frontier["queues"].items():
        for row in qd["rows"]:
            expected = inf.row_id(q, pop, row["subject_declarations"], row["gain_kind"])
            if expected != row["row_id"]:
                failures.append(
                    f"ROW_ID_PURITY: row {row['row_id']!r} in queue {q!r} does not match "
                    f"a hash recomputed from its own (queue, population, subject, gain_kind) "
                    f"-- expected {expected!r}. A stable id must not depend on volatile fields."
                )
    return failures
# GUARD:ROW_ID_PURITY end


# GUARD:EMPTY_QUEUE_REASON begin
def check_empty_queue_reason(frontier: dict) -> list[str]:
    failures = []
    for q, qd in frontier["queues"].items():
        if qd["rows"]:
            continue
        reason = qd.get("empty_reason") or ""
        if len(reason.strip()) < 40:
            failures.append(
                f"EMPTY_QUEUE_REASON: queue {q!r} has zero rows and no substantive "
                f"declared empty_reason (got {reason!r})"
            )
    return failures
# GUARD:EMPTY_QUEUE_REASON end


# GUARD:ROW_EVIDENCE_COMPLETE begin
def check_row_evidence_complete(frontier: dict) -> list[str]:
    failures = []
    for q, qd in frontier["queues"].items():
        for row in qd["rows"]:
            rid = row["row_id"]
            if not row.get("current_blockers"):
                failures.append(f"ROW_EVIDENCE_COMPLETE: {rid} has no current_blockers")
            if row.get("gain_kind") not in inf.GAIN_KINDS:
                failures.append(f"ROW_EVIDENCE_COMPLETE: {rid} has invalid gain_kind {row.get('gain_kind')!r}")
            pm = row.get("preregistered_metric") or {}
            if not pm.get("command"):
                failures.append(f"ROW_EVIDENCE_COMPLETE: {rid} has no preregistered_metric.command")
            if not row.get("destination_paths") and not row.get("destination_note"):
                failures.append(
                    f"ROW_EVIDENCE_COMPLETE: {rid} has empty destination_paths and no destination_note"
                )
    return failures
# GUARD:ROW_EVIDENCE_COMPLETE end


# GUARD:CROSS_CHECK_PRESENT begin
def check_cross_check_present(frontier: dict) -> list[str]:
    cc = frontier.get("cross_check")
    if not cc:
        return ["CROSS_CHECK_PRESENT: frontier has no cross_check section"]
    if not cc.get("population_overlap_note"):
        return ["CROSS_CHECK_PRESENT: cross_check has no population_overlap_note"]
    if "dispatchable_frontier" not in cc:
        return ["CROSS_CHECK_PRESENT: cross_check has no dispatchable_frontier sub-section"]
    return []
# GUARD:CROSS_CHECK_PRESENT end


def run_all_guards(frontier: dict, join_path: Path, committed_json: str, fresh_json: str, committed_md: str, fresh_md: str) -> list[str]:
    failures: list[str] = []
    failures += check_missing_join(join_path)
    failures += check_stale_artifact(committed_json, fresh_json, committed_md, fresh_md)
    failures += check_row_id_unique(frontier)
    failures += check_row_id_purity(frontier)
    failures += check_empty_queue_reason(frontier)
    failures += check_row_evidence_complete(frontier)
    failures += check_cross_check_present(frontier)
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--population-id", default=DEFAULT_POPULATION)
    ap.add_argument("--frontier-dir", type=Path, default=DEFAULT_FRONTIER_DIR)
    ap.add_argument("--join-dir", type=Path, default=DEFAULT_JOIN_DIR)
    args = ap.parse_args()

    json_path = args.frontier_dir / f"{args.population_id}.frontier.json"
    md_path = args.frontier_dir / f"{args.population_id}.dashboard.md"
    join_path = args.join_dir / f"{args.population_id}.join.json"

    join_failures = check_missing_join(join_path)
    if join_failures:
        for f in join_failures:
            print(f"FAIL: {f}")
        return 1

    if not json_path.is_file():
        print(f"FAIL: {json_path} does not exist -- run scripts/gen-infrastructure-frontier.py")
        return 1
    if not md_path.is_file():
        print(f"FAIL: {md_path} does not exist -- run scripts/gen-infrastructure-frontier.py")
        return 1

    committed_json = json_path.read_text(encoding="utf-8")
    committed_md = md_path.read_text(encoding="utf-8")

    try:
        frontier = json.loads(committed_json)
    except json.JSONDecodeError as ex:
        print(f"FAIL: {json_path} is not valid JSON: {ex}")
        return 1

    try:
        fresh_frontier = inf.build_frontier(args.population_id)
    except ValueError as ex:
        print(f"FAIL: candidate validation failed on fresh recompute: {ex}")
        return 1

    fresh_json = json.dumps(fresh_frontier, indent=2, sort_keys=False) + "\n"

    # Import gen's renderer without re-implementing it.
    gen_spec_path = REPO_ROOT / "scripts" / "gen-infrastructure-frontier.py"
    import importlib.util

    spec = importlib.util.spec_from_file_location("gen_infra_frontier", gen_spec_path)
    gen_mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(gen_mod)
    fresh_md = gen_mod.render_dashboard(fresh_frontier)

    failures = run_all_guards(frontier, join_path, committed_json, fresh_json, committed_md, fresh_md)

    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        print(f"FAIL: {len(failures)} guard failure(s)")
        return 1

    total_rows = sum(len(qd["rows"]) for qd in frontier["queues"].values())
    empty_queues = [q for q, qd in frontier["queues"].items() if not qd["rows"]]
    print(
        f"OK: infrastructure frontier for {args.population_id!r} -- "
        f"{total_rows} row(s) across {len(inf.QUEUES)} queues "
        f"({len(empty_queues)} empty: {', '.join(empty_queues) or 'none'})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
