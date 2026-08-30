#!/usr/bin/env python3
"""Gate: L2 phase G5 -- graph selection as the ordinary dispatcher
(docs/plan/graph-directed-library-roadmap-2026-08-30.md, section G5).

G5's own spec is the failure mode this gate exists to prevent: "The
curriculum chooses the destination, the infrastructure frontier chooses the
capability, and `fact-frontier.py` chooses the specific legal target inside
that cluster. A lane can override the ordering only with an evidence note."
A composed dispatcher that silently recommends nothing and exits 0, or that
can be made to propose a HELD-OUT fact (ADR-0542's blind evaluation
population), is worse than no dispatcher, because lanes will follow it.

Two artifact halves get DIFFERENT treatment here, and the difference is
deliberate, not an oversight:

  - `destination` and `capability` are derived from `docs/curriculum/
    curriculum.toml` and `artifacts/infrastructure-frontier/*.frontier.json`
    -- both effectively FROZEN between G3 regenerations. These ARE checked
    byte-for-byte against a fresh recomputation (STALE_DESTINATION_CAPABILITY),
    the same convention every other G* gate in this pipeline uses.
  - `legal_target` is derived from `check-dispatchable-frontier.py --json`,
    which reads the mutable fact ledger and changes every time a fact is
    proved or a mirror is drawn. Requiring it to match a historical committed
    snapshot byte-for-byte would fail this gate every time the flywheel makes
    ordinary progress -- exactly the false-failure trap CLAUDE.md documents
    elsewhere. So `legal_target` is checked STRUCTURALLY against a FRESH
    recomputation (never held-out/mutation/blocked, authority correctly
    scoped, row citation valid) rather than for historical equality.

Ten guards, each mutation-verified to be killed by exactly one fixture
(scripts/tests/test-graph-dispatcher-mutations.sh):

  MISSING_INPUTS                curriculum.toml or every infrastructure-
                                 frontier document is absent/unreadable
  NO_DESTINATION                layer 1 produced no destination
  NO_CAPABILITY                 layer 2 produced no capability for that
                                 destination
  UPSTREAM_GUARD_PROPAGATION    check-dispatchable-frontier.py itself failed
                                 (nonzero exit, guard_failures, or unparseable
                                 JSON) and this composition did not refuse to
                                 build on top of it
  LEGAL_TARGET_PRESENT          the dispatchable set was empty and this
                                 composition still produced a legal_target
  HELD_OUT_NEVER_PROPOSED       the committed recommendation's legal_target,
                                 OR any override.jsonl entry's overridden_to,
                                 is held-out/mutation/blocked
  AUTHORITY_SCOPE                "authoritative" appears outside exactly the
                                 (population, queue) pair ADR-0865 measured,
                                 or a "fallback"-matched legal target is
                                 labeled authoritative
  ROW_CITATION_VALID             the cited capability row_id/title/subject_
                                 declarations do not match the real frontier
                                 artifact
  OVERRIDE_LEDGER_COMPLETE       an overrides.jsonl entry has an empty/short
                                 evidence_note, or one that does not name the
                                 fact it overrides
  ADR_CITATION_PRESENT           a cited ADR path is missing from the tree,
                                 or ADR-0865 is missing from the citation list

Usage:
    python3 scripts/check-graph-dispatcher.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import graph_dispatcher as gd  # noqa: E402

OUT_DIR = REPO_ROOT / "artifacts" / "graph-dispatcher"
RECOMMENDATION_JSON = OUT_DIR / "recommendation.json"
DASHBOARD_MD = OUT_DIR / "dashboard.md"
OVERRIDES_JSONL = OUT_DIR / "overrides.jsonl"

GUARDS = [
    "MISSING_INPUTS",
    "NO_DESTINATION",
    "NO_CAPABILITY",
    "UPSTREAM_GUARD_PROPAGATION",
    "LEGAL_TARGET_PRESENT",
    "HELD_OUT_NEVER_PROPOSED",
    "AUTHORITY_SCOPE",
    "ROW_CITATION_VALID",
    "OVERRIDE_LEDGER_COMPLETE",
    "ADR_CITATION_PRESENT",
]


# GUARD:MISSING_INPUTS begin
def check_missing_inputs(curriculum_path: Path, frontier_dir: Path) -> list[str]:
    failures = []
    if not curriculum_path.is_file():
        failures.append(f"MISSING_INPUTS: curriculum file missing at {curriculum_path}")
    if not frontier_dir.is_dir() or not list(frontier_dir.glob("*.frontier.json")):
        failures.append(
            f"MISSING_INPUTS: no *.frontier.json under {frontier_dir}")
    return failures
# GUARD:MISSING_INPUTS end


# GUARD:NO_DESTINATION begin
def check_no_destination(destination: dict | None, error: str | None) -> list[str]:
    if destination is None:
        return [f"NO_DESTINATION: layer 1 (curriculum) produced no destination: {error}"]
    return []
# GUARD:NO_DESTINATION end


# GUARD:NO_CAPABILITY begin
def check_no_capability(capability: dict | None, error: str | None) -> list[str]:
    if capability is None:
        return [f"NO_CAPABILITY: layer 2 (infrastructure frontier) produced no capability: {error}"]
    return []
# GUARD:NO_CAPABILITY end


# GUARD:UPSTREAM_GUARD_PROPAGATION begin
def check_upstream_guard_propagation(dispatch_result: dict | None, dispatch_error: str | None) -> list[str]:
    """If check-dispatchable-frontier.py failed (nonzero exit, non-empty
    guard_failures, or its JSON was unparseable), this composition must have
    refused (raised DispatcherError) rather than silently continuing.
    `dispatch_result` is None exactly when it refused correctly."""
    if dispatch_result is None:
        return []
    exit_code = dispatch_result.get("_exit_code")
    failures = dispatch_result.get("guard_failures") or []
    if exit_code != 0 or failures:
        return [
            "UPSTREAM_GUARD_PROPAGATION: check-dispatchable-frontier.py "
            f"reported exit={exit_code} guard_failures={failures!r} and the "
            "dispatcher did not refuse to compose on top of it"
        ]
    return []
# GUARD:UPSTREAM_GUARD_PROPAGATION end


# GUARD:LEGAL_TARGET_PRESENT begin
def check_legal_target_present(dispatchable_count: int | None, legal_target_fact_id: str | None) -> list[str]:
    if dispatchable_count == 0 and legal_target_fact_id is not None:
        return [
            "LEGAL_TARGET_PRESENT: the dispatchable set was empty but a "
            f"legal_target ({legal_target_fact_id!r}) was still produced"
        ]
    return []
# GUARD:LEGAL_TARGET_PRESENT end


# GUARD:HELD_OUT_NEVER_PROPOSED begin
def check_held_out_never_proposed(
    legal_target_fact_id: str | None,
    override_targets: list[str],
    forbidden: set[str],
) -> list[str]:
    failures = []
    if legal_target_fact_id is not None and legal_target_fact_id in forbidden:
        failures.append(
            "HELD_OUT_NEVER_PROPOSED: recommendation.json's legal_target "
            f"{legal_target_fact_id!r} is held-out, a mutation control, or "
            "structurally blocked"
        )
    for fid in override_targets:
        if fid in forbidden:
            failures.append(
                "HELD_OUT_NEVER_PROPOSED: overrides.jsonl records an override "
                f"to {fid!r}, which is held-out, a mutation control, or "
                "structurally blocked"
            )
    return failures
# GUARD:HELD_OUT_NEVER_PROPOSED end


# GUARD:AUTHORITY_SCOPE begin
def check_authority_scope(recommendation: dict) -> list[str]:
    failures = []
    cap = recommendation.get("capability") or {}
    scoped = (
        cap.get("population_id") == gd.PILOTED_POPULATION
        and cap.get("queue") in gd.PILOTED_QUEUES
    )
    if cap.get("authority") == "authoritative" and not scoped:
        failures.append(
            "AUTHORITY_SCOPE: capability is labeled authoritative but "
            f"(population={cap.get('population_id')!r}, queue={cap.get('queue')!r}) "
            f"is outside ADR-0865's tested scope ({gd.PILOTED_POPULATION!r}, "
            f"{sorted(gd.PILOTED_QUEUES)})"
        )
    if scoped and cap.get("authority") != "authoritative":
        failures.append(
            "AUTHORITY_SCOPE: capability IS inside ADR-0865's tested scope "
            f"but is labeled {cap.get('authority')!r}, not authoritative"
        )
    lt = recommendation.get("legal_target") or {}
    if lt.get("match_kind") == "fallback" and lt.get("authority") == "authoritative":
        failures.append(
            "AUTHORITY_SCOPE: legal_target has match_kind 'fallback' (an "
            "unlinked local-ready pick) but is labeled authoritative -- a "
            "fallback was never selected BY the capability"
        )
    return failures
# GUARD:AUTHORITY_SCOPE end


# GUARD:ROW_CITATION_VALID begin
def check_row_citation_valid(recommendation: dict, frontier_docs: dict[str, dict]) -> list[str]:
    cap = recommendation.get("capability") or {}
    pop = cap.get("population_id")
    doc = frontier_docs.get(pop)
    if doc is None:
        return [f"ROW_CITATION_VALID: cited population {pop!r} has no published frontier document"]
    qd = (doc.get("queues") or {}).get(cap.get("queue"))
    if qd is None:
        return [f"ROW_CITATION_VALID: cited queue {cap.get('queue')!r} does not exist in {pop!r}"]
    rows = {r["row_id"]: r for r in qd.get("rows", [])}
    row = rows.get(cap.get("row_id"))
    if row is None:
        return [f"ROW_CITATION_VALID: cited row_id {cap.get('row_id')!r} is not in {pop!r}/{cap.get('queue')!r}"]
    failures = []
    if row.get("title") != cap.get("title"):
        failures.append(
            f"ROW_CITATION_VALID: cited title {cap.get('title')!r} does not "
            f"match the real row's title {row.get('title')!r}"
        )
    if row.get("subject_declarations") != cap.get("subject_declarations"):
        failures.append(
            "ROW_CITATION_VALID: cited subject_declarations do not match the "
            "real row's subject_declarations"
        )
    return failures
# GUARD:ROW_CITATION_VALID end


# GUARD:OVERRIDE_LEDGER_COMPLETE begin
def check_override_ledger_complete(entries: list[dict]) -> list[str]:
    failures = []
    for i, entry in enumerate(entries):
        note = entry.get("evidence_note") or ""
        overridden_to = entry.get("overridden_to")
        if len(note.strip()) < gd.MIN_EVIDENCE_NOTE_CHARS:
            failures.append(
                f"OVERRIDE_LEDGER_COMPLETE: overrides.jsonl entry {i} has an "
                f"evidence_note under {gd.MIN_EVIDENCE_NOTE_CHARS} chars"
            )
        if not overridden_to or overridden_to not in note:
            failures.append(
                f"OVERRIDE_LEDGER_COMPLETE: overrides.jsonl entry {i}'s "
                "evidence_note does not name the fact it overrides "
                f"({overridden_to!r})"
            )
        if not entry.get("lane") or entry.get("lane") == "unknown":
            failures.append(
                f"OVERRIDE_LEDGER_COMPLETE: overrides.jsonl entry {i} has no "
                "identified lane"
            )
    return failures
# GUARD:OVERRIDE_LEDGER_COMPLETE end


# GUARD:ADR_CITATION_PRESENT begin
def check_adr_citation_present(citations: list[str]) -> list[str]:
    failures = []
    if not any("adr-0865" in c for c in citations):
        failures.append("ADR_CITATION_PRESENT: ADR-0865 is missing from adr_citations")
    for c in citations:
        if not (REPO_ROOT / c).is_file():
            failures.append(f"ADR_CITATION_PRESENT: cited path {c!r} does not exist in the tree")
    return failures
# GUARD:ADR_CITATION_PRESENT end


def load_overrides(path: Path) -> list[dict[str, Any]]:
    if not path.is_file():
        return []
    entries = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        entries.append(json.loads(line))
    return entries


def main() -> int:
    inputs_failures = check_missing_inputs(gd.CURRICULUM_PATH, gd.FRONTIER_DIR)
    if inputs_failures:
        for f in inputs_failures:
            print(f"FAIL: {f}")
        return 1

    if not RECOMMENDATION_JSON.is_file():
        print(f"FAIL: {RECOMMENDATION_JSON} does not exist -- run scripts/gen-graph-dispatcher.py")
        return 1
    try:
        recommendation = json.loads(RECOMMENDATION_JSON.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"FAIL: {RECOMMENDATION_JSON} is not valid JSON: {exc}")
        return 1

    failures: list[str] = []

    # Fresh recomputation of layers 1-2 (frozen inputs: curriculum.toml +
    # infrastructure-frontier/*.frontier.json). Checked byte-for-byte against
    # the committed recommendation's destination/capability sections.
    nodes = gd.load_curriculum_nodes()
    frontier_docs = gd.load_frontier_documents()

    destination = None
    destination_error = None
    try:
        destination = gd.select_destination(nodes, frontier_docs)
    except gd.DispatcherError as exc:
        destination_error = str(exc)
    failures += check_no_destination(destination, destination_error)

    capability = None
    capability_error = None
    if destination is not None:
        try:
            capability = gd.select_capability(destination, frontier_docs)
        except gd.DispatcherError as exc:
            capability_error = str(exc)
    failures += check_no_capability(capability, capability_error)

    if destination is not None and capability is not None:
        fresh_destination_section = {
            "node_id": destination["node_id"],
            "title": destination["title"],
            "layer": destination["layer"],
            "path": destination["path"],
            "selection_reason": destination["selection_reason"],
            "candidates_considered": destination["candidates_considered"],
        }
        if fresh_destination_section != recommendation.get("destination"):
            failures.append(
                "STALE_DESTINATION_CAPABILITY: recommendation.json's "
                "destination section does not match a fresh recomputation "
                "-- run scripts/gen-graph-dispatcher.py"
            )
        row = capability["row"]
        fresh_capability_section = {
            "population_id": capability["population_id"],
            "queue": capability["queue"],
            "row_id": row["row_id"],
            "title": row["title"],
            "subject_declarations": row["subject_declarations"],
            "gain_kind": row["gain_kind"],
            "preregistered_metric": row["preregistered_metric"],
            "authority": capability["authority"],
            "authority_reason": capability["authority_reason"],
            "candidates_considered": capability["candidates_considered"],
        }
        if fresh_capability_section != recommendation.get("capability"):
            failures.append(
                "STALE_DESTINATION_CAPABILITY: recommendation.json's "
                "capability section does not match a fresh recomputation "
                "-- run scripts/gen-graph-dispatcher.py"
            )

    # Layer 3 is live (the mutable fact ledger); check STRUCTURALLY against a
    # fresh run, never for historical byte-equality (see module docstring).
    dispatch_result = None
    dispatch_error = None
    try:
        dispatch_result = gd.run_dispatchable_frontier()
    except gd.DispatcherError as exc:
        dispatch_error = str(exc)
    failures += check_upstream_guard_propagation(dispatch_result, dispatch_error)

    dispatchable_count = None
    forbidden: set[str] = set()
    if dispatch_result is not None:
        dispatchable_count = len(dispatch_result.get("dispatchable") or [])
        forbidden = gd.forbidden_fact_ids(dispatch_result)

    lt = recommendation.get("legal_target") or {}
    failures += check_legal_target_present(dispatchable_count, lt.get("fact_id"))

    overrides = load_overrides(OVERRIDES_JSONL)
    override_targets = [e.get("overridden_to") for e in overrides if e.get("overridden_to")]
    failures += check_held_out_never_proposed(lt.get("fact_id"), override_targets, forbidden)

    failures += check_authority_scope(recommendation)
    failures += check_row_citation_valid(recommendation, frontier_docs)
    failures += check_override_ledger_complete(overrides)
    failures += check_adr_citation_present(recommendation.get("adr_citations") or [])

    if not DASHBOARD_MD.is_file():
        failures.append(f"MISSING_INPUTS: {DASHBOARD_MD} does not exist -- run scripts/gen-graph-dispatcher.py")

    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        print(f"FAIL: {len(failures)} guard failure(s)")
        return 1

    print(
        "OK: graph dispatcher -- destination="
        f"{recommendation['destination']['node_id']!r} "
        f"capability={recommendation['capability']['row_id']!r} "
        f"[{recommendation['capability']['authority']}] "
        f"legal_target={lt.get('fact_id')!r} [{lt.get('authority')}] "
        f"overrides={len(overrides)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
