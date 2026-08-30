"""Fixture builder for `check-infrastructure-frontier.py`'s guard functions
(L2 phase G3, ADR-0845). Each guard is a pure function over already-loaded
dicts/strings (or, for MISSING_JOIN, a filesystem path), so fixtures here
are small hand-built dicts rather than a real 446-declaration population --
the same "surgical" philosophy `graph_join_mutations.py` uses: every field
OTHER than the one property under test is kept internally consistent, so a
guard's removal cannot be rescued by an unrelated check catching the same
mutation by accident.

Used by `scripts/tests/test-infrastructure-frontier-mutations.sh` (the
guard-deletion kill table).
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lib"))
import infrastructure_frontier as inf  # noqa: E402

POPULATION_ID = "fixture-population-v1"


def _row(row_id: str, queue: str, subject: list[str], gain_kind: str) -> dict:
    return {
        "row_id": row_id,
        "queue": queue,
        "title": f"fixture row for {queue}",
        "subject_declarations": sorted(subject),
        "population_id": POPULATION_ID,
        "gain_kind": gain_kind,
        "gain_explanation": "fixture gain explanation",
        "evidence": {"raw_inputs_disclaimer": "fixture disclaimer", "per_subject": []},
        "current_blockers": ["fixture:blocker-one"],
        "destination_paths": ["docs/fixture/destination.md"],
        "destination_note": None,
        "estimated_cost": {"tier": "S", "rationale": "fixture cost rationale"},
        "preregistered_metric": {
            "description": "fixture metric description",
            "command": "/usr/bin/grep -c fixture /dev/null",
            "baseline": 0,
        },
        "confidence": "high",
        "not_this": [],
    }


def _row_id(queue: str, subject: list[str], gain_kind: str) -> str:
    return inf.row_id(queue, POPULATION_ID, subject, gain_kind)


def good_frontier() -> dict:
    lang_subject = ["FixtureStruct", "fixture_theorem"]
    lang_row = _row(_row_id("language-infrastructure", lang_subject, "statability"), "language-infrastructure", lang_subject, "statability")
    dom_subject = ["fixture_dominator"]
    dom_row = _row(_row_id("theorem-dominators", dom_subject, "independent_assurance"), "theorem-dominators", dom_subject, "independent_assurance")
    return {
        "schema_version": 1,
        "kind": "axeyum-infrastructure-frontier",
        "generated_by": "scripts/gen-infrastructure-frontier.py",
        "population_id": POPULATION_ID,
        "source_join": f"artifacts/graph-join/{POPULATION_ID}.join.json",
        "declaration_population_count": 10,
        "advisory_notice": "fixture advisory notice",
        "raw_input_disclaimer": "fixture raw input disclaimer",
        "population_summary": {"declaration_count": 10},
        "cross_check": {
            "dispatchable_frontier": {"ran": False, "note": "fixture: not run"},
            "population_overlap_note": "fixture population overlap note, non-empty",
        },
        "diagnostics": {
            "dependency_ready_leaf_candidates_before_filtering": [],
            "note": "fixture diagnostics note",
        },
        "queues": {
            "language-infrastructure": {"rows": [lang_row], "empty_reason": None},
            "proof-producers": {
                "rows": [],
                "empty_reason": (
                    "0 rows. Fixture empty reason with more than forty characters "
                    "so it clears the substantive-reason length guard."
                ),
            },
            "theorem-dominators": {"rows": [dom_row], "empty_reason": None},
            "dependency-ready-leaves": {
                "rows": [],
                "empty_reason": (
                    "0 rows. Another fixture empty reason with more than forty "
                    "characters so it clears the substantive-reason length guard."
                ),
            },
        },
    }


def good_join_dict() -> dict:
    return {
        "schema_version": 1,
        "kind": "axeyum-graph-join",
        "population_id": POPULATION_ID,
        "dimensions": {
            "fact_ids": {"resolved": {}, "unresolved": {}},
        },
        "name_coincidence_candidates": {},
    }


def write_join(path, content: dict | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(good_join_dict() if content is None else content, fh)


def bad_empty_join_dict() -> dict:
    return {"schema_version": 1, "kind": "axeyum-graph-join", "population_id": POPULATION_ID}


def bad_stale_artifact_quad() -> tuple[str, str, str, str]:
    committed_json = json.dumps({"a": 1})
    fresh_json = json.dumps({"a": 2})
    committed_md = "# stale committed\n"
    fresh_md = "# fresh recompute\n"
    return committed_json, fresh_json, committed_md, fresh_md


def bad_row_id_unique_frontier() -> dict:
    fx = copy.deepcopy(good_frontier())
    # Force both rows to share a row_id, in two different queues.
    shared = fx["queues"]["language-infrastructure"]["rows"][0]["row_id"]
    fx["queues"]["theorem-dominators"]["rows"][0]["row_id"] = shared
    return fx


def bad_row_id_purity_frontier() -> dict:
    fx = copy.deepcopy(good_frontier())
    fx["queues"]["language-infrastructure"]["rows"][0]["row_id"] = "IF-LANG-0000000000"
    return fx


def bad_empty_queue_reason_frontier() -> dict:
    fx = copy.deepcopy(good_frontier())
    fx["queues"]["proof-producers"]["empty_reason"] = "too short"
    return fx


def bad_row_evidence_incomplete_frontier() -> dict:
    fx = copy.deepcopy(good_frontier())
    fx["queues"]["language-infrastructure"]["rows"][0]["current_blockers"] = []
    return fx


def bad_cross_check_missing_frontier() -> dict:
    fx = copy.deepcopy(good_frontier())
    del fx["cross_check"]
    return fx
