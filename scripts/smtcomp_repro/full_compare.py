"""Fail-closed same-population comparison for the credited full run.

This module consumes already-validated result records.  It does not launch a
solver or inspect a live host.  Cell-result validation remains the execution
coordinator's responsibility; the authority record binds those completions.
"""

from __future__ import annotations

import copy
import time
from collections import Counter
from pathlib import Path
from typing import Any, Callable, Iterable

from full_population import POPULATION_COUNT, SOLVER_IDS
from resume_contract import (
    RESULT_RECORD_FIELDS,
    RESULT_SCHEMA,
    ContractError,
    digest,
)
from resume_fs import atomic_install_json, read_canonical_json
from resume_runner import sha256_file


COMPARISON_SCHEMA = "axeyum.smtcomp-credited-full-comparison.v1"
PUBLICATION_SCHEMA = "axeyum.smtcomp-credited-full-comparison-publication.v1"
REPORTED_STATUSES = ("no-verdict", "sat", "unknown", "unsat")
DECISION_CLASSES = (
    "known-contradiction",
    "known-correct",
    "no-decision",
    "unadjudicated-decision",
)
PAIR_CLASSES = (
    "both-decide-agree",
    "disagreement",
    "left-only-decides",
    "neither-decides",
    "right-only-decides",
)
THREE_CLASSES = (
    "disagreement",
    "none-decide",
    "one-decides",
    "three-decide-agree",
    "two-decide-agree",
)
PAIR_ROWS = (
    ("axeyum_cvc5", "axeyum", "cvc5"),
    ("axeyum_bitwuzla", "axeyum", "bitwuzla"),
    ("cvc5_bitwuzla", "cvc5", "bitwuzla"),
)
AUTHORITY_FIELDS = {
    "fixture_only",
    "preparation_record_sha256",
    "selection_record_sha256",
    "cell_results",
}
COMPARISON_FIELDS = {
    "schema",
    "authority",
    "population_contract",
    "native_cells",
    "pairwise",
    "three_solver",
    "integrity",
    "claim_boundary",
    "record_sha256",
}
PUBLICATION_FIELDS = {
    "schema",
    "status",
    "comparison_record_sha256",
    "comparison_file_sha256",
    "population_count",
    "key_set_sha256",
    "published_at_ns",
    "record_sha256",
}
PhaseHook = Callable[[str], None]


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _logic(record: dict[str, Any]) -> str:
    benchmark_id = record.get("benchmark_id")
    _expect(
        isinstance(benchmark_id, str) and "/" in benchmark_id,
        "full comparison benchmark ID mismatch",
    )
    return benchmark_id.split("/", 1)[0]


def _key(record: dict[str, Any]) -> tuple[str, str]:
    benchmark_id = record.get("benchmark_id")
    benchmark_sha256 = record.get("benchmark_sha256")
    _expect(isinstance(benchmark_id, str), "full comparison benchmark ID mismatch")
    _expect(
        _is_sha256(benchmark_sha256),
        "full comparison benchmark SHA-256 mismatch",
    )
    return benchmark_id, benchmark_sha256


def _reported(record: dict[str, Any]) -> str:
    reported = record.get("reported_status")
    _expect(
        reported in {None, "sat", "unsat", "unknown"},
        "full comparison reported status mismatch",
    )
    return reported if reported is not None else "no-verdict"


def _is_decision(record: dict[str, Any]) -> bool:
    return record.get("reported_status") in {"sat", "unsat"}


def _decision_class(record: dict[str, Any]) -> str:
    expected = record.get("expected_status")
    _expect(
        expected in {None, "sat", "unsat"},
        "full comparison expected status mismatch",
    )
    if not _is_decision(record):
        return "no-decision"
    if expected is None:
        return "unadjudicated-decision"
    if expected == record["reported_status"]:
        return "known-correct"
    return "known-contradiction"


def _count_all(counter: Counter[str], names: Iterable[str]) -> dict[str, int]:
    return {name: counter[name] for name in names}


def _key_set_sha256(keys: Iterable[tuple[str, str]]) -> str:
    return digest(
        [
            {"benchmark_id": benchmark_id, "benchmark_sha256": benchmark_sha256}
            for benchmark_id, benchmark_sha256 in sorted(keys)
        ]
    )


def _record_set_sha256(records: Iterable[dict[str, Any]]) -> str:
    return digest(
        [
            {
                "benchmark_id": row["benchmark_id"],
                "benchmark_sha256": row["benchmark_sha256"],
                "record_sha256": row["record_sha256"],
            }
            for row in sorted(records, key=_key)
        ]
    )


def _index_records(
    solver_id: str,
    records: Iterable[dict[str, Any]],
    expected_logics: set[str],
    *,
    fixture_only: bool,
) -> dict[tuple[str, str], dict[str, Any]]:
    indexed: dict[tuple[str, str], dict[str, Any]] = {}
    for record in records:
        _expect(isinstance(record, dict), "full comparison record is not an object")
        _expect(
            record.get("record_sha256") == _sealed(record)["record_sha256"],
            "full comparison record seal mismatch",
        )
        if not fixture_only:
            _expect(
                set(record) == RESULT_RECORD_FIELDS
                and record.get("schema") == RESULT_SCHEMA,
                "live full comparison result-record schema mismatch",
            )
        _expect(
            record.get("solver_id") == solver_id,
            "full comparison solver identity drift",
        )
        _expect(
            type(record.get("sequence")) is int and record["sequence"] >= 0,
            "full comparison sequence mismatch",
        )
        _expect(
            isinstance(record.get("termination_class"), str)
            and bool(record["termination_class"]),
            "full comparison termination class mismatch",
        )
        logic = _logic(record)
        _expect(logic in expected_logics, "full comparison logic inventory drift")
        _reported(record)
        _decision_class(record)
        key = _key(record)
        _expect(key not in indexed, "duplicate full comparison benchmark identity")
        indexed[key] = record
    return indexed


def _summary(records: Iterable[dict[str, Any]]) -> dict[str, Any]:
    material = list(records)
    statuses = Counter(_reported(row) for row in material)
    decisions = Counter(_decision_class(row) for row in material)
    terminations = Counter(row["termination_class"] for row in material)
    return {
        "population": len(material),
        "decision_count": sum(_is_decision(row) for row in material),
        "reported_status_counts": _count_all(statuses, REPORTED_STATUSES),
        "decision_expected_status_counts": _count_all(
            decisions, DECISION_CLASSES
        ),
        "termination_counts": dict(sorted(terminations.items())),
    }


def _cell_summary(
    indexed: dict[tuple[str, str], dict[str, Any]], logics: list[str]
) -> dict[str, Any]:
    records = list(indexed.values())
    return {
        **_summary(records),
        "key_set_sha256": _key_set_sha256(indexed),
        "record_set_sha256": _record_set_sha256(records),
        "per_logic": {
            logic: _summary(row for row in records if _logic(row) == logic)
            for logic in logics
        },
    }


def _pair_projection(
    left_id: str,
    right_id: str,
    left: dict[tuple[str, str], dict[str, Any]],
    right: dict[tuple[str, str], dict[str, Any]],
    keys: Iterable[tuple[str, str]],
) -> dict[str, Any]:
    material = sorted(keys)
    counts: Counter[str] = Counter()
    for key in material:
        left_decides = _is_decision(left[key])
        right_decides = _is_decision(right[key])
        if left_decides and right_decides:
            category = (
                "both-decide-agree"
                if left[key]["reported_status"] == right[key]["reported_status"]
                else "disagreement"
            )
        elif left_decides:
            category = "left-only-decides"
        elif right_decides:
            category = "right-only-decides"
        else:
            category = "neither-decides"
        counts[category] += 1
    return {
        "population": len(material),
        "key_set_sha256": _key_set_sha256(material),
        "decision_projection": _count_all(counts, PAIR_CLASSES),
    }


def _pair_summary(
    left_id: str,
    right_id: str,
    indexed: dict[str, dict[tuple[str, str], dict[str, Any]]],
    logics: list[str],
) -> dict[str, Any]:
    left = indexed[left_id]
    right = indexed[right_id]
    keys = set(left)
    return {
        "left_solver": left_id,
        "right_solver": right_id,
        "overall": _pair_projection(left_id, right_id, left, right, keys),
        "per_logic": {
            logic: _pair_projection(
                left_id,
                right_id,
                left,
                right,
                (key for key in keys if _logic(left[key]) == logic),
            )
            for logic in logics
        },
    }


def _three_projection(
    indexed: dict[str, dict[tuple[str, str], dict[str, Any]]],
    keys: Iterable[tuple[str, str]],
) -> dict[str, Any]:
    material = sorted(keys)
    counts: Counter[str] = Counter()
    sole_deciders: Counter[str] = Counter()
    sole_non_deciders: Counter[str] = Counter()
    for key in material:
        decisions = {
            solver_id: indexed[solver_id][key]["reported_status"]
            for solver_id in SOLVER_IDS
            if _is_decision(indexed[solver_id][key])
        }
        if len(set(decisions.values())) > 1:
            counts["disagreement"] += 1
        elif len(decisions) == 3:
            counts["three-decide-agree"] += 1
        elif len(decisions) == 2:
            counts["two-decide-agree"] += 1
            sole_non_deciders[
                next(solver_id for solver_id in SOLVER_IDS if solver_id not in decisions)
            ] += 1
        elif len(decisions) == 1:
            counts["one-decides"] += 1
            sole_deciders[next(iter(decisions))] += 1
        else:
            counts["none-decide"] += 1
    return {
        "population": len(material),
        "key_set_sha256": _key_set_sha256(material),
        "decision_projection": _count_all(counts, THREE_CLASSES),
        "sole_decider_counts": _count_all(sole_deciders, SOLVER_IDS),
        "sole_non_decider_counts": _count_all(sole_non_deciders, SOLVER_IDS),
    }


def _validate_authority(authority: dict[str, Any], population: int) -> None:
    _expect(
        isinstance(authority, dict) and set(authority) == AUTHORITY_FIELDS,
        "full comparison authority field mismatch",
    )
    fixture_only = authority.get("fixture_only")
    _expect(type(fixture_only) is bool, "full comparison fixture scope mismatch")
    for field in ("preparation_record_sha256", "selection_record_sha256"):
        _expect(_is_sha256(authority.get(field)), "full comparison authority hash mismatch")
    cells = authority.get("cell_results")
    _expect(
        isinstance(cells, list)
        and [row.get("solver_id") for row in cells] == list(SOLVER_IDS),
        "full comparison cell authority order mismatch",
    )
    for row in cells:
        _expect(
            set(row) == {
                "solver_id",
                "record_sha256",
                "population_count",
                "safe_to_continue",
            }
            and _is_sha256(row.get("record_sha256"))
            and row.get("population_count") == population
            and row.get("safe_to_continue") is True,
            "full comparison cell authority mismatch",
        )


def _derive_full_comparison(
    records_by_solver: dict[str, Iterable[dict[str, Any]]],
    *,
    authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    _expect(
        tuple(records_by_solver) == SOLVER_IDS,
        "full comparison solver order drift",
    )
    _expect(
        isinstance(expected_logic_counts, dict)
        and bool(expected_logic_counts)
        and all(
            isinstance(logic, str)
            and bool(logic)
            and type(count) is int
            and count > 0
            for logic, count in expected_logic_counts.items()
        ),
        "full comparison expected logic inventory mismatch",
    )
    logics = sorted(expected_logic_counts)
    population = sum(expected_logic_counts.values())
    _validate_authority(authority, population)
    if not authority["fixture_only"]:
        _expect(
            population == POPULATION_COUNT and len(logics) == 88,
            "live full comparison population differs from preregistration",
        )
    indexed = {
        solver_id: _index_records(
            solver_id,
            records_by_solver[solver_id],
            set(expected_logic_counts),
            fixture_only=authority["fixture_only"],
        )
        for solver_id in SOLVER_IDS
    }
    expected_observed = dict(sorted(expected_logic_counts.items()))
    for solver_id in SOLVER_IDS:
        observed = dict(
            sorted(Counter(_logic(row) for row in indexed[solver_id].values()).items())
        )
        _expect(
            observed == expected_observed,
            f"full comparison logic population drift: {solver_id}",
        )
        _expect(
            sorted(row["sequence"] for row in indexed[solver_id].values())
            == list(range(population)),
            f"full comparison sequence coverage drift: {solver_id}",
        )
    common_keys = set(indexed[SOLVER_IDS[0]])
    for solver_id in SOLVER_IDS[1:]:
        _expect(
            set(indexed[solver_id]) == common_keys,
            "full comparison same-population identity drift",
        )
    for key in sorted(common_keys):
        baseline = indexed[SOLVER_IDS[0]][key]
        for solver_id in SOLVER_IDS[1:]:
            current = indexed[solver_id][key]
            _expect(
                current["sequence"] == baseline["sequence"]
                and current["expected_status"] == baseline["expected_status"]
                and _logic(current) == _logic(baseline),
                "full comparison shared benchmark metadata drift",
            )
    contradictions = sum(
        _decision_class(row) == "known-contradiction"
        for solver_id in SOLVER_IDS
        for row in indexed[solver_id].values()
    )
    _expect(
        contradictions == 0,
        "known-status contradiction blocks full comparison publication",
    )
    pairwise = {
        name: _pair_summary(left, right, indexed, logics)
        for name, left, right in PAIR_ROWS
    }
    three_solver = {
        "overall": _three_projection(indexed, common_keys),
        "per_logic": {
            logic: _three_projection(
                indexed,
                (
                    key
                    for key in common_keys
                    if _logic(indexed[SOLVER_IDS[0]][key]) == logic
                ),
            )
            for logic in logics
        },
    }
    disagreements = sum(
        row["overall"]["decision_projection"]["disagreement"]
        for row in pairwise.values()
    )
    _expect(
        disagreements == 0,
        "cross-solver disagreement blocks full comparison publication",
    )
    return _sealed(
        {
            "schema": COMPARISON_SCHEMA,
            "authority": copy.deepcopy(authority),
            "population_contract": {
                "solver_order": list(SOLVER_IDS),
                "population_count": population,
                "logic_count": len(logics),
                "logic_counts": expected_observed,
                "key_set_sha256": _key_set_sha256(common_keys),
                "same_population_all_cells": True,
            },
            "native_cells": {
                solver_id: _cell_summary(indexed[solver_id], logics)
                for solver_id in SOLVER_IDS
            },
            "pairwise": pairwise,
            "three_solver": three_solver,
            "integrity": {
                "known_status_contradictions": 0,
                "cross_solver_disagreements": 0,
                "safe_to_publish": True,
            },
            "claim_boundary": {
                "official_smtcomp_result": False,
                "performance_ranking": False,
                "single_scalar_ranking": False,
            },
        }
    )


def _validate_summary(summary: dict[str, Any], population: int, label: str) -> None:
    _expect(isinstance(summary, dict), f"full comparison {label} summary mismatch")
    statuses = summary.get("reported_status_counts")
    decisions = summary.get("decision_expected_status_counts")
    terminations = summary.get("termination_counts")
    _expect(
        summary.get("population") == population
        and isinstance(statuses, dict)
        and tuple(statuses) == REPORTED_STATUSES
        and sum(statuses.values()) == population
        and isinstance(decisions, dict)
        and tuple(decisions) == DECISION_CLASSES
        and sum(decisions.values()) == population
        and isinstance(terminations, dict)
        and all(
            isinstance(name, str) and type(count) is int and count >= 0
            for name, count in terminations.items()
        )
        and sum(terminations.values()) == population,
        f"full comparison {label} accounting drift",
    )
    _expect(
        summary.get("decision_count")
        == decisions["known-contradiction"]
        + decisions["known-correct"]
        + decisions["unadjudicated-decision"],
        f"full comparison {label} decision total drift",
    )


def _validate_projection(
    projection: dict[str, Any],
    population: int,
    classes: tuple[str, ...],
    label: str,
) -> None:
    counts = projection.get("decision_projection")
    _expect(
        projection.get("population") == population
        and _is_sha256(projection.get("key_set_sha256"))
        and isinstance(counts, dict)
        and tuple(counts) == classes
        and all(type(count) is int and count >= 0 for count in counts.values())
        and sum(counts.values()) == population,
        f"full comparison {label} projection drift",
    )


def validate_full_comparison(
    result: dict[str, Any],
    *,
    records_by_solver: dict[str, Iterable[dict[str, Any]]] | None = None,
    expected_logic_counts: dict[str, int] | None = None,
) -> dict[str, Any]:
    """Validate summary accounting and optionally rederive every projection."""

    _expect(
        isinstance(result, dict)
        and set(result) == COMPARISON_FIELDS
        and result.get("schema") == COMPARISON_SCHEMA
        and result.get("record_sha256") == _sealed(result)["record_sha256"],
        "full comparison field/schema/seal mismatch",
    )
    contract = result.get("population_contract")
    _expect(isinstance(contract, dict), "full comparison population contract mismatch")
    population = contract.get("population_count")
    logic_counts = contract.get("logic_counts")
    _expect(
        type(population) is int
        and population > 0
        and contract.get("solver_order") == list(SOLVER_IDS)
        and type(contract.get("logic_count")) is int
        and isinstance(logic_counts, dict)
        and contract["logic_count"] == len(logic_counts)
        and sum(logic_counts.values()) == population
        and _is_sha256(contract.get("key_set_sha256"))
        and contract.get("same_population_all_cells") is True,
        "full comparison population accounting drift",
    )
    _validate_authority(result["authority"], population)
    if not result["authority"]["fixture_only"]:
        _expect(
            population == POPULATION_COUNT and contract["logic_count"] == 88,
            "live full comparison population differs from preregistration",
        )
    native = result.get("native_cells")
    _expect(
        isinstance(native, dict) and set(native) == set(SOLVER_IDS),
        "full comparison native cell order mismatch",
    )
    for solver_id in SOLVER_IDS:
        cell = native[solver_id]
        _validate_summary(cell, population, solver_id)
        _expect(
            cell.get("key_set_sha256") == contract["key_set_sha256"]
            and _is_sha256(cell.get("record_set_sha256"))
            and isinstance(cell.get("per_logic"), dict)
            and list(cell["per_logic"]) == sorted(logic_counts),
            f"full comparison native identity drift: {solver_id}",
        )
        for logic, count in logic_counts.items():
            _validate_summary(cell["per_logic"][logic], count, f"{solver_id}.{logic}")
    pairwise = result.get("pairwise")
    _expect(
        isinstance(pairwise, dict)
        and set(pairwise) == {row[0] for row in PAIR_ROWS},
        "full comparison pair inventory drift",
    )
    for name, left, right in PAIR_ROWS:
        pair = pairwise[name]
        _expect(
            pair.get("left_solver") == left
            and pair.get("right_solver") == right
            and list(pair.get("per_logic", {})) == sorted(logic_counts),
            f"full comparison pair identity drift: {name}",
        )
        _validate_projection(pair["overall"], population, PAIR_CLASSES, name)
        _expect(
            pair["overall"]["key_set_sha256"] == contract["key_set_sha256"],
            f"full comparison pair key set drift: {name}",
        )
        for logic, count in logic_counts.items():
            _validate_projection(
                pair["per_logic"][logic], count, PAIR_CLASSES, f"{name}.{logic}"
            )
    three = result.get("three_solver")
    _expect(
        isinstance(three, dict)
        and set(three) == {"overall", "per_logic"}
        and list(three["per_logic"]) == sorted(logic_counts),
        "full comparison three-solver inventory drift",
    )
    _validate_projection(three["overall"], population, THREE_CLASSES, "three_solver")
    _expect(
        three["overall"]["key_set_sha256"] == contract["key_set_sha256"],
        "full comparison three-solver key set drift",
    )
    for projection, count, label in [
        (three["overall"], population, "three_solver"),
        *[
            (three["per_logic"][logic], logic_counts[logic], f"three_solver.{logic}")
            for logic in sorted(logic_counts)
        ],
    ]:
        _expect(
            sum(projection.get("sole_decider_counts", {}).values())
            == projection["decision_projection"]["one-decides"]
            and sum(projection.get("sole_non_decider_counts", {}).values())
            == projection["decision_projection"]["two-decide-agree"]
            and set(projection.get("sole_decider_counts", {})) == set(SOLVER_IDS)
            and set(projection.get("sole_non_decider_counts", {}))
            == set(SOLVER_IDS),
            f"full comparison {label} sole-solver accounting drift",
        )
        _expect(projection["population"] == count, f"full comparison {label} population drift")
    _expect(
        result.get("integrity")
        == {
            "known_status_contradictions": 0,
            "cross_solver_disagreements": 0,
            "safe_to_publish": True,
        },
        "full comparison integrity boundary drift",
    )
    _expect(
        result.get("claim_boundary")
        == {
            "official_smtcomp_result": False,
            "performance_ranking": False,
            "single_scalar_ranking": False,
        },
        "full comparison claim boundary drift",
    )
    if records_by_solver is not None or expected_logic_counts is not None:
        _expect(
            records_by_solver is not None and expected_logic_counts is not None,
            "full comparison replay inputs are incomplete",
        )
        rebuilt = _derive_full_comparison(
            records_by_solver,
            authority=result["authority"],
            expected_logic_counts=expected_logic_counts,
        )
        _expect(rebuilt == result, "full comparison replay drift")
    return result


def build_full_comparison(
    records_by_solver: dict[str, Iterable[dict[str, Any]]],
    *,
    authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    """Derive the exact native, pairwise, and three-solver summary."""

    result = _derive_full_comparison(
        records_by_solver,
        authority=authority,
        expected_logic_counts=expected_logic_counts,
    )
    return validate_full_comparison(result)


def validate_full_comparison_publication(
    output_root: Path,
    *,
    records_by_solver: dict[str, Iterable[dict[str, Any]]],
    expected_logic_counts: dict[str, int],
) -> dict[str, Any]:
    """Replay an immutable two-file, completion-last comparison publication."""

    _expect(not output_root.is_symlink(), "full comparison root mismatch")
    root = output_root.resolve(strict=True)
    _expect(root.is_dir(), "full comparison root mismatch")
    names = {path.name for path in root.iterdir()}
    _expect(
        names == {"comparison.json", "complete.json"},
        "full comparison publication inventory mismatch",
    )
    comparison = read_canonical_json(root / "comparison.json")
    validate_full_comparison(
        comparison,
        records_by_solver=records_by_solver,
        expected_logic_counts=expected_logic_counts,
    )
    completion = read_canonical_json(root / "complete.json")
    _expect(
        isinstance(completion, dict)
        and set(completion) == PUBLICATION_FIELDS
        and completion.get("schema") == PUBLICATION_SCHEMA
        and completion.get("record_sha256") == _sealed(completion)["record_sha256"],
        "full comparison completion field/schema/seal mismatch",
    )
    _expect(
        completion.get("status") == "complete-no-performance-ranking"
        and completion.get("comparison_record_sha256")
        == comparison["record_sha256"]
        and completion.get("comparison_file_sha256")
        == sha256_file(root / "comparison.json")
        and completion.get("population_count")
        == comparison["population_contract"]["population_count"]
        and completion.get("key_set_sha256")
        == comparison["population_contract"]["key_set_sha256"]
        and type(completion.get("published_at_ns")) is int
        and completion["published_at_ns"] > 0,
        "full comparison completion drift",
    )
    return completion


def publish_full_comparison(
    output_root: Path,
    *,
    records_by_solver: dict[str, Iterable[dict[str, Any]]],
    authority: dict[str, Any],
    expected_logic_counts: dict[str, int],
    published_at_ns: int | None = None,
    phase_hook: PhaseHook | None = None,
) -> dict[str, Any]:
    """Publish a process-free comparison with ``complete.json`` last."""

    _expect(not output_root.is_symlink(), "full comparison root mismatch")
    root = output_root.resolve()
    if (root / "complete.json").exists():
        raise ContractError("full comparison publication is already complete")
    if root.exists():
        existing = {path.name for path in root.iterdir()}
        _expect(
            existing <= {"comparison.json"},
            "full comparison prepublication inventory mismatch",
        )
    timestamp = time.time_ns() if published_at_ns is None else published_at_ns
    _expect(type(timestamp) is int and timestamp > 0, "full comparison timestamp mismatch")
    material = {
        solver_id: list(records_by_solver[solver_id]) for solver_id in SOLVER_IDS
    }
    comparison = build_full_comparison(
        material,
        authority=authority,
        expected_logic_counts=expected_logic_counts,
    )
    atomic_install_json(root, "comparison.json", comparison)
    if phase_hook is not None:
        phase_hook("after_comparison")
    completion = _sealed(
        {
            "schema": PUBLICATION_SCHEMA,
            "status": "complete-no-performance-ranking",
            "comparison_record_sha256": comparison["record_sha256"],
            "comparison_file_sha256": sha256_file(root / "comparison.json"),
            "population_count": comparison["population_contract"]["population_count"],
            "key_set_sha256": comparison["population_contract"]["key_set_sha256"],
            "published_at_ns": timestamp,
        }
    )
    atomic_install_json(root, "complete.json", completion)
    if phase_hook is not None:
        phase_hook("after_completion")
    return validate_full_comparison_publication(
        root,
        records_by_solver=material,
        expected_logic_counts=expected_logic_counts,
    )
