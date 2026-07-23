"""Fail-closed comparison of the three frozen repaired-P0 solver cells."""

from __future__ import annotations

import hashlib
from collections import Counter
from pathlib import Path
from typing import Any, Iterable

from p0_execute import CELL_ORDER, cell_result_root, validate_cell_result
from p0_prepare import validate_preparation
from resume_contract import (
    ContractError,
    canonical_bytes,
    digest,
    validate_record,
    validate_run,
)
from resume_fs import read_canonical_json
from resume_runner import sha256_file


SCHEMA = "axeyum.smtcomp-repaired-p0-comparison.v1"
FP_LOGICS = ("QF_ABVFP", "QF_BVFP", "QF_FP")
ALL_LOGICS = ("QF_ABVFP", "QF_AUFLIA", "QF_BVFP", "QF_FP")
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

LIVE_LOGIC_COUNTS = {
    "axeyum": {"QF_ABVFP": 525, "QF_AUFLIA": 505, "QF_BVFP": 505, "QF_FP": 275},
    "cvc5": {"QF_ABVFP": 525, "QF_AUFLIA": 505, "QF_BVFP": 505, "QF_FP": 275},
    "bitwuzla": {"QF_ABVFP": 525, "QF_BVFP": 505, "QF_FP": 275},
}

FROZEN_INPUTS = {
    "preparation": {
        "file_sha256": "8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261",
        "record_sha256": "d3ae8e7cd870c48c19417495aeb99b53ed1a797db58092b79d0828b9255b5f7b",
    },
    "cells": {
        "axeyum": {
            "completion_file_sha256": "28402ac34a91715ab60ad2ff6dd1f1774ec60b5594131592da317dd23faa33ca",
            "completion_record_sha256": "97f27a480f9694e97765d669823b05c34ced8825f2f598c16e00ea301b1c4a57",
            "raw_results_sha256": "9424ab09f44c63b7370e3472b299eeab051b1e7d66cfe2de967cb05088581820",
            "run_identity_sha256": "5d75bf98f1fe7e8458ac1f5efbd75ea728bd57cff9b0c674002986c6e8dcd2d3",
            "selected_list_sha256": "e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d",
            "selection_manifest_sha256": "a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4",
        },
        "cvc5": {
            "completion_file_sha256": "4abde0a6b3d02be1a4e4aa80bda32e2808e78e32db3e1e71336bc6e304bd32f8",
            "completion_record_sha256": "e6fbc654535c82bb5d9fa9460ba802cf41d128c28778b859f990df2160a37faf",
            "raw_results_sha256": "0465d0aea6929bdf42c37f5aaa7e3ba24eca67f960a322ad6c8735a8f0d9e010",
            "run_identity_sha256": "1d32c45c1371528cf3d4e6bad5801600490f09151ede779bd348de2f124e7745",
            "selected_list_sha256": "e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d",
            "selection_manifest_sha256": "a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4",
        },
        "bitwuzla": {
            "completion_file_sha256": "4e0c9682931154b6455d02e00ed5a6cc3ec6b58635e7c808de703023c72dcf20",
            "completion_record_sha256": "7ec879514032b00ed5d8fffd119d126df90681a6b0ed4e2bf9ea737ae94df6f3",
            "raw_results_sha256": "390e113f1d6291402e2ae6a59a09e174cfb2d978727a01432b7f6a016b265dd4",
            "run_identity_sha256": "f495615511402433ae6eaa7a5b90f4b62ad417fb5b71e7459ce4f66da145fc94",
            "selected_list_sha256": "6025cf1dedfe7e425601f41f10e29ad594ddc083db3f997cb1303e93e70ca801",
            "selection_manifest_sha256": "498184e470072824eaefe46092ff1b2c7228ee23c35b165800a9169a52026041",
        },
    },
}

COMPARABILITY_FIELDS = (
    "contract_schema",
    "run_schema",
    "result_schema",
    "corpus_identity_sha256",
    "solver_environment_sha256",
    "runner_source_sha256",
    "repository_commit",
    "source_tree_state_sha256",
    "toolchain_identity_sha256",
    "track",
    "wall_limit_ms",
    "cpu_limit_ms",
    "memory_limit_bytes",
    "cores",
    "shard_count",
    "shard_mapping",
    "environment_class_sha256",
    "resource_enforcement_sha256",
    "resource_policy_sha256",
    "output_capture_policy_sha256",
    "verdict_policy",
)


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _logic(row: dict[str, Any]) -> str:
    benchmark_id = row.get("benchmark_id")
    _expect(isinstance(benchmark_id, str) and "/" in benchmark_id, "invalid comparison benchmark ID")
    logic = benchmark_id.split("/", 1)[0]
    _expect(logic in ALL_LOGICS, f"unexpected repaired-P0 logic: {logic}")
    return logic


def _key(row: dict[str, Any]) -> tuple[str, str]:
    benchmark_id = row.get("benchmark_id")
    benchmark_sha256 = row.get("benchmark_sha256")
    _expect(isinstance(benchmark_id, str), "invalid comparison benchmark ID")
    _expect(
        isinstance(benchmark_sha256, str)
        and len(benchmark_sha256) == 64
        and all(character in "0123456789abcdef" for character in benchmark_sha256),
        "invalid comparison benchmark SHA-256",
    )
    return benchmark_id, benchmark_sha256


def _reported(row: dict[str, Any]) -> str:
    status = row.get("reported_status")
    _expect(status in {None, "sat", "unsat", "unknown"}, "invalid comparison reported status")
    return status if status is not None else "no-verdict"


def _is_decision(row: dict[str, Any]) -> bool:
    return row.get("reported_status") in {"sat", "unsat"}


def _decision_class(row: dict[str, Any]) -> str:
    if not _is_decision(row):
        return "no-decision"
    expected = row.get("expected_status")
    _expect(expected in {None, "sat", "unsat"}, "invalid comparison expected status")
    if expected is None:
        return "unadjudicated-decision"
    if expected == row["reported_status"]:
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


def _index_records(
    solver_id: str, records: Iterable[dict[str, Any]]
) -> dict[tuple[str, str], dict[str, Any]]:
    indexed: dict[tuple[str, str], dict[str, Any]] = {}
    for row in records:
        _expect(isinstance(row, dict), "comparison record is not an object")
        if "solver_id" in row:
            _expect(row["solver_id"] == solver_id, "comparison solver identity drift")
        key = _key(row)
        _logic(row)
        _reported(row)
        _decision_class(row)
        termination = row.get("termination_class")
        _expect(isinstance(termination, str) and termination, "invalid comparison termination class")
        _expect(key not in indexed, f"duplicate comparison benchmark identity: {solver_id}")
        indexed[key] = row
    return indexed


def _summary(rows: Iterable[dict[str, Any]]) -> dict[str, Any]:
    material = list(rows)
    status_counts = Counter(_reported(row) for row in material)
    decision_counts = Counter(_decision_class(row) for row in material)
    termination_counts = Counter(row["termination_class"] for row in material)
    return {
        "population": len(material),
        "decision_count": sum(_is_decision(row) for row in material),
        "reported_status_counts": _count_all(status_counts, REPORTED_STATUSES),
        "decision_expected_status_counts": _count_all(decision_counts, DECISION_CLASSES),
        "termination_counts": dict(sorted(termination_counts.items())),
    }


def _cell_summary(indexed: dict[tuple[str, str], dict[str, Any]]) -> dict[str, Any]:
    per_logic = {}
    for logic in ALL_LOGICS:
        rows = [row for row in indexed.values() if _logic(row) == logic]
        if rows:
            per_logic[logic] = _summary(rows)
    return {
        **_summary(indexed.values()),
        "key_set_sha256": _key_set_sha256(indexed),
        "per_logic": per_logic,
    }


def _pair_projection(
    left_id: str,
    right_id: str,
    left: dict[tuple[str, str], dict[str, Any]],
    right: dict[tuple[str, str], dict[str, Any]],
    keys: set[tuple[str, str]],
) -> dict[str, Any]:
    counts: Counter[str] = Counter()
    for key in sorted(keys):
        left_row = left[key]
        right_row = right[key]
        left_decides = _is_decision(left_row)
        right_decides = _is_decision(right_row)
        if left_decides and right_decides:
            category = (
                "both-decide-agree"
                if left_row["reported_status"] == right_row["reported_status"]
                else "disagreement"
            )
        elif left_decides:
            category = "left-only-decides"
        elif right_decides:
            category = "right-only-decides"
        else:
            category = "neither-decides"
        counts[category] += 1
    _expect(sum(counts.values()) == len(keys), "pairwise comparison accounting failure")
    return {
        "left_solver": left_id,
        "right_solver": right_id,
        "population": len(keys),
        "key_set_sha256": _key_set_sha256(keys),
        "decision_projection": _count_all(counts, PAIR_CLASSES),
    }


def _pair_population(
    left_id: str,
    right_id: str,
    indexed: dict[str, dict[tuple[str, str], dict[str, Any]]],
    *,
    logics: set[str] | None = None,
) -> dict[str, Any]:
    left = indexed[left_id]
    right = indexed[right_id]
    left_keys = {key for key, row in left.items() if logics is None or _logic(row) in logics}
    right_keys = {key for key, row in right.items() if logics is None or _logic(row) in logics}
    intersection = left_keys & right_keys
    return {
        "left_population": len(left_keys),
        "right_population": len(right_keys),
        "intersection_count": len(intersection),
        "left_only_count": len(left_keys - right_keys),
        "right_only_count": len(right_keys - left_keys),
        "left_only_logic_counts": dict(
            sorted(Counter(_logic(left[key]) for key in left_keys - right_keys).items())
        ),
        "right_only_logic_counts": dict(
            sorted(Counter(_logic(right[key]) for key in right_keys - left_keys).items())
        ),
        "intersection": _pair_projection(left_id, right_id, left, right, intersection),
    }


def _three_projection(
    indexed: dict[str, dict[tuple[str, str], dict[str, Any]]],
    keys: set[tuple[str, str]],
) -> dict[str, Any]:
    counts: Counter[str] = Counter()
    sole_decider: Counter[str] = Counter()
    sole_non_decider: Counter[str] = Counter()
    for key in sorted(keys):
        decisions = {
            solver_id: indexed[solver_id][key]["reported_status"]
            for solver_id in CELL_ORDER
            if _is_decision(indexed[solver_id][key])
        }
        if len(set(decisions.values())) > 1:
            counts["disagreement"] += 1
        elif len(decisions) == 3:
            counts["three-decide-agree"] += 1
        elif len(decisions) == 2:
            counts["two-decide-agree"] += 1
            sole_non_decider[next(solver for solver in CELL_ORDER if solver not in decisions)] += 1
        elif len(decisions) == 1:
            counts["one-decides"] += 1
            sole_decider[next(iter(decisions))] += 1
        else:
            counts["none-decide"] += 1
    _expect(sum(counts.values()) == len(keys), "three-way comparison accounting failure")
    return {
        "population": len(keys),
        "key_set_sha256": _key_set_sha256(keys),
        "decision_projection": _count_all(counts, THREE_CLASSES),
        "sole_decider_counts": _count_all(sole_decider, CELL_ORDER),
        "sole_non_decider_counts": _count_all(sole_non_decider, CELL_ORDER),
    }


def build_comparison(
    records_by_solver: dict[str, Iterable[dict[str, Any]]],
    *,
    authority: dict[str, Any],
    expected_logic_counts: dict[str, dict[str, int]],
) -> dict[str, Any]:
    """Build and seal the comparison from already validated result records."""

    _expect(tuple(records_by_solver) == CELL_ORDER, "comparison cell order drift")
    indexed = {
        solver_id: _index_records(solver_id, records_by_solver[solver_id])
        for solver_id in CELL_ORDER
    }
    for solver_id in CELL_ORDER:
        observed = dict(sorted(Counter(_logic(row) for row in indexed[solver_id].values()).items()))
        _expect(observed == expected_logic_counts[solver_id], f"comparison logic population drift: {solver_id}")

    axeyum_keys = set(indexed["axeyum"])
    cvc5_keys = set(indexed["cvc5"])
    bitwuzla_keys = set(indexed["bitwuzla"])
    _expect(axeyum_keys == cvc5_keys, "Axeyum/cvc5 all-scope identity drift")
    expected_fp_keys = {
        key for key, row in indexed["axeyum"].items() if _logic(row) in FP_LOGICS
    }
    _expect(bitwuzla_keys == expected_fp_keys, "Bitwuzla is not the exact FP-family subset")

    for key in sorted(axeyum_keys):
        axeyum = indexed["axeyum"][key]
        cvc5 = indexed["cvc5"][key]
        _expect(_logic(axeyum) == _logic(cvc5), "shared benchmark logic drift")
        _expect(axeyum["expected_status"] == cvc5["expected_status"], "shared expected-status drift")
        if key in bitwuzla_keys:
            bitwuzla = indexed["bitwuzla"][key]
            _expect(_logic(axeyum) == _logic(bitwuzla), "shared benchmark logic drift")
            _expect(axeyum["expected_status"] == bitwuzla["expected_status"], "shared expected-status drift")

    contradictions = [
        {"solver_id": solver_id, "benchmark_id": row["benchmark_id"]}
        for solver_id in CELL_ORDER
        for row in indexed[solver_id].values()
        if _decision_class(row) == "known-contradiction"
    ]
    _expect(not contradictions, "known-status contradiction blocks comparison publication")

    all_pair = _pair_population("axeyum", "cvc5", indexed)
    axeyum_bitwuzla = _pair_population("axeyum", "bitwuzla", indexed)
    cvc5_bitwuzla = _pair_population("cvc5", "bitwuzla", indexed)
    auflia_pair = _pair_population(
        "axeyum", "cvc5", indexed, logics={"QF_AUFLIA"}
    )
    three_fp = _three_projection(indexed, bitwuzla_keys)
    disagreements = sum(
        pair["intersection"]["decision_projection"]["disagreement"]
        for pair in (all_pair, axeyum_bitwuzla, cvc5_bitwuzla)
    )
    _expect(disagreements == 0, "cross-solver disagreement blocks comparison publication")

    result = {
        "schema": SCHEMA,
        "authority": authority,
        "population_contract": {
            "all_logics": list(ALL_LOGICS),
            "all_population": len(axeyum_keys),
            "fp_logics": list(FP_LOGICS),
            "fp_population": len(bitwuzla_keys),
            "qf_auflia_population": len(axeyum_keys - bitwuzla_keys),
            "bitwuzla_is_exact_fp_subset": True,
        },
        "native_cells": {
            solver_id: _cell_summary(indexed[solver_id]) for solver_id in CELL_ORDER
        },
        "pairwise": {
            "axeyum_bitwuzla_fp": axeyum_bitwuzla,
            "axeyum_cvc5_all": all_pair,
            "cvc5_bitwuzla_fp": cvc5_bitwuzla,
            "qf_auflia_axeyum_cvc5": auflia_pair,
        },
        "three_solver_fp": three_fp,
        "integrity": {
            "known_status_contradictions": 0,
            "cross_solver_disagreements": 0,
            "safe_to_publish": True,
        },
        "claim_boundary": {
            "aggregate_cross_scope_ranking": False,
            "performance_ranking": False,
            "official_smtcomp_result": False,
            "reason": "Bitwuzla has a smaller FP-only population and a recovery lifecycle; report exact comparable scopes only.",
        },
    }
    result["record_sha256"] = digest(result)
    validate_comparison(result)
    return result


def validate_comparison(result: dict[str, Any]) -> None:
    """Validate the self-seal and complete accounting of a comparison."""

    _expect(result.get("schema") == SCHEMA, "comparison schema mismatch")
    unsealed = dict(result)
    claimed = unsealed.pop("record_sha256", None)
    _expect(claimed == digest(unsealed), "comparison record hash mismatch")
    contract = result["population_contract"]
    _expect(contract["bitwuzla_is_exact_fp_subset"] is True, "comparison subset proof missing")
    _expect(result["integrity"] == {
        "known_status_contradictions": 0,
        "cross_solver_disagreements": 0,
        "safe_to_publish": True,
    }, "comparison integrity boundary drift")
    _expect(result["claim_boundary"]["aggregate_cross_scope_ranking"] is False, "cross-scope ranking was enabled")
    _expect(result["claim_boundary"]["performance_ranking"] is False, "performance ranking was enabled")
    authority = result["authority"]
    if authority.get("fixture") is not True:
        _expect(
            authority["preparation"] == FROZEN_INPUTS["preparation"],
            "comparison preparation authority drift",
        )
        for solver_id in CELL_ORDER:
            frozen = FROZEN_INPUTS["cells"][solver_id]
            observed = authority["cells"][solver_id]
            _expect(
                all(observed.get(field) == value for field, value in frozen.items()),
                f"comparison cell authority drift: {solver_id}",
            )
        common = authority["common_execution_contract"]
        _expect(common["track"] == "single_query", "comparison track drift")
        _expect(common["cores"] == 1, "comparison core count drift")
        _expect(common["wall_limit_ms"] == 20_000, "comparison wall limit drift")
        _expect(common["cpu_limit_ms"] == 20_000, "comparison CPU limit drift")
        _expect(
            common["memory_limit_bytes"] == 8 * 1024 * 1024 * 1024,
            "comparison memory limit drift",
        )
    for solver_id, summary in result["native_cells"].items():
        _expect(summary["population"] == sum(summary["reported_status_counts"].values()), f"status accounting drift: {solver_id}")
        _expect(summary["population"] == sum(summary["decision_expected_status_counts"].values()), f"decision accounting drift: {solver_id}")
        _expect(summary["population"] == sum(summary["termination_counts"].values()), f"termination accounting drift: {solver_id}")
        _expect(summary["population"] == sum(row["population"] for row in summary["per_logic"].values()), f"logic accounting drift: {solver_id}")
        _expect(
            summary["decision_count"]
            == summary["decision_expected_status_counts"]["known-correct"]
            + summary["decision_expected_status_counts"]["unadjudicated-decision"],
            f"decision total drift: {solver_id}",
        )
        for logic, logic_summary in summary["per_logic"].items():
            _expect(
                logic_summary["population"]
                == sum(logic_summary["reported_status_counts"].values())
                == sum(logic_summary["decision_expected_status_counts"].values())
                == sum(logic_summary["termination_counts"].values()),
                f"per-logic accounting drift: {solver_id}.{logic}",
            )
    for pair in result["pairwise"].values():
        projection = pair["intersection"]["decision_projection"]
        _expect(pair["intersection_count"] == sum(projection.values()), "pairwise projection accounting drift")
        _expect(pair["left_population"] == pair["intersection_count"] + pair["left_only_count"], "pairwise left accounting drift")
        _expect(pair["right_population"] == pair["intersection_count"] + pair["right_only_count"], "pairwise right accounting drift")
    _expect(result["three_solver_fp"]["population"] == sum(result["three_solver_fp"]["decision_projection"].values()), "three-way projection accounting drift")
    all_population = contract["all_population"]
    fp_population = contract["fp_population"]
    auflia_population = contract["qf_auflia_population"]
    _expect(all_population == fp_population + auflia_population, "comparison population partition drift")
    _expect(result["native_cells"]["axeyum"]["population"] == all_population, "Axeyum native population drift")
    _expect(result["native_cells"]["cvc5"]["population"] == all_population, "cvc5 native population drift")
    _expect(result["native_cells"]["bitwuzla"]["population"] == fp_population, "Bitwuzla native population drift")
    all_pair = result["pairwise"]["axeyum_cvc5_all"]
    _expect(
        (all_pair["left_population"], all_pair["right_population"], all_pair["intersection_count"], all_pair["left_only_count"], all_pair["right_only_count"])
        == (all_population, all_population, all_population, 0, 0),
        "all-scope pair boundary drift",
    )
    for name in ("axeyum_bitwuzla_fp", "cvc5_bitwuzla_fp"):
        pair = result["pairwise"][name]
        _expect(
            (pair["left_population"], pair["right_population"], pair["intersection_count"], pair["left_only_count"], pair["right_only_count"])
            == (all_population, fp_population, fp_population, auflia_population, 0),
            f"FP pair boundary drift: {name}",
        )
        _expect(
            pair["left_only_logic_counts"] == {"QF_AUFLIA": auflia_population},
            f"FP pair excluded-logic drift: {name}",
        )
    auflia_pair = result["pairwise"]["qf_auflia_axeyum_cvc5"]
    _expect(
        (auflia_pair["left_population"], auflia_pair["right_population"], auflia_pair["intersection_count"], auflia_pair["left_only_count"], auflia_pair["right_only_count"])
        == (auflia_population, auflia_population, auflia_population, 0, 0),
        "QF_AUFLIA pair boundary drift",
    )
    three = result["three_solver_fp"]
    _expect(three["population"] == fp_population, "three-way FP population drift")
    _expect(
        sum(three["sole_decider_counts"].values())
        == three["decision_projection"]["one-decides"],
        "sole-decider accounting drift",
    )
    _expect(
        sum(three["sole_non_decider_counts"].values())
        == three["decision_projection"]["two-decide-agree"],
        "sole-non-decider accounting drift",
    )


def _load_live_records(
    run_dir: Path, identity: dict[str, Any], run_identity_sha256: str
) -> list[dict[str, Any]]:
    records = []
    for path in sorted((run_dir / "records").glob("*.json")):
        row = read_canonical_json(path)
        validate_record(row, run_identity_sha256, identity)
        _expect(path.name == f"{row['result_key']}.json", "comparison record filename drift")
        records.append(row)
    return records


def derive_live_comparison(preparation_root: Path) -> dict[str, Any]:
    """Validate the frozen live roots and derive their exact comparison."""

    complete_path = preparation_root / "complete.json"
    _expect(sha256_file(complete_path) == FROZEN_INPUTS["preparation"]["file_sha256"], "comparison preparation file hash drift")
    completion = validate_preparation(preparation_root, require_empty=False)
    _expect(completion["record_sha256"] == FROZEN_INPUTS["preparation"]["record_sha256"], "comparison preparation record hash drift")
    _expect(tuple(cell["solver_id"] for cell in completion["cells"]) == CELL_ORDER, "comparison preparation cell order drift")

    records_by_solver = {}
    cell_authority = {}
    identities = {}
    for cell in completion["cells"]:
        solver_id = cell["solver_id"]
        frozen = FROZEN_INPUTS["cells"][solver_id]
        run_dir = Path(cell["attempt_root"])
        observed = validate_cell_result(
            preparation_root=preparation_root,
            completion=completion,
            cell_id=solver_id,
            run_dir=run_dir,
        )
        result_root = cell_result_root(preparation_root, solver_id)
        _expect(sha256_file(result_root / "complete.json") == frozen["completion_file_sha256"], f"comparison external completion file drift: {solver_id}")
        _expect(observed["record_sha256"] == frozen["completion_record_sha256"], f"comparison external completion record drift: {solver_id}")
        _expect(observed["raw_results_sha256"] == frozen["raw_results_sha256"], f"comparison raw result drift: {solver_id}")
        run = read_canonical_json(Path(cell["run_manifest_path"]))
        identity, run_identity_sha256 = validate_run(run)
        _expect(run_identity_sha256 == frozen["run_identity_sha256"], f"comparison run identity drift: {solver_id}")
        _expect(identity["selected_list_sha256"] == frozen["selected_list_sha256"], f"comparison selected-list drift: {solver_id}")
        _expect(identity["selection_manifest_sha256"] == frozen["selection_manifest_sha256"], f"comparison selection-manifest drift: {solver_id}")
        records_by_solver[solver_id] = _load_live_records(run_dir, identity, run_identity_sha256)
        identities[solver_id] = identity
        cell_authority[solver_id] = {
            **frozen,
            "record_count": observed["raw_result_count"],
        }

    reference = identities["axeyum"]
    for solver_id in CELL_ORDER[1:]:
        for field in COMPARABILITY_FIELDS:
            _expect(identities[solver_id][field] == reference[field], f"comparison execution contract drift: {solver_id}.{field}")
    common_execution_contract = {field: reference[field] for field in COMPARABILITY_FIELDS}
    authority = {
        "preparation_root": str(preparation_root),
        "preparation": FROZEN_INPUTS["preparation"],
        "cells": cell_authority,
        "common_execution_contract": common_execution_contract,
    }
    return build_comparison(
        records_by_solver,
        authority=authority,
        expected_logic_counts=LIVE_LOGIC_COUNTS,
    )


def comparison_json_bytes(result: dict[str, Any]) -> bytes:
    validate_comparison(result)
    return canonical_bytes(result)


def render_markdown(result: dict[str, Any], json_sha256: str) -> bytes:
    """Render the human view exclusively from validated comparison JSON."""

    validate_comparison(result)
    cells = result["native_cells"]
    lines = [
        "# SMT-COMP repaired P0 combined comparison",
        "",
        "Status: complete, bounded repaired-P0 comparison",
        "",
        "This is a correctness and decision-coverage map, not an official",
        "SMT-COMP result or a cross-scope performance ranking.",
        "",
        "## Artifact identity",
        "",
        f"- JSON file SHA-256: `{json_sha256}`",
        f"- JSON record SHA-256: `{result['record_sha256']}`",
        f"- preparation completion SHA-256: `{result['authority']['preparation']['file_sha256']}`",
        "",
        "## Native cell scopes",
        "",
        "| Solver | Rows | Decisions | `sat` | `unsat` | `unknown` | No verdict | Known contradiction |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for solver_id in CELL_ORDER:
        row = cells[solver_id]
        statuses = row["reported_status_counts"]
        classes = row["decision_expected_status_counts"]
        lines.append(
            f"| {solver_id} | {row['population']:,} | {row['decision_count']:,} | "
            f"{statuses['sat']:,} | {statuses['unsat']:,} | {statuses['unknown']:,} | "
            f"{statuses['no-verdict']:,} | {classes['known-contradiction']:,} |"
        )
    lines.extend([
        "",
        "Bitwuzla's rows are exactly the 1,305-row FP-family subset. The other",
        "505 rows are exactly QF_AUFLIA and are compared only between Axeyum and cvc5.",
        "",
        "## Per-logic decision coverage",
        "",
        "| Logic | Solver | Rows | Decisions | `sat` | `unsat` | `unknown` | No verdict |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
    ])
    for logic in ALL_LOGICS:
        for solver_id in CELL_ORDER:
            if logic not in cells[solver_id]["per_logic"]:
                continue
            row = cells[solver_id]["per_logic"][logic]
            statuses = row["reported_status_counts"]
            lines.append(
                f"| {logic} | {solver_id} | {row['population']:,} | {row['decision_count']:,} | "
                f"{statuses['sat']:,} | {statuses['unsat']:,} | {statuses['unknown']:,} | "
                f"{statuses['no-verdict']:,} |"
            )
    lines.extend([
        "",
        "## Pairwise decision projections",
        "",
        "Only `sat` and `unsat` count as decisions. `unknown` is an observed",
        "response but remains a non-decision.",
        "",
        "| Population | Solvers | Rows | Both agree | Left only | Right only | Neither | Disagree |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
    ])
    pair_labels = (
        ("axeyum_cvc5_all", "all 4 logics"),
        ("axeyum_bitwuzla_fp", "FP-family"),
        ("cvc5_bitwuzla_fp", "FP-family"),
        ("qf_auflia_axeyum_cvc5", "QF_AUFLIA"),
    )
    for key, label in pair_labels:
        pair = result["pairwise"][key]["intersection"]
        counts = pair["decision_projection"]
        lines.append(
            f"| {label} | {pair['left_solver']} / {pair['right_solver']} | {pair['population']:,} | "
            f"{counts['both-decide-agree']:,} | {counts['left-only-decides']:,} | "
            f"{counts['right-only-decides']:,} | {counts['neither-decides']:,} | "
            f"{counts['disagreement']:,} |"
        )
    three = result["three_solver_fp"]
    three_counts = three["decision_projection"]
    lines.extend([
        "",
        "## Three-solver FP-family projection",
        "",
        "| Rows | Three decide | Two decide | One decides | None decide | Disagree |",
        "|---:|---:|---:|---:|---:|---:|",
        f"| {three['population']:,} | {three_counts['three-decide-agree']:,} | "
        f"{three_counts['two-decide-agree']:,} | {three_counts['one-decides']:,} | "
        f"{three_counts['none-decide']:,} | {three_counts['disagreement']:,} |",
        "",
        "Sole decider counts: "
        + ", ".join(f"{solver} {three['sole_decider_counts'][solver]:,}" for solver in CELL_ORDER)
        + ".",
        "Sole non-decider counts: "
        + ", ".join(f"{solver} {three['sole_non_decider_counts'][solver]:,}" for solver in CELL_ORDER)
        + ".",
        "",
        "## Bounded verdict",
        "",
        "All exact populations account completely, with zero known-status",
        "contradictions and zero cross-solver `sat`/`unsat` disagreements.",
        "The data supports per-scope capability comparison only. It does not",
        "support combining the 1,305-row and 1,810-row populations into one",
        "score or claiming general SMT-COMP parity.",
        "",
    ])
    return ("\n".join(lines)).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()
