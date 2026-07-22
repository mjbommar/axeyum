#!/usr/bin/env python3
"""Validate the preregistered official Lean construct matrix fail closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-official-construct-matrix-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-official-construct-matrix.md"
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

from prototype_lean4export_census import census_bytes  # noqa: E402

SCHEMA = "axeyum-lean-official-construct-matrix-v1"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "decision",
    "pins",
    "resource_policy",
    "retention_policy",
    "commands",
    "historical_controls",
    "sources",
    "cases",
    "stage_b",
    "product_measurement",
    "tl2_12_update",
    "tl2_13_update",
    "tl2_14_update",
}
CASE_KEYS = {
    "id",
    "source_family",
    "role",
    "source_key",
    "module",
    "selected_root",
    "computation_witness",
    "expected_official_source",
    "stage_b_wire",
    "product_measurement",
}
HISTORICAL_CONTROL_KEYS = {
    "id",
    "source_path",
    "source_sha256",
    "stream_path",
    "stream_sha256",
    "regenerated_runs",
    "imported_runs",
    "expected_report",
}
REPORT_KEYS = {
    "names",
    "levels",
    "expressions",
    "declaration_records",
    "admitted_declarations",
    "axioms",
}
STAGE_B_KEYS = {
    "frozen_date",
    "independent_reader",
    "independent_census",
    "new_stream_aggregate_bytes",
    "streams",
}
STREAM_KEYS = {
    "path",
    "selected_root",
    "export_runs",
    "byte_identical",
    "max_rss_kib",
    "retained",
    "inventory",
}
PRODUCT_KEYS = {
    "measured_date",
    "source_revision",
    "crate",
    "example",
    "memory_max",
    "rust_jobs",
    "runs_per_case",
    "control_before_each_run",
    "control_runs",
    "control",
    "outcomes",
}
OUTCOME_KEYS = {
    "runs",
    "repeatable",
    "outcome_layer",
    "variant",
    "line",
    "declaration",
    "source_variant",
    "code",
    "message",
    "completed_import_published",
}
TL212_UPDATE_KEYS = {
    "measured_date",
    "source_revision",
    "construct_test",
    "computation_test",
    "runs_per_case",
    "resource_runner",
    "memory_max",
    "rust_jobs",
    "lean_jobs",
    "lean_source_runs",
    "lean_olean_sha256",
    "lean_elapsed_ms",
    "lean_max_rss_kib",
    "rust_gate_elapsed_ms",
    "rust_gate_max_rss_kib",
    "outcomes",
    "computations",
}
TL212_OUTCOME_KEYS = {"variant", "runs", "report", "line", "code", "message"}
TL212_REPORT_KEYS = REPORT_KEYS | {"axiom_identities", "declaration_identities"}
TL212_COMPUTATION_KEYS = {
    "path",
    "sha256",
    "bytes",
    "records",
    "runs",
    "completed",
    "reduction_checked",
    "theorem",
    "normal_form",
    "report",
}
TL213_UPDATE_KEYS = {
    "measured_date",
    "source_revision",
    "product_test",
    "runs_per_case",
    "resource_runner",
    "memory_max",
    "rust_jobs",
    "rust_test_threads",
    "lean_jobs",
    "lean_source_runs",
    "lean_olean_sha256",
    "lean_elapsed_ms",
    "lean_max_rss_kib",
    "rust_gate_elapsed_ms",
    "rust_gate_max_rss_kib",
    "outcomes",
    "computations",
}
TL213_OUTCOME_KEYS = TL212_OUTCOME_KEYS
TL213_REPORT_KEYS = TL212_REPORT_KEYS
TL213_COMPUTATION_KEYS = TL212_COMPUTATION_KEYS
TL214_UPDATE_KEYS = TL213_UPDATE_KEYS
TL214_OUTCOME_KEYS = TL213_OUTCOME_KEYS
TL214_REPORT_KEYS = TL213_REPORT_KEYS
TL214_COMPUTATION_KEYS = TL213_COMPUTATION_KEYS
TL214_UPDATE_ORDER = (
    "measured_date",
    "source_revision",
    "product_test",
    "runs_per_case",
    "resource_runner",
    "memory_max",
    "rust_jobs",
    "rust_test_threads",
    "lean_jobs",
    "lean_source_runs",
    "lean_olean_sha256",
    "lean_elapsed_ms",
    "lean_max_rss_kib",
    "rust_gate_elapsed_ms",
    "rust_gate_max_rss_kib",
    "outcomes",
    "computations",
)
TL214_OUTCOME_ORDER = ("variant", "runs", "report", "line", "code", "message")
TL214_REPORT_ORDER = (
    "names",
    "levels",
    "expressions",
    "declaration_records",
    "admitted_declarations",
    "axioms",
    "axiom_identities",
    "declaration_identities",
)
TL214_COMPUTATION_ORDER = (
    "path",
    "sha256",
    "bytes",
    "records",
    "runs",
    "completed",
    "reduction_checked",
    "theorem",
    "normal_form",
    "report",
)
EXPECTED_PINS = {
    "lean": {
        "toolchain": "leanprover/lean4:v4.30.0",
        "version": "4.30.0",
        "git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
    },
    "lean4export": {
        "version": "v4.30.0",
        "git_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "format": "3.1.0",
    },
}
EXPECTED_RESOURCES = {
    "runner": "systemd-run --user --scope",
    "memory_high": "3G",
    "memory_max": "4G",
    "memory_swap_max": "512M",
    "lean_jobs": 1,
    "rust_jobs": 2,
}
EXPECTED_RETENTION = {
    "per_stream_max_bytes": 1_048_576,
    "aggregate_new_stream_max_bytes": 2_097_152,
}
EXPECTED_CONTROL_REPORTS = {
    "flat": {
        "names": 14,
        "levels": 2,
        "expressions": 43,
        "declaration_records": 5,
        "admitted_declarations": 8,
        "axioms": 1,
    },
    "direct-recursive-control": {
        "names": 30,
        "levels": 4,
        "expressions": 130,
        "declaration_records": 5,
        "admitted_declarations": 11,
        "axioms": 0,
    },
}
EXPECTED_STAGE_B_PATHS = {
    "recursive-indexed": (
        "docs/plan/fixtures/"
        "lean4export-v4.30-construct-matrix-recursive-indexed.ndjson"
    ),
    "reflexive-higher-order": (
        "docs/plan/fixtures/"
        "lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson"
    ),
    "mutual": "docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson",
    "nested": "docs/plan/fixtures/lean4export-v4.30-construct-matrix-nested.ndjson",
    "well-founded": (
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson"
    ),
}
EXPECTED_PRODUCT_CONTROL = {
    "id": "direct-recursive-control",
    "all_passed": True,
    "names": 30,
    "levels": 4,
    "expressions": 130,
    "declaration_records": 5,
    "admitted_declarations": 11,
    "axioms": 0,
    "axiom_identities": 0,
    "declaration_identities": 11,
}
EXPECTED_PRODUCT_OUTCOMES = {
    "recursive-indexed": (
        "kernel",
        "Kernel",
        148,
        "AxeyumConstructMatrix.MiniVector",
        "RecursiveIndexedNotSupported",
        None,
        None,
    ),
    "reflexive-higher-order": (
        "import-policy",
        "Unsupported",
        117,
        None,
        None,
        "inductive-reflexive",
        None,
    ),
    "mutual": (
        "import-policy",
        "Unsupported",
        233,
        None,
        None,
        "inductive-mutual",
        None,
    ),
    "nested": (
        "format-misclassification",
        "Malformed",
        248,
        None,
        None,
        None,
        "single-family inductive must export one recursor",
    ),
    "well-founded": (
        "import-policy",
        "Unsupported",
        208,
        None,
        None,
        "inductive-reflexive",
        None,
    ),
}
EXPECTED_TL212_OUTCOMES = {
    "recursive-indexed": (
        "CompletedImport",
        None,
        None,
        None,
        (34, 4, 132, 4, 12, 0, 0, 12),
    ),
    "reflexive-higher-order": (
        "CompletedImport",
        None,
        None,
        None,
        (47, 3, 139, 6, 11, 0, 0, 11),
    ),
    "mutual": ("Unsupported", 233, "inductive-mutual", None, None),
    "nested": (
        "Malformed",
        248,
        None,
        "single-family inductive must export one recursor",
        None,
    ),
    "well-founded": (
        "CompletedImport",
        None,
        None,
        None,
        (160, 5, 731, 23, 35, 0, 0, 35),
    ),
}
EXPECTED_TL212_COMPUTATIONS = {
    "recursive-indexed": (
        "docs/plan/fixtures/lean4export-v4.30-recursive-ih-vector-computation.ndjson",
        "1ab5a38b50d4d2c7ba01ef2831bb5af5d3c56ce1b9879c1942070519a9f6df19",
        15_944,
        284,
        "AxeyumRecursiveIHComputation.vectorHeightComputes",
        "MiniNat.succ MiniNat.zero",
        (60, 4, 211, 8, 18, 0, 0, 18),
    ),
    "reflexive-higher-order": (
        "docs/plan/fixtures/lean4export-v4.30-recursive-ih-acc-computation.ndjson",
        "3cb06283f1e757d79d28335dfe77ccd00231a8d323c2310dddced6473933c003",
        17_722,
        314,
        "AxeyumRecursiveIHComputation.accPropertyComputes",
        "True",
        (67, 3, 232, 11, 20, 0, 0, 20),
    ),
}
EXPECTED_TL213_OUTCOMES = {
    "mutual": (
        "CompletedImport",
        None,
        None,
        None,
        (75, 4, 305, 10, 26, 0, 0, 26),
    ),
}
EXPECTED_TL213_COMPUTATIONS = {
    "cross-family": (
        "docs/plan/fixtures/lean4export-v4.30-mutual-cross-computation.ndjson",
        "5013aff1165c8a50a63c54cd946ab2b489d0edfee7e0862bc53b061eabac0070",
        18_827,
        318,
        "AxeyumMutualInductiveComputation.crossFamilyComputes",
        "MiniNat.succ (MiniNat.succ MiniNat.zero)",
        (60, 4, 246, 7, 21, 0, 0, 21),
    ),
    "indexed-cross-family": (
        "docs/plan/fixtures/lean4export-v4.30-mutual-indexed-computation.ndjson",
        "fe867639eeed25db9672730b092db32a49b79e82c6c59c386d9ff0e6a48b3787",
        21_455,
        374,
        "AxeyumMutualInductiveComputation.indexedCrossFamilyComputes",
        "MiniNat.succ (MiniNat.succ MiniNat.zero)",
        (72, 4, 290, 7, 21, 0, 0, 21),
    ),
}
EXPECTED_TL214_OUTCOMES = {
    "nested": (
        "CompletedImport",
        None,
        None,
        None,
        (70, 6, 322, 10, 22, 0, 0, 22),
    ),
}
EXPECTED_TL214_COMPUTATIONS = {
    "auxiliary-recursion-computation": (
        "docs/plan/fixtures/lean4export-v4.30-nested-aux-computation.ndjson",
        "36fb9c6f85a99a7d6d1f6329a2cfe5265b148f0138e979d6d391d9e8879e07de",
        36_706,
        642,
        "AxeyumNestedInductiveComputation.roseAuxiliaryRecursorComputes",
        "MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))",
        (122, 8, 494, 17, 34, 0, 0, 34),
    ),
    "indexed-container-computation": (
        "docs/plan/fixtures/lean4export-v4.30-nested-indexed-computation.ndjson",
        "a14ca423410c4f0a86c2a2cea193e5a76bd91428e348402b3dd32e1603481429",
        40_119,
        714,
        "AxeyumNestedInductiveComputation.indexedAuxiliaryRecursorComputes",
        "MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))",
        (134, 8, 554, 17, 34, 0, 0, 34),
    ),
    "repeated-container-reuse-computation": (
        "docs/plan/fixtures/lean4export-v4.30-nested-repeated-container-computation.ndjson",
        "af369edb2d9e0346a5457ba4c9cde6f3030ca08002dc931c5fb26709e0f74344",
        37_771,
        666,
        "AxeyumNestedInductiveComputation.repeatedContainerReusesAuxiliaryRecursor",
        "MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))))",
        (122, 8, 518, 17, 34, 0, 0, 34),
    ),
}
ALLOWED_ASSURANCE_CLASSES = {
    "official-source-rejected",
    "official-export-inventory-only",
    "parsed-declined",
    "translated-kernel-declined",
    "independently-admitted",
    "dual-admitted-computation-checked",
}
EXPECTED_CASES = [
    (
        "direct-recursive-control",
        "direct-recursive-non-indexed",
        "positive-control",
        "historical-direct-recursive-control",
        "AxeyumImportShapes",
        "AxeyumImportShapes",
        "miniOne",
        "accepted",
    ),
    (
        "recursive-indexed",
        "recursive-indexed",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.recursiveIndexedWitness",
        "AxeyumConstructMatrix.recursiveIndexedWitness",
        "accepted",
    ),
    (
        "reflexive-higher-order",
        "reflexive-higher-order",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.reflexiveWitness",
        "AxeyumConstructMatrix.reflexiveWitness",
        "accepted",
    ),
    (
        "mutual",
        "mutual",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.mutualWitness",
        "AxeyumConstructMatrix.mutualWitness",
        "accepted",
    ),
    (
        "nested",
        "nested",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.nestedWitness",
        "AxeyumConstructMatrix.nestedWitness",
        "accepted",
    ),
    (
        "well-founded",
        "well-founded",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.wellFoundedWitness",
        "AxeyumConstructMatrix.wellFoundedWitness",
        "accepted",
    ),
    (
        "non-positive-source-negative",
        "non-positive-inductive",
        "official-source-negative",
        "negative",
        "AxeyumConstructMatrixNegative",
        None,
        None,
        "rejected",
    ),
]


def load_manifest(path: Path = MANIFEST) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("manifest root must be an object")
    return data


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def check_exact_keys(value: Any, expected: set[str], context: str, failures: list[str]) -> None:
    if not isinstance(value, dict):
        failures.append(f"{context} must be an object")
        return
    actual = set(value)
    if actual != expected:
        failures.append(
            f"{context} fields drift: missing={sorted(expected - actual)} "
            f"extra={sorted(actual - expected)}"
        )


def checked_repo_path(raw: Any, context: str, failures: list[str]) -> Path | None:
    if not isinstance(raw, str) or not raw:
        failures.append(f"{context} must be a non-empty repository-relative path")
        return None
    path = (ROOT / raw).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError:
        failures.append(f"{context} escapes the repository: {raw}")
        return None
    if not path.is_file():
        failures.append(f"{context} is missing: {raw}")
        return None
    return path


def validate_file_hash(entry: Any, path_key: str, hash_key: str, context: str) -> list[str]:
    failures: list[str] = []
    if not isinstance(entry, dict):
        return [f"{context} must be an object"]
    path = checked_repo_path(entry.get(path_key), f"{context}.{path_key}", failures)
    expected_hash = entry.get(hash_key)
    if not isinstance(expected_hash, str) or len(expected_hash) != 64:
        failures.append(f"{context}.{hash_key} must be a 64-character SHA-256")
    elif path is not None:
        actual_hash = sha256(path)
        if actual_hash != expected_hash:
            failures.append(
                f"{context} hash drift for {entry[path_key]}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
    return failures


def validate_stage_b(data: dict[str, Any], failures: list[str]) -> None:
    stage_b = data.get("stage_b")
    check_exact_keys(stage_b, STAGE_B_KEYS, "stage_b", failures)
    if not isinstance(stage_b, dict):
        return
    if stage_b.get("frozen_date") != "2026-07-22":
        failures.append("Stage B freeze date drift")
    for key, expected in (
        ("independent_reader", "scripts/prototype_lean4export_reader.py"),
        ("independent_census", "scripts/prototype_lean4export_census.py"),
    ):
        if stage_b.get(key) != expected:
            failures.append(f"Stage B {key} drift")
        else:
            checked_repo_path(stage_b[key], f"stage_b.{key}", failures)

    streams = stage_b.get("streams")
    if not isinstance(streams, dict):
        failures.append("stage_b.streams must be an object")
        return
    if list(streams) != list(EXPECTED_STAGE_B_PATHS):
        failures.append("Stage B stream population/order drift")

    total_bytes = 0
    retention = data.get("retention_policy")
    per_stream_limit = EXPECTED_RETENTION["per_stream_max_bytes"]
    aggregate_limit = EXPECTED_RETENTION["aggregate_new_stream_max_bytes"]
    if isinstance(retention, dict):
        per_stream_limit = retention.get("per_stream_max_bytes", per_stream_limit)
        aggregate_limit = retention.get("aggregate_new_stream_max_bytes", aggregate_limit)

    roots = {case[0]: case[5] for case in EXPECTED_CASES}
    for case_id, expected_path in EXPECTED_STAGE_B_PATHS.items():
        stream = streams.get(case_id)
        check_exact_keys(stream, STREAM_KEYS, f"stage_b.streams.{case_id}", failures)
        if not isinstance(stream, dict):
            continue
        if stream.get("path") != expected_path:
            failures.append(f"{case_id}: retained stream path drift")
        path = checked_repo_path(stream.get("path"), f"{case_id}.path", failures)
        if stream.get("selected_root") != roots[case_id]:
            failures.append(f"{case_id}: selected root drift")
        if stream.get("export_runs") != 2 or stream.get("byte_identical") is not True:
            failures.append(f"{case_id}: two byte-identical official exports are required")
        if stream.get("retained") is not True:
            failures.append(f"{case_id}: retained Stage B stream must be marked retained")
        rss = stream.get("max_rss_kib")
        if not (
            isinstance(rss, list)
            and len(rss) == 2
            and all(isinstance(value, int) and 0 < value <= 4 * 1024 * 1024 for value in rss)
        ):
            failures.append(f"{case_id}: both export RSS values must fit the 4 GiB cgroup")
        inventory = stream.get("inventory")
        if path is not None:
            observed = json.loads(
                json.dumps(census_bytes(path.read_bytes(), label=case_id), sort_keys=True)
            )
            if inventory != observed:
                failures.append(f"{case_id}: independent wire inventory drift")
            size = path.stat().st_size
            total_bytes += size
            if size > per_stream_limit:
                failures.append(f"{case_id}: retained stream exceeds the per-stream limit")
        if isinstance(inventory, dict):
            declarations = inventory.get("declaration_names")
            if not isinstance(declarations, list) or not declarations:
                failures.append(f"{case_id}: inventory must contain declaration names")
            elif declarations[-1] != roots[case_id]:
                failures.append(f"{case_id}: final declaration is not the selected root")

    if total_bytes > aggregate_limit:
        failures.append("Stage B retained streams exceed the aggregate limit")
    if stage_b.get("new_stream_aggregate_bytes") != total_bytes:
        failures.append("Stage B aggregate byte count drift")


def validate_product(data: dict[str, Any], failures: list[str]) -> None:
    product = data.get("product_measurement")
    check_exact_keys(product, PRODUCT_KEYS, "product_measurement", failures)
    if not isinstance(product, dict):
        return
    expected_scalars = {
        "measured_date": "2026-07-22",
        "source_revision": "22f51b4b0a94a1ae4d1c18b3f0dee6f56005edf4",
        "crate": "axeyum-lean-import",
        "example": "lean4export_import",
        "memory_max": "4G",
        "rust_jobs": 2,
        "runs_per_case": 2,
        "control_before_each_run": True,
        "control_runs": 10,
    }
    for key, expected in expected_scalars.items():
        if product.get(key) != expected:
            failures.append(f"product measurement {key} drift")
    if product.get("control") != EXPECTED_PRODUCT_CONTROL:
        failures.append("product direct-recursive control report drift")

    outcomes = product.get("outcomes")
    if not isinstance(outcomes, dict):
        failures.append("product outcomes must be an object")
        return
    if list(outcomes) != list(EXPECTED_PRODUCT_OUTCOMES):
        failures.append("product outcome population/order drift")
    for case_id, expected in EXPECTED_PRODUCT_OUTCOMES.items():
        outcome = outcomes.get(case_id)
        check_exact_keys(outcome, OUTCOME_KEYS, f"product.outcomes.{case_id}", failures)
        if not isinstance(outcome, dict):
            continue
        actual = (
            outcome.get("outcome_layer"),
            outcome.get("variant"),
            outcome.get("line"),
            outcome.get("declaration"),
            outcome.get("source_variant"),
            outcome.get("code"),
            outcome.get("message"),
        )
        if actual != expected:
            failures.append(f"{case_id}: typed product outcome drift")
        if outcome.get("runs") != 2 or outcome.get("repeatable") is not True:
            failures.append(f"{case_id}: product outcome must repeat twice")
        if outcome.get("completed_import_published") is not False:
            failures.append(f"{case_id}: a decline must not publish CompletedImport")


def report_tuple(report: Any) -> tuple[Any, ...] | None:
    if not isinstance(report, dict):
        return None
    return (
        report.get("names"),
        report.get("levels"),
        report.get("expressions"),
        report.get("declaration_records"),
        report.get("admitted_declarations"),
        report.get("axioms"),
        report.get("axiom_identities"),
        report.get("declaration_identities"),
    )


def validate_tl212_update(data: dict[str, Any], failures: list[str]) -> None:
    update = data.get("tl2_12_update")
    check_exact_keys(update, TL212_UPDATE_KEYS, "tl2_12_update", failures)
    if not isinstance(update, dict):
        return
    expected_scalars = {
        "measured_date": "2026-07-22",
        "source_revision": "cca3ee6d33d22be696b75c6af95883dcf9d3b72a",
        "runs_per_case": 2,
        "resource_runner": "systemd-run --user --scope",
        "memory_max": "4G",
        "rust_jobs": 1,
        "lean_jobs": 1,
        "lean_source_runs": 2,
        "lean_olean_sha256": "8b5136f7e66b18c9ad00b7f67b732ebb0fd9ff437128a80bdce831f011c7f573",
        "lean_elapsed_ms": [220, 210],
        "lean_max_rss_kib": [462632, 462832],
        "rust_gate_elapsed_ms": 430,
        "rust_gate_max_rss_kib": 144304,
    }
    for key, expected in expected_scalars.items():
        if update.get(key) != expected:
            failures.append(f"TL2.12 update {key} drift")
    for key in ("construct_test", "computation_test"):
        checked_repo_path(update.get(key), f"tl2_12_update.{key}", failures)

    outcomes = update.get("outcomes")
    if not isinstance(outcomes, dict):
        failures.append("TL2.12 outcomes must be an object")
    elif list(outcomes) != list(EXPECTED_TL212_OUTCOMES):
        failures.append("TL2.12 outcome population/order drift")
    else:
        for case_id, expected in EXPECTED_TL212_OUTCOMES.items():
            outcome = outcomes[case_id]
            check_exact_keys(
                outcome,
                TL212_OUTCOME_KEYS,
                f"tl2_12_update.outcomes.{case_id}",
                failures,
            )
            if not isinstance(outcome, dict):
                continue
            actual = (
                outcome.get("variant"),
                outcome.get("line"),
                outcome.get("code"),
                outcome.get("message"),
                report_tuple(outcome.get("report")),
            )
            if actual != expected:
                failures.append(f"{case_id}: TL2.12 typed outcome/report drift")
            if outcome.get("runs") != 2:
                failures.append(f"{case_id}: TL2.12 outcome must repeat twice")
            report = outcome.get("report")
            if report is not None:
                check_exact_keys(
                    report,
                    TL212_REPORT_KEYS,
                    f"tl2_12_update.outcomes.{case_id}.report",
                    failures,
                )

    computations = update.get("computations")
    if not isinstance(computations, dict):
        failures.append("TL2.12 computations must be an object")
    elif list(computations) != list(EXPECTED_TL212_COMPUTATIONS):
        failures.append("TL2.12 computation population/order drift")
    else:
        for case_id, expected in EXPECTED_TL212_COMPUTATIONS.items():
            computation = computations[case_id]
            check_exact_keys(
                computation,
                TL212_COMPUTATION_KEYS,
                f"tl2_12_update.computations.{case_id}",
                failures,
            )
            if not isinstance(computation, dict):
                continue
            path = checked_repo_path(
                computation.get("path"),
                f"tl2_12_update.computations.{case_id}.path",
                failures,
            )
            actual = (
                computation.get("path"),
                computation.get("sha256"),
                computation.get("bytes"),
                computation.get("records"),
                computation.get("theorem"),
                computation.get("normal_form"),
                report_tuple(computation.get("report")),
            )
            if actual != expected:
                failures.append(f"{case_id}: TL2.12 computation contract drift")
            if (
                computation.get("runs") != 2
                or computation.get("completed") is not True
                or computation.get("reduction_checked") is not True
            ):
                failures.append(f"{case_id}: two checked TL2.12 computations required")
            check_exact_keys(
                computation.get("report"),
                TL212_REPORT_KEYS,
                f"tl2_12_update.computations.{case_id}.report",
                failures,
            )
            if path is not None:
                if sha256(path) != computation.get("sha256"):
                    failures.append(f"{case_id}: TL2.12 computation hash drift")
                if path.stat().st_size != computation.get("bytes"):
                    failures.append(f"{case_id}: TL2.12 computation size drift")
                if len(path.read_bytes().splitlines()) != computation.get("records"):
                    failures.append(f"{case_id}: TL2.12 computation record drift")


def validate_tl213_update(data: dict[str, Any], failures: list[str]) -> None:
    update = data.get("tl2_13_update")
    check_exact_keys(update, TL213_UPDATE_KEYS, "tl2_13_update", failures)
    if not isinstance(update, dict):
        return
    expected_scalars = {
        "measured_date": "2026-07-22",
        "source_revision": "931524688efea5da928a14cfec03cf2fb0cf5a81",
        "product_test": (
            "crates/axeyum-lean-import/tests/official_mutual_inductive_groups.rs"
        ),
        "runs_per_case": 2,
        "resource_runner": "systemd-run --user --scope",
        "memory_max": "4G",
        "rust_jobs": 1,
        "rust_test_threads": 1,
        "lean_jobs": 1,
        "lean_source_runs": 2,
        "lean_olean_sha256": (
            "b2582c150c5901728a871919e1c04922f44c11ddeba1a8a446189b6c4d604aba"
        ),
        "lean_elapsed_ms": [460, 220],
        "lean_max_rss_kib": [474312, 474740],
        "rust_gate_elapsed_ms": 280,
        "rust_gate_max_rss_kib": 52892,
    }
    for key, expected in expected_scalars.items():
        if update.get(key) != expected:
            failures.append(f"TL2.13 update {key} drift")
    checked_repo_path(update.get("product_test"), "tl2_13_update.product_test", failures)

    outcomes = update.get("outcomes")
    if not isinstance(outcomes, dict):
        failures.append("TL2.13 outcomes must be an object")
    elif list(outcomes) != list(EXPECTED_TL213_OUTCOMES):
        failures.append("TL2.13 outcome population/order drift")
    else:
        for case_id, expected in EXPECTED_TL213_OUTCOMES.items():
            outcome = outcomes[case_id]
            check_exact_keys(
                outcome,
                TL213_OUTCOME_KEYS,
                f"tl2_13_update.outcomes.{case_id}",
                failures,
            )
            if not isinstance(outcome, dict):
                continue
            actual = (
                outcome.get("variant"),
                outcome.get("line"),
                outcome.get("code"),
                outcome.get("message"),
                report_tuple(outcome.get("report")),
            )
            if actual != expected:
                failures.append(f"{case_id}: TL2.13 typed outcome/report drift")
            if outcome.get("runs") != 2:
                failures.append(f"{case_id}: TL2.13 outcome must repeat twice")
            check_exact_keys(
                outcome.get("report"),
                TL213_REPORT_KEYS,
                f"tl2_13_update.outcomes.{case_id}.report",
                failures,
            )

    computations = update.get("computations")
    if not isinstance(computations, dict):
        failures.append("TL2.13 computations must be an object")
    elif list(computations) != list(EXPECTED_TL213_COMPUTATIONS):
        failures.append("TL2.13 computation population/order drift")
    else:
        for computation_id, expected in EXPECTED_TL213_COMPUTATIONS.items():
            computation = computations[computation_id]
            check_exact_keys(
                computation,
                TL213_COMPUTATION_KEYS,
                f"tl2_13_update.computations.{computation_id}",
                failures,
            )
            if not isinstance(computation, dict):
                continue
            path = checked_repo_path(
                computation.get("path"),
                f"tl2_13_update.computations.{computation_id}.path",
                failures,
            )
            actual = (
                computation.get("path"),
                computation.get("sha256"),
                computation.get("bytes"),
                computation.get("records"),
                computation.get("theorem"),
                computation.get("normal_form"),
                report_tuple(computation.get("report")),
            )
            if actual != expected:
                failures.append(f"{computation_id}: TL2.13 computation contract drift")
            if (
                computation.get("runs") != 2
                or computation.get("completed") is not True
                or computation.get("reduction_checked") is not True
            ):
                failures.append(
                    f"{computation_id}: two checked TL2.13 computations required"
                )
            check_exact_keys(
                computation.get("report"),
                TL213_REPORT_KEYS,
                f"tl2_13_update.computations.{computation_id}.report",
                failures,
            )
            if path is not None:
                if sha256(path) != computation.get("sha256"):
                    failures.append(f"{computation_id}: TL2.13 computation hash drift")
                if path.stat().st_size != computation.get("bytes"):
                    failures.append(f"{computation_id}: TL2.13 computation size drift")
                if len(path.read_bytes().splitlines()) != computation.get("records"):
                    failures.append(f"{computation_id}: TL2.13 computation record drift")


def validate_tl214_update(data: dict[str, Any], failures: list[str]) -> None:
    update = data.get("tl2_14_update")
    check_exact_keys(update, TL214_UPDATE_KEYS, "tl2_14_update", failures)
    if not isinstance(update, dict):
        return
    if tuple(update) != TL214_UPDATE_ORDER:
        failures.append("TL2.14 update field order drift")
    expected_scalars = {
        "measured_date": "2026-07-22",
        "source_revision": "edfa7924adde416393db74325bf29ce280e3f8a7",
        "product_test": (
            "crates/axeyum-lean-import/tests/official_nested_inductive_groups.rs"
        ),
        "runs_per_case": 2,
        "resource_runner": "systemd-run --user --scope",
        "memory_max": "4G",
        "rust_jobs": 1,
        "rust_test_threads": 1,
        "lean_jobs": 1,
        "lean_source_runs": 2,
        "lean_olean_sha256": (
            "d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2"
        ),
        "lean_elapsed_ms": [1500, 260],
        "lean_max_rss_kib": [457700, 462308],
        "rust_gate_elapsed_ms": 1070,
        "rust_gate_max_rss_kib": 170852,
    }
    for key, expected in expected_scalars.items():
        if update.get(key) != expected:
            failures.append(f"TL2.14 update {key} drift")
    checked_repo_path(update.get("product_test"), "tl2_14_update.product_test", failures)

    outcomes = update.get("outcomes")
    if not isinstance(outcomes, dict):
        failures.append("TL2.14 outcomes must be an object")
    elif list(outcomes) != list(EXPECTED_TL214_OUTCOMES):
        failures.append("TL2.14 outcome population/order drift")
    else:
        for case_id, expected in EXPECTED_TL214_OUTCOMES.items():
            outcome = outcomes[case_id]
            check_exact_keys(
                outcome,
                TL214_OUTCOME_KEYS,
                f"tl2_14_update.outcomes.{case_id}",
                failures,
            )
            if not isinstance(outcome, dict):
                continue
            if tuple(outcome) != TL214_OUTCOME_ORDER:
                failures.append(f"{case_id}: TL2.14 outcome field order drift")
            actual = (
                outcome.get("variant"),
                outcome.get("line"),
                outcome.get("code"),
                outcome.get("message"),
                report_tuple(outcome.get("report")),
            )
            if actual != expected:
                failures.append(f"{case_id}: TL2.14 typed outcome/report drift")
            if outcome.get("runs") != 2:
                failures.append(f"{case_id}: TL2.14 outcome must repeat twice")
            check_exact_keys(
                outcome.get("report"),
                TL214_REPORT_KEYS,
                f"tl2_14_update.outcomes.{case_id}.report",
                failures,
            )
            if isinstance(outcome.get("report"), dict) and tuple(
                outcome["report"]
            ) != TL214_REPORT_ORDER:
                failures.append(f"{case_id}: TL2.14 report field order drift")

    computations = update.get("computations")
    if not isinstance(computations, dict):
        failures.append("TL2.14 computations must be an object")
    elif list(computations) != list(EXPECTED_TL214_COMPUTATIONS):
        failures.append("TL2.14 computation population/order drift")
    else:
        for computation_id, expected in EXPECTED_TL214_COMPUTATIONS.items():
            computation = computations[computation_id]
            check_exact_keys(
                computation,
                TL214_COMPUTATION_KEYS,
                f"tl2_14_update.computations.{computation_id}",
                failures,
            )
            if not isinstance(computation, dict):
                continue
            if tuple(computation) != TL214_COMPUTATION_ORDER:
                failures.append(
                    f"{computation_id}: TL2.14 computation field order drift"
                )
            path = checked_repo_path(
                computation.get("path"),
                f"tl2_14_update.computations.{computation_id}.path",
                failures,
            )
            actual = (
                computation.get("path"),
                computation.get("sha256"),
                computation.get("bytes"),
                computation.get("records"),
                computation.get("theorem"),
                computation.get("normal_form"),
                report_tuple(computation.get("report")),
            )
            if actual != expected:
                failures.append(f"{computation_id}: TL2.14 computation contract drift")
            if (
                computation.get("runs") != 2
                or computation.get("completed") is not True
                or computation.get("reduction_checked") is not True
            ):
                failures.append(
                    f"{computation_id}: two checked TL2.14 computations required"
                )
            check_exact_keys(
                computation.get("report"),
                TL214_REPORT_KEYS,
                f"tl2_14_update.computations.{computation_id}.report",
                failures,
            )
            if isinstance(computation.get("report"), dict) and tuple(
                computation["report"]
            ) != TL214_REPORT_ORDER:
                failures.append(
                    f"{computation_id}: TL2.14 report field order drift"
                )
            if path is not None:
                if sha256(path) != computation.get("sha256"):
                    failures.append(f"{computation_id}: TL2.14 computation hash drift")
                if path.stat().st_size != computation.get("bytes"):
                    failures.append(f"{computation_id}: TL2.14 computation size drift")
                if len(path.read_bytes().splitlines()) != computation.get("records"):
                    failures.append(f"{computation_id}: TL2.14 computation record drift")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    check_exact_keys(data, TOP_LEVEL_KEYS, "manifest", failures)
    if tuple(data)[-3:] != ("tl2_12_update", "tl2_13_update", "tl2_14_update"):
        failures.append("construct-matrix assurance overlay order drift")

    if data.get("schema") != SCHEMA:
        failures.append(f"schema must be {SCHEMA!r}")
    stage = data.get("stage")
    if stage not in {"source-frozen", "wire-frozen", "product-measured"}:
        failures.append("manifest stage must be source-frozen, wire-frozen, or product-measured")
    if data.get("date") != "2026-07-22":
        failures.append("Stage A date drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0351-preregister-official-lean-construct-matrix.md"
    ):
        failures.append("decision path drift")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("Lean/exporter pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")
    if data.get("retention_policy") != EXPECTED_RETENTION:
        failures.append("retention policy drift")
    if stage == "source-frozen":
        if data.get("stage_b") is not None:
            failures.append("Stage A must not contain Stage B wire observations")
        if data.get("product_measurement") is not None:
            failures.append("pre-product manifest must not contain product measurements")
        if data.get("tl2_12_update") is not None:
            failures.append("pre-product manifest must not contain TL2.12 updates")
        if data.get("tl2_13_update") is not None:
            failures.append("pre-product manifest must not contain TL2.13 updates")
        if data.get("tl2_14_update") is not None:
            failures.append("pre-product manifest must not contain TL2.14 updates")
    elif stage == "wire-frozen":
        validate_stage_b(data, failures)
        if data.get("product_measurement") is not None:
            failures.append("pre-product manifest must not contain product measurements")
        if data.get("tl2_12_update") is not None:
            failures.append("pre-product manifest must not contain TL2.12 updates")
        if data.get("tl2_13_update") is not None:
            failures.append("pre-product manifest must not contain TL2.13 updates")
        if data.get("tl2_14_update") is not None:
            failures.append("pre-product manifest must not contain TL2.14 updates")
    elif stage == "product-measured":
        validate_stage_b(data, failures)
        validate_product(data, failures)
        validate_tl212_update(data, failures)
        validate_tl213_update(data, failures)
        validate_tl214_update(data, failures)

    toolchain_path = ROOT / "lean-toolchain"
    if toolchain_path.read_text(encoding="utf-8").strip() != EXPECTED_PINS["lean"]["toolchain"]:
        failures.append("lean-toolchain does not match the registered pin")

    commands = data.get("commands")
    command_keys = {
        "working_directory",
        "resource_runner_argv",
        "lean_executable",
        "compile_positive_argv",
        "compile_negative_argv",
    }
    check_exact_keys(commands, command_keys, "commands", failures)
    if isinstance(commands, dict):
        expected_runner = [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            "-p",
            "MemoryHigh=3G",
            "-p",
            "MemoryMax=4G",
            "-p",
            "MemorySwapMax=512M",
        ]
        if commands.get("resource_runner_argv") != expected_runner:
            failures.append("resource runner argv drift")
        lean = commands.get("lean_executable")
        for key, output, source in (
            ("compile_positive_argv", "AxeyumConstructMatrix.olean", "AxeyumConstructMatrix.lean"),
            (
                "compile_negative_argv",
                "AxeyumConstructMatrixNegative.olean",
                "AxeyumConstructMatrixNegative.lean",
            ),
        ):
            expected = ["/usr/bin/time", "-v", lean, "-j1", "-o", output, source]
            if commands.get(key) != expected:
                failures.append(f"{key} drift")

    controls = data.get("historical_controls")
    if not isinstance(controls, list):
        failures.append("historical_controls must be an array")
    else:
        ids = [entry.get("id") for entry in controls if isinstance(entry, dict)]
        if ids != ["flat", "direct-recursive-control"]:
            failures.append("historical control order/population drift")
        for index, entry in enumerate(controls):
            check_exact_keys(
                entry,
                HISTORICAL_CONTROL_KEYS,
                f"historical_controls[{index}]",
                failures,
            )
            failures.extend(
                validate_file_hash(entry, "source_path", "source_sha256", f"historical_controls[{index}]")
            )
            failures.extend(
                validate_file_hash(entry, "stream_path", "stream_sha256", f"historical_controls[{index}]")
            )
            if isinstance(entry, dict):
                if entry.get("regenerated_runs") != 2 or entry.get("imported_runs") != 2:
                    failures.append(f"historical_controls[{index}] must record two reproductions and imports")
                report = entry.get("expected_report")
                check_exact_keys(
                    report,
                    REPORT_KEYS,
                    f"historical_controls[{index}].expected_report",
                    failures,
                )
                if report != EXPECTED_CONTROL_REPORTS.get(entry.get("id")):
                    failures.append(f"historical_controls[{index}] importer report drift")

    sources = data.get("sources")
    check_exact_keys(sources, {"positive", "negative"}, "sources", failures)
    if isinstance(sources, dict):
        positive = sources.get("positive")
        negative = sources.get("negative")
        check_exact_keys(
            positive,
            {"path", "sha256", "module", "official_source_outcome", "exit_status", "max_rss_kib"},
            "sources.positive",
            failures,
        )
        check_exact_keys(
            negative,
            {
                "path",
                "sha256",
                "module",
                "official_source_outcome",
                "exit_status",
                "diagnostic_substring",
                "max_rss_kib",
            },
            "sources.negative",
            failures,
        )
        failures.extend(validate_file_hash(positive, "path", "sha256", "sources.positive"))
        failures.extend(validate_file_hash(negative, "path", "sha256", "sources.negative"))
        if isinstance(positive, dict) and (
            positive.get("module") != "AxeyumConstructMatrix"
            or positive.get("official_source_outcome") != "accepted"
            or positive.get("exit_status") != 0
        ):
            failures.append("positive source compile outcome drift")
        if isinstance(positive, dict) and not (
            isinstance(positive.get("max_rss_kib"), int)
            and 0 < positive["max_rss_kib"] <= 4 * 1024 * 1024
        ):
            failures.append("positive source RSS must fit the 4 GiB cgroup")
        if isinstance(negative, dict) and (
            negative.get("module") != "AxeyumConstructMatrixNegative"
            or negative.get("official_source_outcome") != "rejected"
            or negative.get("exit_status") != 1
            or negative.get("diagnostic_substring")
            != "has a non positive occurrence of the datatypes being declared"
        ):
            failures.append("negative source rejection outcome drift")
        if isinstance(negative, dict) and not (
            isinstance(negative.get("max_rss_kib"), int)
            and 0 < negative["max_rss_kib"] <= 4 * 1024 * 1024
        ):
            failures.append("negative source RSS must fit the 4 GiB cgroup")

    cases = data.get("cases")
    if not isinstance(cases, list):
        failures.append("cases must be an array")
    else:
        if len(cases) != len(EXPECTED_CASES):
            failures.append(
                f"case population drift: expected {len(EXPECTED_CASES)}, got {len(cases)}"
            )
        ids = [case.get("id") for case in cases if isinstance(case, dict)]
        if len(ids) != len(set(ids)):
            failures.append("case IDs must be unique")
        for index, case in enumerate(cases):
            check_exact_keys(case, CASE_KEYS, f"cases[{index}]", failures)
            if not isinstance(case, dict):
                continue
            if stage != "product-measured" and case.get("product_measurement") is not None:
                failures.append(f"cases[{index}] contains premature product data")
            if stage == "source-frozen" and case.get("stage_b_wire") is not None:
                failures.append(f"cases[{index}] contains premature Stage B wire data")
            if stage in {"wire-frozen", "product-measured"}:
                case_id = case.get("id")
                if case_id == "direct-recursive-control":
                    expected_wire = "historical-direct-recursive-control"
                elif case_id == "non-positive-source-negative":
                    expected_wire = None
                else:
                    expected_wire = case_id
                if case.get("stage_b_wire") != expected_wire:
                    failures.append(f"cases[{index}] Stage B wire link drift")
            if stage == "product-measured":
                case_id = case.get("id")
                expected_product = None if case_id == "non-positive-source-negative" else case_id
                if case.get("product_measurement") != expected_product:
                    failures.append(f"cases[{index}] product measurement link drift")
            if index < len(EXPECTED_CASES):
                actual = (
                    case.get("id"),
                    case.get("source_family"),
                    case.get("role"),
                    case.get("source_key"),
                    case.get("module"),
                    case.get("selected_root"),
                    case.get("computation_witness"),
                    case.get("expected_official_source"),
                )
                if actual != EXPECTED_CASES[index]:
                    failures.append(f"cases[{index}] source-freeze contract drift")

    return failures


def derive_matrix_rows(data: dict[str, Any]) -> list[dict[str, str]]:
    failures = validate_manifest(data)
    if failures:
        raise ValueError("invalid registration: " + "; ".join(failures))
    if data.get("stage") != "product-measured":
        raise ValueError("assurance rows require the frozen product-measured stage")

    historical = {entry["id"]: entry for entry in data["historical_controls"]}
    streams = data["stage_b"]["streams"]
    outcomes = dict(data["tl2_12_update"]["outcomes"])
    outcomes.update(data["tl2_13_update"]["outcomes"])
    outcomes.update(data["tl2_14_update"]["outcomes"])
    tl212_computations = data["tl2_12_update"]["computations"]
    tl213_computations = data["tl2_13_update"]["computations"]
    tl214_computations = data["tl2_14_update"]["computations"]
    rows: list[dict[str, str]] = []
    for case in data["cases"]:
        case_id = case["id"]
        common = {
            "id": case_id,
            "source_family": case["source_family"],
            "official_source": case["expected_official_source"],
            "selected_root": case["selected_root"] or "—",
            "computation_streams": [],
        }
        if case_id == "non-positive-source-negative":
            row = {
                **common,
                "stream": "none",
                "wire_inventory": "not applicable",
                "rust_outcome": "not run: official source rejected",
                "rust_variant": "NotRun",
                "independent_admission": "no",
                "computation": "not applicable",
                "assurance_class": "official-source-rejected",
                "boundary": "official kernel strict-positivity rejection; no NDJSON assigned",
            }
        elif case_id == "direct-recursive-control":
            control = historical["direct-recursive-control"]
            report = control["expected_report"]
            row = {
                **common,
                "stream": control["stream_path"],
                "wire_inventory": (
                    f"N/L/E/D={report['names']}/{report['levels']}/"
                    f"{report['expressions']}/{report['declaration_records']}; "
                    "direct recursive, non-indexed"
                ),
                "rust_outcome": "CompletedImport: 11 declarations, 0 axioms",
                "rust_variant": "CompletedImport",
                "independent_admission": "yes",
                "computation": "not checked in this matrix",
                "assurance_class": "independently-admitted",
                "boundary": "exact fixture only; no computation or ecosystem credit",
            }
        else:
            stream = streams[case_id]
            inventory = stream["inventory"]
            outcome = outcomes[case_id]
            blockers = ", ".join(inventory["blockers"]) or "none"
            selected_computations: list[dict[str, Any]] = []
            if outcome["variant"] == "CompletedImport":
                report = outcome["report"]
                rust_outcome = (
                    f"CompletedImport: {report['admitted_declarations']} declarations, "
                    f"{report['axioms']} axioms"
                )
                if case_id == "mutual":
                    selected_computations = list(tl213_computations.values())
                elif case_id == "nested":
                    selected_computations = list(tl214_computations.values())
                elif case_id in tl212_computations:
                    selected_computations = [tl212_computations[case_id]]
                else:
                    selected_computations = []
                if not selected_computations:
                    computation_status = "not selected"
                    assurance = "independently-admitted"
                else:
                    computation_status = "checked"
                    assurance = "dual-admitted-computation-checked"
            elif outcome["variant"] == "Unsupported":
                rust_outcome = (
                    f"Unsupported line {outcome['line']}: {outcome['code']}"
                )
                assurance = "parsed-declined"
                computation_status = "not reached"
            else:
                rust_outcome = (
                    f"Malformed line {outcome['line']}: {outcome['message']}"
                )
                assurance = "official-export-inventory-only"
                computation_status = "not reached"
            if case_id == "well-founded":
                boundary = (
                    "pre-elaborated root admitted through Acc.rec; no frontend-lowering credit"
                )
            elif case_id == "mutual":
                computation_values = list(tl213_computations.values())
                boundary = "companion official streams check " + "; ".join(
                    f"{computation['theorem']} -> {computation['normal_form']}"
                    for computation in computation_values
                )
            elif case_id == "nested":
                computation_values = list(tl214_computations.values())
                boundary = "companion official streams check " + "; ".join(
                    f"{computation['theorem']} -> {computation['normal_form']}"
                    for computation in computation_values
                )
            elif case_id in tl212_computations:
                computation = tl212_computations[case_id]
                boundary = (
                    f"companion official stream checks {computation['theorem']} -> "
                    f"{computation['normal_form']}"
                )
            else:
                boundary = "stable transactional decline; no completed environment"
            row = {
                **common,
                "stream": stream["path"],
                "wire_inventory": (
                    f"N/L/E/D={inventory['names']}/{inventory['levels']}/"
                    f"{inventory['exprs']}/{inventory['decls']}; {blockers}"
                ),
                "rust_outcome": rust_outcome,
                "rust_variant": outcome["variant"],
                "independent_admission": (
                    "yes" if outcome["variant"] == "CompletedImport" else "no"
                ),
                "computation": computation_status,
                "assurance_class": assurance,
                "boundary": boundary,
            }
            row["computation_streams"] = [
                computation["path"] for computation in selected_computations
            ]
        row_failures = validate_matrix_row(row)
        if row_failures:
            raise ValueError(f"{case_id}: " + "; ".join(row_failures))
        rows.append(row)
    return rows


def validate_matrix_row(row: dict[str, str]) -> list[str]:
    failures: list[str] = []
    assurance = row.get("assurance_class")
    admitted = row.get("independent_admission") == "yes"
    computation_checked = row.get("computation") == "checked"
    variant = row.get("rust_variant")
    if assurance not in ALLOWED_ASSURANCE_CLASSES:
        failures.append("unregistered assurance class")
    if admitted != (
        assurance
        in {
            "independently-admitted",
            "dual-admitted-computation-checked",
        }
    ):
        failures.append("independent-admission/class implication violated")
    if computation_checked != (assurance == "dual-admitted-computation-checked"):
        failures.append("computation/class implication violated")
    if assurance == "official-source-rejected" and (
        row.get("official_source") != "rejected" or row.get("stream") != "none"
    ):
        failures.append("source-rejected credit requires rejection and no stream")
    if assurance == "translated-kernel-declined" and variant != "Kernel":
        failures.append("translated-kernel decline requires a Kernel outcome")
    if assurance == "parsed-declined" and variant != "Unsupported":
        failures.append("parsed decline requires an Unsupported outcome")
    if assurance == "official-export-inventory-only" and variant not in {"NotRun", "Malformed"}:
        failures.append("inventory-only credit has an incompatible Rust outcome")
    if admitted and variant != "CompletedImport":
        failures.append("independent admission requires CompletedImport")
    return failures


def markdown_link(path: str) -> str:
    if path == "none":
        return "none"
    prefix = "../" if path.startswith("docs/plan/") else "../../../"
    relative = path.removeprefix("docs/plan/")
    return f"[fixture]({prefix}{relative})"


def escape_cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def render_matrix(data: dict[str, Any]) -> str:
    rows = derive_matrix_rows(data)
    counts: dict[str, int] = {}
    for row in rows:
        assurance = row["assurance_class"]
        counts[assurance] = counts.get(assurance, 0) + 1
    admitted_count = sum(row["independent_admission"] == "yes" for row in rows)
    computation_count = sum(row["computation"] == "checked" for row in rows)
    decline_count = sum(
        row["rust_variant"] in {"Unsupported", "Malformed", "Kernel"} for row in rows
    )
    lines = [
        "# Official Lean construct matrix",
        "",
        "Generated from [`lean-official-construct-matrix-v1.json`](../lean-official-construct-matrix-v1.json).",
        "Do not edit by hand; regenerate with",
        "`python3 scripts/check-lean-official-construct-matrix.py --write`.",
        "",
        "This selected-family matrix separates official source/export evidence, independent Python",
        "wire inventory, current Rust outcomes, independent admission, and computation. It is not",
        "full Lean kernel, frontend, ecosystem, or mathlib compatibility.",
        "",
        "## Summary",
        "",
        f"- rows: {len(rows)}; official accepted: 6; official rejected: 1;",
        f"- independently admitted: {admitted_count}; computation-checked: {computation_count};",
        f"- current transactional declines: {decline_count};",
        "- assurance classes: "
        + ", ".join(f"`{key}`={counts[key]}" for key in sorted(counts))
        + ".",
        "",
        "## Matrix",
        "",
        "| Case | Source family | Official source | Selected root | Exact stream / independent wire inventory | Current Rust outcome | Independent admission | Computation | Assurance class | Exact boundary |",
        "|---|---|---|---|---|---|---|---|---|---|",
    ]
    for row in rows:
        stream = markdown_link(row["stream"])
        wire = f"{stream}; {row['wire_inventory']}" if stream != "none" else row["wire_inventory"]
        computation_streams = row["computation_streams"]
        if computation_streams:
            wire += "; computation " + ", ".join(
                markdown_link(path) for path in computation_streams
            )
        values = [
            f"`{row['id']}`",
            row["source_family"],
            row["official_source"],
            f"`{row['selected_root']}`" if row["selected_root"] != "—" else "—",
            wire,
            row["rust_outcome"],
            row["independent_admission"],
            row["computation"],
            f"`{row['assurance_class']}`",
            row["boundary"],
        ]
        lines.append("| " + " | ".join(escape_cell(value) for value in values) + " |")
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "- `independently-admitted` means the exact official stream produced a completed owned",
            "  environment through Axeyum's trusted gate. It does not imply a checked computation.",
            "- `dual-admitted-computation-checked` adds one or more separate frozen official",
            "  streams whose exported `rfl` theorems and registered normal forms are checked by",
            "  Axeyum reduction.",
            "- `translated-kernel-declined` means an official declaration reached the independent",
            "  kernel and received a typed rejection.",
            "- `parsed-declined` means importer policy recognized and transactionally declined the",
            "  official construct before independent admission.",
            "- `official-export-inventory-only` grants official bytes and independent Python wire",
            "  inventory only, without laundering it into parser or kernel credit.",
            "- `official-source-rejected` has no export by construction.",
            "",
            "The well-founded row now admits the already-elaborated selected root through `Acc.rec`.",
            "That is kernel/import evidence for this exact stream, not well-founded source elaboration,",
            "frontend lowering, or general ecosystem credit.",
            "The mutual row requires both the non-indexed and indexed companion computations; neither",
            "the construct witness nor only one companion stream is sufficient for computation credit.",
            "The nested row requires all three auxiliary-recursion companion computations; construct",
            "admission alone is likewise insufficient for computation credit.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="check generated Markdown")
    mode.add_argument("--write", action="store_true", help="write generated Markdown")
    args = parser.parse_args()
    try:
        data = load_manifest()
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"lean construct matrix: unable to load manifest: {error}", file=sys.stderr)
        return 1
    failures = validate_manifest(data)
    if failures:
        for failure in failures:
            print(f"lean construct matrix: {failure}", file=sys.stderr)
        return 1
    try:
        rendered = render_matrix(data) if data.get("stage") == "product-measured" else None
    except ValueError as error:
        print(f"lean construct matrix: {error}", file=sys.stderr)
        return 1
    if args.write:
        if rendered is None:
            print("lean construct matrix: product measurement is not frozen", file=sys.stderr)
            return 1
        OUT_MD.write_text(rendered, encoding="utf-8")
    elif args.check:
        if rendered is None or not OUT_MD.is_file():
            print("lean construct matrix: generated matrix is missing", file=sys.stderr)
            return 1
        if OUT_MD.read_text(encoding="utf-8") != rendered:
            print("lean construct matrix: generated matrix drift", file=sys.stderr)
            return 1
    print(
        f"lean construct matrix {data['stage']} valid: "
        f"{len(data['cases'])} cases, 2 source outcomes, "
        f"{len(data['historical_controls'])} reproduced controls, "
        f"Stage B={'frozen' if data['stage'] != 'source-frozen' else 'absent'}, "
        f"product={'frozen' if data['stage'] == 'product-measured' else 'absent'}, "
        f"TL2.12={'frozen' if data.get('tl2_12_update') else 'absent'}, "
        f"TL2.13={'frozen' if data.get('tl2_13_update') else 'absent'}, "
        f"TL2.14={'current' if data.get('tl2_14_update') else 'absent'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
