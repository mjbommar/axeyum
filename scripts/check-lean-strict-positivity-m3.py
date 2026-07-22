#!/usr/bin/env python3
"""Validate the observed TL2.11 M3 official/import boundary fail closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-strict-positivity-m3-v1.json"
SCHEMA = "axeyum-lean-strict-positivity-m3-v1"
IMPLEMENTATION_REVISION = "9a954695ed109e1b00877f1f28ef44e9caca4e1d"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "implementation_revision",
    "source_freeze",
    "lean",
    "official_runs",
    "official_summary",
    "synthetic_importer",
    "construct_matrix_regression",
}
RUN_KEYS = {
    "repetition",
    "source",
    "exit_status",
    "outcome",
    "diagnostic_stream",
    "max_rss_kib",
}
EXPECTED_RUNS = (
    (1, "construct-matrix-positive", 0, "accepted", None, 468120),
    (1, "negative-domain", 1, "rejected", "stdout", 88584),
    (1, "negative-mixed", 1, "rejected", "stdout", 86692),
    (1, "negative-deep", 1, "rejected", "stdout", 88512),
    (2, "construct-matrix-positive", 0, "accepted", None, 468432),
    (2, "negative-domain", 1, "rejected", "stdout", 88652),
    (2, "negative-mixed", 1, "rejected", "stdout", 86056),
    (2, "negative-deep", 1, "rejected", "stdout", 88880),
)
EXPECTED_SUMMARY = {
    "sources": 4,
    "runs": 8,
    "accepted": 2,
    "rejected": 6,
    "diagnostic_matches": 6,
    "max_rss_kib": 468432,
}


def sha256(path: Path) -> str:
    """Return the lowercase SHA-256 digest of *path*."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_manifest() -> dict[str, Any]:
    """Load the committed M3 observation manifest."""

    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def check_bound_file(binding: Any, label: str, failures: list[str]) -> None:
    """Validate one exact path/hash binding."""

    if not isinstance(binding, dict) or set(binding) != {"path", "sha256"}:
        failures.append(f"{label} binding fields drift")
        return
    path = ROOT / binding["path"]
    if not path.is_file():
        failures.append(f"{label} file missing")
    elif sha256(path) != binding["sha256"]:
        failures.append(f"{label} hash drift")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    """Return every fail-closed M3 observation violation."""

    failures: list[str] = []
    if set(data) != TOP_LEVEL_KEYS:
        failures.append("top-level fields drift")
    if data.get("schema") != SCHEMA:
        failures.append("schema drift")
    if data.get("stage") != "official-and-product-observed":
        failures.append("M3 stage drift")
    if data.get("implementation_revision") != IMPLEMENTATION_REVISION:
        failures.append("implementation revision drift")
    check_bound_file(data.get("source_freeze"), "source freeze", failures)

    lean = data.get("lean", {})
    if lean != {
        "version": "4.30.0",
        "git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "version_output": (
            "Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit "
            "d024af099ca4bf2c86f649261ebf59565dc8c622, Release)"
        ),
    }:
        failures.append("Lean identity drift")

    observed: list[tuple[Any, ...]] = []
    for index, run in enumerate(data.get("official_runs", [])):
        if not isinstance(run, dict) or set(run) != RUN_KEYS:
            failures.append(f"official run fields drift: {index}")
            continue
        observed.append(
            (
                run["repetition"],
                run["source"],
                run["exit_status"],
                run["outcome"],
                run["diagnostic_stream"],
                run["max_rss_kib"],
            )
        )
        if not 0 < run["max_rss_kib"] <= 4 * 1024 * 1024:
            failures.append(f"official run exceeds resource envelope: {index}")
    if tuple(observed) != EXPECTED_RUNS:
        failures.append("official run population/order/outcomes drift")
    if data.get("official_summary") != EXPECTED_SUMMARY:
        failures.append("official summary drift")

    synthetic = data.get("synthetic_importer", {})
    expected_synthetic = {
        "assurance": "synthetic-format-mutation-not-official-wire",
        "base_fixture": (
            "docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson"
        ),
        "base_sha256": (
            "91df1e44219483b213000b94b06016f9569dc648d0680d9ae91ff3198817db08"
        ),
        "inserted_expression": (
            '{"forallE":{"binderInfo":"default","body":84,'
            '"name":10,"type":85},"ie":114}'
        ),
        "group_mutation": "MiniNat.succ type 85 -> 114",
        "expected_line": 151,
        "expected_declaration": "MiniNat",
        "expected_error": "NonPositiveInductiveOccurrence(field_index=0)",
        "completed_import_published": False,
        "test": (
            "cargo test -p axeyum-lean-import --test "
            "strict_positivity_propagation"
        ),
    }
    if synthetic != expected_synthetic:
        failures.append("synthetic importer observation drift")
    else:
        base = ROOT / synthetic["base_fixture"]
        if not base.is_file() or sha256(base) != synthetic["base_sha256"]:
            failures.append("synthetic importer base hash drift")

    matrix = data.get("construct_matrix_regression", {})
    expected_matrix = {
        "registration": "docs/plan/lean-official-construct-matrix-v1.json",
        "historical_registration_sha256": (
            "e76d334f4354eac297d447ae31b3f6f2b3460f99d0817af14e95faf30e8ef0d1"
        ),
        "current_registration_sha256": (
            "f6c11499ab38130de75c7acbd7ad1db79afcd080ab405a7233087f8f67c3ac3e"
        ),
        "test": "cargo test -p axeyum-lean-import --test official_construct_matrix",
        "control_repetitions": 10,
        "decline_observations": 10,
        "outcomes_unchanged_at_m3": True,
        "superseded_by_tl2_12": True,
    }
    if matrix != expected_matrix:
        failures.append("construct-matrix observation drift")
    else:
        registration = ROOT / matrix["registration"]
        if not registration.is_file() or sha256(registration) != matrix[
            "current_registration_sha256"
        ]:
            failures.append("construct-matrix registration hash drift")
        elif "tl2_12_update" not in json.loads(registration.read_text(encoding="utf-8")):
            failures.append("construct-matrix TL2.12 update missing")
    return failures


def main() -> int:
    """CLI entry point."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.parse_args()
    failures = validate_manifest(load_manifest())
    if failures:
        for failure in failures:
            print(f"lean strict positivity M3: {failure}", file=sys.stderr)
        return 1
    print(
        "lean strict positivity M3 observed: "
        "4 sources, 8 official runs, 1 synthetic importer rejection, "
        "construct matrix unchanged"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
