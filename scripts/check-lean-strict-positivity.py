#!/usr/bin/env python3
"""Validate the TL2.11 strict-positivity source freeze fail closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-strict-positivity-v1.json"
SCHEMA = "axeyum-lean-strict-positivity-v1"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "decision",
    "plan",
    "pins",
    "resource_policy",
    "commands",
    "sources",
    "cases",
}
SOURCE_KEYS = {
    "path",
    "sha256",
    "module",
    "expected_official_outcome",
    "expected_diagnostic_substring",
}
CASE_KEYS = {
    "id",
    "source",
    "source_family",
    "expected_rule_class",
    "expected_official_outcome",
}
EXPECTED_PINS = {
    "lean_toolchain": "leanprover/lean4:v4.30.0",
    "lean_version": "4.30.0",
    "lean_git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
}
EXPECTED_RESOURCES = {
    "runner": "systemd-run --user --scope",
    "memory_high": "3G",
    "memory_max": "4G",
    "memory_swap_max": "512M",
    "lean_jobs": 1,
    "rust_jobs": 2,
}
EXPECTED_SOURCE_ORDER = (
    "construct-matrix-positive",
    "negative-domain",
    "negative-mixed",
    "negative-deep",
)
EXPECTED_CASES = (
    (
        "direct-recursive",
        "construct-matrix-positive",
        "direct-recursive-non-indexed",
        "positive-direct",
        "accepted",
    ),
    (
        "recursive-indexed",
        "construct-matrix-positive",
        "recursive-indexed",
        "positive-valid-indexed-application",
        "accepted",
    ),
    (
        "reflexive-higher-order",
        "construct-matrix-positive",
        "reflexive-higher-order",
        "positive-pi-codomain",
        "accepted",
    ),
    (
        "negative-domain",
        "negative-domain",
        "negative-function-domain",
        "non-positive-pi-domain",
        "rejected",
    ),
    (
        "negative-mixed",
        "negative-mixed",
        "mixed-positive-negative",
        "non-positive-pi-domain",
        "rejected",
    ),
    (
        "negative-deep",
        "negative-deep",
        "deep-negative-domain",
        "non-positive-pi-domain",
        "rejected",
    ),
)
EXPECTED_RUNNER = [
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
EXPECTED_LEAN_ARGV = [
    "/usr/bin/time",
    "-v",
    "<pinned-lean>",
    "-j1",
    "-o",
    "<module>.olean",
    "<module>.lean",
]


def sha256(path: Path) -> str:
    """Return the lowercase SHA-256 digest of *path*."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_manifest() -> dict[str, Any]:
    """Load the committed source-freeze manifest."""

    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def validate_manifest(data: dict[str, Any]) -> list[str]:
    """Return every fail-closed source-freeze violation."""

    failures: list[str] = []
    if set(data) != TOP_LEVEL_KEYS:
        failures.append("top-level fields drift")
    if data.get("schema") != SCHEMA:
        failures.append("schema drift")
    if data.get("stage") != "source-frozen":
        failures.append("M0 stage must remain source-frozen")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("Lean pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0352-preregister-lean-strict-positivity.md"
    ):
        failures.append("decision path drift")
    if data.get("plan") != (
        "docs/plan/lean-strict-positivity-tl2.11-plan-2026-07-22.md"
    ):
        failures.append("plan path drift")

    commands = data.get("commands", {})
    if commands.get("resource_runner_argv") != EXPECTED_RUNNER:
        failures.append("resource runner argv drift")
    if commands.get("lean_argv_template") != EXPECTED_LEAN_ARGV:
        failures.append("Lean argv template drift")
    if set(commands) != {
        "working_directory",
        "resource_runner_argv",
        "lean_argv_template",
    }:
        failures.append("command fields drift")

    sources = data.get("sources", {})
    if tuple(sources) != EXPECTED_SOURCE_ORDER:
        failures.append("source population/order drift")
    for source_id, source in sources.items():
        if set(source) != SOURCE_KEYS:
            failures.append(f"source fields drift: {source_id}")
            continue
        path = ROOT / source["path"]
        if not path.is_file():
            failures.append(f"source missing: {source_id}")
        elif sha256(path) != source["sha256"]:
            failures.append(f"source hash drift: {source_id}")
        outcome = source["expected_official_outcome"]
        diagnostic = source["expected_diagnostic_substring"]
        if outcome not in {"accepted", "rejected"}:
            failures.append(f"source expected outcome invalid: {source_id}")
        if outcome == "accepted" and diagnostic is not None:
            failures.append(f"accepted source carries rejection diagnostic: {source_id}")
        if outcome == "rejected" and diagnostic != (
            "has a non positive occurrence of the datatypes being declared"
        ):
            failures.append(f"negative diagnostic drift: {source_id}")

    cases = data.get("cases", [])
    observed_cases: list[tuple[str, str, str, str, str]] = []
    for index, case in enumerate(cases):
        if set(case) != CASE_KEYS:
            failures.append(f"case fields drift: {index}")
            continue
        observed_cases.append(
            (
                case["id"],
                case["source"],
                case["source_family"],
                case["expected_rule_class"],
                case["expected_official_outcome"],
            )
        )
        source = sources.get(case["source"])
        if source is None:
            failures.append(f"case source missing: {case['id']}")
        elif source["expected_official_outcome"] != case["expected_official_outcome"]:
            failures.append(f"case/source outcome drift: {case['id']}")
    if tuple(observed_cases) != EXPECTED_CASES:
        failures.append("case population/order/expectation drift")
    case_ids = [case.get("id") for case in cases]
    if len(case_ids) != len(set(case_ids)):
        failures.append("case IDs must be unique")

    forbidden = {
        "official_observations",
        "product_observations",
        "kernel_results",
        "importer_results",
        "generated_summary",
    }
    if forbidden.intersection(data):
        failures.append("source freeze contains premature observations")

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_PINS["lean_toolchain"]:
        failures.append("repository lean-toolchain drift")
    return failures


def main() -> int:
    """CLI entry point."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.parse_args()
    failures = validate_manifest(load_manifest())
    if failures:
        for failure in failures:
            print(f"lean strict positivity: {failure}", file=sys.stderr)
        return 1
    print(
        "lean strict positivity source-frozen valid: "
        f"{len(EXPECTED_SOURCE_ORDER)} sources, {len(EXPECTED_CASES)} cases, "
        "no product observations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
