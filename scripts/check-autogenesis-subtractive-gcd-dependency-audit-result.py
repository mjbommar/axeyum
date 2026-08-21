#!/usr/bin/env python3
"""Verify the measured subtractive gcd dependency split and route pruning."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-dependency-audit-plan-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-dependency-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
PARENT_PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1"
)
PARENT_MANIFEST = PARENT_PACK / "manifest.json"
STREAM = PARENT_PACK / "gcd-roots.ndjson"
RESULT_SHA256 = "384066c42b6fc1599c869a15ca5da21716cdb508113bc8855763072b95e33092"
PLAN_SHA256 = "a5c9c20c1d2d5f8eb9399b8d22bd7f955bb43edb3ad4111f0c6db15049613fe1"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
MANIFEST_SHA256 = "f93cd95d1126efbcc028b57e051441ced525d2ef4a321b6e352ce099f2fc6b4c"
PARENT_MANIFEST_SHA256 = "6b03e14eccbbbdf9dbb76750f0f60ba8c045237ba355eea04f436f66cfd39aa0"
STREAM_SHA256 = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b"
RELEVANT = [
    "Nat.gcd_comm",
    "Nat.gcd_sub_mul_right_left",
    "Nat.gcd_sub_mul_right_right",
    "_private.Init.Data.Nat.Gcd.0.Nat.gcd.eq_1",
]


class SubtractiveGcdDependencyAuditResultError(RuntimeError):
    """The measurement, route pruning, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise SubtractiveGcdDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise SubtractiveGcdDependencyAuditResultError("measured dependency audit changed")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-subtractive-gcd-dependency-audit-result"
        or result.get("state")
        != "fourteen-direct-dependencies-classified-seven-clean-seven-assumption-bearing"
    ):
        raise SubtractiveGcdDependencyAuditResultError("dependency result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or sha256(TOOL) != TOOL_SHA256:
        raise SubtractiveGcdDependencyAuditResultError("plan or producing tool changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(PARENT_PACK.stat().st_mode) != 0o555
        or sha256(PARENT_MANIFEST) != PARENT_MANIFEST_SHA256
        or stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 1_152_342
        or sha256(STREAM) != STREAM_SHA256
    ):
        raise SubtractiveGcdDependencyAuditResultError("sealed evidence changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "audit_result": (
            "audit-result.json",
            "37ebf592a576ca9a1a4151317313ef8ae27967ff0efb6c255a0eff0637961190",
            5_856,
        ),
        "audit_stderr": (
            "audit.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
    }.items():
        row = manifest[key]
        path = PACK / row["path"]
        if (
            row.get("path") != expected[0]
            or row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise SubtractiveGcdDependencyAuditResultError(f"{key} changed")
    if manifest.get("authority") != {
        "exporter_invocations": 0,
        "importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "replacement_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
        "retries": 0,
    }:
        raise SubtractiveGcdDependencyAuditResultError("manifest authority changed")

    audit = load(AUDIT)
    if (
        audit.get("kind") != "axeyum-theorem-footprint-batch-audit"
        or audit.get("ordered_roots") != [row["name"] for row in result["rows"]]
        or audit.get("rows") != result["rows"]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("summary")
        != {
            "all_roots_empty": False,
            "class_counts": {
                "empty-footprint": 7,
                "other-assumption-bearing": 2,
                "propext-bearing": 5,
            },
            "population": 14,
        }
    ):
        raise SubtractiveGcdDependencyAuditResultError("batch measurement changed")
    if result.get("summary") != {
        "population": 14,
        "class_counts": {
            "empty-footprint": 7,
            "other-assumption-bearing": 2,
            "propext-bearing": 5,
        },
        "all_roots_empty": False,
        "replacement_authorized": False,
    }:
        raise SubtractiveGcdDependencyAuditResultError("measurement aggregate changed")
    rows = {row["name"]: row for row in result["rows"]}
    if result.get("route_relevant_assumption_carriers") != RELEVANT or any(
        rows[name]["class"] == "empty-footprint" for name in RELEVANT
    ):
        raise SubtractiveGcdDependencyAuditResultError("route carrier selection changed")
    frontier = sorted(
        {
            dependency
            for name in RELEVANT
            for dependency in rows[name]["direct_theorem_dependencies"]
            if dependency not in rows
        }
    )
    if result.get("route_relevant_novel_dependency_frontier") != frontier or len(frontier) != 7:
        raise SubtractiveGcdDependencyAuditResultError("route frontier changed")
    if result.get("budget") != {
        "exporter_invocations": 0,
        "batch_importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "retries": 0,
        "replacement_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    }:
        raise SubtractiveGcdDependencyAuditResultError("audit budget changed")
    if result.get("authority") != {
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise SubtractiveGcdDependencyAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_DEPENDENCY_AUDIT_RESULT_OK|"
            "roots=14|empty=7|assumption_bearing=7|route_carriers=4|"
            "novel_frontier=7|replacements=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdDependencyAuditResultError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
