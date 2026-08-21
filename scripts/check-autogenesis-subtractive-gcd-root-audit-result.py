#!/usr/bin/env python3
"""Verify the declined seven-root subtractive gcd foundation audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/subtractive-gcd-root-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-root-audit-plan-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "c4c2d52cc52f34d168b8894be33ae0074975e9a86685a4774dce6771514d1471"
PLAN_SHA256 = "451eb0d6206ad22f98babec7ae543e3db565eb42439f83e4600b7cf012136a75"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
MANIFEST_SHA256 = "6b03e14eccbbbdf9dbb76750f0f60ba8c045237ba355eea04f436f66cfd39aa0"
NAMES = [
    "Nat.gcd_one_left",
    "Nat.gcd_one_right",
    "Nat.gcd_self",
    "Nat.gcd_sub_self_left",
    "Nat.gcd_sub_self_right",
    "Nat.gcd_zero_left",
    "Nat.gcd_zero_right",
]


class SubtractiveGcdAuditResultError(RuntimeError):
    """The evidence, decline, dependency frontier, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise SubtractiveGcdAuditResultError("tracked audit result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise SubtractiveGcdAuditResultError("measured subtractive gcd audit changed")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-subtractive-gcd-root-audit-result"
        or result.get("state")
        != "subtractive-gcd-shortcut-declined-all-seven-roots-assumption-bearing"
    ):
        raise SubtractiveGcdAuditResultError("subtractive gcd result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or sha256(TOOL) != TOOL_SHA256:
        raise SubtractiveGcdAuditResultError("plan or producing tool identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise SubtractiveGcdAuditResultError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "proof_bearing_stream": (
            "gcd-roots.ndjson",
            "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b",
            1_152_342,
        ),
        "export_stderr": (
            "export.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
        "audit_result": (
            "audit-result.json",
            "cb7c75eb180d3d8a329e6af01ceac529c108892b187fa5ce8c8cca9192cfeb2e",
            4_142,
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
            raise SubtractiveGcdAuditResultError(f"{key} identity or mode changed")
    if (
        manifest.get("plan")
        != {
            "path": "artifacts/autogenesis/subtractive-gcd-root-audit-plan-v1.json",
            "sha256": PLAN_SHA256,
        }
        or manifest.get("audit_tool")
        != {
            "path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
            "sha256": TOOL_SHA256,
        }
        or manifest.get("authority")
        != {
            "exporter_invocations": 1,
            "importer_runs": 1,
            "proof_bearing_stream_reads": 1,
            "proof_terms_rendered": 0,
            "theorem_types_rendered": 0,
            "theorem_values_rendered": 0,
            "bezout_source_compilations": 0,
            "new_theorem_submissions": 0,
            "exact_target_submissions": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
            "retries": 0,
        }
    ):
        raise SubtractiveGcdAuditResultError("manifest authority changed")

    audit = load(AUDIT)
    if (
        audit.get("kind") != "axeyum-theorem-footprint-batch-audit"
        or audit.get("ordered_roots") != NAMES
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("summary")
        != {
            "all_roots_empty": False,
            "class_counts": {
                "empty-footprint": 0,
                "other-assumption-bearing": 2,
                "propext-bearing": 5,
            },
            "population": 7,
        }
    ):
        raise SubtractiveGcdAuditResultError("batch measurement changed")
    measured_rows = audit["rows"]
    tracked_rows = [
        {key: value for key, value in row.items() if key != "accepted"}
        for row in result["rows"]
    ]
    if measured_rows != tracked_rows or any(row.get("accepted") is not False for row in result["rows"]):
        raise SubtractiveGcdAuditResultError("measured root rows or declines changed")
    dependency_union = sorted(
        {dependency for row in measured_rows for dependency in row["direct_theorem_dependencies"]}
    )
    if result.get("direct_dependency_union") != dependency_union:
        raise SubtractiveGcdAuditResultError("direct dependency union changed")
    if result.get("summary") != {
        "population": 7,
        "class_counts": {
            "empty-footprint": 0,
            "other-assumption-bearing": 2,
            "propext-bearing": 5,
        },
        "all_roots_empty": False,
        "accepted_subtractive_foundation": False,
        "direct_dependency_union_population": 17,
    }:
        raise SubtractiveGcdAuditResultError("decline aggregate changed")
    if result.get("budget") != {
        "exporter_invocations": 1,
        "batch_importer_runs": 1,
        "retries": 0,
        "bezout_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    }:
        raise SubtractiveGcdAuditResultError("audit budget changed")
    if result.get("authority") != {
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise SubtractiveGcdAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_ROOT_AUDIT_RESULT_OK|roots=7|"
            "empty=0|quot=2|quot_propext=5|dependency_union=17|"
            "bezout_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdAuditResultError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
