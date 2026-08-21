#!/usr/bin/env python3
"""Verify the generated-carrier result of the gcd route-frontier audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-plan-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-route-frontier-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1/gcd-roots.ndjson"
)
RESULT_SHA256 = "bb53a104cfe76b46d3fed31b521682c6721389fd98c8812d3f1855cb71dabe3b"
PLAN_SHA256 = "edd310e9ffa037394e2d7287c1705576b43d3dd960f8bc5691e9f64efb97639a"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
MANIFEST_SHA256 = "cd13ae221f70309ec586a1ace4f664b72404fb957325949b2d8d2f1a747b60b2"
STREAM_SHA256 = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b"
GENERATED = "_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def"


class SubtractiveGcdRouteFrontierAuditResultError(RuntimeError):
    """The measurement, generated carrier, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdRouteFrontierAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise SubtractiveGcdRouteFrontierAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise SubtractiveGcdRouteFrontierAuditResultError("measured route audit changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-subtractive-gcd-route-frontier-audit-result"
        or result.get("state")
        != "six-route-roots-declined-generated-gcd-recursor-carrier-exposed"
        or sha256(PLAN) != PLAN_SHA256
        or sha256(TOOL) != TOOL_SHA256
    ):
        raise SubtractiveGcdRouteFrontierAuditResultError("result or producer changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 1_152_342
        or sha256(STREAM) != STREAM_SHA256
    ):
        raise SubtractiveGcdRouteFrontierAuditResultError("sealed evidence changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "audit_result": (
            "audit-result.json",
            "6a95a73f3e6fd6ae99f480d8cfb7307cfa3c6141a39e71bc7d7895e14aeae92a",
            3_573,
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
            raise SubtractiveGcdRouteFrontierAuditResultError(f"{key} changed")
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
        raise SubtractiveGcdRouteFrontierAuditResultError("manifest authority changed")
    audit = load(AUDIT)
    if (
        audit.get("rows") != result.get("rows")
        or audit.get("ordered_roots") != [row["name"] for row in result["rows"]]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("summary")
        != {
            "all_roots_empty": False,
            "class_counts": {
                "empty-footprint": 0,
                "other-assumption-bearing": 1,
                "propext-bearing": 5,
            },
            "population": 6,
        }
    ):
        raise SubtractiveGcdRouteFrontierAuditResultError("batch measurement changed")
    private = next(
        row for row in result["rows"] if row["name"].endswith("Nat.gcd.eq_def")
    )
    expected_footprint = ["Quot", "Quot.lift", "Quot.mk", "Quot.sound"]
    if (
        private["axiom_footprint"] != expected_footprint
        or private["direct_theorem_dependencies"] != [GENERATED]
        or result.get("generated_gcd_carrier")
        != {
            "name": GENERATED,
            "inherited_axiom_footprint": expected_footprint,
            "direct_dependency_audit_pending": True,
        }
    ):
        raise SubtractiveGcdRouteFrontierAuditResultError("generated gcd carrier changed")
    if result.get("summary") != {
        "population": 6,
        "class_counts": {
            "empty-footprint": 0,
            "other-assumption-bearing": 1,
            "propext-bearing": 5,
        },
        "all_roots_empty": False,
        "clean_computational_base_found": False,
        "replacement_authorized": False,
    }:
        raise SubtractiveGcdRouteFrontierAuditResultError("decline aggregate changed")
    if result.get("budget") != {
        "exporter_invocations": 0,
        "batch_importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "retries": 0,
        "replacement_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise SubtractiveGcdRouteFrontierAuditResultError("no-replacement authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_ROUTE_FRONTIER_AUDIT_RESULT_OK|"
            "roots=6|empty=0|generated_carrier=1|replacements=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        StopIteration,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdRouteFrontierAuditResultError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-route-frontier-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
