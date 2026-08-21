#!/usr/bin/env python3
"""Verify the one-shot direct xgcd projection reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-direct-reconstruction-plan-v1.json"
FRONTIER = ROOT / "artifacts/autogenesis/extended-gcd-novel-dependency-audit-result-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_xgcd_val_direct.lean"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
FRONTIER_SHA256 = "15ae23fb0107b76e59905eb2c58f8988db45a406f1e8cc178fb24ec704fa1cb9"
SOURCE_SHA256 = "077e5c6320ac8972ca18edb0b75226faac0b062b726609e9d7a213b7f27d2e62"
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"


class XgcdValDirectPlanError(RuntimeError):
    """The target, direct method, budget, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValDirectPlanError(f"{path} is not an object")
    return value


def inventory_target() -> dict[str, Any]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise XgcdValDirectPlanError("statement inventory changed")
    with INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            if row.get("name") == "Nat.xgcd_val":
                return {
                    "module": row["module"],
                    "name": row["name"],
                    "source_row_sha256": hashlib.sha256(
                        json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
                    ).hexdigest(),
                    "type": row["type"],
                    "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
                    "type_repr_sha256": hashlib.sha256(
                        row["type_repr"].encode()
                    ).hexdigest(),
                    "authored_name": "Axeyum.Autogenesis.xgcdValDirect",
                }
    raise XgcdValDirectPlanError("Nat.xgcd_val is absent")


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("kind") != "axeyum-autogenesis-xgcd-val-direct-reconstruction-plan"
        or plan.get("state")
        != "preregistered-before-one-source-compilation-no-projection-credit"
        or plan.get("policy_version") != "xgcd-val-direct-reconstruction-v1"
    ):
        raise XgcdValDirectPlanError("plan identity changed")
    if (
        sha256(FRONTIER) != FRONTIER_SHA256
        or sha256(SOURCE) != SOURCE_SHA256
        or plan.get("target") != inventory_target()
    ):
        raise XgcdValDirectPlanError("frontier, source, or target identity changed")
    if plan.get("inputs") != {
        "frontier_result": {
            "path": "artifacts/autogenesis/extended-gcd-novel-dependency-audit-result-v1.json",
            "sha256": FRONTIER_SHA256,
        },
        "statement_inventory": {
            "path": str(INVENTORY),
            "sha256": INVENTORY_SHA256,
            "mode": "0444",
        },
    }:
        raise XgcdValDirectPlanError("plan inputs changed")
    if plan.get("fixed_environment") != {
        "ssh_alias": "s5",
        "hostname": "server5",
        "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449",
    }:
        raise XgcdValDirectPlanError("fixed environment changed")
    if plan.get("construction") != {
        "source_path": "scripts/lean/autogenesis_xgcd_val_direct.lean",
        "source_sha256": SOURCE_SHA256,
        "module_name": "AxeyumAutogenesisXgcdVal",
        "evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/17cf9888b-xgcd-val-direct-v1",
        "method": "definitional equality only",
        "proof_search_allowed": False,
        "upstream_proof_bodies_read": False,
        "forbidden_dependencies": [
            "Nat.xgcd_val",
            "Nat.xgcd.eq_1",
            "propext",
            "Quot",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
        ],
        "forbidden_tactics": ["aesop", "simp", "simpa", "omega", "native_decide"],
    }:
        raise XgcdValDirectPlanError("construction changed")
    if plan.get("acceptance") != {
        "source_must_compile": True,
        "exported_type_must_match_target": True,
        "fresh_kernel_imports_required": 2,
        "axiom_footprint_must_be_empty": True,
        "forbidden_dependencies_must_be_absent": True,
        "failed_compilation_ends_increment": True,
    }:
        raise XgcdValDirectPlanError("acceptance changed")
    if plan.get("budget") != {
        "max_source_compilations": 1,
        "max_exporter_invocations": 1,
        "max_importer_runs": 2,
        "max_proof_bearing_stream_reads": 2,
        "max_retries": 0,
        "max_new_theorem_submissions": 2,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise XgcdValDirectPlanError("budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "proof_search_allowed": False,
        "projection_equation_credit": 0,
        "extended_gcd_reconstruction_allowed": False,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValDirectPlanError("authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/xgcd-val-direct-reconstruction-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-xgcd-val-direct-reconstruction-plan.py"
        or plan.get("limitations")
        != "The one-shot probe tests only whether the public xgcd/gcdA/gcdB projection equation follows by definitional equality. Success does not prove the extended-gcd coefficient identity; failure requires target-owned coefficient definitions."
    ):
        raise XgcdValDirectPlanError("output boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_DIRECT_PLAN_OK|compilations=0/1|exports=0/1|"
            "imports=0/2|projection_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValDirectPlanError,
    ) as error:
        print(f"autogenesis-xgcd-val-direct-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
