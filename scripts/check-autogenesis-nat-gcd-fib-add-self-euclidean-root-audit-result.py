#!/usr/bin/env python3
"""Verify the retained official Euclidean computation-root audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-euclidean-root-audit-result-v1.json"
EXPECTED_ROOTS = {
    "Nat.div.go.eq_1": {
        "declaration_sha256": "c31f2e764891ad2ce5d2d1e59638636302c236096f8fefd91dfaa9f289155763",
        "axiom_footprint": [],
        "direct_theorem_dependencies": ["Nat.div_rec_fuel_lemma"],
    },
    "Nat.modCore.go.eq_1": {
        "declaration_sha256": "aaf85a61edef7f6416bfccd8d817ca53c88cf7fe3d5b34bfbf166287e485448d",
        "axiom_footprint": [],
        "direct_theorem_dependencies": ["Nat.div_rec_fuel_lemma"],
    },
    "Nat.mod.eq_2": {
        "declaration_sha256": "47a0f25d2575086bb8d8ad687beca4e69ef71644bb6057f55ec052d5c2084610",
        "axiom_footprint": [],
        "direct_theorem_dependencies": [],
    },
}
EXPECTED_COUNTERS = {
    "equation_root_audits": 1,
    "imported_declarations_admitted_per_root_audit": 186,
    "authored_support_theorem_submissions": 0,
    "exact_source_target_submissions": 0,
    "executor_invocations": 0,
    "proof_search_invocations": 0,
    "semantic_theorem_receipts": 0,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}


class ResultError(RuntimeError):
    """The retained audit, roots, or no-credit boundary changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_manifest(manifest: dict[str, Any]) -> None:
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-lean430-div-mod-equation-root-audit"
        or manifest.get("tooling_commit")
        != "62858ff72aee3bb1b99b6679712ed0277efa2b7c"
        or manifest.get("plan", {}).get("sha256")
        != "a0e9099ee41c1e54d408e0ea86d13c28518749971e37e726ba9d6fe7ebfd40e5"
        or manifest.get("lean")
        != {
            "version": "4.30.0",
            "githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        }
        or manifest.get("generation", {}).get("roots") != list(EXPECTED_ROOTS)
        or manifest.get("generation", {}).get("proof_bodies_displayed") is not False
        or manifest.get("stream", {}).get("axioms") != []
        or manifest.get("audit", {}).get("theorems") != EXPECTED_ROOTS
        or manifest.get("authority", {}).get("equation_root_audits") != 1
        or any(
            manifest.get("authority", {}).get(key) != 0
            for key in (
                "authored_support_theorem_submissions",
                "exact_source_target_submissions",
                "executor_invocations",
                "proof_search_invocations",
                "semantic_theorem_receipts",
                "evaluation_credit",
                "ledger_writes",
            )
        )
    ):
        raise ResultError("reference manifest contract changed")

def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-bridge-root-audit-result"
        or result.get("state") != "equation-roots-audited-no-support-submissions"
        or result.get("tooling_commit")
        != "62858ff72aee3bb1b99b6679712ed0277efa2b7c"
        or result.get("roots") != EXPECTED_ROOTS
        or result.get("counters") != EXPECTED_COUNTERS
        or result.get("next_stage") != "joint-div-mod-fuel-invariant-v1"
    ):
        raise ResultError("result contract changed")

    plan = result["plan"]
    if sha256(ROOT / plan["path"]) != plan["sha256"]:
        raise ResultError("frozen plan changed")
    importer = "crates/axeyum-lean-import/examples/lean4export_import.rs"
    completed = subprocess.run(
        ["git", "show", f"{result['tooling_commit']}:{importer}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if (
        completed.returncode
        or hashlib.sha256(completed.stdout).hexdigest()
        != "93eb88ab27abff7498e60cfdbc5208cafc58fdf5da7b9f9c3eb96e3ba70c8963"
    ):
        raise ResultError("historical importer changed")

    archive = result["reference_pack"]
    pack = pathlib.Path(archive["root"])
    manifest_path = pack / archive["manifest"]
    if (
        archive.get("mode") != "0555"
        or stat.S_IMODE(pack.stat().st_mode) != 0o555
        or stat.S_IMODE(manifest_path.stat().st_mode) != 0o444
        or manifest_path.stat().st_size != archive["manifest_bytes"]
        or sha256(manifest_path) != archive["manifest_sha256"]
    ):
        raise ResultError("reference pack changed or is mutable")
    manifest = load(manifest_path)
    validate_manifest(manifest)
    for key in ("stream", "export_stderr"):
        row = manifest[key]
        path = pack / row["path"]
        if (
            row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != row["bytes"]
            or sha256(path) != row["sha256"]
        ):
            raise ResultError(f"{key} changed or is mutable")
    audit = manifest["audit"]
    audit_path = pack / audit["path"]
    if (
        stat.S_IMODE(audit_path.stat().st_mode) != 0o444
        or audit_path.stat().st_size != audit["bytes"]
        or sha256(audit_path) != audit["sha256"]
    ):
        raise ResultError("audit changed or is mutable")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_ROOT_AUDIT_OK|roots=3/3|footprints=empty|"
            "support_submissions=0|target_submissions=0|executions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ResultError) as error:
        print(f"autogenesis-euclidean-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
