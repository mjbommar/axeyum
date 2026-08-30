#!/usr/bin/env python3
"""Verify the pre-elaboration xgcd projection execution decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/xgcd-val-direct-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-direct-reconstruction-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_xgcd_val_direct.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/17cf9888b-xgcd-val-direct-v1"
)
MANIFEST = PACK / "manifest.json"
RESULT_SHA256 = "932b622a69ef4fdc3bbeee5862c7e62d5e9e91d353dbfab52c73b7d40e224914"
PLAN_SHA256 = "561ed56fe4d9529292889e26ac7f95eeb38ab299ade0a149f85186aa9c362e66"
SOURCE_SHA256 = "077e5c6320ac8972ca18edb0b75226faac0b062b726609e9d7a213b7f27d2e62"
MANIFEST_SHA256 = "9192ab6af236f36f68d16f59e1cc4ada80b2f22dae4dc740a945f93f7d0613c6"


class XgcdValDirectResultError(RuntimeError):
    """The diagnostic identity, pre-elaboration conclusion, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValDirectResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise XgcdValDirectResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise XgcdValDirectResultError("measured direct result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-xgcd-val-direct-reconstruction-result"
        or result.get("state")
        != "execution-boundary-decline-before-elaboration-source-outside-package-root"
        or sha256(PLAN) != PLAN_SHA256
        or sha256(SOURCE) != SOURCE_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise XgcdValDirectResultError("result producer or pack changed")
    for name, size, digest in [
        ("AxeyumAutogenesisXgcdVal.lean", 322, SOURCE_SHA256),
        ("compile.stdout", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("compile.stderr", 199, "d62fd91a273c5dbbe8380517c218a36b532944cb4247190915ff35cb0068ecb1"),
    ]:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise XgcdValDirectResultError(f"{name} changed")
    if result.get("outcome") != {
        "source_compiled": False,
        "compile_exit": 1,
        "error_kind": "input-source-outside-mathlib-package-root",
        "theorem_elaborated": False,
        "definitional_equality_tested": False,
        "exported": False,
        "kernel_imports": 0,
        "projection_equation_accepted": False,
        "decline_reason": "Lean rejected the source path before elaboration because it was outside the Mathlib package root",
    }:
        raise XgcdValDirectResultError("pre-elaboration outcome changed")
    if result.get("budget") != {
        "source_compilations": 1,
        "exporter_invocations": 0,
        "importer_runs": 0,
        "proof_bearing_stream_reads": 0,
        "retries": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "projection_equation_credit": 0,
        "extended_gcd_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValDirectResultError("no-credit authority changed")
    if (
        result.get("next_boundary")
        != "Preregister a corrected one-shot execution that copies the identical source under the pinned Mathlib package root, compiles there, exports only on success, and removes only its exact temporary source and build products after sealing evidence."
        or result.get("limitations")
        != "This is an execution-boundary decline, not evidence for or against definitional equality of xgcd, gcdA, and gcdB. Lean never elaborated the theorem body."
    ):
        raise XgcdValDirectResultError("next boundary or limitation changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_DIRECT_RESULT_OK|compile=declined-before-elaboration|"
            "exports=0|imports=0|projection_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValDirectResultError,
    ) as error:
        print(f"autogenesis-xgcd-val-direct-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
