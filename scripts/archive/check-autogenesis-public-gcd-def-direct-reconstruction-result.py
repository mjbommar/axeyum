#!/usr/bin/env python3
"""Verify the one-shot direct public gcd equation decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/public-gcd-def-direct-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/public-gcd-def-direct-reconstruction-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_gcd_def_direct.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "a3b075724-public-gcd-def-direct-decline-v1"
)
MANIFEST = PACK / "manifest.json"
RESULT_SHA256 = "fe3c2ffc68d89e64c7a179cb87e5aa1ac534bfe7de0be89566240fb6ae473f90"
PLAN_SHA256 = "c3f5ca6da437966dd53d3ba3e1b8f1bf287affe254db88601fa930cac66a12a6"
SOURCE_SHA256 = "a3b075724bcd132970279726883c91c2d8a7bd930115175315f2baefb885cd41"
MANIFEST_SHA256 = "e53376f7beae3a29cfed9244434a7f4db2d94559a3c39fec27f70b4e68d68be1"


class PublicGcdDefDirectResultError(RuntimeError):
    """The compile evidence, decline, budget, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PublicGcdDefDirectResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise PublicGcdDefDirectResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise PublicGcdDefDirectResultError("measured direct result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-public-gcd-def-direct-reconstruction-result"
        or result.get("state")
        != "direct-reconstruction-declined-both-constructor-branches-opaque"
        or sha256(PLAN) != PLAN_SHA256
        or sha256(SOURCE) != SOURCE_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise PublicGcdDefDirectResultError("result producer or pack changed")
    for name, digest, size in [
        ("source.lean", SOURCE_SHA256, 450),
        (
            "compile.stdout",
            "ab1af9bea46c6d4eb8254919239c93b3e3c4cf10027f4b95ede67231ad5dee7f",
            674,
        ),
        (
            "compile.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
        (
            "compile.exit",
            "4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865",
            2,
        ),
    ]:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise PublicGcdDefDirectResultError(f"{name} changed")
    diagnostics = (PACK / "compile.stdout").read_text()
    if diagnostics.count("not definitionally equal") != 2 or not all(
        marker in diagnostics for marker in ["case zero", "case succ", "Nat.gcd 0 y"]
    ):
        raise PublicGcdDefDirectResultError("constructor diagnostics changed")
    if result.get("outcome") != {
        "source_compiled": False,
        "compile_exit": 1,
        "zero_branch_definitionally_equal": False,
        "successor_branch_definitionally_equal": False,
        "exported": False,
        "kernel_imports": 0,
        "public_gcd_equation_accepted": False,
        "decline_reason": "Nat.gcd is opaque to direct definitional reduction in both constructor branches",
    }:
        raise PublicGcdDefDirectResultError("decline outcome changed")
    if result.get("budget") != {
        "source_compilations": 1,
        "exporter_invocations": 0,
        "importer_runs": 0,
        "retries": 0,
        "new_theorem_submissions": 0,
        "exact_fibonacci_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "public_gcd_equation_credit": 0,
        "balanced_bezout_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PublicGcdDefDirectResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_PUBLIC_GCD_DEF_DIRECT_RESULT_OK|compiled=false|"
            "zero_defeq=false|succ_defeq=false|exports=0|imports=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        PublicGcdDefDirectResultError,
    ) as error:
        print(f"autogenesis-public-gcd-def-direct-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
