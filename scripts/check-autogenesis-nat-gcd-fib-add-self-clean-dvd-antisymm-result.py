#!/usr/bin/env python3
"""Verify the retained cross-kernel clean-antisymmetry decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/53242139f-clean-dvd-antisymm-v1/manifest.json")
PLAN_SHA256 = "b966022098c76324dae1736ff01bcfe9b9dd3cdcee80342354de502f827e6c72"
MANIFEST_SHA256 = "5a99581d6a321f9f9c0951b1fa68e2946b75f953c1d68493e600ea567d8b1567"
EXECUTION = {"binary_builds": 1, "complete_invocations": 1, "input_stream_reads": 2, "successful_composition_operations_before_decline": 2, "clean_le_of_dvd_private_submissions": 1, "clean_dvd_antisymm_rejected_submissions": 1, "published_support_theorems": 0, "exact_target_submissions": 0, "retries": 0, "second_invocation_skipped": True}
DECLINE = {"operation": "declare clean divisibility antisymmetry in the imported r091 kernel using NatPrelude handles created in a distinct native kernel", "class": "UnknownConst", "diagnostic": "UnknownConst { name: NameId(4) }", "interpretation": "kernel-local numeric identities cannot be transported as a NatPrelude value across independently built environments", "partial_kernel_published": False}
AUTHORITY = {"support_credit": 0, "exact_target_submissions": 0, "target_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class CleanDvdAntisymmResultError(RuntimeError):
    """The decline, evidence, or zero-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CleanDvdAntisymmResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-result", "first-invocation-declined-at-cross-kernel-native-prelude-handle-no-retry"):
        raise CleanDvdAntisymmResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result["plan"]["sha256"] != PLAN_SHA256:
        raise CleanDvdAntisymmResultError("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or result["evidence_pack"]["sha256"] != MANIFEST_SHA256:
        raise CleanDvdAntisymmResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise CleanDvdAntisymmResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    manifest_execution = {"binary_builds": manifest["implementation"]["binary_builds"], **manifest["execution"]}
    if result.get("execution") != EXECUTION or manifest_execution != EXECUTION:
        raise CleanDvdAntisymmResultError("execution changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise CleanDvdAntisymmResultError("decline changed")
    if (MANIFEST.parent / "run-1.json").read_bytes() or (MANIFEST.parent / "run-1.stderr").read_text() != "clean-dvd-antisymm: clean divisibility antisymmetry rejected: UnknownConst { name: NameId(4) }\n":
        raise CleanDvdAntisymmResultError("failed-run output changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise CleanDvdAntisymmResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_CLEAN_DVD_ANTISYMM_RESULT_OK|runs=1|decline=UnknownConst|published=0|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CleanDvdAntisymmResultError) as error:
        print(f"autogenesis-clean-dvd-antisymm-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
