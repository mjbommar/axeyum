#!/usr/bin/env python3
"""Fail closed over the sealed four-capsule Fibonacci/GCD support pack."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-portable-support-capsules-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-portable-support-capsules-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/9b21389e9-nat-gcd-fib-add-self-portable-support-capsules-v1")
MANIFEST = PACK / "manifest.json"
PLAN_SHA256 = "f22c37554374c2e6caa8ebf2cf084be2fd355b78b7d274687f78c948da31ef4a"
MANIFEST_SHA256 = "92fcd7e46f2204569728ef89ecf1c9c41a78c606d48d16fcdd5e9c301fe65926"
PREFIXES = {
    "clean_order": "clean-order",
    "official_cancellation": "official-cancellation",
    "fibonacci_addition": "fibonacci-addition",
    "fibonacci_coprimality": "fibonacci-coprimality",
}
AUTHORITY = {
    "capsule_credit": 0,
    "exact_target_submissions": 0,
    "target_credit": 0,
    "fact_status_changes": 0,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}


class PortableCapsuleResultError(RuntimeError):
    """The sealed proof-capsule evidence or its authority boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PortableCapsuleResultError(f"{path} is not an object")
    return value


def portable_capsule(value: Any) -> dict[str, Any]:
    if isinstance(value, dict):
        candidate = value.get("portable_capsule")
        if isinstance(candidate, dict):
            return candidate
        for child in value.values():
            try:
                return portable_capsule(child)
            except PortableCapsuleResultError:
                pass
    elif isinstance(value, list):
        for child in value:
            try:
                return portable_capsule(child)
            except PortableCapsuleResultError:
                pass
    raise PortableCapsuleResultError("run evidence has no portable capsule")


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    identity = (result.get("schema_version"), result.get("kind"), result.get("state"))
    expected_identity = (
        1,
        "axeyum-autogenesis-nat-gcd-fib-add-self-portable-support-capsules-result",
        "four-portable-support-capsules-accepted-empty-footprint-and-sealed",
    )
    if identity != expected_identity:
        raise PortableCapsuleResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result["plan"]["sha256"] != PLAN_SHA256:
        raise PortableCapsuleResultError("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or result["evidence_pack"]["manifest_sha256"] != MANIFEST_SHA256:
        raise PortableCapsuleResultError("manifest identity changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555:
        raise PortableCapsuleResultError("evidence pack directory is not sealed")
    if any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir() if path.is_file()):
        raise PortableCapsuleResultError("an evidence pack file is not sealed")

    manifest = load(MANIFEST)
    if result.get("capsules") != {
        name: {key: row[key] for key in ("root", "declaration_sha256", "capsule_sha256", "bytes")}
        for name, row in manifest["capsules"].items()
    }:
        raise PortableCapsuleResultError("result and manifest capsule identities differ")
    if set(result["capsules"]) != set(PREFIXES):
        raise PortableCapsuleResultError("capsule family set changed")

    for name, prefix in PREFIXES.items():
        expected = result["capsules"][name]
        first = PACK / f"{prefix}-1.ndjson"
        second = PACK / f"{prefix}-2.ndjson"
        run_first = PACK / f"{prefix}-run-1.json"
        run_second = PACK / f"{prefix}-run-2.json"
        if first.read_bytes() != second.read_bytes():
            raise PortableCapsuleResultError(f"{name} repeated exports differ")
        if sha256(first) != expected["capsule_sha256"] or first.stat().st_size != expected["bytes"]:
            raise PortableCapsuleResultError(f"{name} capsule identity changed")
        if run_first.read_bytes() != run_second.read_bytes():
            raise PortableCapsuleResultError(f"{name} repeated run evidence differs")
        if sha256(run_first) != manifest["capsules"][name]["run_json_sha256"]:
            raise PortableCapsuleResultError(f"{name} run evidence identity changed")
        evidence = portable_capsule(load(run_first))
        theorem = evidence["theorem"]
        if (
            evidence["root"] != expected["root"]
            or evidence["sha256"] != expected["capsule_sha256"]
            or evidence["bytes"] != expected["bytes"]
            or evidence["fresh_imports"] != 2
            or theorem["name"] != expected["root"]
            or theorem["declaration_sha256"] != expected["declaration_sha256"]
            or theorem["axiom_footprint"] != []
            or evidence["rendered_material"] != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        ):
            raise PortableCapsuleResultError(f"{name} checked theorem evidence changed")
        for suffix in ("run-1.stderr", "run-2.stderr"):
            if (PACK / f"{prefix}-{suffix}").read_bytes():
                raise PortableCapsuleResultError(f"{name} stderr is nonempty")

    verification = result["verification"]
    if (
        verification["fresh_exports"] != 8
        or verification["raw_fresh_import_invocations"] != 16
        or verification["budgeted_distinct_capsule_imports"] != 8
        or verification["all_axiom_footprints"] != []
        or not verification["all_repeated_exports_byte_identical"]
        or not verification["all_declaration_identities_match"]
    ):
        raise PortableCapsuleResultError("verification totals changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise PortableCapsuleResultError("zero-authority boundary changed")
    if result["budget_accounting"]["exact_target_submissions"] != 0 or result["budget_accounting"]["retries"] != 0:
        raise PortableCapsuleResultError("target submission or retry was credited")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_PORTABLE_SUPPORT_CAPSULES_OK|roots=4|exports=8|imports=16|axioms=0|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PortableCapsuleResultError) as error:
        print(f"autogenesis-portable-support-capsules-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
