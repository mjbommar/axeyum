#!/usr/bin/env python3
"""Verify the twice-replayed official cancellation result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-exact-reuse-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-exact-reuse-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/d8fae64fe-official-coprime-factor-cancellation-exact-reuse-v1/manifest.json")
PLAN_SHA256 = "80bd45011e0c1beb20f9bc7a8daa5d6941fc03e3740cc9c5c87e71d32df54c47"
MANIFEST_SHA256 = "9047d5d9f43cbdc7e7d14d37b9d2f17a311ab4044124b6867f697ade5f1af396"
OUTPUT_SHA256 = "d09639df8885eff3b70cb3d5ef97fc127c604c5dd220d2f8362afcd58c91cc68"
THEOREM_SHA256 = "4696bda19c2353f795c95d700cc63c456d0fe750bfdf519c4646c76a1efdb147"
DEPENDENCIES = ["Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1", "Axeyum.Autogenesis.coprimeFactorDivisibilityCancellationResidualV2", "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1", "Axeyum.Autogenesis.officialGcdBalancedBezoutClosedOfficialKernelV1"]
EXECUTION = {"binary_builds": 1, "complete_invocations": 2, "input_stream_reads": 16, "successful_composition_operations": 12, "successful_specialization_operations": 10, "final_theorem_submissions": 2, "retries": 0, "outputs_byte_identical": True}
AUTHORITY = {"official_cancellation_credit": 1, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialCancellationExactReuseResultError(RuntimeError):
    """The accepted theorem, replay evidence, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialCancellationExactReuseResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-coprime-factor-cancellation-exact-reuse-result", "official-coprime-factor-cancellation-closed-twice-empty-footprint"):
        raise OfficialCancellationExactReuseResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result["plan"]["sha256"] != PLAN_SHA256:
        raise OfficialCancellationExactReuseResultError("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or result["evidence_pack"]["sha256"] != MANIFEST_SHA256:
        raise OfficialCancellationExactReuseResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialCancellationExactReuseResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    manifest_execution = {"binary_builds": manifest["implementation"]["binary_builds"], **manifest["execution"]}
    if result.get("execution") != EXECUTION or manifest_execution != EXECUTION:
        raise OfficialCancellationExactReuseResultError("execution changed")
    run1 = MANIFEST.parent / "run-1.json"
    run2 = MANIFEST.parent / "run-2.json"
    if sha256(run1) != OUTPUT_SHA256 or sha256(run2) != OUTPUT_SHA256 or run1.read_bytes() != run2.read_bytes():
        raise OfficialCancellationExactReuseResultError("replay output changed")
    if (MANIFEST.parent / "run-1.stderr").read_bytes() or (MANIFEST.parent / "run-2.stderr").read_bytes():
        raise OfficialCancellationExactReuseResultError("execution wrote stderr")
    audit = load(run1)
    theorem = audit["specializations"]["official_coprime_factor_cancellation"]["evidence"]
    if theorem.get("name") != "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1" or theorem.get("declaration_sha256") != THEOREM_SHA256 or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES:
        raise OfficialCancellationExactReuseResultError("final theorem evidence changed")
    if result["theorem"]["declaration_sha256"] != THEOREM_SHA256 or result["theorem"]["axiom_footprint"] != [] or result["theorem"]["direct_theorem_dependencies"] != DEPENDENCIES:
        raise OfficialCancellationExactReuseResultError("tracked theorem changed")
    for name, receipt in result["reused_declarations"].items():
        observed = audit["reused_declarations"].get(name)
        if observed != receipt or receipt["source_declaration_sha256"] != receipt["target_declaration_sha256"] or receipt["source_type_shape_sha256"] != receipt["target_type_shape_sha256"] or receipt["compatibility"] != "kernel-type-shape":
            raise OfficialCancellationExactReuseResultError(f"exact reuse changed: {name}")
    if audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise OfficialCancellationExactReuseResultError("proof material was rendered")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialCancellationExactReuseResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_EXACT_REUSE_RESULT_OK|runs=2|reused=2|footprint=0|credit=1|fibonacci=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialCancellationExactReuseResultError) as error:
        print(f"autogenesis-official-cancellation-exact-reuse-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
