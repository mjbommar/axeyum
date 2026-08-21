#!/usr/bin/env python3
"""Verify the sealed official-gcd balanced-Bezout exact-reuse result."""

import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = Path(os.environ.get("AXEYUM_EXACT_REUSE_RESULT", ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-exact-reuse-result-v1.json"))
EXPECTED_DEPS = ["Axeyum.Autogenesis.nat_gcd_zero_left", "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1", "Axeyum.Autogenesis.officialNatGcdSuccClosedV1"]
EXPECTED_AUTHORITY = {"closed_gcd_balanced_bezout_credit": 1, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    result = json.loads(RESULT.read_text())
    require(result["state"] == "official-gcd-balanced-bezout-closed-twice-empty-footprint", "state changed")
    plan_path = ROOT / result["plan"]["path"]
    require(digest(plan_path) == result["plan"]["sha256"], "plan identity changed")
    pack = Path(result["evidence"]["pack"])
    manifest_path = pack / "manifest.json"
    require(digest(manifest_path) == result["evidence"]["manifest_sha256"], "manifest identity changed")
    manifest = json.loads(manifest_path.read_text())
    require(manifest["state"] == result["state"], "manifest state differs")
    require(digest(pack / "run-1.json") == result["evidence"]["run_sha256"], "run 1 identity changed")
    require(digest(pack / "run-2.json") == result["evidence"]["run_sha256"], "runs are not identical")
    require((pack / "run-1.stderr").read_bytes() == b"" and (pack / "run-2.stderr").read_bytes() == b"", "stderr is not empty")
    execution = result["execution"]
    require(execution == {"binary_builds": 1, "complete_invocations": 2, "input_stream_reads": 10, "successful_composition_operations": 6, "successful_specialization_operations": 6, "new_closed_theorem_submissions": 2, "retries": 0, "outputs_byte_identical": True}, "execution budget changed")
    reuse = result["reused_declaration"]
    require(reuse["name"] == "Nat.mod_lt", "reused declaration changed")
    require(reuse["source_declaration_sha256"] == reuse["target_declaration_sha256"], "Nat.mod_lt declaration identities differ")
    require(reuse["source_type_shape_sha256"] == reuse["target_type_shape_sha256"], "Nat.mod_lt type shapes differ")
    require(reuse["compatibility"] == "kernel-type-shape", "Nat.mod_lt compatibility changed")
    theorem = result["theorem"]
    require(theorem["name"] == "Axeyum.Autogenesis.officialGcdBalancedBezoutClosedOfficialKernelV1", "theorem changed")
    require(theorem["axiom_footprint"] == [], "theorem reaches assumptions")
    require(theorem["direct_theorem_dependencies"] == EXPECTED_DEPS, "theorem dependencies changed")
    require(theorem["fresh_reconstructions"] == 2, "fresh reconstruction count changed")
    require(theorem["rendered_material"] == {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}, "proof material was rendered")
    require(result["authority"] == EXPECTED_AUTHORITY, "authority changed")
    require(manifest["theorem"] == {**theorem, "outputs_byte_identical": True}, "manifest theorem differs")
    print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_EXACT_REUSE_RESULT_OK|runs=2|reuse=exact|footprint=0|closed=1")


if __name__ == "__main__":
    main()
