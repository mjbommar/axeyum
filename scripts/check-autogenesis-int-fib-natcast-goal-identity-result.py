#!/usr/bin/env python3
"""Verify the one-read, non-rendering Int.fib_natCast identity result."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-goal-identity-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-goal-identity-result-v1.json"
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-fib-clean-definition-construction-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_goal_identity_audit.rs"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        construction = json.loads(CONSTRUCTION.read_text())
        theorem = result["theorem"]
        source = pathlib.Path(result["input"]["path"])
        if (
            result["state"] != "single-read-hash-only-identity-qualified"
            or sha256(PLAN) != result["plan_sha256"]
            or sha256(TOOL) != result["tool"]["sha256"]
            or source.stat().st_size != result["input"]["bytes"]
            or stat.S_IMODE(source.stat().st_mode) != 0o444
            or sha256(source) != result["input"]["sha256"]
            or theorem["name"] != construction["theorem"]["name"]
            or theorem["canonical_declaration_sha256"]
            != construction["theorem"]["declaration_sha256"]
            or len(theorem["canonical_type_sha256"]) != 64
            or theorem["axiom_footprint"] != []
            or theorem["direct_theorem_dependencies"] != []
            or result["execution"] != {
                "importer_runs": 1,
                "proof_bearing_stream_reads": 1,
                "retries": 0,
                "theorem_submissions": 0,
                "rendered_proof_terms": 0,
                "rendered_theorem_types": 0,
                "rendered_theorem_values": 0,
            }
            or result["authority"]["fact_admission_authorized"] is not False
            or result["authority"]["ledger_writes"] != 0
        ):
            raise RuntimeError("plan, tool, stream, theorem identity, or authority changed")
        int(theorem["canonical_type_sha256"], 16)
        print("AUTOGENESIS_INT_FIB_NATCAST_GOAL_IDENTITY_RESULT_OK|reads=1|type_hash=bound|footprint=0|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-goal-identity-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
