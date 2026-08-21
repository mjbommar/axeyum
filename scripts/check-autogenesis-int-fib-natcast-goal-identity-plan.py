#!/usr/bin/env python3
"""Verify the preregistered hash-only Int.fib_natCast identity audit."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-goal-identity-plan-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-natcast-d5886be4.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_goal_identity_audit.rs"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        fact = json.loads(FACT.read_text())
        source = pathlib.Path(plan["input"]["path"])
        if (
            plan["state"] != "preregistered-before-hash-only-tool-and-single-sealed-stream-read"
            or fact["id"] != plan["target"]["fact_id"]
            or fact["epistemic_status"] != "open"
            or plan["target"]["theorem"] != "Int.fib_natCast"
            or TOOL.exists() != plan["measurement"]["tool_present_at_plan_commit"]
            or source.stat().st_size != plan["input"]["bytes"]
            or stat.S_IMODE(source.stat().st_mode) != 0o444
            or sha256(source) != plan["input"]["sha256"]
            or plan["budget"] != {
                "max_importer_runs": 1,
                "max_proof_bearing_stream_reads": 1,
                "max_retries": 0,
                "max_theorem_submissions": 0,
                "max_ledger_writes": 0,
            }
            or plan["authority"]["fact_admission_authorized"] is not False
            or plan["authority"]["ledger_writes"] != 0
        ):
            raise RuntimeError("fact, stream, tool state, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_NATCAST_GOAL_IDENTITY_PLAN_OK|reads=0/1|rendered=0|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-goal-identity-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
