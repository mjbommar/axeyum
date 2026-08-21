#!/usr/bin/env python3
"""Verify the V5 decline and its exact dependency-audit plan."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v5.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-v5-dependency-audit-plan-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        plan = json.loads(PLAN.read_text())
        source = pathlib.Path(plan["input"]["path"])
        tool = ROOT / plan["measurement"]["tool"]
        if (
            result["state"] != "v5-compiles-reproducibly-but-declines-assumption-bearing-Abel-closure"
            or result["execution"]["observations_byte_identical"] is not True
            or result["conclusion"]["construction_accepted"] is not False
            or "propext" not in result["theorem"]["axiom_footprint"]
            or result["theorem"]["direct_theorem_dependency_count"] != 23
            or plan["state"] != "preregistered-after-v5-footprint-decline-before-single-dependency-read"
            or len(plan["ordered_roots"]) != 23
            or len(set(plan["ordered_roots"])) != 23
            or source.stat().st_size != plan["input"]["bytes"]
            or stat.S_IMODE(source.stat().st_mode) != 0o444
            or sha256(source) != plan["input"]["sha256"]
            or sha256(tool) != plan["measurement"]["tool_sha256"]
            or plan["budget"]["max_importer_runs"] != 1
            or plan["budget"]["max_retries"] != 0
            or plan["authority"]["ledger_writes"] != 0
        ):
            raise RuntimeError("V5 evidence, root set, stream, tool, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_V5_RESULT_AUDIT_PLAN_OK|compiled=1|accepted=0|roots=23|reads=0/1")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-v5-result-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
