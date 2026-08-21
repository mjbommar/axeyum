#!/usr/bin/env python3
"""Verify the absent-aware Int.fib blocker partition plan."""

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-definition-blocker-partition-plan-v2.json"
PRIOR = ROOT / "artifacts/autogenesis/mathlib-int-fib-definition-blocker-path-audit-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/declaration_blocker_path_batch_audit.rs"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        prior = json.loads(PRIOR.read_text())
        source = pathlib.Path(plan["input"]["path"])
        if prior["state"] != plan["prior_result"]["required_state"] or plan["root"] != "Int.fib" or len(plan["ordered_blockers"]) != 9 or sha256(TOOL) != plan["measurement"]["tool_sha256"] or source.stat().st_size != plan["input"]["bytes"] or stat.S_IMODE(source.stat().st_mode) != 0o444 or sha256(source) != plan["input"]["sha256"] or plan["budget"] != {"max_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_theorem_submissions": 0, "max_ledger_writes": 0} or plan["authority"]["definition_bodies_readable_by_model"] is not False or plan["authority"]["ledger_writes"] != 0:
            raise RuntimeError("prior failure, root, tool, evidence, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_DEFINITION_BLOCKER_PARTITION_PLAN_OK|blockers=9|imports=0/1|rendered=0|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-definition-blocker-partition-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
