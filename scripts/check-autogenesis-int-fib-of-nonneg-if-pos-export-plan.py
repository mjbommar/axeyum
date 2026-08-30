#!/usr/bin/env python3
"""Validate the bounded pinned if_pos export plan."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-nonneg-if-pos-export-plan-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        predecessor = plan["predecessor"]
        target = plan["target"]
        environment = plan["fixed_environment"]
        execution = plan["execution"]
        fact = ROOT / target["fact_path"]
        assert plan["state"] == "preregistered-before-pinned-core-root-export-or-proof-stream-read"
        assert sha256(ROOT / predecessor["path"]) == predecessor["sha256"]
        assert target["fact_id"] == "F:ml430-int-fib-of-nonneg-438018c5"
        assert sha256(fact) == target["fact_sha256"]
        assert json.loads(fact.read_text())["epistemic_status"] == "open"
        assert environment["hostname"] == "server5"
        assert environment["mathlib_commit"] == "c5ea00351c28e24afc9f0f84379aa41082b1188f"
        assert environment["lean_version"] == "4.30.0"
        assert environment["lean4export_binary_sha256"] == "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
        assert plan["support"] == {
            "module": "Init.Prelude",
            "root": "if_pos",
            "role": "rewrite only the already-selected nonnegative branch of transparent Int.fib",
            "target_proof_body_allowed": False,
        }
        assert plan["command"]["output_must_not_preexist"] is True
        assert execution["max_exporter_invocations"] == execution["max_root_stream_writes"] == 1
        assert execution["max_importer_runs"] == 2
        assert execution["max_retries"] == 0
        assert execution["rendered_proof_terms"] == execution["rendered_theorem_types"] == execution["rendered_theorem_values"] == 0
        assert execution["target_theorem_submissions"] == execution["ledger_writes"] == 0
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-of-nonneg-if-pos-export-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-of-nonneg-if-pos-export-plan: PASS: exporters=0/1|imports=0/2|targets=0|writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
