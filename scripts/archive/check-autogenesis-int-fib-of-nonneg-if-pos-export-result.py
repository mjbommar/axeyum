#!/usr/bin/env python3
"""Validate rejection of the zero-exit metadata-only if_pos export."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-nonneg-if-pos-export-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        plan = result["plan"]
        output = result["output"]
        execution = result["execution"]
        stream = pathlib.Path(output["path"])
        assert result["state"] == "rejected-exporter-zero-exit-panic-root-absent"
        assert sha256(ROOT / plan["path"]) == plan["sha256"]
        assert result["attempt"]["exporter_exit_status"] == 0
        assert "Constant if_pos not found" in result["attempt"]["stderr_diagnostic"]
        assert sha256(stream) == output["sha256"]
        assert stream.stat().st_size == output["bytes"] == 173
        assert output["records"] == "metadata-only"
        assert output["root_present"] is False
        assert result["verification"] == {
            "importer_runs": 2,
            "identical_diagnostic": "requested theorem is absent: if_pos",
            "accepted_roots": 0,
            "axiom_footprint": None,
        }
        assert execution == {
            "exporter_invocations": 1,
            "root_stream_writes": 1,
            "importer_runs": 2,
            "retries": 0,
            "target_theorem_submissions": 0,
            "ledger_writes": 0,
        }
        assert result["authority"] == {"support_credit": 0, "theorem_credit": 0, "fact_status_changes": 0, "ledger_writes": 0}
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-of-nonneg-if-pos-export-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-of-nonneg-if-pos-export-result: PASS: zero_exit_rejected=1|roots=0|writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
