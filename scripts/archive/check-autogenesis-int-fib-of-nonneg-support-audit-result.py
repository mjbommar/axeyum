#!/usr/bin/env python3
"""Validate the declined Int.fib_of_nonneg support audit."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-nonneg-support-audit-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        plan = result["plan"]
        input_ = result["input"]
        execution = result["execution"]
        fact = ROOT / "artifacts/facts/F-ml430-int-fib-of-nonneg-438018c5.json"
        assert result["state"] == "declined-candidate-support-absent-from-clean-definition-capsule"
        assert sha256(ROOT / plan["path"]) == plan["sha256"]
        assert sha256(ROOT / result["tool"]["path"]) == result["tool"]["sha256"]
        assert sha256(pathlib.Path(input_["path"])) == input_["sha256"]
        assert result["candidate_support"] == {
            "name": "if_pos",
            "verdict": "absent",
            "diagnostic": "requested theorem is absent: if_pos",
        }
        assert execution == {
            "complete_invocations": 1,
            "importer_runs": 1,
            "stream_reads": 1,
            "exit_status": 1,
            "retries": 0,
            "target_theorem_submissions": 0,
            "exports": 0,
            "ledger_writes": 0,
        }
        assert result["rendered_material"] == {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        assert result["authority"] == {"theorem_credit": 0, "fact_status_changes": 0, "ledger_writes": 0}
        assert sha256(fact) == "312711e8dc1d54a17b9efdad9c61ab46ca9ef77747acc80a0c24d5f6821d6d6e"
        assert json.loads(fact.read_text())["epistemic_status"] == "open"
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-of-nonneg-support-audit-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-of-nonneg-support-audit-result: PASS: absent=if_pos|targets=0|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
