#!/usr/bin/env python3
"""Check the exact cancellation dependency audit preregistration."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-dependency-audit-plan-v1.json"


def main() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    assert hashlib.sha256((ROOT / predecessor["path"]).read_bytes()).hexdigest() == predecessor["sha256"]
    assert plan["state"] == "preregistered-exact-seventeen-root-audit-before-sealed-stream-reread"
    assert len(plan["ordered_roots"]) == 17 and len(set(plan["ordered_roots"])) == 17
    assert plan["budget"] == {"max_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_theorem_submissions": 0, "max_retries": 0}
    assert plan["tool"]["proof_terms_types_or_values_may_be_rendered"] is False
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_DEPENDENCY_AUDIT_PLAN_OK|roots=17|reads=1|authority=0")


if __name__ == "__main__":
    main()
