#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-dvd-mul-dependency-audit-plan-v1.json"

def main() -> None:
    plan = json.loads(PLAN.read_text())
    row = plan["predecessor"]
    assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]
    assert plan["ordered_roots"] == ["Eq.trans", "Nat.mul_assoc", "congrArg"]
    assert plan["budget"] == {"max_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_theorem_submissions": 0, "max_retries": 0}
    assert plan["acceptance"]["proof_terms_types_or_values_may_be_rendered"] is False
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_COPRIME_FACTOR_DVD_MUL_DEPENDENCY_AUDIT_PLAN_OK|roots=3|reads=1|authority=0")

if __name__ == "__main__":
    main()
