#!/usr/bin/env python3
"""Fail closed over the V5 dependent-induction repair plan."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v5.json"
PREDECESSOR = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v4.json"

def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()

def check() -> None:
    plan = json.loads(PLAN.read_text())
    assert plan["state"] == "preregistered-branch-specialized-dependent-induction-before-code-or-stream-access"
    assert plan["predecessor"]["sha256"] == sha256(PREDECESSOR)
    construction = plan["construction"]
    assert "bind both hypotheses separately inside each a branch" in construction["dependent_induction_rule"]
    assert "branch-specialized forward proof" in construction["zero_branch"]
    assert construction["clean_dvd_antisymm"]["required_direct_dependencies"] == ["Axeyum.Autogenesis.eqZeroOfZeroDvdCleanV1", "Axeyum.Autogenesis.leOfDvdCleanV1", "Nat.le_antisymm", "Nat.le_succ_succ", "Nat.zero_le"]
    assert plan["acceptance"]["fresh_complete_invocations"] == 2 and plan["acceptance"]["outputs_must_be_byte_identical"] is True
    assert plan["budget"]["max_exact_target_submissions"] == plan["budget"]["max_retries"] == 0
    assert all(value == 0 for value in plan["authority"].values())

def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-plan-v5: {error}", file=sys.stderr); return 1
    print("autogenesis-clean-dvd-antisymm-plan-v5: ok"); return 0
if __name__ == "__main__": raise SystemExit(main())
