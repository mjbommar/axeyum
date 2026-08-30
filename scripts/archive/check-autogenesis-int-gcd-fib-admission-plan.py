#!/usr/bin/env python3
"""Validate exact crash-safe Int.gcd_fib admission authority."""

import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-admission-plan-v1.json"

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    try:
        plan = json.loads(PLAN.read_text()); target = plan["target"]; evidence = plan["evidence"]; fact = ROOT / "artifacts/facts/F-ml430-int-gcd-fib-73bdafc2.json"
        valid = (plan.get("state") == "preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write"
            and target.get("fact_id") == "F:ml430-int-gcd-fib-73bdafc2" and target.get("fact_sha256") == sha256(fact)
            and json.loads(fact.read_text()).get("epistemic_status") == "open"
            and sha256(ROOT / evidence["construction_result"]) == evidence.get("construction_result_sha256")
            and sha256(ROOT / evidence["identity_result"]) == evidence.get("identity_result_sha256")
            and sha256(pathlib.Path(evidence["capsule_path"])) == evidence.get("capsule_sha256")
            and evidence.get("axiom_footprint") == [] and len(evidence.get("direct_theorem_dependencies", [])) == 5
            and plan["operation"].get("registry_writes") == 1 and plan["protocol"].get("authoritative_ledger_writes") == 1
            and plan["budget"].get("max_fault_injection_executions") == 1 and plan["budget"].get("max_recovery_executions") == 1
            and plan["budget"].get("max_clean_replays") == 1 and plan["budget"].get("max_search_invocations") == 0
            and plan.get("expected_newly_ready") == ["F:ml430-int-fib-gcd-3a8bfdec"])
        if not valid: raise ValueError("admission authority changed")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-admission-plan: FAIL: {error}", file=sys.stderr); return 1
    print("autogenesis-int-gcd-fib-admission-plan: PASS: fact=Int.gcd_fib|operation_writes=1|ledger_writes=1|replays=1"); return 0

if __name__ == "__main__": raise SystemExit(main())
