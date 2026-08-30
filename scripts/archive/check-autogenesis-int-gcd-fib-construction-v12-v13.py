#!/usr/bin/env python3
"""Validate p1 localization and the Eq.rec congruence repair."""

import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v12.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v13.json"
OUTPUT = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1/root.ndjson")

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    try:
        result, plan = json.loads(RESULT.read_text()), json.loads(PLAN.read_text())
        valid = (result.get("state") == "closed-diagnostic-localizes-first-congrarg-no-target-submission"
            and result["observation"].get("accepted_links") == ["p0 Int.gcd_def"]
            and result["observation"].get("first_failing_link") == "p1 first natAbs transport"
            and result["execution"].get("target_theorem_submissions") == 0 and not OUTPUT.exists()
            and plan.get("state") == "preregistered-eq-rec-congruence-repair-before-code"
            and plan["predecessor"].get("sha256") == sha256(RESULT)
            and plan["repair"].get("mathematical_chain_changes") == 0
            and len(plan["repair"].get("expected_direct_theorem_dependencies", [])) == 5
            and plan["execution"].get("max_complete_invocations") == 1
            and plan["execution"].get("max_retries") == 0 and plan["execution"].get("max_ledger_writes") == 0)
        if not valid: raise ValueError("Eq.rec congruence repair authority changed")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v12-v13: FAIL: {error}", file=sys.stderr); return 1
    print("autogenesis-int-gcd-fib-construction-v12-v13: PASS: p0=accepted|p1=localized|repair=Eq.rec|dependencies=5|ledger_writes=0"); return 0

if __name__ == "__main__": raise SystemExit(main())
