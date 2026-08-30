#!/usr/bin/env python3
"""Verify the V6 decline and bounded WellFounded.fix path audit."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v6.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-coprime-carrier-audit-plan-v2.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/11c3938ed-nat-gcd-fib-add-self-exact-v6")
MANIFEST_SHA = "a9dc7413d037830406120021b4d65167d6c09791f773b29fdde1170206226692"

class PlanError(RuntimeError): pass
def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise PlanError(f"{path} is not an object")
    return value
def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result; plan = load(PLAN) if plan is None else plan
    if result["decline"]["name"] != "WellFounded.fix" or result["execution"]["accepted_target_leaf_reuses"] != 1: raise PlanError("V6 boundary changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise PlanError("V6 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(p.stat().st_mode) != 0o444 for p in PACK.iterdir()): raise PlanError("V6 evidence unsealed")
    if plan["inputs"]["blocked_dependency"] != "WellFounded.fix" or plan["audit"]["proof_terms_types_or_values_may_be_rendered"]: raise PlanError("V2 audit changed")
    if plan["budget"]["max_complete_audits"] != 1 or plan["budget"]["max_retries"] != 0 or any(plan["authority"].values()): raise PlanError("V2 authority changed")
    return result, plan
def main():
    try: validate(); print("AUTOGENESIS_GCD_FIB_COPRIME_CARRIER_AUDIT_V2_PLAN_OK|blocked=WellFounded.fix|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error: print(f"coprime-carrier-audit-v2: {error}", file=sys.stderr); return 1
if __name__ == "__main__": raise SystemExit(main())
