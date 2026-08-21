#!/usr/bin/env python3
"""Verify the V5 decline and bounded coprimality carrier audit plan."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v5.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-coprime-carrier-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/5c1680853-nat-gcd-fib-add-self-exact-v5")
MANIFEST_SHA = "c41ac0eea1e724c562a4d17e7530bcce848af929c6fafe82c0edff30ed55fac0"
ACCEPTED = ["Axeyum.Autogenesis.dvdAntisymmOfficialV1", "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1", "Axeyum.Autogenesis.NatFibSuccessorAddition"]

class PlanError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise PlanError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "three-capsules-composed-coprimality-gcd-model-shape-declined-second-skipped": raise PlanError("V5 state changed")
    decline = result["decline"]
    if decline["accepted_roots"] != ACCEPTED or decline["rejected_root"] != "Nat.fib_coprime_fib_succ" or decline["name"] != "Axeyum.Autogenesis.gcdModel_succ": raise PlanError("V5 boundary changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise PlanError("sealed V5 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise PlanError("V5 evidence is not sealed")
    inputs = plan["inputs"]
    if inputs["source_root"] != "Nat.fib_coprime_fib_succ" or inputs["blocked_dependency"] != "Axeyum.Autogenesis.gcdModel_succ": raise PlanError("audit target changed")
    audit = plan["audit"]
    if audit["proof_terms_types_or_values_may_be_rendered"] or audit["kernel_submissions"] != 0 or audit["exports"] != 0: raise PlanError("nonrendering audit boundary changed")
    budget = plan["budget"]
    if budget != {"max_audit_driver_builds": 1, "max_complete_audits": 1, "max_reads_per_input": 1, "max_retries": 0, "max_exact_target_submissions": 0}: raise PlanError("audit budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise PlanError("audit authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_GCD_FIB_COPRIME_CARRIER_AUDIT_PLAN_OK|reads=1|submissions=0|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"gcd-fib-coprime-carrier-audit-plan: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
