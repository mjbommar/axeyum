#!/usr/bin/env python3
"""Verify the measured exact parent and bounded exact-target V6 pruning."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-coprime-carrier-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v6.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/audits/b2871748b-gcd-fib-coprime-carrier-audit-v1")
MANIFEST_SHA = "53f620bcfcb5536130b8e59ecdc880aab4069f4fa408aa492e0141694a045973"
PARENT = "Axeyum.Autogenesis.nat_gcd_succ"
PARENT_SHA = "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16"

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "single-conflicting-helper-below-exact-target-parent": raise BoundaryError("audit state changed")
    measurement = result["measurement"]
    if measurement["blocked_dependency"] != "Axeyum.Autogenesis.gcdModel_succ" or measurement["carrier_count"] != 7 or measurement["introducing_capsule"] != "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1": raise BoundaryError("audit measurement changed")
    parent = result["nearest_exact_parent"]
    if parent != {"name": PARENT, "declaration_sha256": PARENT_SHA, "source_axiom_footprint": [], "source_closure_size": 258, "target_compatibility": "exact-declaration"}: raise BoundaryError("exact parent changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise BoundaryError("sealed audit changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("audit evidence is not sealed")
    execution = result["execution"]
    if execution["kernel_submissions"] != 0 or execution["exports"] != 0 or any(execution[key] != 0 for key in ["rendered_proof_terms", "rendered_theorem_types", "rendered_theorem_values"]): raise BoundaryError("audit trust boundary changed")
    change = plan["authorized_change"]
    if change["root"] != "Nat.fib_coprime_fib_succ" or PARENT not in change["new_composition"] or change["required_target_leaf_declaration_sha256"] != PARENT_SHA or change["other_source_changes_authorized"]: raise BoundaryError("V6 change broadened")
    if plan["acceptance"]["exact_target_submissions"] != 2 or plan["budget"]["max_retries"] != 0: raise BoundaryError("V6 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("V6 authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_GCD_FIB_COPRIME_CARRIER_AUDIT_RESULT_OK|exact-parent=nat_gcd_succ|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"gcd-fib-coprime-carrier-audit-result: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
