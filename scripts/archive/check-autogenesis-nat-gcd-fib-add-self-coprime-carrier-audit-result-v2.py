#!/usr/bin/env python3
"""Verify the WellFounded path result and bounded zero-left V7 bridge."""
from __future__ import annotations
import hashlib, json, pathlib, stat, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-coprime-carrier-audit-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v7.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/audits/f042f87ac-gcd-fib-coprime-well-founded-fix-audit-v2")
MANIFEST_SHA = "5adefb5d464d24130b4750a6d232616b4669a19b126ffc86ac52916f87956bf1"
class BoundaryError(RuntimeError): pass
def load(path):
    value=json.loads(path.read_text())
    if not isinstance(value,dict): raise BoundaryError("not object")
    return value
def validate(result=None,plan=None):
    result=load(RESULT) if result is None else result; plan=load(PLAN) if plan is None else plan
    if result["measurement"]["blocked_dependency"] != "WellFounded.fix" or result["path"][1]["name"] != "Nat.gcd_zero_left": raise BoundaryError("path changed")
    if hashlib.sha256((PACK/"manifest.json").read_bytes()).hexdigest()!=MANIFEST_SHA: raise BoundaryError("evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode)!=0o555 or any(stat.S_IMODE(p.stat().st_mode)!=0o444 for p in PACK.iterdir()): raise BoundaryError("unsealed")
    c=plan["construction"]
    if c["coprimality_target_leaves"] != ["Axeyum.Autogenesis.nat_gcd_succ","Nat.gcd_zero_left"] or not c["require_source_public_name_checked_type_shape"] or c["other_source_changes_authorized"]: raise BoundaryError("construction changed")
    if plan["budget"]["max_zero_left_alias_submissions"]!=2 or plan["budget"]["max_retries"]!=0 or any(plan["authority"].values()): raise BoundaryError("authority changed")
    return result,plan
def main():
    try: validate(); print("AUTOGENESIS_GCD_FIB_COPRIME_CARRIER_AUDIT_RESULT_V2_OK|leaf=Nat.gcd_zero_left|target=0"); return 0
    except (OSError,KeyError,TypeError,ValueError,json.JSONDecodeError,BoundaryError) as error: print(f"coprime-carrier-result-v2: {error}",file=sys.stderr); return 1
if __name__=="__main__": raise SystemExit(main())
