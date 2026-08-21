#!/usr/bin/env python3
"""Verify the V7 decline and exact two-leaf V8 replacement."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v7.json"
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v8.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/29c126c0e-official-r091-clean-dvd-antisymm-v7")
MANIFEST_SHA = "0ec6fa6b0a5accddae6373c05da9a1ae2ec22aa7bb99a39fe027e3bdeecd1f6c"
NAMES = ["Axeyum.Autogenesis.mulLeMulLeftOfficialV1", "Axeyum.Autogenesis.leAntisymmOfficialV1"]

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "positive-factor-ready-first-run-declined-at-missing-multiplicative-monotonicity-second-skipped" or result["decline"]["name"] != "Nat.mul_le_mul_left": raise BoundaryError("V7 decline changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise BoundaryError("sealed V7 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("V7 evidence is not sealed")
    if [row["name"] for row in plan["new_supports"]] != NAMES: raise BoundaryError("V8 support names changed")
    if plan["acceptance"]["support_submissions"] != 12 or plan["acceptance"]["exact_target_submissions"] != 0 or plan["budget"]["max_retries"] != 0: raise BoundaryError("V8 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("V8 authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_OFFICIAL_R091_CLEAN_ORDER_V7_V8_OK|supports=mul_le+le_antisymm|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-r091-clean-order-v7-v8: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
