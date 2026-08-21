#!/usr/bin/env python3
"""Verify V9's antisymmetry decline and V10's structural congruence boundary."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v9.json"
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v10.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/64b0eed45-official-r091-clean-dvd-antisymm-v9")
MANIFEST_SHA = "864bc3e8738e576c2d3cf037604ecc9fddbd6808f645077f3b899badd38a8a44"
LOCAL = ["Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1", "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1", "Axeyum.Autogenesis.mulLeMulLeftOfficialV1", "Axeyum.Autogenesis.leOfDvdOfficialV1"]

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "four-supports-local-order-antisymmetry-type-mismatch-second-skipped": raise BoundaryError("V9 state changed")
    if result["decline"] != {"stage": "official-order-antisymmetry-submission", "class": "TypeMismatch", "partial_kernel_published": False}: raise BoundaryError("V9 decline changed")
    if result["local_progress"] != LOCAL or result["execution"]["published_supports"] != 0: raise BoundaryError("V9 local-only boundary changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise BoundaryError("sealed V9 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("V9 evidence is not sealed")
    correction = plan["correction"]
    if correction["target"] != "Axeyum.Autogenesis.leAntisymmOfficialV1" or correction["rejected_subterm"] != "congrArg Nat.succ predecessorEquality": raise BoundaryError("V10 correction target changed")
    if not correction["replacement"].startswith("Eq.rec transport") or correction["statement_changed"] or correction["induction_structure_changed"] or correction["other_term_changes_authorized"]: raise BoundaryError("V10 correction broadened")
    if plan["acceptance"]["support_submissions"] != 12 or plan["budget"]["max_retries"] != 0: raise BoundaryError("V10 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("V10 authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_OFFICIAL_R091_CLEAN_ORDER_V9_V10_OK|correction=structural-succ-congruence|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-r091-clean-order-v9-v10: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
