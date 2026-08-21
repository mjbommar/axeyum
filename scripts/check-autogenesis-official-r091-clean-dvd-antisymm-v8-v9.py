#!/usr/bin/env python3
"""Verify the V8 recursor-arity decline and exact V9 correction boundary."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v8.json"
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v9.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/4ccca2216-official-r091-clean-dvd-antisymm-v8")
MANIFEST_SHA = "941c5ec95915c29d07d449ed0dcec0cb6bb2040114e6f550f4dfc6e8cccecd70"
SUPPORTS = [
    "Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1",
    "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1",
    "Axeyum.Autogenesis.mulLeMulLeftOfficialV1",
    "Axeyum.Autogenesis.leOfDvdOfficialV1",
    "Axeyum.Autogenesis.leAntisymmOfficialV1",
    "Axeyum.Autogenesis.dvdAntisymmOfficialV1",
]

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    decline = result["decline"]
    correction = plan["correction"]
    if result.get("state") != "first-run-declined-at-monomorphic-le-recursor-second-skipped": raise BoundaryError("V8 decline state changed")
    if decline != {"stage": "official-multiplicative-monotonicity-submission", "class": "UniverseArityMismatch", "name": "Nat.le.rec", "expected_universe_arity": 0, "supplied_universe_arity": 1, "partial_kernel_published": False}: raise BoundaryError("V8 decline changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise BoundaryError("sealed V8 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("V8 evidence is not sealed")
    if correction != {"declaration": "Nat.le.rec", "observed_expected_universe_arity": 0, "v8_supplied_universe_arity": 1, "v9_supplied_universe_arity": 0, "statement_changed": False, "proof_method_changed": False, "other_term_changes_authorized": False}: raise BoundaryError("V9 correction broadened")
    if plan["supports"] != SUPPORTS: raise BoundaryError("V9 support sequence changed")
    if plan["acceptance"]["support_submissions"] != 12 or plan["budget"]["max_retries"] != 0: raise BoundaryError("V9 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("V9 authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_OFFICIAL_R091_CLEAN_ORDER_V8_V9_OK|correction=le.rec-universe-arity-0|target=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-r091-clean-order-v8-v9: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
