#!/usr/bin/env python3
"""Verify accepted official clean order and the bounded exact-target V4 plan."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v10.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v4.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/9ff54f11c-official-r091-clean-dvd-antisymm-v10")
MANIFEST_SHA = "6b65cf54c943d6c93262483c2b21a3791a6dc2c8813241f1eb7e384e14ebd937"
CAPSULE_SHA = "bc147e08e6425ce8c31f3a10ccd5e9a7f7774ef0265b45784700588cb4bbcb25"
ROOT_NAME = "Axeyum.Autogenesis.dvdAntisymmOfficialV1"
SUPPORT_NAMES = [
    "Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1",
    "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1",
    "Axeyum.Autogenesis.mulLeMulLeftOfficialV1",
    "Axeyum.Autogenesis.leOfDvdOfficialV1",
    "Axeyum.Autogenesis.leAntisymmOfficialV1",
    ROOT_NAME,
]

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "official-clean-order-reconstructed-twice-byte-identical-empty-footprint": raise BoundaryError("V10 state changed")
    if result["root"] != {"name": ROOT_NAME, "declaration_sha256": "d0bb666f4bbebafb01c3dc821317d86c10eaa538222d64b2cf4fac1caefa4f26", "capsule_sha256": CAPSULE_SHA, "bytes": 189710, "axiom_footprint": []}: raise BoundaryError("V10 root changed")
    if [row["name"] for row in result["supports"]] != SUPPORT_NAMES or any(row["axiom_footprint"] for row in result["supports"]): raise BoundaryError("V10 supports changed")
    execution = result["execution"]
    if execution["complete_invocations"] != 2 or execution["support_submissions"] != 12 or execution["fresh_imports"] != 4 or not execution["outputs_byte_identical"] or execution["exact_target_submissions"] != 0: raise BoundaryError("V10 execution changed")
    if sha(PACK / "manifest.json") != MANIFEST_SHA or sha(PACK / "clean-order-1.ndjson") != CAPSULE_SHA or sha(PACK / "clean-order-2.ndjson") != CAPSULE_SHA: raise BoundaryError("V10 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("V10 evidence is not sealed")
    change = plan["authorized_source_change"]
    if change["new_root"] != ROOT_NAME or change["new_capsule_sha256"] != CAPSULE_SHA or change["other_proof_route_changes_authorized"]: raise BoundaryError("exact V4 source authority broadened")
    acceptance = plan["acceptance"]
    if acceptance["fresh_complete_invocations"] != 2 or acceptance["exact_target_submissions"] != 2 or acceptance["target_axiom_footprint"] != []: raise BoundaryError("exact V4 acceptance changed")
    if plan["budget"]["max_retries"] != 0 or any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("exact V4 authority changed")
    for row in plan["inputs"].values():
        if sha(pathlib.Path(row["path"])) != row["sha256"]: raise BoundaryError(f"input changed: {row['path']}")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_OFFICIAL_CLEAN_ORDER_EXACT_V4_OK|supports=6|target-runs=2|target-credit=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-clean-order-exact-v4: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
