#!/usr/bin/env python3
"""Verify the same-capsule Nat.mod_lt bootstrap clean-order V3 plan."""
from __future__ import annotations
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
PLAN=ROOT/"artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v3.json"
RESULT=ROOT/"artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v2.json"
def sha256(path:pathlib.Path)->str:return hashlib.sha256(path.read_bytes()).hexdigest()
def check()->None:
 p=json.loads(PLAN.read_text());r=json.loads(RESULT.read_text())
 assert sha256(RESULT)==p["predecessor"]["sha256"]
 assert r["execution"]["support_submissions"]==r["execution"]["exact_target_submissions"]==0
 assert p["input_capsule"]["bootstrap_root"]=="Nat.mod_lt"
 assert p["sequence"][1].startswith("compose Nat.mod_lt alone")
 assert p["acceptance"]["all_axiom_footprints"]==[] and p["acceptance"]["exact_target_submissions"]==0
 assert p["budget"]["max_exact_target_submissions"]==p["budget"]["max_retries"]==0
 assert all(value==0 for value in p["authority"].values())
def main()->int:
 try:check()
 except (AssertionError,KeyError,OSError,json.JSONDecodeError) as error:print(f"autogenesis-official-r091-clean-dvd-antisymm-plan-v3: {error}",file=sys.stderr);return 1
 print("AUTOGENESIS_OFFICIAL_R091_CLEAN_DVD_ANTISYMM_PLAN_V3_OK|bootstrap=Nat.mod_lt|target=0");return 0
if __name__=="__main__":raise SystemExit(main())
