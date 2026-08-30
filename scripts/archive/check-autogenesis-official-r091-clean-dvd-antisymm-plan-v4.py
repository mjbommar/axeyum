#!/usr/bin/env python3
"""Verify exact Nat.mod_lt target-leaf reuse for official clean order V4."""
from __future__ import annotations
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];PLAN=ROOT/"artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v4.json";RESULT=ROOT/"artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v3.json"
def sha256(path:pathlib.Path)->str:return hashlib.sha256(path.read_bytes()).hexdigest()
def check()->None:
 p=json.loads(PLAN.read_text());r=json.loads(RESULT.read_text())
 assert sha256(RESULT)==p["predecessor"]["sha256"]
 assert r["decline"]["class"]=="NoAdditions" and r["execution"]["support_submissions"]==0
 assert p["reuse"]["name"]=="Nat.mod_lt" and len(p["reuse"]["requirements"])==4
 assert "sole explicit target theorem leaf" in p["reuse"]["composition"]
 assert p["acceptance"]["all_axiom_footprints"]==[] and p["acceptance"]["exact_target_submissions"]==0
 assert p["budget"]["max_exact_target_submissions"]==p["budget"]["max_retries"]==0
 assert all(value==0 for value in p["authority"].values())
def main()->int:
 try:check()
 except (AssertionError,KeyError,OSError,json.JSONDecodeError) as error:print(f"autogenesis-official-r091-clean-dvd-antisymm-plan-v4: {error}",file=sys.stderr);return 1
 print("AUTOGENESIS_OFFICIAL_R091_CLEAN_DVD_ANTISYMM_PLAN_V4_OK|leaf=Nat.mod_lt|target=0");return 0
if __name__=="__main__":raise SystemExit(main())
