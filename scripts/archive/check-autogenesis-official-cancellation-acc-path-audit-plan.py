#!/usr/bin/env python3
"""Verify the bounded non-rendering official-cancellation Acc path audit."""
from __future__ import annotations
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];PLAN=ROOT/"artifacts/autogenesis/official-cancellation-acc-path-audit-plan-v1.json";RESULT=ROOT/"artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v4.json"
def sha256(path:pathlib.Path)->str:return hashlib.sha256(path.read_bytes()).hexdigest()
def check()->None:
 p=json.loads(PLAN.read_text());r=json.loads(RESULT.read_text())
 assert sha256(RESULT)==p["predecessor"]["sha256"] and r["decline"]["name"]=="Acc"
 assert p["inputs"]["root"].endswith("officialCoprimeFactorDivisibilityCancellationV1") and p["inputs"]["blocked_dependency"]=="Acc"
 measurement=" ".join(p["measurement"]);assert "complete declaration dependency closure" in measurement and "never render theorem types" in measurement
 assert p["budget"]=={"binary_builds":1,"source_reads":1,"target_reads":1,"audit_invocations":1,"kernel_submissions":0,"retries":0}
 assert all(value==0 for value in p["authority"].values())
def main()->int:
 try:check()
 except (AssertionError,KeyError,OSError,json.JSONDecodeError) as error:print(f"autogenesis-official-cancellation-acc-path-audit-plan: {error}",file=sys.stderr);return 1
 print("AUTOGENESIS_OFFICIAL_CANCELLATION_ACC_PATH_AUDIT_PLAN_OK|reads=2|submissions=0");return 0
if __name__=="__main__":raise SystemExit(main())
