#!/usr/bin/env python3
"""Verify the exact V4 stale-binary decline and source-frozen V5 execution."""

from __future__ import annotations
import hashlib, json, pathlib, stat, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v4.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v5.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/5c1680853-nat-gcd-fib-add-self-exact-v4")
MANIFEST_SHA = "acead5d0bd3f74a627af0965916217abcbe563f3a986ae7b43a3acb9b8ea632d"

class BoundaryError(RuntimeError): pass

def load(path):
    value = json.loads(path.read_text())
    if not isinstance(value, dict): raise BoundaryError(f"{path} is not an object")
    return value

def validate(result=None, plan=None):
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "stale-executable-declined-before-import-second-run-skipped": raise BoundaryError("V4 state changed")
    decline = result["decline"]
    if decline["class"] != "StaleExecutable" or decline["stage"] != "driver-input-identity-check-before-import" or decline["partial_kernel_published"]: raise BoundaryError("V4 decline changed")
    execution = result["execution"]
    if execution["complete_invocations"] != 0 or execution["capsule_compositions"] != 0 or execution["exact_target_submissions"] != 0: raise BoundaryError("V4 zero-execution boundary changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA: raise BoundaryError("sealed V4 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()): raise BoundaryError("V4 evidence is not sealed")
    correction = plan["execution_correction"]
    if correction != {"source_commit": "5c1680853", "source_changes_authorized": False, "required_command": "cargo build -p axeyum-lean-import --example nat_gcd_fib_add_self_exact --all-features", "reason": "cargo clippy checked source but did not replace target/debug/examples/nat_gcd_fib_add_self_exact", "other_changes_authorized": False}: raise BoundaryError("V5 correction broadened")
    if plan["acceptance"]["exact_target_submissions"] != 2 or plan["budget"]["max_explicit_driver_builds"] != 1 or plan["budget"]["max_retries"] != 0: raise BoundaryError("V5 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]): raise BoundaryError("V5 authority changed")
    return result, plan

def main():
    try:
        validate(); print("AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EXACT_V4_V5_OK|source-changes=0|explicit-builds=1|target-credit=0"); return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"nat-gcd-fib-add-self-exact-v4-v5: {error}", file=sys.stderr); return 1

if __name__ == "__main__": raise SystemExit(main())
