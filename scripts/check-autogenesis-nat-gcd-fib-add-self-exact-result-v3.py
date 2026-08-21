#!/usr/bin/env python3
"""Verify the retained cross-capsule V3 decline and zero-credit boundary."""
from __future__ import annotations
import hashlib, json, pathlib, stat, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v3.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/ce1ea969e-nat-gcd-fib-add-self-exact-v3")
MANIFEST_SHA256 = "e4f9e0e3ffec308b415a5099305ba81b816554b30bf35d4f001674975340582d"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def check() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "first-complete-invocation-declined-at-cross-capsule-mul-zero-shape-second-skipped"
    assert sha256(PACK / "manifest.json") == result["evidence_pack"]["manifest_sha256"] == MANIFEST_SHA256
    assert stat.S_IMODE(PACK.stat().st_mode) == 0o555
    assert all(stat.S_IMODE(path.stat().st_mode) == 0o444 for path in PACK.iterdir() if path.is_file())
    assert result["decline"]["class"] == "TypeShapeMismatch" and result["decline"]["name"] == "Nat.mul_zero"
    assert result["decline"]["partial_kernel_published"] is False
    execution = result["execution"]
    assert execution["complete_invocations"] == 1 and execution["second_complete_invocation_skipped"] is True
    assert execution["local_gcd_comm_submissions"] == execution["exact_target_submissions"] == execution["retries"] == 0
    assert all(value == 0 for value in result["authority"].values())
def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-exact-result-v3: {error}", file=sys.stderr); return 1
    print("AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EXACT_RESULT_V3_OK|runs=1|decline=Nat.mul_zero|target=0"); return 0
if __name__ == "__main__": raise SystemExit(main())
