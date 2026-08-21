#!/usr/bin/env python3
"""Validate the retained compile-only GCD recursion bridge decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-gcd-recursion-bridge-result-v1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    pack = result.get("evidence_pack") or {}
    observation = result.get("observation") or {}
    pack_path = pathlib.Path(pack["path"])
    if (
        result.get("state") != "driver-compile-declined-before-input-read-or-audit"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation.json") != pack.get("observation_sha256")
        or sha(pack_path / "stderr.txt") != pack.get("stderr_sha256")
        or (pack_path / "observation.json").stat().st_size != 0
        or "no method named `map_err`" not in (pack_path / "stderr.txt").read_text()
        or observation.get("proof_input_reads") != 0
        or observation.get("complete_audits") != 0
        or observation.get("kernel_submissions") != 0
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise RuntimeError("compile decline identity, evidence, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-gcd-recursion-bridge-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_GCD_RECURSION_BRIDGE_RESULT_OK|compile=fail|reads=0|audits=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
