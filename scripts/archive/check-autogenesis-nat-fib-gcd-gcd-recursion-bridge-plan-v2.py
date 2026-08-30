#!/usr/bin/env python3
"""Validate the footprint-count-only bridge audit correction."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-gcd-recursion-bridge-plan-v2.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan["input"]
    implementation = plan["implementation_prestate"]
    if (
        plan.get("state") != "preregistered-public-footprint-count-correction-before-code"
        or sha(ROOT / source["result"]) != source["sha256"]
        or sha(ROOT / implementation["path"]) != implementation["sha256"]
        or plan.get("correction") != {
            "replace": "map_err plus private render_name over axiom_footprint",
            "with": "the length of the public Vec<NameId> returned by axiom_footprint",
            "required_count": 0,
            "other_source_changes": 0,
        }
        or plan.get("budget") != {
            "complete_audits": 1,
            "kernel_submissions": 0,
            "capsule_writes": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("V2 correction identity or authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-gcd-recursion-bridge-plan-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_GCD_RECURSION_BRIDGE_PLAN_V2_OK|audits=0/1|corrections=0/1")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
