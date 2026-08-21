#!/usr/bin/env python3
"""Fail closed over the V4 clean divisibility-antisymmetry plan."""

from __future__ import annotations
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v4.json"
PREDECESSOR = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v3.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check() -> None:
    plan = json.loads(PLAN.read_text())
    assert plan["state"] == "preregistered-inline-native-successor-positivity-and-antisymmetry-before-code-or-stream-access"
    assert plan["predecessor"]["sha256"] == sha256(PREDECESSOR)
    construction = plan["construction"]
    assert construction["inline_successor_positivity"]["named_submission"] is False
    assert "Nat.le_succ_succ" in construction["inline_successor_positivity"]["method"]
    assert construction["clean_dvd_antisymm"]["required_direct_dependencies"] == [
        "Axeyum.Autogenesis.eqZeroOfZeroDvdCleanV1", "Axeyum.Autogenesis.leOfDvdCleanV1",
        "Nat.le_antisymm", "Nat.le_succ_succ", "Nat.zero_le"
    ]
    assert len(construction["transport_roots"]) == 3
    assert plan["acceptance"]["fresh_complete_invocations"] == 2
    assert plan["acceptance"]["outputs_must_be_byte_identical"] is True
    assert plan["budget"]["max_retries"] == plan["budget"]["max_exact_target_submissions"] == 0
    assert all(value == 0 for value in plan["authority"].values())


def main() -> int:
    try:
        check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-plan-v4: {error}", file=sys.stderr)
        return 1
    print("autogenesis-clean-dvd-antisymm-plan-v4: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
