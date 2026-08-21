#!/usr/bin/env python3
"""Fail closed over the V3 clean divisibility-antisymmetry plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v3.json"
PREDECESSOR = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-result-v2.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check() -> None:
    plan = json.loads(PLAN.read_text())
    assert plan["state"] == "preregistered-single-kernel-zero-divisibility-leaf-and-antisymmetry-before-code-or-stream-access"
    assert plan["predecessor"]["sha256"] == sha256(PREDECESSOR)
    construction = plan["construction"]
    assert construction["clean_zero_dvd"]["required_direct_dependencies"] == ["Nat.zero_mul"]
    assert construction["clean_dvd_antisymm"]["required_direct_dependencies"] == [
        "Axeyum.Autogenesis.eqZeroOfZeroDvdCleanV1",
        "Axeyum.Autogenesis.leOfDvdCleanV1",
        "Nat.le_antisymm",
        "Nat.succ_pos",
    ]
    assert len(construction["transport_roots"]) == 3
    assert all(not theorem["axiom_footprint"] for theorem in (
        construction["clean_zero_dvd"], construction["clean_le_of_dvd"], construction["clean_dvd_antisymm"]
    ))
    acceptance = plan["acceptance"]
    assert acceptance["fresh_complete_invocations"] == 2
    assert acceptance["outputs_must_be_byte_identical"] is True
    assert acceptance["source_and_target_theorem_evidence_must_match"] is True
    assert acceptance["checked_named_composition_must_replay"] is True
    assert plan["budget"] == {
        "max_binary_builds": 1,
        "max_complete_invocations": 2,
        "max_input_stream_reads": 2,
        "max_composition_operations": 2,
        "max_new_support_theorem_submissions": 6,
        "max_exact_target_submissions": 0,
        "max_retries": 0,
    }
    assert all(value == 0 for value in plan["authority"].values())


def main() -> int:
    try:
        check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-clean-dvd-antisymm-plan-v3: {error}", file=sys.stderr)
        return 1
    print("autogenesis-clean-dvd-antisymm-plan-v3: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
