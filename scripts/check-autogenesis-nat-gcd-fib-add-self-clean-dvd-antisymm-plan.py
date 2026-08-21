#!/usr/bin/env python3
"""Fail closed over the clean divisibility-antisymmetry construction plan."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = pathlib.Path(os.environ.get("AXEYUM_CLEAN_DVD_ANTISYMM_PLAN", ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v1.json"))
BUDGET = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 4, "max_composition_operations": 4, "max_new_support_theorem_submissions": 4, "max_exact_target_submissions": 0, "max_retries": 0}


class CleanDvdAntisymmPlanError(RuntimeError):
    """The support construction or authority boundary changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CleanDvdAntisymmPlanError("plan is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan", "preregistered-clean-le-of-dvd-and-antisymm-before-code-or-stream-access"):
        raise CleanDvdAntisymmPlanError("plan identity changed")
    for predecessor in plan["predecessors"].values():
        if hashlib.sha256((ROOT / predecessor["path"]).read_bytes()).hexdigest() != predecessor["sha256"]:
            raise CleanDvdAntisymmPlanError("predecessor identity changed")
    for input_row in plan["inputs"].values():
        if hashlib.sha256(pathlib.Path(input_row["path"]).read_bytes()).hexdigest() != input_row["sha256"]:
            raise CleanDvdAntisymmPlanError("input identity changed")
    construction = plan["construction"]
    if construction["clean_le_of_dvd"].get("name") != "Axeyum.Autogenesis.leOfDvdCleanV1" or construction["clean_le_of_dvd"].get("source") != "duplicate the independently kernel-checked native Nat.le_of_dvd type and proof under a target-owned name" or construction["clean_le_of_dvd"]["required_direct_dependencies"] != ["Nat.mul_le_mul_left", "Nat.mul_one", "Nat.one_le_right_of_mul"] or construction["clean_le_of_dvd"]["axiom_footprint"] != []:
        raise CleanDvdAntisymmPlanError("clean le_of_dvd contract changed")
    if construction["clean_dvd_antisymm"].get("name") != "Axeyum.Autogenesis.dvdAntisymmCleanV1" or construction["clean_dvd_antisymm"]["required_direct_dependencies"] != ["Axeyum.Autogenesis.leOfDvdCleanV1", "Eq.symm", "Nat.eq_zero_of_zero_dvd", "Nat.le_antisymm", "Nat.succ_pos"] or construction["clean_dvd_antisymm"]["axiom_footprint"] != []:
        raise CleanDvdAntisymmPlanError("clean antisymmetry contract changed")
    acceptance = plan["acceptance"]
    if acceptance != {"fresh_complete_invocations": 2, "outputs_must_be_byte_identical": True, "both_theorems_must_reconstruct_in_the_exact_r091_kernel": True, "every_composition_must_replay": True, "proof_terms_types_or_values_may_be_rendered": False}:
        raise CleanDvdAntisymmPlanError("acceptance changed")
    if plan.get("budget") != BUDGET:
        raise CleanDvdAntisymmPlanError("budget changed")
    if any(value != 0 for value in plan["authority"].values()):
        raise CleanDvdAntisymmPlanError("plan grants authority before execution")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_CLEAN_DVD_ANTISYMM_PLAN_OK|runs=2|supports=2|submissions=4|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CleanDvdAntisymmPlanError) as error:
        print(f"autogenesis-clean-dvd-antisymm-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
