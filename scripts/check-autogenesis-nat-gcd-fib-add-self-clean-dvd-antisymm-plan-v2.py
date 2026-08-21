#!/usr/bin/env python3
"""Fail closed over the single-kernel clean antisymmetry V2 plan."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = pathlib.Path(os.environ.get("AXEYUM_CLEAN_DVD_ANTISYMM_PLAN_V2", ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-clean-dvd-antisymm-plan-v2.json"))
BUDGET = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 2, "max_composition_operations": 2, "max_new_support_theorem_submissions": 4, "max_exact_target_submissions": 0, "max_retries": 0}


class CleanDvdAntisymmPlanV2Error(RuntimeError):
    """The single-kernel or zero-target boundary changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CleanDvdAntisymmPlanV2Error("plan is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan", "preregistered-single-kernel-construction-and-named-transport-before-code-or-stream-access"):
        raise CleanDvdAntisymmPlanV2Error("plan identity changed")
    predecessor = plan["predecessor"]
    if hashlib.sha256((ROOT / predecessor["path"]).read_bytes()).hexdigest() != predecessor["sha256"]:
        raise CleanDvdAntisymmPlanV2Error("predecessor identity changed")
    input_row = plan["input"]
    if hashlib.sha256(pathlib.Path(input_row["path"]).read_bytes()).hexdigest() != input_row["sha256"]:
        raise CleanDvdAntisymmPlanV2Error("input identity changed")
    construction = plan["construction"]
    if "one native kernel" not in construction["kernel_identity_rule"] or construction["clean_dvd_antisymm"]["name"] != "Axeyum.Autogenesis.dvdAntisymmCleanV2":
        raise CleanDvdAntisymmPlanV2Error("single-kernel construction changed")
    if construction["clean_dvd_antisymm"]["required_direct_dependencies"] != ["Axeyum.Autogenesis.leOfDvdCleanV1", "Nat.eq_zero_of_zero_dvd", "Nat.le_antisymm", "Nat.succ_pos"] or construction["clean_dvd_antisymm"]["axiom_footprint"] != []:
        raise CleanDvdAntisymmPlanV2Error("antisymmetry contract changed")
    if construction["transport_roots"] != ["Axeyum.Autogenesis.leOfDvdCleanV1", "Axeyum.Autogenesis.dvdAntisymmCleanV2"]:
        raise CleanDvdAntisymmPlanV2Error("transport roots changed")
    acceptance = plan["acceptance"]
    if acceptance != {"fresh_complete_invocations": 2, "outputs_must_be_byte_identical": True, "source_and_target_theorem_evidence_must_match": True, "checked_named_composition_must_replay": True, "final_target_axiom_footprints": [], "proof_terms_types_or_values_may_be_rendered": False}:
        raise CleanDvdAntisymmPlanV2Error("acceptance changed")
    if plan.get("budget") != BUDGET or any(value != 0 for value in plan["authority"].values()):
        raise CleanDvdAntisymmPlanV2Error("budget or authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_CLEAN_DVD_ANTISYMM_PLAN_V2_OK|runs=2|single_kernel=1|compositions=2|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CleanDvdAntisymmPlanV2Error) as error:
        print(f"autogenesis-clean-dvd-antisymm-plan-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
