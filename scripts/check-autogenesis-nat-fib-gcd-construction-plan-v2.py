#!/usr/bin/env python3
"""Validate the fresh bounded Nat.fib_gcd construction authorization."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-plan-v2.json"


class PlanError(RuntimeError):
    """The repaired route, gate coupling, or fresh submission ceiling changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    target = plan.get("target") or {}
    authority = plan.get("authority") or {}
    if (
        plan.get("kind") != "axeyum-autogenesis-mathlib-nat-fib-gcd-construction-plan-v2"
        or plan.get("state")
        != "preregistered-fresh-two-run-construction-after-defeq-repair-before-submission"
        or target.get("fact_id") != "F:ml430-nat-fib-gcd-d1d98407"
        or target.get("name") != "Nat.fib_gcd"
        or sha(ROOT / "artifacts/facts/F-ml430-nat-fib-gcd-d1d98407.json")
        != target.get("fact_file_sha256")
    ):
        raise PlanError("target identity changed")
    for key in ["contract_result", "repair_result"]:
        row = authority.get(key) or {}
        if sha(ROOT / row["path"]) != row.get("sha256"):
            raise PlanError(f"{key} identity changed")
    implementation = authority.get("implementation") or {}
    result_path = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-result-v2.json"
    if sha(ROOT / implementation["path"]) != implementation.get("sha256"):
        result = json.loads(result_path.read_text())
        if (
            result.get("state")
            != "helper-accepted-target-type-mismatch-second-run-skipped-zero-credit"
            or result.get("plan", {}).get("sha256") != sha(PLAN)
        ):
            raise PlanError("implementation changed without the exact spent-attempt result")
    if authority["implementation"].get("permitted_source_edits") != 0:
        raise PlanError("source edit authority changed")
    couplings = plan.get("historical_gate_couplings") or []
    if len(couplings) != 2:
        raise PlanError("historical coupling set changed")
    for row in couplings:
        checker = ROOT / row["checker"]
        policy = ROOT / row["policy"]
        if (
            sha(checker) != row.get("checker_sha256")
            or sha(policy) != row.get("policy_sha256")
            or row.get("preexecution_result") != "pass"
            or subprocess.run([sys.executable, str(checker)], cwd=ROOT).returncode != 0
        ):
            raise PlanError("historical gate coupling no longer passes monotonically")
    inputs = plan.get("inputs") or []
    if (
        [row.get("root") for row in inputs]
        != ["Nat.gcd_greatest", "Nat.gcd_fib_add_self"]
        or any(sha(pathlib.Path(row["capsule"])) != row.get("sha256") for row in inputs)
    ):
        raise PlanError("sealed input roots changed")
    submissions = plan.get("submissions") or []
    if [(row.get("order"), row.get("name")) for row in submissions] != [
        (1, "Axeyum.Autogenesis.fibGcdQuotientIterationV1"),
        (2, "Nat.fib_gcd"),
    ]:
        raise PlanError("submission order changed")
    if plan.get("budget") != {
        "complete_invocations": 2,
        "capsule_reads": 4,
        "fresh_output_imports": 4,
        "helper_theorem_submissions": 2,
        "target_theorem_submissions": 2,
        "proof_search_invocations": 0,
        "retries": 0,
        "ledger_writes": 0,
    } or plan.get("acceptance") != {
        "both_invocations_accept_both_exact_statements": True,
        "all_theorem_axiom_footprints": [],
        "outputs_byte_identical": True,
        "receipts_byte_identical": True,
        "target_fact_status_changes": 0,
    }:
        raise PlanError("fresh budget or acceptance changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-construction-plan-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_CONSTRUCTION_PLAN_V2_OK|budget=spent|run2=skipped|retries=0|edits=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
