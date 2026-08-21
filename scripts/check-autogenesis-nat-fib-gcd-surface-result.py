#!/usr/bin/env python3
"""Validate the single preregistered Nat.fib_gcd surface observation."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-surface-result-v1.json"
PLAN_CHECKER = ROOT / "scripts/check-autogenesis-nat-fib-gcd-surface-plan.py"


class ResultError(RuntimeError):
    """The bounded observation or non-authority boundary changed."""


def byte_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def historical_digest(commit: str, path: str) -> str:
    value = subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)
    return hashlib.sha256(value).hexdigest()


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ResultError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate() -> dict:
    plan_checker = load_module("nat_fib_gcd_surface_plan_for_result", PLAN_CHECKER)
    try:
        plan_checker.validate()
    except plan_checker.PlanError as error:
        raise ResultError(f"plan failed: {error}") from error
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    pack = result.get("evidence_pack") or {}
    composition = result.get("composition") or {}
    execution = result.get("execution") or {}
    authority = result.get("authority") or {}
    pack_path = pathlib.Path(pack.get("path", ""))
    observation_path = pack_path / "observation.json"
    index_path = pack_path / "SHA256SUMS"
    observation = json.loads(observation_path.read_text())
    observed_surface = observation.get("surface") or {}
    observed_present = [row.get("name") for row in observed_surface.get("present", [])]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-surface-result-v1"
        or result.get("state")
        != "two-admitted-roots-composed-euclidean-surface-ready-two-convenience-names-absent"
        or byte_digest(ROOT / plan["path"]) != plan.get("sha256")
        or historical_digest("6db583249", implementation["path"])
        != implementation.get("sha256")
        or byte_digest(index_path) != pack.get("index_sha256")
        or byte_digest(observation_path) != pack.get("observation_sha256")
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or composition
        != {
            "root": "Nat.gcd_fib_add_self",
            "receipt_sha256": "541513911a8298cb9464ce6275e1a65208c038bd3559de289ce13901ad2cb1cd",
            "added_theorems": 22,
            "fresh_imports": 2,
        }
        or observed_present != result.get("present")
        or observed_surface.get("missing") != result.get("missing")
        or result.get("missing") != ["Nat.gcd_zero_left", "Nat.gcd_succ"]
        or any(row.get("axiom_footprint") != [] for row in observed_surface["present"])
        or observation.get("authority", {}).get("target_theorem_submissions") != 0
        or execution
        != {
            "driver_builds": 1,
            "complete_audits": 1,
            "capsule_reads": 2,
            "fresh_imports": 2,
            "proof_search_invocations": 0,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or authority
        != {
            "target_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("surface identity, observation, or authority changed")
    return result


def main() -> int:
    try:
        result = validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-surface-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_SURFACE_RESULT_OK|"
        f"present={len(result['present'])}|missing={len(result['missing'])}|"
        "footprint=0|submissions=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
