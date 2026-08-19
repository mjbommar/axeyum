#!/usr/bin/env python3
"""Verify the Fibonacci coprimality premise plan and composition blocker."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-fib-coprime-premise-plan-v1.json"


class PlanError(RuntimeError):
    """The frozen plan, evidence, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = load(MANIFEST) if manifest is None else manifest
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-coprime-premise-plan"
        or manifest.get("state")
        != "proof-plan-frozen-execution-blocked-on-native-prelude-composition"
    ):
        raise PlanError("manifest identity changed")
    source = manifest["source"]
    if sha256(pathlib.Path(source["stream"])) != source["stream_sha256"]:
        raise PlanError("source stream changed")
    probe = manifest["composition_probe"]
    if sha256(ROOT / probe["tool"]) != probe["tool_sha256"]:
        raise PlanError("composition probe changed")
    observation_path = pathlib.Path(probe["observation"])
    if (
        sha256(observation_path) != probe["observation_sha256"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_path.parent.stat().st_mode) != 0o555
    ):
        raise PlanError("composition observation changed or is mutable")
    observation = load(observation_path)
    required = manifest["proof_plan"]["required_native_declarations"]
    presence = observation["source"]["required_declarations_present"]
    if (
        observation["source"]["stream_sha256"] != source["stream_sha256"]
        or observation["source"]["axioms"] != []
        or observation["source"]["declarations_before"]
        != probe["imported_declarations"]
        or observation["source"]["theorems_before"] != probe["imported_theorems"]
        or observation["result"]["outcome"] != probe["outcome"]
        or observation["result"]["conflicting_name"] != probe["first_conflict"]
        or any(presence[name] for name in required)
        or not presence["Nat.rec"]
        or manifest["proof_plan"]["required_present_in_import"] != []
        or manifest["proof_plan"]["already_present_in_import"] != ["Nat.rec"]
    ):
        raise PlanError("composition observation semantics changed")
    if (
        manifest["target"]["fact_id"]
        != "F:ml430-nat-fib-coprime-fib-succ-162fc738"
        or manifest["target"]["sole_admitted_theorem_premise"]
        != "F:ml430-nat-fib-add-two-b86e0c82"
    ):
        raise PlanError("target premise boundary changed")
    if manifest["authority"] != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_displayed": False,
        "proof_search_invocations": 0,
        "kernel_submissions": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("plan authority changed")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_NAT_FIB_COPRIME_PREMISE_PLAN_OK|"
            f"required={len(manifest['proof_plan']['required_native_declarations'])}|"
            "present=0|first_conflict=True|submissions=0|evaluation=0|writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-nat-fib-coprime-premise-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
