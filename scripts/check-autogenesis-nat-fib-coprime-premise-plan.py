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
        or observation["source"]["native_declarations"]
        != probe["native_declarations"]
        or len(observation["source"]["exact_overlap_names"])
        != probe["exact_overlaps"]
        or len(
            observation["source"][
                "alpha_type_compatible_content_mismatched_names"
            ]
        )
        != probe["alpha_type_compatible_content_mismatches"]
        or len(
            observation["source"][
                "kernel_type_shape_compatible_content_mismatched_names"
            ]
        )
        != probe["kernel_type_shape_compatible_content_mismatches"]
        or len(observation["source"]["type_mismatched_overlaps"])
        != probe["unresolved_type_overlaps"]
        or any(presence[name] for name in required)
        or not presence["Nat.rec"]
        or manifest["proof_plan"]["required_present_in_import"] != []
        or manifest["proof_plan"]["already_present_in_import"] != ["Nat.rec"]
    ):
        raise PlanError("composition observation semantics changed")
    categories = [
        observation["source"]["exact_overlap_names"],
        observation["source"]["alpha_type_compatible_content_mismatched_names"],
        observation["source"][
            "kernel_type_shape_compatible_content_mismatched_names"
        ],
        [row["name"] for row in observation["source"]["type_mismatched_overlaps"]],
    ]
    flattened = [name for category in categories for name in category]
    if (
        len(flattened) != 43
        or len(set(flattened)) != len(flattened)
        or any(category != sorted(category) for category in categories)
        or observation["authority"]
        != {
            "proof_bodies_displayed": False,
            "proof_search_invocations": 0,
            "kernel_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("composition overlap partition or authority changed")
    closures = observation["source"]["required_native_theorem_dependency_closures"]
    for row in closures:
        closure_categories = [
            row["missing_dependency_names"],
            row["exact_dependency_names"],
            row["alpha_type_compatible_dependency_names"],
            row["kernel_type_shape_compatible_dependency_names"],
            row["type_mismatched_dependency_names"],
        ]
        closure_names = [name for category in closure_categories for name in category]
        if (
            len(closure_names) != row["native_dependency_count"]
            or len(set(closure_names)) != len(closure_names)
            or any(category != sorted(category) for category in closure_categories)
        ):
            raise PlanError(f"invalid dependency closure partition for {row['theorem']}")
    closure_census = manifest["closure_census"]
    unblocked = [
        row for row in closures if not row["type_mismatched_dependency_names"]
    ]
    blocked = sorted(
        row["theorem"] for row in closures if row["type_mismatched_dependency_names"]
    )
    if (
        len(closures) != closure_census["required_theorems"]
        or len(unblocked) != 1
        or unblocked[0]["theorem"]
        != closure_census["first_structurally_unblocked_theorem"]
        or unblocked[0]["native_dependency_count"]
        != closure_census["first_dependency_count"]
        or unblocked[0]["missing_dependency_names"]
        != closure_census["first_missing_dependencies"]
        or blocked != closure_census["structurally_blocked_theorems"]
    ):
        raise PlanError("required theorem closure census changed")
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
