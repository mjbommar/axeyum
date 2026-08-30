#!/usr/bin/env python3
"""Verify the local subtraction-restoration replacement plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-local-subtraction-replacement-plan-v1.json"
)
ORIGINAL_SOURCE = ROOT / "scripts/lean/autogenesis_div_mod_go_reconstruct.lean"


class ReplacementPlanError(RuntimeError):
    """The blocker, replacement scope, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ReplacementPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-euclidean-local-subtraction-replacement-plan"
        or plan.get("state") != "preregistered-before-v2-source-or-reconstruction"
        or plan.get("policy_version") != "euclidean-local-sub-add-cancel-replacement-v1"
    ):
        raise ReplacementPlanError("replacement plan identity changed")
    for key, expected in {
        "proof_capsule": "17ef795517c8373a52889597f859cc1d5a75fa74b3a0c38bf334c4f523eb14f1",
        "first_decline": "70bcd809a42774c75956c7f9cf0a89db0f847a2d03be3fb309fcd8084e8798ce",
        "dependency_audit": "9a27f06239e54fdd4979901c377f8f4675f6ff580d043244360d144aee7b29de",
    }.items():
        row = plan["inputs"][key]
        if row.get("sha256") != expected or sha256(ROOT / row["path"]) != expected:
            raise ReplacementPlanError(f"{key} identity changed")
    audit = plan["inputs"]["dependency_audit"]
    receipt = pathlib.Path(audit["receipt_path"])
    if (
        audit.get("receipt_sha256")
        != "fc6cffc7baec14790cc4f23461389c5ef229ccb5281ffea5c317efc91b7031f5"
        or stat.S_IMODE(receipt.stat().st_mode) != 0o444
        or sha256(receipt) != audit["receipt_sha256"]
    ):
        raise ReplacementPlanError("dependency audit receipt changed")
    if sha256(ORIGINAL_SOURCE) != "2387f116f1eb94cb0d46027f100f5912d186094d229af2f16f421398be118a80":
        raise ReplacementPlanError("first failed source changed")
    if plan.get("measured_blocker") != {
        "name": "Nat.sub_add_cancel",
        "declaration_sha256": "756d178b67958fe684cb9e64c8d0b40ff557a375ed14ba122c070bfa7b3616a5",
        "axiom_footprint": ["propext"],
        "other_direct_dependencies_empty": 14,
    }:
        raise ReplacementPlanError("measured blocker changed")
    replacement = plan["fixed_replacement"]
    if replacement != {
        "source_path": "scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean",
        "original_source_must_remain_unchanged": True,
        "replacement_scope": "replace only the Nat.sub_add_cancel call with a local primitive-recursive proof",
        "local_proof_may_create_a_global_declaration": False,
        "forbidden_theorem_dependencies": ["Nat.sub_add_cancel", "Nat.add_sub_of_le"],
        "forbidden_axioms": ["propext"],
        "proof_search_allowed": False,
        "upstream_proof_bodies_allowed": False,
        "alternative_proof_routes_allowed": False,
    }:
        raise ReplacementPlanError("fixed replacement changed")
    target = plan["target"]
    if (
        target.get("theorem_name") != "Axeyum.Autogenesis.divModGoReconstruct"
        or target.get("required_axiom_footprint") != []
        or target.get("required_fresh_reconstructions") != 2
        or target.get("second_run_requires_first_run_acceptance") is not True
        or target.get("both_declaration_identities_must_match") is not True
        or target.get("direct_dependencies_must_be_enumerated") is not True
    ):
        raise ReplacementPlanError("target reconstruction gate changed")
    if plan["budget"] != {
        "max_revised_source_paths": 1,
        "max_new_support_theorem_declarations": 1,
        "max_kernel_theorem_submissions": 2,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
        "max_retries_after_kernel_decline": 0,
    }:
        raise ReplacementPlanError("replacement budget changed")
    if plan["authority"] != {
        "public_euclidean_lift_allowed": False,
        "balanced_bezout_reconstruction_allowed": False,
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ReplacementPlanError("replacement authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_LOCAL_SUB_REPLACEMENT_PLAN_OK|blockers=1|"
            "source_paths=0/1|submissions=0/2|target_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ReplacementPlanError) as error:
        print(f"autogenesis-euclidean-local-sub-replacement-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
