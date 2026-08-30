#!/usr/bin/env python3
"""Verify the exact three-theorem closed Euclidean-update wrapper plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-closed-plan-v1.json"
UPDATE_RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-result-v2.json"
LEAF_RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-clean-mul-leaves-result-v1.json"
SOURCES = {
    "scripts/lean/autogenesis_balanced_bezout_euclidean_update_v2.lean": "a589b50e7743a4853f9c5eb5d0e970e6e5c40afb58bf7cd59f5a00e0094afd40",
    "scripts/lean/autogenesis_balanced_bezout_clean_mul_leaves_v1.lean": "2c925db23b545067f1842b5914bce79990f94e576ff093bd79717f2a978aad89",
    "scripts/lean/autogenesis_balanced_bezout_euclidean_update_closed_v1.lean": "efb4ea9bb4760ee496260e60ab991b28c5b491bbba85dade4a9bc86c59338112",
}
UPDATE_RESULT_SHA256 = "acf28ea301b77acd6844c5fbbdd2bc09bd277942d5e1d4685491babfcbed6e60"
LEAF_RESULT_SHA256 = "f4f0ce40c469d65e24639cfef76edd4ec1ce9ce7d6a0d865e7b95d9d71c1700c"
DEPENDENCIES = ["Axeyum.Autogenesis.balancedBezoutEuclideanUpdateV2", "Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1"]


class BalancedBezoutClosedUpdatePlanError(RuntimeError):
    """The exact wrapper inputs, dependencies, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutClosedUpdatePlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-closed-plan", "preregistered-exact-three-theorem-wrapper-before-compilation-no-composition-credit"):
        raise BalancedBezoutClosedUpdatePlanError("plan identity changed")
    if sha256(UPDATE_RESULT) != UPDATE_RESULT_SHA256 or plan.get("inputs", {}).get("parameterized_update_result", {}).get("sha256") != UPDATE_RESULT_SHA256:
        raise BalancedBezoutClosedUpdatePlanError("update result identity changed")
    if sha256(LEAF_RESULT) != LEAF_RESULT_SHA256 or plan.get("inputs", {}).get("clean_leaves_result", {}).get("sha256") != LEAF_RESULT_SHA256:
        raise BalancedBezoutClosedUpdatePlanError("leaf result identity changed")
    for path, digest in SOURCES.items():
        if sha256(ROOT / path) != digest:
            raise BalancedBezoutClosedUpdatePlanError(f"source identity changed: {path}")
    construction = plan.get("construction", {})
    if construction.get("exact_required_direct_dependencies") != DEPENDENCIES or construction.get("new_mathematical_proof_steps") != 0:
        raise BalancedBezoutClosedUpdatePlanError("exact wrapper contract changed")
    budget = {"max_source_copies": 3, "max_source_compilations": 3, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_generic_gcd_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise BalancedBezoutClosedUpdatePlanError("execution budget changed")
    authority = plan.get("authority", {})
    for key in ("generic_balanced_bezout_credit", "target_specialization_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutClosedUpdatePlanError(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_CLOSED_UPDATE_PLAN_OK|dependencies=3|compilations<=3|exports<=1|imports<=2|generic_gcd=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutClosedUpdatePlanError) as error:
        print(f"autogenesis-balanced-bezout-closed-update-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
