#!/usr/bin/env python3
"""Verify the V6 missing-factor decline and bounded V7 support plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v6.json"
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v7.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/f37c82184-official-r091-clean-dvd-antisymm-v6")
MANIFEST_SHA = "2e0718bb4d8f609c11976cbcd80ad7c8f0f867c756694c53122f5b884bc8198b"
LEAVES = ["Nat.mul_zero", "Nat.not_succ_le_zero", "Nat.zero_le", "Nat.le_succ_succ"]


class BoundaryError(RuntimeError):
    """The decline or target-owned replacement scope changed."""


def load(path: pathlib.Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BoundaryError(f"{path} is not an object")
    return value


def validate(result: dict | None = None, plan: dict | None = None) -> tuple[dict, dict]:
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "lazy-iff-cleared-first-run-declined-at-missing-positive-product-factor-second-skipped" or result["decline"]["name"] != "Nat.one_le_right_of_mul":
        raise BoundaryError("V6 decline changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA:
        raise BoundaryError("sealed V6 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()):
        raise BoundaryError("V6 evidence is not sealed")
    support = plan["new_support"]
    if support["name"] != "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1" or support["exact_required_theorem_leaves"] != LEAVES or support["required_inductive_leaves"] != ["False", "False.rec"]:
        raise BoundaryError("V7 support contract changed")
    if plan["acceptance"]["support_submissions"] != 8 or plan["acceptance"]["exact_target_submissions"] != 0 or plan["budget"]["max_retries"] != 0:
        raise BoundaryError("V7 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]):
        raise BoundaryError("V7 pre-acceptance authority changed")
    return result, plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_R091_CLEAN_ORDER_V6_V7_OK|missing=one_le_right_of_mul|replacement=target-owned|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-r091-clean-order-v6-v7: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
