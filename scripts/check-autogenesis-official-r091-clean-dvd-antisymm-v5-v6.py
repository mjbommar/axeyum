#!/usr/bin/env python3
"""Verify the V5 clean-order decline and bounded V6 correction."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v5.json"
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v6.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/344c32835-official-r091-clean-dvd-antisymm-v5")
MANIFEST_SHA = "bc5f3191f6e08b9039386a6039c94410a01c6248a3f9c711c5ae7a61e01818c0"


class BoundaryError(RuntimeError):
    """The retained decline or bounded correction changed."""


def load(path: pathlib.Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BoundaryError(f"{path} is not an object")
    return value


def validate(result: dict | None = None, plan: dict | None = None) -> tuple[dict, dict]:
    result = load(RESULT) if result is None else result
    plan = load(PLAN) if plan is None else plan
    if result.get("state") != "first-run-declined-at-eager-unused-iff-resolution-second-skipped":
        raise BoundaryError("V5 decline identity changed")
    if result["decline"] != {"stage": "support-builder-initialization-after-successful-cancellation-composition", "class": "MissingDeclaration", "name": "Iff", "used_by_official_support_route": False, "partial_kernel_published": False}:
        raise BoundaryError("V5 decline changed")
    if hashlib.sha256((PACK / "manifest.json").read_bytes()).hexdigest() != MANIFEST_SHA:
        raise BoundaryError("sealed V5 evidence changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()):
        raise BoundaryError("V5 evidence is not sealed")
    if plan.get("state") != "preregistered-lazy-unused-iff-resolution-before-code-or-rerun" or plan.get("proof_route_unchanged") is not True:
        raise BoundaryError("V6 correction scope changed")
    if "only method" not in plan["only_code_change"]:
        raise BoundaryError("V6 correction is no longer call-site-local")
    if plan["budget"]["max_retries"] != 0 or plan["budget"]["max_exact_target_submissions"] != 0:
        raise BoundaryError("V6 budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]):
        raise BoundaryError("V6 pre-acceptance authority changed")
    return result, plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_R091_CLEAN_ORDER_V5_V6_OK|decline=Iff|correction=lazy|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BoundaryError) as error:
        print(f"official-r091-clean-order-v5-v6: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
