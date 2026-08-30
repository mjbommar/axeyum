#!/usr/bin/env python3
"""Verify the fail-closed opaque public-division lift decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / (
    "artifacts/autogenesis/euclidean-public-div-add-mod-lift-decline-v1.json"
)
PLAN = ROOT / "artifacts/autogenesis/euclidean-public-div-add-mod-lift-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_div_add_mod_reconstruct.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "e4650d1d4-public-euclidean-lift-decline-v1"
)
MANIFEST = PACK / "manifest.json"


class PublicLiftDeclineError(RuntimeError):
    """The compiler seam, zero-submission boundary, or no-credit state changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PublicLiftDeclineError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-public-wrapper-lift-decline"
        or result.get("state")
        != "opaque-public-division-seam-declined-before-kernel-submission"
    ):
        raise PublicLiftDeclineError("public lift decline identity changed")
    if (
        sha256(PLAN) != "39978cbf2d05290ed4cfe459070ee1438bc7aaf1eb7ace25ab1ece76afcd04f5"
        or sha256(SOURCE)
        != "e4650d1d4ff92f40e9c1f66462be263469adb35b63fda93a9fb31ba4f5145d08"
    ):
        raise PublicLiftDeclineError("plan or authored source identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "75485603293e18ee466d7420545a890807865eb8cd045143e458d84ea64d9f9b"
    ):
        raise PublicLiftDeclineError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "stdout": (
            "compile.stdout",
            "c97f41bfd5acf1e515dea023e9c86428e0663a4cd7a93d30acb085bf48743dad",
            164,
        ),
        "stderr": (
            "compile.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
    }.items():
        row = manifest["compiler"][key]
        path = PACK / row["path"]
        if (
            row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise PublicLiftDeclineError(f"compiler {key} identity changed")
    observation = result["observation"]
    if observation != {
        "zero_divisor_branch_completed": True,
        "public_mod_to_modCore_rewrite_completed": True,
        "first_blocked_operation": "unfold Nat.div",
        "blocked_goal": "(n + 1) * (m / (n + 1)) + m.modCore (n + 1) = m",
        "nat_div_is_transparent_to_elaborator": False,
        "proof_free_div_go_to_public_div_bridge_statements": [],
        "accepted_public_support": False,
    }:
        raise PublicLiftDeclineError("measured opaque division seam changed")
    if result["budget"] != {
        "public_support_theorem_declarations": 0,
        "kernel_theorem_submissions": 0,
        "exact_fibonacci_target_submissions": 0,
        "executor_invocations": 0,
        "retries_after_kernel_decline": 0,
    }:
        raise PublicLiftDeclineError("zero-submission boundary changed")
    if result["authority"] != {
        "proof_bodies_read": 0,
        "theorem_values_read": 0,
        "balanced_bezout_reconstructions": 0,
        "coprime_cancellation_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PublicLiftDeclineError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_PUBLIC_LIFT_DECLINE_OK|blocked=Nat.div-opacity|"
            "kernel_submissions=0|accepted=0|fibonacci_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        PublicLiftDeclineError,
    ) as error:
        print(f"autogenesis-euclidean-public-lift-decline: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
