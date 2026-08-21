#!/usr/bin/env python3
"""Verify deterministic official Acc and cancellation composition evidence."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-cancellation-acc-package-composition-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-cancellation-acc-package-composition-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/b26edf6aa-official-cancellation-acc-package-composition-v1")
PLAN_SHA = "5f92ad135d33a8715d327755055b48a81cd5ebb61a8262eb0c242aec6d2c63c6"
MANIFEST_SHA = "fda89891b57fa88c8453c16f4d5175638a40b1dfa6e360b89bbfb9c8af43ee1b"
RECEIPT_SHA = "bef90af9e0873162281365f8bbdb0902c096d04790b56c57bb8dc0daca5cd626"
ROOT_NAME = "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1"
ACC = {
    "Acc": "ae8b799311c1ef25f167d7413eb10abf55df398053cf994f953bd31624f96e27",
    "Acc.intro": "73c42b8287c3b2b680731deb89003732efda90b571c0dd737a81cbcf2ef024c2",
    "Acc.rec": "67cc978e963fa24e78a117380175be35753a051986230e1c5f2fd2b3a2df85ac",
}


class CompositionResultError(RuntimeError):
    """The accepted package, theorem, receipt, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CompositionResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (
        1,
        "axeyum-autogenesis-official-cancellation-acc-package-composition-result",
        "exact-official-acc-and-cancellation-compose-twice-byte-identically-empty-footprint",
    ):
        raise CompositionResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA or result["plan"]["sha256"] != PLAN_SHA:
        raise CompositionResultError("plan identity changed")
    if sha256(PACK / "manifest.json") != MANIFEST_SHA:
        raise CompositionResultError("manifest identity changed")
    receipts = [PACK / "composition-1.json", PACK / "composition-2.json"]
    if any(sha256(path) != RECEIPT_SHA for path in receipts):
        raise CompositionResultError("composition receipts differ")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(
        stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()
    ):
        raise CompositionResultError("evidence pack is not sealed")
    receipt = load(receipts[0])
    acc_rows = [row for row in receipt["added_singleton_inductives"] if row["family"] == "Acc"]
    if len(acc_rows) != 1 or acc_rows[0]["source_declaration_sha256"] != ACC or acc_rows[0]["target_declaration_sha256"] != ACC:
        raise CompositionResultError("official Acc package identity changed")
    roots = [row for row in receipt["added_theorems"] if row["name"] == ROOT_NAME]
    if len(roots) != 1 or roots[0]["axiom_footprint"] or roots[0]["source_declaration_sha256"] != roots[0]["target_declaration_sha256"]:
        raise CompositionResultError("cancellation root evidence changed")
    if (len(receipt["reused_declarations"]), len(receipt["added_definitions"]), len(receipt["added_singleton_inductives"]), len(receipt["added_theorems"])) != (250, 51, 8, 75):
        raise CompositionResultError("receipt population changed")
    for key in ("support_credit", "target_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if result["authority"][key] != 0:
            raise CompositionResultError("downstream authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_ACC_PACKAGE_RESULT_OK|runs=2|Acc=exact|cancellation=empty-footprint")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CompositionResultError) as error:
        print(f"official-cancellation-acc-package-composition-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
