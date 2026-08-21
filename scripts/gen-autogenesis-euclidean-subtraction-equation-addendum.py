#!/usr/bin/env python3
"""Generate the proof-free subtraction-equation addendum for Euclidean V2."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-local-subtraction-equation-addendum-v1.json"
)
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-local-subtraction-replacement-plan-v1.json"
)
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)

PLAN_SHA256 = "6a54f6d3a3fddc279e3718aeed1293be503f9092e7da84869edbe67f0e329420"
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
NAME = "Nat.succ_sub_succ_eq_sub"


class AddendumError(RuntimeError):
    """The statement identity, use scope, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def row_sha256(row: dict[str, Any]) -> str:
    encoded = json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def selected_statement() -> dict[str, Any]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise AddendumError("statement inventory changed or is mutable")
    selected: dict[str, Any] | None = None
    with INVENTORY.open() as source:
        for line_number, line in enumerate(source, 1):
            row = json.loads(line)
            if row.get("name") != NAME:
                continue
            if selected is not None:
                raise AddendumError(f"duplicate statement at row {line_number}")
            selected = row
    if selected is None:
        raise AddendumError("subtraction equation is absent")
    if (
        selected.get("module") != "Init.Prelude"
        or selected.get("type") != "∀ (n m : ℕ), n.succ - m.succ = n - m"
        or hashlib.sha256(selected["type"].encode()).hexdigest()
        != "8385e10288e30a041b9d2a2e35552dc76171966d22110b03521e313da78bf850"
        or hashlib.sha256(selected["type_repr"].encode()).hexdigest()
        != "5ccab900ba0a1faf682bc498f34ddd1fdf0c20c4fb0f39cd4841522f383696c3"
        or row_sha256(selected)
        != "898d1ff7c17c268a9323d0fdd0fc55a753d43f58c0d0c0db6741dceef21b0045"
    ):
        raise AddendumError("subtraction equation statement changed")
    return {
        "name": NAME,
        "module": selected["module"],
        "type": selected["type"],
        "type_sha256": "8385e10288e30a041b9d2a2e35552dc76171966d22110b03521e313da78bf850",
        "type_repr_sha256": "5ccab900ba0a1faf682bc498f34ddd1fdf0c20c4fb0f39cd4841522f383696c3",
        "source_row_sha256": "898d1ff7c17c268a9323d0fdd0fc55a753d43f58c0d0c0db6741dceef21b0045",
    }


def build() -> dict[str, Any]:
    if sha256(PLAN) != PLAN_SHA256:
        raise AddendumError("local replacement plan changed")
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-proof-free-subtraction-equation-addendum",
        "state": "one-statement-bound-before-v2-kernel-submission",
        "predecessor_plan": {
            "path": str(PLAN.relative_to(ROOT)),
            "sha256": PLAN_SHA256,
        },
        "source_inventory": {
            "path": str(INVENTORY),
            "sha256": INVENTORY_SHA256,
            "mode": "0444",
        },
        "compiler_observation": {
            "opaque_constant": "Nat.sub",
            "blocked_local_branch": "successor dividend and successor subtrahend",
            "kernel_theorem_submissions_before_addendum": 0,
        },
        "allowed_statement": selected_statement(),
        "use_scope": {
            "source_path": "scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean",
            "only_allowed_use": "reduce the successor-successor Nat.sub occurrence inside the local hrestore proof",
            "additional_statement_names_allowed": 0,
            "official_proof_may_be_read": False,
            "eventual_target_footprint_must_be_empty": True,
            "forbidden_theorem_dependencies": [
                "Nat.sub_add_cancel",
                "Nat.add_sub_of_le",
            ],
        },
        "authority": {
            "proof_bodies_read": 0,
            "theorem_values_read": 0,
            "proof_search_invocations": 0,
            "kernel_theorem_submissions": 0,
            "exact_target_submissions": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": (
            "The addendum exposes one proposition only. It does not establish the "
            "official equation proof's footprint or grant theorem credit."
        ),
    }


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate(value: dict[str, Any]) -> None:
    if value != build():
        raise AddendumError("addendum differs from generated statement contract")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        value = build()
        expected = render(value)
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != expected:
                raise AddendumError(f"{OUTPUT.relative_to(ROOT)} is stale")
            print(
                "AUTOGENESIS_EUCLIDEAN_SUB_EQUATION_ADDENDUM_OK|statements=1|"
                "proof_bodies=0|submissions=0|evaluation=0|ledger_writes=0"
            )
        else:
            OUTPUT.write_text(expected)
            print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, AddendumError) as error:
        print(f"autogenesis-euclidean-sub-equation-addendum: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
