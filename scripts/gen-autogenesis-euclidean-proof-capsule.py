#!/usr/bin/env python3
"""Generate the proof-isolated statement capsule for the Euclidean bridge."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/euclidean-joint-div-mod-proof-capsule-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
AUDIT_MANIFEST = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "62858ff72-lean430-div-mod-equations-v1/manifest.json"
)
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "mathlib-nat-gcd-fib-add-self-euclidean-bridge-plan-v1.json"
)
ROOT_AUDIT = ROOT / (
    "artifacts/autogenesis/"
    "mathlib-nat-gcd-fib-add-self-euclidean-root-audit-result-v1.json"
)

INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
AUDIT_MANIFEST_SHA256 = "3c53903f86a43e516751d6f440e2472bd987df799db3948ae8cd49754e28a130"
PLAN_SHA256 = "a0e9099ee41c1e54d408e0ea86d13c28518749971e37e726ba9d6fe7ebfd40e5"
ROOT_AUDIT_SHA256 = "acb9f497b28b837a8dd1eb87295658f31485f297d0c160cf8db264847cdc7567"

ALLOWED_NAMES = [
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div.go.eq_1",
    "Nat.div_add_mod",
    "Nat.div_rec_fuel_lemma",
    "Nat.mod.eq_2",
    "Nat.modCore.go.eq_1",
    "Nat.mod_lt",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_lt_zero",
    "Nat.sub_add_cancel",
    "Nat.zero_lt_succ",
]
AUDITED_ROOTS = {
    "Nat.div.go.eq_1": "c31f2e764891ad2ce5d2d1e59638636302c236096f8fefd91dfaa9f289155763",
    "Nat.modCore.go.eq_1": "aaf85a61edef7f6416bfccd8d817ca53c88cf7fe3d5b34bfbf166287e485448d",
    "Nat.mod.eq_2": "47a0f25d2575086bb8d8ad687beca4e69ef71644bb6057f55ec052d5c2084610",
}


class CapsuleError(RuntimeError):
    """The capsule input, statement set, isolation policy, or output changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def checked_source(path: pathlib.Path, expected_sha256: str) -> None:
    if stat.S_IMODE(path.stat().st_mode) != 0o444 or sha256(path) != expected_sha256:
        raise CapsuleError(f"{path} changed or is mutable")


def selected_statements() -> list[dict[str, str]]:
    checked_source(INVENTORY, INVENTORY_SHA256)
    selected: dict[str, dict[str, str]] = {}
    with INVENTORY.open() as rows:
        for line_number, line in enumerate(rows, 1):
            row = json.loads(line)
            name = row.get("name")
            if name not in ALLOWED_NAMES:
                continue
            if name in selected:
                raise CapsuleError(f"duplicate statement {name} at line {line_number}")
            if not all(isinstance(row.get(key), str) for key in ("module", "type", "type_repr")):
                raise CapsuleError(f"incomplete statement row {name}")
            selected[name] = {
                "name": name,
                "module": row["module"],
                "type": row["type"],
                "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
                "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
            }
    missing = sorted(set(ALLOWED_NAMES) - set(selected))
    if missing:
        raise CapsuleError(f"missing statements: {', '.join(missing)}")
    return [selected[name] for name in ALLOWED_NAMES]


def build_capsule() -> dict[str, Any]:
    checked_source(AUDIT_MANIFEST, AUDIT_MANIFEST_SHA256)
    if sha256(PLAN) != PLAN_SHA256 or sha256(ROOT_AUDIT) != ROOT_AUDIT_SHA256:
        raise CapsuleError("tracked bridge input changed")
    manifest = json.loads(AUDIT_MANIFEST.read_text())
    audited = manifest.get("audit", {}).get("theorems", {})
    if (
        {name: row.get("declaration_sha256") for name, row in audited.items()}
        != AUDITED_ROOTS
        or any(row.get("axiom_footprint") != [] for row in audited.values())
    ):
        raise CapsuleError("audited root identity or footprint changed")
    stream = manifest["stream"]
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-proof-isolated-statement-capsule",
        "capsule_id": "euclidean-joint-div-mod-fuel-invariant-v1",
        "state": "generated-proof-free-construction-input-no-proof-credit",
        "sources": {
            "statement_inventory": {
                "path": str(INVENTORY),
                "sha256": INVENTORY_SHA256,
                "mode": "0444",
            },
            "bridge_plan": {
                "path": str(PLAN.relative_to(ROOT)),
                "sha256": PLAN_SHA256,
            },
            "root_audit_result": {
                "path": str(ROOT_AUDIT.relative_to(ROOT)),
                "sha256": ROOT_AUDIT_SHA256,
            },
            "equation_root_manifest": {
                "path": str(AUDIT_MANIFEST),
                "sha256": AUDIT_MANIFEST_SHA256,
                "mode": "0444",
            },
        },
        "allowed_statements": selected_statements(),
        "audited_computation_roots": [
            {
                "name": name,
                "declaration_sha256": declaration_sha256,
                "axiom_footprint": [],
            }
            for name, declaration_sha256 in AUDITED_ROOTS.items()
        ],
        "proof_bearing_kernel_input": {
            "path": str(AUDIT_MANIFEST.parent / stream["path"]),
            "sha256": stream["sha256"],
            "textual_read_allowed": False,
            "allowed_consumer": "axeyum-lean-import kernel admission only",
        },
        "construction_contract": {
            "theorem_name": "Axeyum.Autogenesis.divModGoReconstruct",
            "statement": (
                "forall y (hy : 0 < y) fuel x (hfuel : x < fuel), "
                "y * Nat.div.go y hy fuel x hfuel + "
                "Nat.modCore.go y hy fuel x hfuel = x"
            ),
            "method": (
                "induction on shared fuel using the audited quotient and remainder "
                "equations plus explicit subtraction restoration"
            ),
            "fresh_reconstructions": 2,
            "required_axiom_footprint": [],
            "exact_target_submissions": 0,
        },
        "isolation_policy": {
            "allowed_inputs": [
                "this capsule",
                "independently authored Lean source",
                "compiler diagnostics from that source",
                "kernel audit summaries without proof terms",
            ],
            "forbidden_inputs": [
                "Mathlib or Lean theorem source bodies",
                "olean theorem values",
                "textual reads of full or root-selected lean4export streams",
                "upstream proof terms or tactic scripts",
                "the contaminated predecessor conversation or source-viewing transcript",
            ],
            "on_violation": (
                "discard authored proof work, issue zero proof credit, and restart in a "
                "fresh context from this capsule"
            ),
        },
        "authority": {
            "proof_search_invocations": 0,
            "kernel_theorem_submissions": 0,
            "exact_source_target_submissions": 0,
            "executor_invocations": 0,
            "semantic_theorem_receipts": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": (
            "This generated capsule contains theorem statements and identities only. "
            "It proves nothing and grants no permission to read proof-bearing artifacts."
        ),
    }


def validate_capsule(capsule: dict[str, Any]) -> None:
    expected = build_capsule()
    if capsule != expected:
        raise CapsuleError("capsule differs from generated proof-isolated contract")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        capsule = build_capsule()
        rendered = canonical(capsule)
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != rendered:
                raise CapsuleError(f"{OUTPUT.relative_to(ROOT)} is stale")
            print(
                "AUTOGENESIS_EUCLIDEAN_PROOF_CAPSULE_OK|statements=13|roots=3|"
                "proof_bodies=0|submissions=0|evaluation=0|ledger_writes=0"
            )
        else:
            OUTPUT.write_text(rendered)
            print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CapsuleError) as error:
        print(f"autogenesis-euclidean-proof-capsule: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
