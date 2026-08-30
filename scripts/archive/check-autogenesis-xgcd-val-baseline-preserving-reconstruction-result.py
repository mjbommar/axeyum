#!/usr/bin/env python3
"""Verify the twice-imported propext-bearing rfl projection result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/xgcd-val-baseline-preserving-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-baseline-preserving-reconstruction-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "1e74d4601-xgcd-val-baseline-preserving-v1"
)
MANIFEST = PACK / "manifest.json"
RESULT_SHA256 = "9246ec6f9df1736679819a78cf5bdb5c4e5f7b2dbc77a9c4c89a2c1f46923828"
PLAN_SHA256 = "96739ef717856624b2934d205e58a1fcf5e598bdd864da7493bc014a7e671b6f"
MANIFEST_SHA256 = "6d5838bded7408ada8a6e1babced0a2eb3d7ee4962c8ed0fe6106a5847d7fe00"


class XgcdValBaselineResultError(RuntimeError):
    """The two imports, restored baseline, route decision, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValBaselineResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise XgcdValBaselineResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise XgcdValBaselineResultError("measured baseline result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-xgcd-val-baseline-preserving-reconstruction-result"
        or result.get("state")
        != "rfl-projection-remains-propext-bearing-public-xgcd-surface-closed"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise XgcdValBaselineResultError("result producer or pack changed")
    identities = [
        ("AxeyumAutogenesisXgcdVal.lean", 322, "077e5c6320ac8972ca18edb0b75226faac0b062b726609e9d7a213b7f27d2e62"),
        ("AxeyumAutogenesisXgcdVal.olean", 6_016, "ed34656d2c1d923f73fb69426afbdb5a2200a3ea483c20b814607003feda6d64"),
        ("AxeyumAutogenesisXgcdVal.ilean", 863, "873e45ce2a0ea8309439e8505cf6702bd0211cda1e3a13c444b4a6c5ee510ebe"),
        ("xgcd-val-direct.ndjson", 463_226, "1180a739ab86bcc2f1faa75fb34fad70e519a541fe4f35014b2ca840ea0563cd"),
        ("audit-1.json", 1_027, "41a4df5a15fe5d6075ae8cdb25a720d0661b30a814e6e2504c5f2303a4296e92"),
        ("audit-2.json", 1_027, "41a4df5a15fe5d6075ae8cdb25a720d0661b30a814e6e2504c5f2303a4296e92"),
        ("postflight.json", 842, "a8717f744505bfd492c55c5c7f88667d7eaa988452ecde7819ce98c1ba5ebb83"),
    ]
    empty = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    identities.extend(
        (name, 0, empty)
        for name in [
            "compile.stdout",
            "compile.stderr",
            "export.stderr",
            "audit-1.stderr",
            "audit-2.stderr",
        ]
    )
    for name, size, digest in identities:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise XgcdValBaselineResultError(f"{name} changed")
    audit_one = load(PACK / "audit-1.json")
    audit_two = load(PACK / "audit-2.json")
    row = result.get("measured_row")
    if (
        audit_one != audit_two
        or audit_one.get("rows") != [row]
        or audit_one.get("ordered_roots")
        != ["Axeyum.Autogenesis.xgcdValDirect"]
        or audit_one.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or row
        != {
            "name": "Axeyum.Autogenesis.xgcdValDirect",
            "declaration_sha256": "fc9c5089a789d624a685a42050b433edfeea329508ebb0ccf5a7b9425c4a374d",
            "class": "propext-bearing",
            "axiom_footprint": ["propext"],
            "direct_theorem_dependencies": [],
        }
    ):
        raise XgcdValBaselineResultError("two-import measurement changed")
    postflight = load(PACK / "postflight.json")
    if (
        postflight.get("baseline_identity_matched_before") is not True
        or postflight.get("baseline_identity_matched_after") is not True
        or postflight.get("planned_temporary_paths_present_after") != 0
        or len(postflight.get("cleanup_scope", [])) != 3
    ):
        raise XgcdValBaselineResultError("baseline restoration changed")
    if result.get("outcome") != {
        "source_compiled": True,
        "compile_exit": 0,
        "exported": True,
        "kernel_imports": 2,
        "audit_rows_identical": True,
        "definitional_equality_elaborated": True,
        "axiom_footprint_empty": False,
        "projection_equation_accepted": False,
        "preexisting_baseline_restored": True,
        "planned_temporary_paths_present_after": 0,
        "conclusion": "the public xgcd/gcdA/gcdB definitional surface itself reaches propext even for an rfl theorem",
    }:
        raise XgcdValBaselineResultError("route conclusion changed")
    if result.get("budget") != {
        "source_copies": 1,
        "source_compilations": 1,
        "exporter_invocations": 1,
        "importer_runs": 2,
        "proof_bearing_stream_reads": 2,
        "retries": 0,
        "new_theorem_submissions": 2,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "preexisting_files_changed_or_removed": 0,
        "projection_equation_credit": 0,
        "extended_gcd_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValBaselineResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_BASELINE_RESULT_OK|compiled=1|imports=2|"
            "footprint=propext|baseline_restored=1|projection_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValBaselineResultError,
    ) as error:
        print(f"autogenesis-xgcd-val-baseline-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
