#!/usr/bin/env python3
"""Verify the fail-closed first Euclidean construction decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/euclidean-joint-div-mod-proof-decline-v1.json"
CAPSULE = ROOT / "artifacts/autogenesis/euclidean-joint-div-mod-proof-capsule-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_div_mod_go_reconstruct.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "2387f116f-proof-isolated-div-mod-go-decline-v1"
)
MANIFEST = PACK / "manifest.json"

CAPSULE_SHA256 = "17ef795517c8373a52889597f859cc1d5a75fa74b3a0c38bf334c4f523eb14f1"
SOURCE_SHA256 = "2387f116f1eb94cb0d46027f100f5912d186094d229af2f16f421398be118a80"
MANIFEST_SHA256 = "f4dfdeec6ec422bf63748e4a6629d128d3b8487d82da9fb2df92d8db96312601"
DEPENDENCIES = [
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div.go.eq_1",
    "Nat.div_rec_fuel_lemma",
    "Nat.modCore.go.eq_1",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_lt_zero",
    "Nat.sub_add_cancel",
    "congr",
    "congrArg",
    "congrFun'",
    "dif_neg",
    "dif_pos",
]


class DeclineError(RuntimeError):
    """The failed proof identity, stop boundary, or no-credit state changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise DeclineError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-proof-isolated-euclidean-construction-decline"
        or result.get("state") != "first-reconstruction-declined-no-second-run-or-credit"
    ):
        raise DeclineError("decline identity changed")
    if sha256(CAPSULE) != CAPSULE_SHA256 or sha256(SOURCE) != SOURCE_SHA256:
        raise DeclineError("capsule or independently authored source changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise DeclineError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "proof_bearing_stream": (
            "div-mod-go-reconstruct.ndjson",
            "b4793d50d2ef0d69786d28d044012f74d5f5f2279bf5d5a55e39acf0ffb1af7a",
            460363,
        ),
        "export_stderr": (
            "export.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
        "first_import_summary": (
            "import-1.txt",
            "0f500dafa448857f63547801df027dc4fe8af16ecf4b059ca1e79888e689cf93",
            599,
        ),
    }.items():
        row = manifest[key]
        path = PACK / row["path"]
        if (
            row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise DeclineError(f"{key} identity or mode changed")
    if manifest["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise DeclineError("proof-bearing stream became model-readable")
    theorem = manifest["first_import_summary"]["theorem"]
    observation = result["observation"]
    if (
        theorem.get("name") != "Axeyum.Autogenesis.divModGoReconstruct"
        or theorem.get("declaration_sha256")
        != "8c496681b3d26c68e0d915791fd5163eaa429dbf4259f722854286fe8fcd1271"
        or theorem.get("axiom_footprint") != ["propext"]
        or theorem.get("direct_theorem_dependencies") != DEPENDENCIES
        or observation.get("axiom_footprint") != ["propext"]
        or observation.get("direct_theorem_dependencies") != DEPENDENCIES
        or observation.get("required_axiom_footprint") != []
        or observation.get("accepted") is not False
        or observation.get("decline_reason") != "nonempty-kernel-derived-axiom-footprint"
    ):
        raise DeclineError("measured theorem decline changed")
    if result["budget"] != {
        "fresh_reconstructions_attempted": 1,
        "fresh_reconstructions_planned": 2,
        "second_reconstruction_run": False,
        "support_theorems_accepted": 0,
        "kernel_theorem_submissions": 1,
        "exact_target_submissions": 0,
        "retries": 0,
    }:
        raise DeclineError("fail-closed stop boundary changed")
    if result["authority"] != {
        "proof_bodies_read": 0,
        "theorem_values_read": 0,
        "executor_invocations": 0,
        "semantic_theorem_receipts": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise DeclineError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_PROOF_DECLINE_OK|attempted=1/2|accepted=0|"
            "footprint=propext|second_run=false|target_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, DeclineError) as error:
        print(f"autogenesis-euclidean-proof-decline: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
