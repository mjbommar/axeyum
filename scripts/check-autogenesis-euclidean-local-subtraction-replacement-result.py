#!/usr/bin/env python3
"""Verify the twice-reconstructed local subtraction replacement result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-local-subtraction-replacement-result-v1.json"
)
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-local-subtraction-replacement-plan-v1.json"
)
ADDENDUM = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-local-subtraction-equation-addendum-v1.json"
)
SOURCE = ROOT / "scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean"
V1_SOURCE = ROOT / "scripts/lean/autogenesis_div_mod_go_reconstruct.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "d6daa848b-proof-isolated-div-mod-go-v2-v1"
)
MANIFEST = PACK / "manifest.json"
DEPENDENCIES = [
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div.go.eq_1",
    "Nat.div_rec_fuel_lemma",
    "Nat.le_of_succ_le_succ",
    "Nat.modCore.go.eq_1",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_lt_zero",
    "Nat.not_succ_le_zero",
    "Nat.succ_sub_succ_eq_sub",
    "congr",
    "congrArg",
    "congrFun'",
    "dif_neg",
    "dif_pos",
]


class ReplacementResultError(RuntimeError):
    """The accepted theorem, two-run evidence, or no-public-credit state changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ReplacementResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-local-subtraction-replacement-result"
        or result.get("state")
        != "private-joint-invariant-reconstructed-twice-empty-footprint"
    ):
        raise ReplacementResultError("replacement result identity changed")
    for path, expected, label in [
        (
            PLAN,
            "6a54f6d3a3fddc279e3718aeed1293be503f9092e7da84869edbe67f0e329420",
            "plan",
        ),
        (
            ADDENDUM,
            "87858ff825369c5900eb7707e7ffff578634c4e1f31f36686efc7320cb117aec",
            "statement addendum",
        ),
        (
            SOURCE,
            "d6daa848bea4fe5a86e9d180f2256a8b0851d44b3dd9c7245ab0c71d344599bf",
            "V2 source",
        ),
        (
            V1_SOURCE,
            "2387f116f1eb94cb0d46027f100f5912d186094d229af2f16f421398be118a80",
            "V1 source",
        ),
    ]:
        if sha256(path) != expected:
            raise ReplacementResultError(f"{label} identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "e140c77f571b73a45bfe7260ca5a9ffc56555201538a3684e3783644fc2de777"
    ):
        raise ReplacementResultError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "proof_bearing_stream": (
            "div-mod-go-reconstruct-v2.ndjson",
            "307e23b8587db00eda2f08210e8ec9624719f440469126c99c3c8db877f83133",
            432549,
        ),
        "export_stderr": (
            "export.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
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
            raise ReplacementResultError(f"{key} identity or mode changed")
    if manifest["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise ReplacementResultError("proof-bearing stream became model-readable")
    runs = manifest.get("reconstructions")
    if not isinstance(runs, list) or len(runs) != 2:
        raise ReplacementResultError("fresh reconstruction count changed")
    for index, run in enumerate(runs, 1):
        path = PACK / run["summary_path"]
        if (
            run.get("run") != index
            or run.get("summary_sha256")
            != "c686c6fc94cb77949d97300beb1a1a0ade26ea28474ad6edbeed2a94c2e49b1d"
            or run.get("summary_bytes") != 642
            or run.get("summary_mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or sha256(path) != run["summary_sha256"]
        ):
            raise ReplacementResultError(f"reconstruction {index} identity changed")
    theorem = result["theorem"]
    if (
        theorem.get("name") != "Axeyum.Autogenesis.divModGoReconstruct"
        or theorem.get("declaration_sha256")
        != "f8d6592cd39d5f249acf0f695b1d77bd255dc9f630e3a588a0044fe62d3360a4"
        or theorem.get("axiom_footprint") != []
        or theorem.get("direct_theorem_dependencies") != DEPENDENCIES
        or theorem.get("forbidden_dependencies_present") != []
        or theorem.get("fresh_reconstructions") != 2
        or theorem.get("identities_match") is not True
        or theorem.get("accepted_private_support") is not True
    ):
        raise ReplacementResultError("accepted theorem evidence changed")
    if any(
        forbidden in theorem["direct_theorem_dependencies"]
        for forbidden in ["Nat.sub_add_cancel", "Nat.add_sub_of_le"]
    ):
        raise ReplacementResultError("forbidden dependency reappeared")
    if result["budget"] != {
        "revised_source_paths": 1,
        "new_support_theorem_declarations": 1,
        "kernel_theorem_submissions": 2,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
        "retries_after_kernel_decline": 0,
    }:
        raise ReplacementResultError("reconstruction budget changed")
    if result["authority"] != {
        "public_euclidean_lift_submissions": 0,
        "balanced_bezout_reconstructions": 0,
        "coprime_cancellation_reconstructions": 0,
        "semantic_theorem_receipts": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ReplacementResultError("private-support authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_LOCAL_SUB_REPLACEMENT_OK|reconstructions=2/2|"
            "identity=f8d6592cd39d|footprint=empty|forbidden_deps=0|"
            "public_lifts=0|target_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ReplacementResultError,
    ) as error:
        print(f"autogenesis-euclidean-local-sub-replacement-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
