#!/usr/bin/env python3
"""Verify the bounded-induction Euclidean footprint decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/euclidean-bounded-induction-decline-v1.json"
PLAN = ROOT / "artifacts/autogenesis/euclidean-bounded-induction-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_div_add_mod_bounded_induction.lean"
TYPE_SOURCE = ROOT / "scripts/lean/autogenesis_div_add_mod_bounded_type_inventory.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "6fe0cd29e-public-euclidean-bounded-induction-decline-v1"
)
MANIFEST = PACK / "manifest.json"
EMPTY_SHA256 = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
TYPE_REPR_SHA256 = "0a0c92fdac6e526a524d7883d9676e19dc679fca46ebb25ea049df56f0d4ccbb"
DEPENDENCIES = [
    "And.left",
    "And.right",
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div_eq",
    "Nat.le_of_lt_succ",
    "Nat.le_of_succ_le_succ",
    "Nat.le_or_eq_of_le_succ",
    "Nat.le_refl",
    "Nat.lt_of_lt_of_le",
    "Nat.mod_eq",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_succ_le_zero",
    "Nat.sub_lt",
    "Nat.succ_sub_succ_eq_sub",
    "congr",
    "congrArg",
    "congrFun'",
    "if_neg",
    "if_pos",
]


class BoundedInductionDeclineError(RuntimeError):
    """The explicit-dependency decline or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BoundedInductionDeclineError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-bounded-induction-decline"
        or result.get("state")
        != "generated-recursion-removed-first-import-still-propext"
    ):
        raise BoundedInductionDeclineError("bounded induction decline identity changed")
    for path, expected, label in [
        (
            PLAN,
            "d36261b9212678fd704f7efd03b4f84c012c9fd0b7e3ea09eeffc2355968379b",
            "plan",
        ),
        (
            SOURCE,
            "6fe0cd29e1548d0dfc1b40447263b148285067b97f76533b8357860905020cf1",
            "authored source",
        ),
        (
            TYPE_SOURCE,
            "4a3ac8fe4a12a5174d4f7c702b0e028e815dad23c90209fcfc6f962f909f5c02",
            "type inventory source",
        ),
    ]:
        if sha256(path) != expected:
            raise BoundedInductionDeclineError(f"{label} identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "e8c273c1550eeffbe1fd775a667a75c18539140880ab8c15f344d3a22df39054"
    ):
        raise BoundedInductionDeclineError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "proof_bearing_stream": (
            "bounded-induction.ndjson",
            "d71692e97b7bae7ab43043ed4490a79b2134650b4bfe4d8e20220693fe033844",
            715764,
        ),
        "export_stderr": ("export.stderr", EMPTY_SHA256, 0),
    }.items():
        row = manifest[key]
        path = PACK / row["path"]
        if (
            row.get("path") != expected[0]
            or row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise BoundedInductionDeclineError(f"{key} identity or mode changed")
    if manifest["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise BoundedInductionDeclineError("proof-bearing stream became model-readable")
    first = manifest["first_kernel_import"]
    for path_key, sha_key, bytes_key, mode_key, expected in [
        (
            "summary_path",
            "summary_sha256",
            "summary_bytes",
            "summary_mode",
            ("import-1.txt", "4b38fe0f3015221cc9b55dc083bc809092c4921401579f2d2295de9d2e377258", 704),
        ),
        (
            "stderr_path",
            "stderr_sha256",
            "stderr_bytes",
            "stderr_mode",
            ("import-1.stderr", EMPTY_SHA256, 0),
        ),
    ]:
        path = PACK / first[path_key]
        if (
            first.get(path_key) != expected[0]
            or first.get(sha_key) != expected[1]
            or first.get(bytes_key) != expected[2]
            or first.get(mode_key) != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise BoundedInductionDeclineError("first kernel import evidence changed")
    observation = result["observation"]
    if (
        observation.get("authored_type_repr_sha256") != TYPE_REPR_SHA256
        or observation.get("official_type_repr_sha256") != TYPE_REPR_SHA256
        or observation.get("exact_type_match") is not True
        or observation.get("first_import_exit_status") != 0
        or observation.get("declaration_sha256")
        != "4a19626c02c927336e2c88f024d30582127b5f0d98998bf712d013fe3162ebfa"
        or observation.get("axiom_footprint") != ["propext"]
        or observation.get("direct_theorem_dependencies") != DEPENDENCIES
        or observation.get("generated_recursion_dependencies") != []
        or observation.get("generated_recursion_removed") is not True
        or observation.get("accepted_public_support") is not False
        or observation.get("second_submission_skipped") is not True
    ):
        raise BoundedInductionDeclineError("measured bounded-induction seam changed")
    if any("divAddModBoundedInduction." in name for name in DEPENDENCIES):
        raise BoundedInductionDeclineError("generated recursion dependency reappeared")
    if result["budget"] != {
        "revised_source_paths": 1,
        "public_support_theorem_declarations": 1,
        "kernel_theorem_submissions": 1,
        "exact_fibonacci_target_submissions": 0,
        "executor_invocations": 0,
        "retries_after_kernel_decline": 0,
    }:
        raise BoundedInductionDeclineError("first-decline budget changed")
    if result["authority"] != {
        "proof_bodies_read": 0,
        "theorem_values_read": 0,
        "balanced_bezout_reconstructions": 0,
        "coprime_cancellation_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise BoundedInductionDeclineError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_BOUNDED_INDUCTION_DECLINE_OK|"
            "type=exact|generated_recursion=0|dependencies=22|"
            "footprint=propext|second_skipped=1|accepted=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        BoundedInductionDeclineError,
    ) as error:
        print(f"autogenesis-euclidean-bounded-induction-decline: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
