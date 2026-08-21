#!/usr/bin/env python3
"""Verify the fail-closed public Euclidean recursion decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/euclidean-public-recursion-decline-v1.json"
PLAN = ROOT / "artifacts/autogenesis/euclidean-public-recursion-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_div_add_mod_public_recursion.lean"
TYPE_SOURCE = ROOT / "scripts/lean/autogenesis_div_add_mod_type_inventory.lean"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "52721420e-public-euclidean-recursion-decline-v1"
)
MANIFEST = PACK / "manifest.json"
EMPTY_SHA256 = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
TYPE_REPR_SHA256 = "0a0c92fdac6e526a524d7883d9676e19dc679fca46ebb25ea049df56f0d4ccbb"


class PublicRecursionDeclineError(RuntimeError):
    """The exact-type, first-decline, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PublicRecursionDeclineError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-public-recursion-decline"
        or result.get("state")
        != "exact-public-equation-declined-after-first-propext-kernel-import"
    ):
        raise PublicRecursionDeclineError("public recursion decline identity changed")
    for path, expected, label in [
        (
            PLAN,
            "1d5fad47b16a2d6cae1f3e9c3c5ae332a0a9e19d0a0f7297f2e09940e5fdec35",
            "plan",
        ),
        (
            SOURCE,
            "52721420e47706b35ebfe600b9a81c9019c0015304e9e79ebe20f3001a1f5c50",
            "authored source",
        ),
        (
            TYPE_SOURCE,
            "25b9fd758da84fbd843850b1996a4f91e435de948fb1bee6d7d04837b3bc61ea",
            "type inventory source",
        ),
    ]:
        if sha256(path) != expected:
            raise PublicRecursionDeclineError(f"{label} identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "9d4c00992ffab48b6ac5bf7b2b620c677aa6c5b3b50955ba1024486099725444"
    ):
        raise PublicRecursionDeclineError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    immutable_files = {
        "type_inventory": (
            "type-inventory.ndjson",
            "22946b45773092ab4bb694b6114f55ef88bf3830dbcdb26987b30e16126d20f7",
            3237,
        ),
        "proof_bearing_stream": (
            "public-recursion.ndjson",
            "a0b36eabbaf7cf4363f03435469cb376417ba567cda2e769844fa18616123b20",
            631701,
        ),
        "export_stderr": ("export.stderr", EMPTY_SHA256, 0),
    }
    for key, expected in immutable_files.items():
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
            raise PublicRecursionDeclineError(f"{key} identity or mode changed")
    if manifest["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise PublicRecursionDeclineError("proof-bearing stream became model-readable")
    first = manifest["first_kernel_import"]
    for path_key, sha_key, bytes_key, mode_key, expected in [
        (
            "summary_path",
            "summary_sha256",
            "summary_bytes",
            "summary_mode",
            ("import-1.txt", "2f15cb3131670532861d0cbf8917abc3b4170c5f02df2b4adda3b45c806ea92b", 462),
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
            raise PublicRecursionDeclineError("first kernel import evidence changed")
    observation = result["observation"]
    if observation != {
        "authored_type_repr_sha256": TYPE_REPR_SHA256,
        "official_type_repr_sha256": TYPE_REPR_SHA256,
        "exact_type_match": True,
        "first_import_exit_status": 0,
        "declaration_sha256": "00d72d9368679215749fcc9d33f3aa3ad3c7d3301cc67835029e100f1f141a69",
        "axiom_footprint": ["propext"],
        "direct_theorem_dependencies": [
            "Axeyum.Autogenesis.divAddModPublicRecursion._unary"
        ],
        "generated_recursion_dependency_count": 1,
        "accepted_public_support": False,
        "second_submission_skipped": True,
    }:
        raise PublicRecursionDeclineError("measured recursion seam changed")
    if result["budget"] != {
        "revised_source_paths": 1,
        "public_support_theorem_declarations": 1,
        "kernel_theorem_submissions": 1,
        "exact_fibonacci_target_submissions": 0,
        "executor_invocations": 0,
        "retries_after_kernel_decline": 0,
    }:
        raise PublicRecursionDeclineError("first-decline budget changed")
    if result["authority"] != {
        "proof_bodies_read": 0,
        "theorem_values_read": 0,
        "balanced_bezout_reconstructions": 0,
        "coprime_cancellation_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PublicRecursionDeclineError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_PUBLIC_RECURSION_DECLINE_OK|"
            "type=exact|kernel_submissions=1/2|footprint=propext|"
            "second_skipped=1|accepted=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        PublicRecursionDeclineError,
    ) as error:
        print(f"autogenesis-euclidean-public-recursion-decline: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
