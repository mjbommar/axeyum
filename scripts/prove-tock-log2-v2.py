#!/usr/bin/env python3
"""Run ADR-0336's lock-corrected Tock log2 proof scoreboard."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
BASE_PATH = REPO / "scripts/prove-tock-log2.py"
V1_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v1-registration.json"
)
V1_NEGATIVE = REPO / "bench-results/verify-tock-log2-20260721/proof-v1-negative.json"
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v2-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/proof-v2"
REGISTRATION_SCHEMA = "axeyum.tock-log2-proof-v2-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-proof-v2-result.v1"
V1_REGISTRATION_SHA256 = (
    "183728343ff8e764b659bf40e61a9eeaba176f9795006fd85d8584cc7a5ca741"
)
V1_NEGATIVE_SHA256 = (
    "8e1fbeb5f3d1becabedd9bf196bb5e90df8ace2367a228d6e3a974192af78d5a"
)
CORRECTED_LOCK_SHA256 = (
    "e9da054b3407171fcf77aa140098d30dff85f67ec9c499acf6b903b52825181f"
)


def load_base():
    spec = importlib.util.spec_from_file_location("tock_log2_proof_v1", BASE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base producer: {BASE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


BASE = load_base()
CaptureError = BASE.CaptureError
require = BASE.require
BASE_READ_REGISTRATION = BASE.read_registration


def validate_lineage(
    registration_path: Path = V1_REGISTRATION,
    negative_path: Path = V1_NEGATIVE,
) -> dict[str, Any]:
    BASE.SUPPORT.validate_file(
        registration_path,
        V1_REGISTRATION_SHA256,
        "lineage",
        "v1_registration",
    )
    BASE.SUPPORT.validate_file(
        negative_path,
        V1_NEGATIVE_SHA256,
        "lineage",
        "v1_negative",
    )
    negative = BASE.SUPPORT.read_json(negative_path)
    require(
        negative.get("schema") == "axeyum.tock-log2-proof-v1-negative.v1"
        and negative.get("status") == "rejected",
        "lineage",
        "v1_status",
        str(negative),
    )
    attempt = negative.get("attempt", {})
    outputs = negative.get("outputs", {})
    require(
        attempt.get("official_invocations") == 1
        and attempt.get("cargo_invocations") == 1
        and attempt.get("compilations_started") == 0
        and attempt.get("compilations_completed") == 0,
        "lineage",
        "v1_attempt",
        str(attempt),
    )
    require(
        outputs.get("property_queries") == 0
        and outputs.get("proofs") == 0
        and outputs.get("controls") == 0
        and outputs.get("scoreboard_rows") == 0
        and outputs.get("output_directory_exists") is False
        and outputs.get("partial_directories") == 0,
        "lineage",
        "v1_outputs",
        str(outputs),
    )
    require(
        negative.get("resource_scope", {}).get("oom_delta_failure_reported") is False,
        "lineage",
        "v1_resource",
        str(negative.get("resource_scope")),
    )
    return negative


def configure_base() -> None:
    BASE.REGISTRATION_SCHEMA = REGISTRATION_SCHEMA
    BASE.RESULT_SCHEMA = RESULT_SCHEMA


def read_registration(path: Path) -> dict[str, Any]:
    configure_base()
    registration = BASE_READ_REGISTRATION(path)
    lock_rows = [
        row for row in registration["source_files"] if row["path"] == "Cargo.lock"
    ]
    require(
        lock_rows == [{"path": "Cargo.lock", "sha256": CORRECTED_LOCK_SHA256}],
        "registration",
        "corrected_lock",
        str(lock_rows),
    )
    return registration


def run_scoreboard(args: argparse.Namespace) -> dict[str, Any]:
    validate_lineage()
    configure_base()
    original_reader = BASE.read_registration
    BASE.read_registration = read_registration
    try:
        return BASE.run_scoreboard(args)
    finally:
        BASE.read_registration = original_reader


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_scoreboard(args)
    except CaptureError as error:
        print(f"stage={error.stage}", file=sys.stderr)
        print(f"kind={error.kind}", file=sys.stderr)
        print(f"detail={error.detail}", file=sys.stderr)
        return 1
    print(f"status={result['status']}")
    print(f"identity_sha256={result['identity_sha256']}")
    print(f"output={args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
