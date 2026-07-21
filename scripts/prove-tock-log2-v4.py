#!/usr/bin/env python3
"""Run ADR-0338's prefix-corrected Tock log2 scoreboard."""

from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
V3_PATH = REPO / "scripts/prove-tock-log2-v3.py"
V3_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v3-registration.json"
)
V3_PREFLIGHT = REPO / "bench-results/verify-tock-log2-20260721/proof-v3-preflight.json"
V3_NEGATIVE = REPO / "bench-results/verify-tock-log2-20260721/proof-v3-negative.json"
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v4-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/proof-v4"
REGISTRATION_SCHEMA = "axeyum.tock-log2-proof-v4-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-proof-v4-result.v1"
V3_REGISTRATION_SHA256 = (
    "a458ce330969d397b74306a41b056014c4969d305e8a77cd13ac2af467227960"
)
V3_PREFLIGHT_SHA256 = (
    "1d7505f8654557a1a05ba02134e82c3c4cd621b1bf42c6961681c5ab4e2e5286"
)
V3_NEGATIVE_SHA256 = (
    "31cfa00951cfa5f7cad5e8113424dc26d97c16586483dc6c0f57e6c3a97ae075"
)
CORRECTED_LOCK_SHA256 = (
    "e9da054b3407171fcf77aa140098d30dff85f67ec9c499acf6b903b52825181f"
)
HARNESS_PREFIX = "test authenticated_tock_log2_scoreboard ... "
MARKERS = ("TOCK_PROOF|", "TOCK_CONTROL|", "TOCK_SCOREBOARD|")


def load_v3():
    spec = importlib.util.spec_from_file_location("tock_log2_proof_v3_base", V3_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load v3 producer: {V3_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


V3 = load_v3()
BASE = V3.BASE
CaptureError = V3.CaptureError
require = V3.require


def validate_lineage(
    registration_path: Path = V3_REGISTRATION,
    preflight_path: Path = V3_PREFLIGHT,
    negative_path: Path = V3_NEGATIVE,
) -> dict[str, Any]:
    for path, digest, kind in (
        (registration_path, V3_REGISTRATION_SHA256, "v3_registration"),
        (preflight_path, V3_PREFLIGHT_SHA256, "v3_preflight"),
        (negative_path, V3_NEGATIVE_SHA256, "v3_negative"),
    ):
        BASE.SUPPORT.validate_file(path, digest, "lineage", kind)
    negative = BASE.SUPPORT.read_json(negative_path)
    attempt = negative.get("attempt", {})
    error = negative.get("error", {})
    outputs = negative.get("outputs", {})
    require(
        negative.get("schema") == "axeyum.tock-log2-proof-v3-negative.v1"
        and negative.get("status") == "rejected"
        and attempt.get("official_invocations") == 1
        and attempt.get("cargo_test_exit_code") == 0
        and attempt.get("property_queries_completed_in_test") == 8
        and attempt.get("controls_completed_in_test") == 6
        and attempt.get("scoreboard_emitted_by_test") is True,
        "lineage",
        "v3_status",
        str(negative),
    )
    require(
        error.get("stage") == "result"
        and error.get("kind") == "proof_count"
        and error.get("observed_proof_rows") == 7
        and error.get("required_proof_rows") == 8,
        "lineage",
        "v3_parser_failure",
        str(error),
    )
    require(
        outputs.get("result_accepted") is False
        and outputs.get("scoreboard_rows_credited") == 0
        and outputs.get("output_directory_exists") is False
        and outputs.get("partial_directories") == 0
        and negative.get("resource_scope", {}).get("oom_delta_failure_reported") is False,
        "lineage",
        "v3_outputs",
        str(outputs),
    )
    return negative


def configure_base() -> None:
    BASE.REGISTRATION_SCHEMA = REGISTRATION_SCHEMA
    BASE.RESULT_SCHEMA = RESULT_SCHEMA
    BASE.EXPECTED_SOLVER = V3.EXPECTED_SOLVER


def read_registration(path: Path) -> dict[str, Any]:
    configure_base()
    registration = V3.BASE_READ_REGISTRATION(path)
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


def normalize_runner_output(stdout: str) -> str:
    normalized = []
    prefixed_proofs = 0
    for line in stdout.splitlines():
        occurrences = []
        for marker in MARKERS:
            start = 0
            while (position := line.find(marker, start)) >= 0:
                occurrences.append((marker, position))
                start = position + len(marker)
        require(
            len(occurrences) <= 1,
            "result",
            "marker_multiplicity",
            line,
        )
        if not occurrences:
            normalized.append(line)
            continue
        marker, position = occurrences[0]
        if position == 0:
            normalized.append(line)
            continue
        require(
            marker == "TOCK_PROOF|"
            and line[:position] == HARNESS_PREFIX
            and prefixed_proofs == 0,
            "result",
            "marker_prefix",
            line,
        )
        prefixed_proofs += 1
        normalized.append(line[position:])
    require(prefixed_proofs == 1, "result", "prefixed_proof_count", str(prefixed_proofs))
    return "\n".join(normalized) + "\n"


def parse_runner_output(stdout: str) -> dict[str, Any]:
    return V3.parse_runner_output(normalize_runner_output(stdout))


def run_scoreboard(args: argparse.Namespace) -> dict[str, Any]:
    validate_lineage()
    configure_base()
    original_reader = BASE.read_registration
    original_parser = BASE.parse_runner_output
    BASE.read_registration = read_registration
    BASE.parse_runner_output = parse_runner_output
    try:
        return BASE.run_scoreboard(args)
    finally:
        BASE.read_registration = original_reader
        BASE.parse_runner_output = original_parser


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
