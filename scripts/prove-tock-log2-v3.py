#!/usr/bin/env python3
"""Run ADR-0337's end-to-end-certified Tock log2 scoreboard."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
BASE_PATH = REPO / "scripts/prove-tock-log2.py"
V2_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v2-registration.json"
)
V2_PREFLIGHT = REPO / "bench-results/verify-tock-log2-20260721/proof-v2-preflight.json"
V2_NEGATIVE = REPO / "bench-results/verify-tock-log2-20260721/proof-v2-negative.json"
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v3-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/proof-v3"
REGISTRATION_SCHEMA = "axeyum.tock-log2-proof-v3-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-proof-v3-result.v1"
V2_REGISTRATION_SHA256 = (
    "47ac58722b2d21e6175506c67741372dc2970a8e3419df21a7ccdc7c3089c6f4"
)
V2_PREFLIGHT_SHA256 = (
    "9222aa62416e5c02589ae2726415d70b7f49cf9292977cd484ade74ab983663f"
)
V2_NEGATIVE_SHA256 = (
    "2a5841067653d8a1b7fc07474daa8a5267d887257d0d03afc596104524c14b75"
)
CORRECTED_LOCK_SHA256 = (
    "e9da054b3407171fcf77aa140098d30dff85f67ec9c499acf6b903b52825181f"
)


def load_base():
    spec = importlib.util.spec_from_file_location("tock_log2_proof_base", BASE_PATH)
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
BASE_PARSE_RUNNER_OUTPUT = BASE.parse_runner_output
CONTROL_SOLVER = json.loads(json.dumps(BASE.EXPECTED_SOLVER))
EXPECTED_SOLVER = {
    "controls": CONTROL_SOLVER,
    "proofs": {
        "backend": "end-to-end-qfbv",
        "deadline_seconds": 30,
        "faithfulness": "independent-reference-miter-drat",
        "final_refutation": "drat",
        "rechecks": [
            "faithfulness_drat",
            "final_drat",
            "final_lrat_if_present",
        ],
    },
}


def validate_lineage(
    registration_path: Path = V2_REGISTRATION,
    preflight_path: Path = V2_PREFLIGHT,
    negative_path: Path = V2_NEGATIVE,
) -> dict[str, Any]:
    for path, digest, kind in (
        (registration_path, V2_REGISTRATION_SHA256, "v2_registration"),
        (preflight_path, V2_PREFLIGHT_SHA256, "v2_preflight"),
        (negative_path, V2_NEGATIVE_SHA256, "v2_negative"),
    ):
        BASE.SUPPORT.validate_file(path, digest, "lineage", kind)
    preflight = BASE.SUPPORT.read_json(preflight_path)
    require(
        preflight.get("status") == "accepted"
        and preflight.get("outputs", {}).get("property_queries") == 0
        and preflight.get("outputs", {}).get("official_output_directory_exists") is False,
        "lineage",
        "v2_preflight_status",
        str(preflight),
    )
    negative = BASE.SUPPORT.read_json(negative_path)
    attempt = negative.get("attempt", {})
    first = negative.get("first_query", {})
    outputs = negative.get("outputs", {})
    require(
        negative.get("schema") == "axeyum.tock-log2-proof-v2-negative.v1"
        and negative.get("status") == "rejected"
        and attempt.get("official_invocations") == 1
        and attempt.get("property_queries_started") == 1
        and attempt.get("property_queries_completed") == 1,
        "lineage",
        "v2_status",
        str(negative),
    )
    require(
        first.get("target") == "log_base_two"
        and first.get("width") == 32
        and first.get("property") == "defined"
        and first.get("raw_outcome") == "Proved"
        and first.get("accepted_for_credit") is False
        and first.get("trust_steps")
        == [
            {"certified": False, "id": "BitBlast"},
            {"certified": True, "id": "Tseitin"},
            {"certified": True, "id": "SatRefutation"},
        ],
        "lineage",
        "v2_first_query",
        str(first),
    )
    require(
        outputs.get("proofs_credited") == 0
        and outputs.get("controls") == 0
        and outputs.get("scoreboard_rows") == 0
        and outputs.get("output_directory_exists") is False
        and outputs.get("partial_directories") == 0
        and negative.get("resource_scope", {}).get("oom_delta_failure_reported") is False,
        "lineage",
        "v2_outputs",
        str(outputs),
    )
    return negative


def configure_base() -> None:
    BASE.REGISTRATION_SCHEMA = REGISTRATION_SCHEMA
    BASE.RESULT_SCHEMA = RESULT_SCHEMA
    BASE.EXPECTED_SOLVER = EXPECTED_SOLVER


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


def parse_runner_output(stdout: str) -> dict[str, Any]:
    parsed = BASE_PARSE_RUNNER_OUTPUT(stdout)
    expected_trust = (
        "bit-blast-miter:certified,tseitin:certified,sat-refutation:certified"
    )
    artifact_names = (
        "faithfulness_dimacs",
        "faithfulness_drat",
        "final_dimacs",
        "final_drat",
        "final_lrat",
    )
    for row in parsed["proofs"]:
        require(
            row.get("backend") == "end-to-end-qfbv"
            and row.get("evidence") == "drat"
            and row.get("trust") == expected_trust
            and row.get("faithfulness") == "miter_drat"
            and row.get("recheck") == "pass",
            "result",
            "proof_certificate",
            str(row),
        )
        for name in artifact_names:
            byte_count = BASE.numeric(row, f"{name}_bytes", positive=name != "final_lrat")
            digest = row.get(f"{name}_sha256", "")
            require(
                len(digest) == 64
                and all(character in "0123456789abcdef" for character in digest),
                "result",
                "proof_artifact_hash",
                f"{name}={digest}",
            )
            if byte_count == 0:
                require(
                    digest
                    == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
                    "result",
                    "proof_empty_artifact_hash",
                    f"{name}={digest}",
                )
    return parsed


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
