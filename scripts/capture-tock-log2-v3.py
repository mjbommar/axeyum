#!/usr/bin/env python3
"""Run ADR-0334's corrected Tock log2 LLVM capture."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Sequence


def load_support(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load support module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REPO = Path(__file__).resolve().parents[1]
V2 = load_support("tock_capture_v2_for_v3", REPO / "scripts/capture-tock-log2-v2.py")
V2_READ_REGISTRATION = V2.read_registration
V2_VALIDATE_REGISTRATION = V2.validate_registration
V2_VALIDATE_CACHE = V2.validate_cache
V2_RESULT_SCHEMA = V2.RESULT_SCHEMA
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v3-registration.json"
)
V2_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v2-registration.json"
)
V2_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/capture-v2-registration.json",
    "sha256": "09b61b38b3552fce512a5ace05f5c8bf4f33212d423543c1d976124007ff5c16",
}
V2_NEGATIVE = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v2-negative.json"
)
V2_NEGATIVE_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/capture-v2-negative.json",
    "sha256": "2d640758eb00a003ab456953b867830fd6a88bfee702c325774803815822c91d",
}
DEFAULT_TOCK_REPO = V2.DEFAULT_TOCK_REPO
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/capture-v3"
DEFAULT_ADMITTER = V2.DEFAULT_ADMITTER
REGISTRATION_SCHEMA = "axeyum.tock-log2-capture-v3-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-capture-v3-result.v1"
V2_NEGATIVE_SHA_FIELD = "capture_v2_negative_sha256"


CaptureError = V2.CaptureError
require = V2.require


def read_registration(path: Path) -> dict[str, Any]:
    overlay = V2.V1.read_json(path)
    require(
        set(overlay)
        == {
            "schema",
            "capture_v2_registration",
            "capture_v2_negative",
            "producer_files",
        },
        "registration",
        "overlay_fields",
        str(sorted(overlay)),
    )
    require(
        overlay.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(overlay.get("schema")),
    )
    require(
        overlay.get("capture_v2_registration") == V2_REGISTRATION_IDENTITY,
        "registration",
        "capture_v2_registration",
        str(overlay.get("capture_v2_registration")),
    )
    require(
        overlay.get("capture_v2_negative") == V2_NEGATIVE_IDENTITY,
        "registration",
        "capture_v2_negative",
        str(overlay.get("capture_v2_negative")),
    )
    V2.V1.validate_file(
        V2_REGISTRATION,
        V2_REGISTRATION_IDENTITY["sha256"],
        "registration",
        "capture_v2_registration",
    )
    V2.V1.validate_file(
        V2_NEGATIVE,
        V2_NEGATIVE_IDENTITY["sha256"],
        "registration",
        "capture_v2_negative",
    )
    base = V2_READ_REGISTRATION(V2_REGISTRATION)
    V2_VALIDATE_REGISTRATION(base)
    producers = overlay.get("producer_files")
    require(
        isinstance(producers, list) and producers,
        "registration",
        "shape",
        "producer_files",
    )
    registration = json.loads(json.dumps(base))
    registration["schema"] = REGISTRATION_SCHEMA
    registration["capture_v2_registration"] = V2_REGISTRATION_IDENTITY
    registration["capture_v2_negative"] = V2_NEGATIVE_IDENTITY
    registration["producer_files"] = sorted(
        [*registration["producer_files"], *producers], key=lambda row: row["path"]
    )
    registration["upstream"][V2_NEGATIVE_SHA_FIELD] = V2_NEGATIVE_IDENTITY["sha256"]
    return registration


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(registration.get("schema")),
    )
    require(
        registration.get("capture_v2_registration") == V2_REGISTRATION_IDENTITY,
        "registration",
        "capture_v2_registration",
        str(registration.get("capture_v2_registration")),
    )
    require(
        registration.get("capture_v2_negative") == V2_NEGATIVE_IDENTITY,
        "registration",
        "capture_v2_negative",
        str(registration.get("capture_v2_negative")),
    )
    require(
        registration.get("upstream", {}).get(V2_NEGATIVE_SHA_FIELD)
        == V2_NEGATIVE_IDENTITY["sha256"],
        "registration",
        "capture_v2_lineage",
        str(registration.get("upstream")),
    )
    inherited = json.loads(json.dumps(registration))
    inherited["schema"] = V2.REGISTRATION_SCHEMA
    inherited.pop("capture_v2_registration", None)
    inherited.pop("capture_v2_negative", None)
    inherited["upstream"].pop(V2_NEGATIVE_SHA_FIELD, None)
    V2_VALIDATE_REGISTRATION(inherited)


def full_cache_registration() -> dict[str, Any]:
    registration = V2.V5.read_registration(V2.CACHE_REGISTRATION)
    V2.V5.validate_registration(registration)
    require(
        registration.get("expected_lock_packages") == 169,
        "cache",
        "expected_lock_packages",
        str(registration.get("expected_lock_packages")),
    )
    return registration


def validate_cache(
    registration: dict[str, Any], source: Path, target: Path
) -> None:
    before = V2.validate_local_cache(registration)
    cache_registration = full_cache_registration()
    actual_probe = V2.V5.structural_probe(
        cache_registration, source, V2.LOCAL_CACHE_HOME, target
    )
    require(
        actual_probe == registration["cache_result"]["probe"],
        "cache",
        "probe_drift",
        str(actual_probe),
    )
    after = V2.V5.V4.inventory_cache(V2.LOCAL_CACHE_HOME)
    require(before == after, "cache", "probe_inventory_drift", str(after))


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    V2.read_registration = read_registration
    V2.validate_registration = validate_registration
    V2.validate_cache = validate_cache
    V2.RESULT_SCHEMA = RESULT_SCHEMA
    try:
        return V2.run_capture(args)
    finally:
        V2.read_registration = V2_READ_REGISTRATION
        V2.validate_registration = V2_VALIDATE_REGISTRATION
        V2.validate_cache = V2_VALIDATE_CACHE
        V2.RESULT_SCHEMA = V2_RESULT_SCHEMA


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--tock-repo", type=Path, default=DEFAULT_TOCK_REPO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--admitter", type=Path, default=DEFAULT_ADMITTER)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_capture(args)
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
