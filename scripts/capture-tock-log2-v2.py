#!/usr/bin/env python3
"""Run ADR-0333's dedicated-cache Tock log2 LLVM capture."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
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
V1 = load_support("tock_capture_v1", REPO / "scripts/capture-tock-log2.py")
V1_READ_JSON = V1.read_json
V1_VALIDATE_REGISTRATION = V1.validate_registration
V1_BWRAP_COMMAND = V1.bwrap_command
V1_REJECT_HOST_TOKENS = V1.reject_host_tokens
V1_VALIDATE_CACHE = V1.validate_cache
V1_RESULT_SCHEMA = V1.RESULT_SCHEMA
V5 = load_support(
    "tock_cache_v5_for_capture", REPO / "scripts/prepare-tock-log2-cache-v5.py"
)
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v2-registration.json"
)
BASE_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/capture-v1-registration.json"
)
BASE_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/capture-v1-registration.json",
    "sha256": "051a031073ce2343198a21fb6839897ce2f0a16a2045749d5188d0ab2669169a",
}
CACHE_REGISTRATION = (
    REPO
    / "bench-results/verify-tock-log2-20260721/cache-v5-preparation-registration.json"
)
CACHE_REGISTRATION_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/cache-v5-preparation-registration.json",
    "sha256": "80ea7f09efc6a6983eb9924978695795451546dde36dd4324ca1195a2781faf7",
}
CACHE_SUMMARY = (
    REPO / "bench-results/verify-tock-log2-20260721/cache-v5-preparation-result.json"
)
CACHE_SUMMARY_IDENTITY = {
    "path": "bench-results/verify-tock-log2-20260721/cache-v5-preparation-result.json",
    "sha256": "b7c21f2d2d62a1ec8259ea2ffbe7487785aca95e5dc83f5a3ef966c69c132418",
}
LOCAL_CACHE_ENVELOPE = REPO / "target/tock-log2-20260721/cache-v5"
LOCAL_CACHE_HOME = LOCAL_CACHE_ENVELOPE / "cargo-home"
LOCAL_CACHE_RESULT = LOCAL_CACHE_ENVELOPE / "preparation-result.json"
DEFAULT_TOCK_REPO = REPO / "references/tock"
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/capture-v2"
DEFAULT_ADMITTER = V1.DEFAULT_ADMITTER
REGISTRATION_SCHEMA = "axeyum.tock-log2-capture-v2-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-capture-v2-result.v1"
CACHE_INPUT_IDENTITY = {
    "active_resolution_sha256": "da6971e417c906a9c0fa81768cfd511136d0946f651a1ec891ce1f7891dbf305",
    "inventory_sha256": "fd6ee33dd536c75d654bb750a8919911dd6065f382ea59d8ac0e26464097d379",
    "preparation_identity_sha256": "3c926909d28380f95da23ef3170f069b46cd2642d23e712b660074c61068fb06",
}


def without_ambient_cargo(values: list[str]) -> list[str]:
    result = list(values)
    needle = [
        "--ro-bind",
        "/home/mjbommar/.cargo",
        "/home/mjbommar/.cargo",
    ]
    matches = [index for index in range(len(result) - 2) if result[index : index + 3] == needle]
    V1.require(
        len(matches) == 1,
        "registration",
        "ambient_cache_mount",
        str(matches),
    )
    del result[matches[0] : matches[0] + 3]
    return result


EXPECTED_ROOT = without_ambient_cargo(V1.EXPECTED_BWRAP_ROOT)
EXPECTED_ENVIRONMENT = [
    [name, "/axeyum-vroot/cache" if name == "CARGO_HOME" else value]
    for name, value in V1.EXPECTED_ENVIRONMENT
]


CaptureError = V1.CaptureError
require = V1.require


def read_registration(path: Path) -> dict[str, Any]:
    overlay = V1.read_json(path)
    require(
        set(overlay)
        == {
            "schema",
            "base_registration",
            "cache_registration",
            "cache_summary",
            "cache_mount",
            "producer_files",
        },
        "registration",
        "overlay_fields",
        str(sorted(overlay)),
    )
    require(overlay.get("schema") == REGISTRATION_SCHEMA, "registration", "schema", str(overlay.get("schema")))
    require(overlay.get("base_registration") == BASE_REGISTRATION_IDENTITY, "registration", "base_registration", str(overlay.get("base_registration")))
    require(overlay.get("cache_registration") == CACHE_REGISTRATION_IDENTITY, "registration", "cache_registration", str(overlay.get("cache_registration")))
    require(overlay.get("cache_summary") == CACHE_SUMMARY_IDENTITY, "registration", "cache_summary", str(overlay.get("cache_summary")))
    require(
        overlay.get("cache_mount")
        == {"host": "target/tock-log2-20260721/cache-v5/cargo-home", "virtual": "/axeyum-vroot/cache", "read_only": True},
        "registration",
        "cache_mount",
        str(overlay.get("cache_mount")),
    )
    V1.validate_file(BASE_REGISTRATION, BASE_REGISTRATION_IDENTITY["sha256"], "registration", "base_registration")
    V1.validate_file(CACHE_REGISTRATION, CACHE_REGISTRATION_IDENTITY["sha256"], "registration", "cache_registration")
    V1.validate_file(CACHE_SUMMARY, CACHE_SUMMARY_IDENTITY["sha256"], "registration", "cache_summary")
    base = V1.read_json(BASE_REGISTRATION)
    V1_VALIDATE_REGISTRATION(base)
    V5.read_registration(CACHE_REGISTRATION)
    summary = V1.read_json(CACHE_SUMMARY)
    producers = overlay.get("producer_files")
    require(isinstance(producers, list) and producers, "registration", "shape", "producer_files")
    registration = json.loads(json.dumps(base))
    registration["schema"] = REGISTRATION_SCHEMA
    registration["base_registration"] = BASE_REGISTRATION_IDENTITY
    registration["cache_registration"] = CACHE_REGISTRATION_IDENTITY
    registration["cache_summary"] = CACHE_SUMMARY_IDENTITY
    registration["cache_mount"] = overlay["cache_mount"]
    registration["environment"] = EXPECTED_ENVIRONMENT
    registration["namespace"]["root_argv"] = EXPECTED_ROOT
    registration["producer_files"] = sorted(
        [*registration["producer_files"], *producers], key=lambda row: row["path"]
    )
    registration["upstream"]["authenticated_cache"] = CACHE_INPUT_IDENTITY
    registration["cache_result"] = summary
    return registration


def validate_registration(registration: dict[str, Any]) -> None:
    require(registration.get("schema") == REGISTRATION_SCHEMA, "registration", "schema", str(registration.get("schema")))
    require(registration.get("base_registration") == BASE_REGISTRATION_IDENTITY, "registration", "base_registration", str(registration.get("base_registration")))
    require(registration.get("cache_registration") == CACHE_REGISTRATION_IDENTITY, "registration", "cache_registration", str(registration.get("cache_registration")))
    require(registration.get("cache_summary") == CACHE_SUMMARY_IDENTITY, "registration", "cache_summary", str(registration.get("cache_summary")))
    require(registration.get("environment") == EXPECTED_ENVIRONMENT, "registration", "environment", "environment drift")
    require(registration.get("namespace", {}).get("root_argv") == EXPECTED_ROOT, "registration", "namespace", "root drift")
    require(registration.get("upstream", {}).get("authenticated_cache") == CACHE_INPUT_IDENTITY, "registration", "cache_identity", str(registration.get("upstream")))
    inherited = json.loads(json.dumps(registration))
    inherited["schema"] = V1.REGISTRATION_SCHEMA
    inherited["environment"] = V1.EXPECTED_ENVIRONMENT
    inherited["namespace"]["root_argv"] = V1.EXPECTED_BWRAP_ROOT
    inherited["upstream"].pop("authenticated_cache", None)
    V1_VALIDATE_REGISTRATION(inherited)


def validate_local_cache(registration: dict[str, Any]) -> dict[str, Any]:
    require(LOCAL_CACHE_ENVELOPE.is_dir(), "cache", "envelope", str(LOCAL_CACHE_ENVELOPE))
    require(LOCAL_CACHE_HOME.is_dir() and not LOCAL_CACHE_HOME.is_symlink(), "cache", "cargo_home", str(LOCAL_CACHE_HOME))
    V1.validate_file(LOCAL_CACHE_RESULT, registration["cache_result"]["local_result_sha256"], "cache", "local_result")
    local = V1.read_json(LOCAL_CACHE_RESULT)
    committed = registration["cache_result"]
    for key in ("identity_sha256", "inventory", "probe", "status", "summary", "upstream"):
        require(local.get(key) == committed.get(key), "cache", "result_drift", key)
    actual = V5.V4.inventory_cache(LOCAL_CACHE_HOME)
    require(actual == committed["inventory"], "cache", "inventory_drift", str(actual))
    return actual


def bwrap_command(
    registration: dict[str, Any], source: Path, target: Path, child: Sequence[str]
) -> list[str]:
    command_line = [registration["tools"]["bwrap"]["path"], *EXPECTED_ROOT]
    command_line.extend(["--ro-bind", str(LOCAL_CACHE_HOME), "/axeyum-vroot/cache"])
    command_line.extend(["--ro-bind", str(source), "/axeyum-vroot/source"])
    command_line.extend(["--bind", str(target), "/axeyum-vroot/target"])
    command_line.extend(["--chdir", "/axeyum-vroot/source", "--clearenv"])
    for name, value in EXPECTED_ENVIRONMENT:
        command_line.extend(["--setenv", name, value])
    command_line.extend(["--", *child])
    return command_line


def reject_host_tokens(module: bytes, roots: Sequence[Path]) -> dict[str, int]:
    paths = V1_REJECT_HOST_TOKENS(module, [*roots, LOCAL_CACHE_HOME])
    paths["virtual_cache_occurrences"] = module.count(b"/axeyum-vroot/cache")
    return paths


def validate_cache(
    registration: dict[str, Any], source: Path, target: Path
) -> None:
    before = validate_local_cache(registration)
    actual_probe = V5.structural_probe(registration, source, LOCAL_CACHE_HOME, target)
    require(actual_probe == registration["cache_result"]["probe"], "cache", "probe_drift", str(actual_probe))
    after = V5.V4.inventory_cache(LOCAL_CACHE_HOME)
    require(before == after, "cache", "probe_inventory_drift", str(after))


def finalize_capture(
    delegate: Path, output: Path, result: dict[str, Any]
) -> dict[str, Any]:
    result_path = delegate / "capture-result.json"
    module_path = delegate / "kernel.ll"
    require(result_path.is_file(), "output", "missing_result", str(result_path))
    require(module_path.is_file(), "output", "missing_module", str(module_path))
    saved = json.loads(result_path.read_text(encoding="utf-8"))
    require(saved == result, "output", "result_drift", str(result_path))
    count = module_path.read_bytes().count(b"/axeyum-vroot/cache")
    builds = result.get("observations", {}).get("builds")
    require(
        isinstance(builds, list)
        and len(builds) == 2
        and all(row.get("virtual_cache_occurrences") == count for row in builds),
        "identity",
        "virtual_cache_counts",
        str(builds),
    )
    result["module"]["virtual_cache_occurrences"] = count
    result["identity_sha256"] = V1.sha256_bytes(
        (
            json.dumps(
                V1.identity_projection(result), sort_keys=True, separators=(",", ":")
            )
            + "\n"
        ).encode()
    )
    result_path.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    delegate.rename(output)
    return result


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_registration(registration)
    validate_local_cache(registration)
    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    require(not output.exists(), "output", "exists", str(output))
    delegate = output.with_name(f".{output.name}.delegate-{os.getpid()}")
    require(not delegate.exists(), "output", "delegate_exists", str(delegate))
    V1.read_json = lambda path: (
        registration
        if path.resolve() == args.registration.resolve()
        else json.loads(path.read_text(encoding="utf-8"))
    )
    V1.validate_registration = validate_registration
    V1.bwrap_command = bwrap_command
    V1.reject_host_tokens = reject_host_tokens
    V1.validate_cache = validate_cache
    V1.RESULT_SCHEMA = RESULT_SCHEMA
    delegated_args = argparse.Namespace(**vars(args))
    delegated_args.output = delegate
    try:
        result = V1.run_capture(delegated_args)
        return finalize_capture(delegate, output, result)
    except BaseException:
        shutil.rmtree(delegate, ignore_errors=True)
        raise
    finally:
        V1.read_json = V1_READ_JSON
        V1.validate_registration = V1_VALIDATE_REGISTRATION
        V1.bwrap_command = V1_BWRAP_COMMAND
        V1.reject_host_tokens = V1_REJECT_HOST_TOKENS
        V1.validate_cache = V1_VALIDATE_CACHE
        V1.RESULT_SCHEMA = V1_RESULT_SCHEMA


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
