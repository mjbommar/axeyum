#!/usr/bin/env python3
"""Run ADR-0325's dependency-wide-remapped Maestro capture."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]


def load_support(name: str, path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load support from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CAPTURE = load_support("maestro_capture_v1", Path(__file__).with_name("capture-maestro-device-id.py"))
DIAGNOSE = load_support(
    "maestro_drift_support", Path(__file__).with_name("diagnose-maestro-llvm-root-drift.py")
)
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-maestro-device-id-20260721/capture-v2-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/maestro-device-id-20260721/capture-v2"
RESULT_SCHEMA = "axeyum.maestro-device-id-capture-v2-result.v1"
AMBIENT_RUSTFLAGS = ("RUSTFLAGS", "CARGO_BUILD_RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS")


def validate_registration(registration: dict[str, Any]) -> dict[str, Any]:
    CAPTURE.require(
        registration.get("schema") == "axeyum.maestro-device-id-capture-v2-registration.v1",
        "registration", "schema", "v2 registration schema drift",
    )
    base_entry = registration.get("base_registration")
    CAPTURE.require(isinstance(base_entry, dict), "registration", "shape", "base registration")
    base_path = REPO / CAPTURE.require_string(base_entry.get("path"), "base.path")
    base_hash = CAPTURE.require_string(base_entry.get("sha256"), "base.sha256")
    CAPTURE.require(base_path.is_file(), "registration", "missing_base", str(base_path))
    CAPTURE.require(CAPTURE.sha256_file(base_path) == base_hash,
                    "registration", "base_hash", str(base_path))
    base = CAPTURE.read_json(base_path)
    CAPTURE.validate_registration(base)
    CAPTURE.validate_producers(base)

    diagnostic = registration.get("diagnostic_result")
    CAPTURE.require(isinstance(diagnostic, dict), "registration", "shape", "diagnostic result")
    diagnostic_path = REPO / CAPTURE.require_string(diagnostic.get("path"), "diagnostic.path")
    diagnostic_hash = CAPTURE.require_string(diagnostic.get("sha256"), "diagnostic.sha256")
    CAPTURE.require(diagnostic_path.is_file(), "registration", "missing_diagnostic",
                    str(diagnostic_path))
    CAPTURE.require(CAPTURE.sha256_file(diagnostic_path) == diagnostic_hash,
                    "registration", "diagnostic_hash", str(diagnostic_path))

    flags = registration.get("encoded_rustflags")
    CAPTURE.require(isinstance(flags, list) and flags == [
        "-Zexport-executable-symbols",
        "--remap-path-prefix=<isolated-root>=/axeyum-external/maestro",
    ], "registration", "flags", "encoded rustflags drift")
    tail = registration.get("final_rustc_tail")
    CAPTURE.require(tail == ["-Ccodegen-units=1", "-Clink-dead-code", "--emit=llvm-ir"],
                    "registration", "flags", "final rustc tail drift")

    producers = registration.get("producer_files")
    CAPTURE.require(isinstance(producers, list) and producers,
                    "registration", "shape", "producer files")
    paths = [entry.get("path") for entry in producers if isinstance(entry, dict)]
    CAPTURE.require(paths == sorted(set(paths)), "registration", "ordering", "producer files")
    for entry in producers:
        path = REPO / CAPTURE.require_string(entry.get("path"), "producer.path")
        digest = CAPTURE.require_string(entry.get("sha256"), "producer.sha256")
        CAPTURE.require(path.is_file(), "registration", "missing_producer", str(path))
        CAPTURE.require(CAPTURE.sha256_file(path) == digest,
                        "registration", "producer_hash", str(path))
    return base


def encoded_flags(root: Path) -> str:
    return "\x1f".join(
        [
            "-Zexport-executable-symbols",
            f"--remap-path-prefix={root}=/axeyum-external/maestro",
        ]
    )


def build_module_v2(
    root: Path, target_dir: Path, registration: dict[str, Any], base: dict[str, Any]
) -> tuple[Path, dict[str, int]]:
    for name in AMBIENT_RUSTFLAGS:
        CAPTURE.require(name not in os.environ, "build", "ambient_rustflags", name)
    kernel = root / "kernel"
    (kernel / "target/x86_64/release").mkdir(parents=True, exist_ok=True)
    target_dir.mkdir(parents=True)
    timing = target_dir / "time.txt"
    toolchain = base["build"]["toolchain"]
    cargo = [
        "cargo", f"+{toolchain}", "rustc", "--locked", "--offline", "--lib", "--release",
        "--target", "arch/x86_64/x86_64.json", "--jobs", "1", "--",
        *registration["final_rustc_tail"],
    ]
    wrapped = [
        "systemd-run", "--user", "--scope", "--quiet",
        "-p", "MemoryHigh=2500M", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=512M",
        "choom", "-n", "200", "--", "/usr/bin/time", "-v", "-o", str(timing), *cargo,
    ]
    env = CAPTURE.fixed_env(target_dir, base["build"]["source_date_epoch"])
    env["CARGO_ENCODED_RUSTFLAGS"] = encoded_flags(root)
    started = time.monotonic_ns()
    CAPTURE.command(
        wrapped, cwd=kernel, env=env, stage="build", kind="cargo_rustc_v2"
    )
    wall_ms = (time.monotonic_ns() - started) // 1_000_000
    modules = sorted((target_dir / "x86_64/release/deps").glob("kernel-*.ll"))
    CAPTURE.require(len(modules) == 1, "build", "module_count", str(len(modules)))
    return modules[0], {"wall_ms": wall_ms, "peak_rss_kib": CAPTURE.parse_time_report(timing)}


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    registration_path = args.registration.resolve()
    registration = CAPTURE.read_json(registration_path)
    base = validate_registration(registration)
    CAPTURE.validate_source(args.maestro_repo.resolve(), base)

    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    CAPTURE.require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    CAPTURE.require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    CAPTURE.require(not partial.exists(), "output", "partial_exists", str(partial))
    partial.mkdir()

    llvm_as = Path(base["tools"]["llvm_as"]["path"])
    llvm_extract = Path(base["tools"]["llvm_extract"]["path"])
    CAPTURE.validate_tool(llvm_as, base["tools"]["llvm_as"]["sha256"], "llvm_as")
    CAPTURE.validate_tool(
        llvm_extract, base["tools"]["llvm_extract"]["sha256"], "llvm_extract"
    )
    admitter = args.admitter.resolve()
    CAPTURE.require(admitter.is_file(), "admission", "missing_binary", str(admitter))

    try:
        with tempfile.TemporaryDirectory(prefix="maestro-capture-v2-") as raw_temp:
            temp = Path(raw_temp)
            roots = [temp / "root-a", temp / "root-b"]
            for root in roots:
                CAPTURE.materialize(args.maestro_repo.resolve(), base["upstream"]["commit"], root)
            if args.prepare_cache:
                CAPTURE.prepare_cache(roots[0], base)

            modules: list[Path] = []
            builds: list[dict[str, Any]] = []
            for label, root in zip(("a", "b"), roots):
                module, observation = build_module_v2(
                    root, temp / f"cargo-{label}", registration, base
                )
                retained = partial / "modules" / f"kernel-{label}.ll"
                retained.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(module, retained)
                CAPTURE.assemble(llvm_as, retained)
                data = retained.read_bytes()
                root_tokens = {
                    "source_root": data.count(str(root).encode()),
                    "temporary_parent": data.count(str(temp).encode()),
                }
                CAPTURE.require(all(count == 0 for count in root_tokens.values()),
                                "build", "root_token", f"{label}: {root_tokens}")
                modules.append(retained)
                builds.append(
                    {
                        "root": label,
                        "module_bytes": len(data),
                        "module_sha256": CAPTURE.sha256_bytes(data),
                        "module_lines": len(data.splitlines()),
                        "root_tokens": root_tokens,
                        "canonical_prefix_occurrences": data.count(b"/axeyum-external/maestro"),
                        **observation,
                    }
                )

            CAPTURE.require(builds[0]["module_bytes"] == builds[1]["module_bytes"],
                            "build", "module_size_drift", str(builds))
            CAPTURE.require(builds[0]["module_sha256"] == builds[1]["module_sha256"],
                            "build", "module_hash_drift", str(builds))

            discovered = [DIAGNOSE.discover_symbols(module.read_bytes()) for module in modules]
            CAPTURE.require(discovered[0] == discovered[1],
                            "symbols", "cross_root_drift", str(discovered))
            selected: list[dict[str, Any]] = []
            for target in base["targets"]:
                rows = [
                    DIAGNOSE.selected_projection(
                        module, label, target, symbols[target["name"]], partial / "selected",
                        llvm_extract, llvm_as, admitter,
                    )
                    for module, label, symbols in zip(modules, ("a", "b"), discovered)
                ]
                CAPTURE.require(rows[0]["moduleid_agnostic_sha256"] ==
                                rows[1]["moduleid_agnostic_sha256"],
                                "extract", "canonical_drift", target["name"])
                CAPTURE.require(rows[0]["frontend_canonical_sha256"] ==
                                rows[1]["frontend_canonical_sha256"],
                                "admission", "canonical_drift", target["name"])
                selected.append({"name": target["name"], "symbol": discovered[0][target["name"]],
                                 "roots": rows})

        result: dict[str, Any] = {
            "schema": RESULT_SCHEMA,
            "status": "accepted_capture_no_proof",
            "capture_credit": True,
            "registration_sha256": CAPTURE.sha256_file(registration_path),
            "upstream": base["upstream"],
            "encoded_rustflags_template": registration["encoded_rustflags"],
            "final_rustc_tail": registration["final_rustc_tail"],
            "builds": builds,
            "full_module": {
                "bytes": builds[0]["module_bytes"],
                "sha256": builds[0]["module_sha256"],
                "raw_byte_identical": True,
            },
            "selected": selected,
            "summary": {"builds": 2, "targets": 3, "accepted": 3, "dropped": 0,
                        "solver_queries": 0},
        }
        result["identity_sha256"] = CAPTURE.sha256_bytes(
            (json.dumps({k: v for k, v in result.items() if k != "identity_sha256"},
                        sort_keys=True, separators=(",", ":")) + "\n").encode()
        )
        (partial / "capture-v2-result.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        partial.rename(output)
        return result
    except BaseException:
        shutil.rmtree(partial, ignore_errors=True)
        raise


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--maestro-repo", type=Path, default=CAPTURE.DEFAULT_MAESTRO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--admitter", type=Path, default=CAPTURE.DEFAULT_ADMITTER)
    parser.add_argument("--prepare-cache", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_capture(args)
    except CAPTURE.CaptureError as error:
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
