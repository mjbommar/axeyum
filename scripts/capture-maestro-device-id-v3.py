#!/usr/bin/env python3
"""Run ADR-0326's stable-virtual-root Maestro LLVM capture."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
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


CAPTURE = load_support(
    "maestro_capture_v1", Path(__file__).with_name("capture-maestro-device-id.py")
)
DIAGNOSE = load_support(
    "maestro_drift_support",
    Path(__file__).with_name("diagnose-maestro-llvm-root-drift.py"),
)
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-maestro-device-id-20260721/capture-v3-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/maestro-device-id-20260721/capture-v3"
RESULT_SCHEMA = "axeyum.maestro-device-id-capture-v3-result.v1"
REGISTRATION_SCHEMA = "axeyum.maestro-device-id-capture-v3-registration.v1"
AMBIENT_RUSTFLAGS = (
    "RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
)
EXPECTED_BWRAP_BASE = [
    "--die-with-parent",
    "--new-session",
    "--unshare-all",
    "--ro-bind",
    "/",
    "/",
    "--dev-bind",
    "/dev",
    "/dev",
    "--proc",
    "/proc",
]
EXPECTED_BUILD_ROOT = [
    "--die-with-parent",
    "--new-session",
    "--unshare-all",
    "--tmpfs",
    "/",
    "--dir",
    "/usr",
    "--ro-bind",
    "/usr",
    "/usr",
    "--symlink",
    "usr/bin",
    "/bin",
    "--symlink",
    "usr/sbin",
    "/sbin",
    "--symlink",
    "usr/lib",
    "/lib",
    "--symlink",
    "usr/lib64",
    "/lib64",
    "--dir",
    "/etc",
    "--ro-bind",
    "/etc",
    "/etc",
    "--dir",
    "/home",
    "--dir",
    "/home/mjbommar",
    "--ro-bind",
    "/home/mjbommar/.cargo",
    "/home/mjbommar/.cargo",
    "--ro-bind",
    "/home/mjbommar/.rustup",
    "/home/mjbommar/.rustup",
    "--dir",
    "/dev",
    "--dev-bind",
    "/dev",
    "/dev",
    "--dir",
    "/proc",
    "--proc",
    "/proc",
    "--dir",
    "/tmp",
    "--tmpfs",
    "/tmp",
    "--dir",
    "/axeyum-vroot",
]
EXPECTED_ENVIRONMENT = [
    ["CARGO_BUILD_JOBS", "1"],
    ["CARGO_HOME", "/home/mjbommar/.cargo"],
    ["CARGO_INCREMENTAL", "0"],
    ["CARGO_PROFILE_RELEASE_DEBUG", "0"],
    ["CARGO_TARGET_DIR", "/axeyum-vroot/target"],
    ["HOME", "/home/mjbommar"],
    ["LANG", "C.UTF-8"],
    ["LC_ALL", "C.UTF-8"],
    ["PATH", "/home/mjbommar/.cargo/bin:/usr/local/bin:/usr/bin:/bin"],
    ["RUSTUP_HOME", "/home/mjbommar/.rustup"],
    ["SOURCE_DATE_EPOCH", "1783984251"],
]
EXPECTED_TAIL = ["-Ccodegen-units=1", "-Clink-dead-code", "--emit=llvm-ir"]


def validate_registration(registration: dict[str, Any]) -> dict[str, Any]:
    CAPTURE.require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        "v3 registration schema drift",
    )
    base_entry = registration.get("base_registration")
    CAPTURE.require(
        isinstance(base_entry, dict), "registration", "shape", "base registration"
    )
    base_path = REPO / CAPTURE.require_string(base_entry.get("path"), "base.path")
    base_hash = CAPTURE.require_string(base_entry.get("sha256"), "base.sha256")
    CAPTURE.require(base_path.is_file(), "registration", "missing_base", str(base_path))
    CAPTURE.require(
        CAPTURE.sha256_file(base_path) == base_hash,
        "registration",
        "base_hash",
        str(base_path),
    )
    base = CAPTURE.read_json(base_path)
    CAPTURE.validate_registration(base)
    CAPTURE.validate_producers(base)

    prior_entry = registration.get("prior_result")
    CAPTURE.require(
        isinstance(prior_entry, dict), "registration", "shape", "prior result"
    )
    prior_path = REPO / CAPTURE.require_string(prior_entry.get("path"), "prior.path")
    prior_hash = CAPTURE.require_string(prior_entry.get("sha256"), "prior.sha256")
    CAPTURE.require(
        prior_path.is_file(), "registration", "missing_prior", str(prior_path)
    )
    CAPTURE.require(
        CAPTURE.sha256_file(prior_path) == prior_hash,
        "registration",
        "prior_hash",
        str(prior_path),
    )

    bwrap = registration.get("bwrap")
    CAPTURE.require(isinstance(bwrap, dict), "registration", "shape", "bwrap")
    CAPTURE.require(
        bwrap.get("path") == "/usr/bin/bwrap",
        "registration",
        "bwrap_path",
        str(bwrap.get("path")),
    )
    CAPTURE.require(
        bwrap.get("sha256")
        == "0abea81db798ebf6b4742ac0664802d97521547a353c2a0dbdc21d76cbbfd2c0",
        "registration",
        "bwrap_hash",
        str(bwrap.get("sha256")),
    )
    CAPTURE.require(
        bwrap.get("version") == "bubblewrap 0.11.1",
        "registration",
        "bwrap_version",
        str(bwrap.get("version")),
    )
    CAPTURE.require(
        bwrap.get("base_argv") == EXPECTED_BWRAP_BASE,
        "registration",
        "bwrap_argv",
        str(bwrap.get("base_argv")),
    )
    CAPTURE.require(
        bwrap.get("build_root_argv") == EXPECTED_BUILD_ROOT,
        "registration",
        "bwrap_build_root_argv",
        str(bwrap.get("build_root_argv")),
    )

    namespace = registration.get("namespace")
    CAPTURE.require(isinstance(namespace, dict), "registration", "shape", "namespace")
    CAPTURE.require(
        namespace.get("virtual_root") == "/axeyum-vroot"
        and namespace.get("virtual_source") == "/axeyum-vroot/source"
        and namespace.get("virtual_target") == "/axeyum-vroot/target"
        and namespace.get("working_directory") == "/axeyum-vroot/source/kernel",
        "registration",
        "mount_destination",
        str(namespace),
    )
    CAPTURE.require(
        namespace.get("environment") == EXPECTED_ENVIRONMENT,
        "registration",
        "environment",
        str(namespace.get("environment")),
    )
    CAPTURE.require(
        registration.get("final_rustc_tail") == EXPECTED_TAIL,
        "registration",
        "flags",
        "final rustc tail drift",
    )

    producers = registration.get("producer_files")
    CAPTURE.require(
        isinstance(producers, list) and producers,
        "registration",
        "shape",
        "producer files",
    )
    paths = [entry.get("path") for entry in producers if isinstance(entry, dict)]
    CAPTURE.require(
        paths == sorted(set(paths)), "registration", "ordering", "producer files"
    )
    for entry in producers:
        CAPTURE.require(
            isinstance(entry, dict), "registration", "shape", "producer entry"
        )
        path = REPO / CAPTURE.require_string(entry.get("path"), "producer.path")
        digest = CAPTURE.require_string(entry.get("sha256"), "producer.sha256")
        CAPTURE.require(path.is_file(), "registration", "missing_producer", str(path))
        CAPTURE.require(
            CAPTURE.sha256_file(path) == digest,
            "registration",
            "producer_hash",
            str(path),
        )
    return base


def reject_ambient_rustflags(environment: dict[str, str]) -> None:
    present = [name for name in AMBIENT_RUSTFLAGS if name in environment]
    CAPTURE.require(
        not present, "build", "ambient_rustflags", ",".join(present)
    )


def validate_distinct_physical_roots(paths: Sequence[Path]) -> None:
    resolved = [path.resolve() for path in paths]
    CAPTURE.require(
        len(resolved) == 4 and len(set(resolved)) == 4,
        "build",
        "physical_root_alias",
        str(resolved),
    )


def probe_bwrap(registration: dict[str, Any]) -> dict[str, str]:
    bwrap = registration["bwrap"]
    report = CAPTURE.validate_tool(Path(bwrap["path"]), bwrap["sha256"], "bwrap")
    CAPTURE.require(
        report["version"] == bwrap["version"],
        "tool",
        "bwrap_version",
        report["version"],
    )
    argv = [bwrap["path"], *bwrap["base_argv"], "--", "/usr/bin/true"]
    CAPTURE.command(argv, stage="tool", kind="bwrap_probe")
    return report


def cargo_argv(registration: dict[str, Any], base: dict[str, Any]) -> list[str]:
    return [
        "cargo",
        f"+{base['build']['toolchain']}",
        "rustc",
        "--locked",
        "--offline",
        "--lib",
        "--release",
        "--target",
        "arch/x86_64/x86_64.json",
        "--jobs",
        "1",
        "--",
        *registration["final_rustc_tail"],
    ]


def namespace_argv(
    source_root: Path,
    target_root: Path,
    registration: dict[str, Any],
    base: dict[str, Any],
) -> list[str]:
    bwrap = registration["bwrap"]
    namespace = registration["namespace"]
    argv = [
        bwrap["path"],
        *bwrap["build_root_argv"],
        "--bind",
        str(source_root.resolve()),
        namespace["virtual_source"],
        "--bind",
        str(target_root.resolve()),
        namespace["virtual_target"],
        "--chdir",
        namespace["working_directory"],
        "--clearenv",
    ]
    for name, value in namespace["environment"]:
        argv.extend(("--setenv", name, value))
    argv.extend(
        [
            "--",
            "/usr/bin/time",
            "-v",
            "-o",
            f"{namespace['virtual_target']}/time.txt",
            *cargo_argv(registration, base),
        ]
    )
    return argv


def wrapped_build_argv(namespace_command: Sequence[str]) -> list[str]:
    return [
        "/usr/bin/systemd-run",
        "--user",
        "--scope",
        "--quiet",
        "-p",
        "MemoryHigh=2500M",
        "-p",
        "MemoryMax=4G",
        "-p",
        "MemorySwapMax=512M",
        "/usr/bin/choom",
        "-n",
        "200",
        "--",
        *namespace_command,
    ]


def build_module_v3(
    source_root: Path,
    target_root: Path,
    registration: dict[str, Any],
    base: dict[str, Any],
) -> tuple[Path, dict[str, int]]:
    reject_ambient_rustflags(os.environ)
    kernel = source_root / "kernel"
    (kernel / "target/x86_64/release").mkdir(parents=True, exist_ok=True)
    target_root.mkdir(parents=True)
    command = namespace_argv(source_root, target_root, registration, base)
    started = time.monotonic_ns()
    CAPTURE.command(
        wrapped_build_argv(command),
        stage="build",
        kind="cargo_rustc_v3",
    )
    wall_ms = (time.monotonic_ns() - started) // 1_000_000
    timing = target_root / "time.txt"
    modules = sorted((target_root / "x86_64/release/deps").glob("kernel-*.ll"))
    CAPTURE.require(
        len(modules) == 1, "build", "module_count", f"found {len(modules)} modules"
    )
    return modules[0], {
        "wall_ms": wall_ms,
        "peak_rss_kib": CAPTURE.parse_time_report(timing),
    }


def path_observation(
    data: bytes,
    physical_paths: Sequence[Path],
    registration: dict[str, Any],
) -> dict[str, Any]:
    physical = {
        str(path.resolve()): data.count(str(path.resolve()).encode())
        for path in physical_paths
    }
    CAPTURE.require(
        all(count == 0 for count in physical.values()),
        "build",
        "root_token",
        str(physical),
    )
    namespace = registration["namespace"]
    return {
        "physical_path_occurrences": physical,
        "virtual_source_occurrences": data.count(namespace["virtual_source"].encode()),
        "virtual_target_occurrences": data.count(namespace["virtual_target"].encode()),
    }


def require_module_identity(builds: Sequence[dict[str, Any]]) -> None:
    CAPTURE.require(
        len(builds) == 2, "build", "module_count", f"rows={len(builds)}"
    )
    CAPTURE.require(
        builds[0]["module_bytes"] == builds[1]["module_bytes"],
        "build",
        "module_size_drift",
        str(builds),
    )
    CAPTURE.require(
        builds[0]["module_sha256"] == builds[1]["module_sha256"],
        "build",
        "module_hash_drift",
        str(builds),
    )
    for key in ("virtual_source_occurrences", "virtual_target_occurrences"):
        CAPTURE.require(
            builds[0][key] == builds[1][key],
            "build",
            "virtual_path_count_drift",
            f"{key}: {builds}",
        )


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    registration_path = args.registration.resolve()
    registration = CAPTURE.read_json(registration_path)
    base = validate_registration(registration)
    CAPTURE.validate_source(args.maestro_repo.resolve(), base)
    reject_ambient_rustflags(os.environ)

    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    CAPTURE.require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    CAPTURE.require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    CAPTURE.require(not partial.exists(), "output", "partial_exists", str(partial))

    bwrap_report = probe_bwrap(registration)
    llvm_as = Path(base["tools"]["llvm_as"]["path"])
    llvm_extract = Path(base["tools"]["llvm_extract"]["path"])
    llvm_as_report = CAPTURE.validate_tool(
        llvm_as, base["tools"]["llvm_as"]["sha256"], "llvm_as"
    )
    llvm_extract_report = CAPTURE.validate_tool(
        llvm_extract, base["tools"]["llvm_extract"]["sha256"], "llvm_extract"
    )
    rust_report = CAPTURE.rust_tools(base["build"]["toolchain"])
    CAPTURE.require(
        rust_report["rustc_commit"] == base["build"]["rustc_commit"],
        "tool",
        "rustc_commit",
        rust_report["rustc_commit"],
    )
    CAPTURE.require(
        rust_report["rustc_llvm"] == base["build"]["rustc_llvm"],
        "tool",
        "rustc_llvm",
        rust_report["rustc_llvm"],
    )
    admitter = args.admitter.resolve()
    CAPTURE.require(admitter.is_file(), "admission", "missing_binary", str(admitter))

    partial.mkdir()
    try:
        with tempfile.TemporaryDirectory(prefix="maestro-capture-v3-") as raw_temp:
            temp = Path(raw_temp)
            sources = [temp / "source-a", temp / "source-b"]
            targets = [temp / "target-a", temp / "target-b"]
            validate_distinct_physical_roots([*sources, *targets])
            for source in sources:
                CAPTURE.materialize(
                    args.maestro_repo.resolve(), base["upstream"]["commit"], source
                )
            if args.prepare_cache:
                CAPTURE.prepare_cache(sources[0], base)

            modules: list[Path] = []
            builds: list[dict[str, Any]] = []
            all_physical_paths = [temp, *sources, *targets]
            for label, source, target in zip(("a", "b"), sources, targets):
                module, observation = build_module_v3(
                    source, target, registration, base
                )
                retained = partial / "modules" / f"kernel-{label}.ll"
                retained.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(module, retained)
                CAPTURE.assemble(llvm_as, retained)
                data = retained.read_bytes()
                paths = path_observation(data, all_physical_paths, registration)
                modules.append(retained)
                builds.append(
                    {
                        "root": label,
                        "module_bytes": len(data),
                        "module_sha256": CAPTURE.sha256_bytes(data),
                        "module_lines": len(data.splitlines()),
                        **paths,
                        **observation,
                    }
                )

            require_module_identity(builds)
            discovered = [DIAGNOSE.discover_symbols(module.read_bytes()) for module in modules]
            CAPTURE.require(
                discovered[0] == discovered[1],
                "symbols",
                "cross_root_drift",
                str(discovered),
            )
            selected: list[dict[str, Any]] = []
            for target in base["targets"]:
                rows = [
                    DIAGNOSE.selected_projection(
                        module,
                        label,
                        target,
                        symbols[target["name"]],
                        partial / "selected",
                        llvm_extract,
                        llvm_as,
                        admitter,
                    )
                    for module, label, symbols in zip(
                        modules, ("a", "b"), discovered
                    )
                ]
                CAPTURE.require(
                    rows[0]["moduleid_agnostic_sha256"]
                    == rows[1]["moduleid_agnostic_sha256"],
                    "extract",
                    "canonical_drift",
                    target["name"],
                )
                CAPTURE.require(
                    rows[0]["frontend_canonical_sha256"]
                    == rows[1]["frontend_canonical_sha256"],
                    "admission",
                    "canonical_drift",
                    target["name"],
                )
                selected.append(
                    {
                        "name": target["name"],
                        "symbol": discovered[0][target["name"]],
                        "roots": rows,
                    }
                )

        result: dict[str, Any] = {
            "schema": RESULT_SCHEMA,
            "status": "accepted_capture_no_proof",
            "capture_credit": True,
            "registration_sha256": CAPTURE.sha256_file(registration_path),
            "upstream": base["upstream"],
            "tools": {
                "bwrap": bwrap_report,
                "llvm_as": llvm_as_report,
                "llvm_extract": llvm_extract_report,
                **rust_report,
                "admitter_sha256": CAPTURE.sha256_file(admitter),
            },
            "namespace": registration["namespace"],
            "final_rustc_tail": registration["final_rustc_tail"],
            "builds": builds,
            "full_module": {
                "bytes": builds[0]["module_bytes"],
                "sha256": builds[0]["module_sha256"],
                "raw_byte_identical": True,
            },
            "selected": selected,
            "summary": {
                "builds": 2,
                "targets": 3,
                "accepted": 3,
                "dropped": 0,
                "solver_queries": 0,
            },
        }
        result["identity_sha256"] = CAPTURE.sha256_bytes(
            (
                json.dumps(
                    {k: v for k, v in result.items() if k != "identity_sha256"},
                    sort_keys=True,
                    separators=(",", ":"),
                )
                + "\n"
            ).encode()
        )
        (partial / "capture-v3-result.json").write_text(
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
