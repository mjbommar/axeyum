#!/usr/bin/env python3
"""Capture the local-only Maestro device-ID LLVM corpus from ADR-0323."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-maestro-device-id-20260721/capture-registration.json"
)
DEFAULT_MAESTRO = REPO / "references/maestro"
DEFAULT_OUTPUT = REPO / "target/maestro-device-id-20260721/capture"
DEFAULT_ADMITTER = REPO / "target/debug/axeyum-llvm-scalar-admit"
RESULT_SCHEMA = "axeyum.maestro-device-id-capture-result.v1"
ADMISSION_KEYS = {
    "blocks",
    "canonical_bytes",
    "function",
    "instructions",
    "kind",
    "parameter_widths",
    "phis",
    "return_width",
    "stage",
}
MODULE_ID = re.compile(br"^; ModuleID = '[^\r\n]*'\r?\n$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")


class CaptureError(RuntimeError):
    """One stable stage of the capture failed closed."""

    def __init__(self, stage: str, kind: str, detail: str) -> None:
        super().__init__(detail)
        self.stage = stage
        self.kind = kind
        self.detail = detail


def require(condition: bool, stage: str, kind: str, detail: str) -> None:
    if not condition:
        raise CaptureError(stage, kind, detail)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CaptureError("registration", "decode", f"cannot read {path}: {error}") from error
    require(isinstance(value, dict), "registration", "shape", "registration is not an object")
    return value


def command(
    argv: Sequence[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    stage: str,
    kind: str,
    capture: bool = True,
) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        list(argv),
        cwd=cwd,
        env=env,
        check=False,
        text=True,
        capture_output=capture,
    )
    if completed.returncode != 0:
        diagnostic = (completed.stderr or completed.stdout or "").strip()
        raise CaptureError(stage, kind, diagnostic or f"command exited {completed.returncode}")
    return completed


def require_string(value: Any, where: str) -> str:
    require(isinstance(value, str) and bool(value), "registration", "shape", f"{where}: string")
    return value


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == "axeyum.maestro-device-id-capture-registration.v1",
        "registration",
        "schema",
        "registration schema drift",
    )
    upstream = registration.get("upstream")
    require(isinstance(upstream, dict), "registration", "shape", "missing upstream object")
    for field in ("repository", "commit", "tree"):
        require_string(upstream.get(field), f"upstream.{field}")
    require(len(upstream["commit"]) == 40, "registration", "shape", "bad commit")
    require(len(upstream["tree"]) == 40, "registration", "shape", "bad tree")

    critical = registration.get("critical_files")
    require(isinstance(critical, list) and critical, "registration", "shape", "critical files")
    paths: list[str] = []
    for index, entry in enumerate(critical):
        require(isinstance(entry, dict), "registration", "shape", f"critical[{index}]")
        path = require_string(entry.get("path"), f"critical[{index}].path")
        digest = require_string(entry.get("sha256"), f"critical[{index}].sha256")
        require(not Path(path).is_absolute() and ".." not in Path(path).parts,
                "registration", "unsafe_path", path)
        require(bool(SHA256.fullmatch(digest)), "registration", "shape", "bad SHA-256")
        paths.append(path)
    require(paths == sorted(set(paths)), "registration", "ordering", "critical files drift")

    targets = registration.get("targets")
    require(isinstance(targets, list) and len(targets) == 3,
            "registration", "shape", "expected three targets")
    names: list[str] = []
    symbols: list[str] = []
    for index, target in enumerate(targets):
        require(isinstance(target, dict), "registration", "shape", f"target[{index}]")
        name = require_string(target.get("name"), f"target[{index}].name")
        symbol = require_string(target.get("symbol"), f"target[{index}].symbol")
        widths = target.get("parameter_widths")
        result = target.get("return_width")
        require(isinstance(widths, list) and all(isinstance(v, int) for v in widths),
                "registration", "shape", f"target[{index}] widths")
        require(isinstance(result, int), "registration", "shape", f"target[{index}] result")
        names.append(name)
        symbols.append(symbol)
    require(names == ["major", "minor", "makedev"],
            "registration", "ordering", "target order drift")
    require(len(symbols) == len(set(symbols)), "registration", "shape", "duplicate symbol")

    tools = registration.get("tools")
    require(isinstance(tools, dict), "registration", "shape", "missing tools")
    for name in ("llvm_as", "llvm_extract"):
        tool = tools.get(name)
        require(isinstance(tool, dict), "registration", "shape", f"missing {name}")
        require(Path(require_string(tool.get("path"), f"tools.{name}.path")).is_absolute(),
                "registration", "shape", f"{name} path")
        require(bool(SHA256.fullmatch(require_string(tool.get("sha256"), f"tools.{name}.sha256"))),
                "registration", "shape", f"{name} hash")

    producers = registration.get("producer_files")
    require(isinstance(producers, list) and producers,
            "registration", "shape", "missing producer files")
    producer_paths: list[str] = []
    for index, entry in enumerate(producers):
        require(isinstance(entry, dict), "registration", "shape", f"producer[{index}]")
        path = require_string(entry.get("path"), f"producer[{index}].path")
        digest = require_string(entry.get("sha256"), f"producer[{index}].sha256")
        require(not Path(path).is_absolute() and ".." not in Path(path).parts,
                "registration", "unsafe_path", path)
        require(bool(SHA256.fullmatch(digest)), "registration", "shape", "bad producer hash")
        producer_paths.append(path)
    require(producer_paths == sorted(set(producer_paths)),
            "registration", "ordering", "producer files drift")


def git_bytes(repository: Path, commit: str, path: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(repository), "show", f"{commit}:{path}"],
        check=False,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise CaptureError("source", "missing_blob", completed.stderr.decode(errors="replace"))
    return completed.stdout


def validate_source(repository: Path, registration: dict[str, Any]) -> None:
    require(repository.is_dir(), "source", "missing_repository", str(repository))
    upstream = registration["upstream"]
    commit = upstream["commit"]
    status = command(
        ["git", "-C", str(repository), "status", "--porcelain", "--untracked-files=no"],
        stage="source",
        kind="git_status",
    ).stdout
    require(not status, "source", "tracked_modification", status.strip())
    resolved = command(
        ["git", "-C", str(repository), "rev-parse", f"{commit}^{{commit}}"],
        stage="source",
        kind="missing_commit",
    ).stdout.strip()
    tree = command(
        ["git", "-C", str(repository), "rev-parse", f"{commit}^{{tree}}"],
        stage="source",
        kind="missing_tree",
    ).stdout.strip()
    require(resolved == commit, "source", "commit_mismatch", resolved)
    require(tree == upstream["tree"], "source", "tree_mismatch", tree)
    for entry in registration["critical_files"]:
        actual = sha256_bytes(git_bytes(repository, commit, entry["path"]))
        require(actual == entry["sha256"], "source", "critical_hash", entry["path"])


def validate_producers(registration: dict[str, Any]) -> None:
    for entry in registration["producer_files"]:
        path = REPO / entry["path"]
        require(path.is_file(), "registration", "missing_producer", entry["path"])
        require(sha256_file(path) == entry["sha256"],
                "registration", "producer_hash", entry["path"])


def materialize(repository: Path, commit: str, root: Path) -> None:
    root.mkdir(parents=True)
    archive = root.parent / f"{root.name}.tar"
    command(
        ["git", "-C", str(repository), "archive", "--format=tar", f"--output={archive}", commit],
        stage="source",
        kind="archive",
    )
    try:
        with tarfile.open(archive, "r") as tar:
            tar.extractall(root, filter="data")
    except (OSError, tarfile.TarError) as error:
        raise CaptureError("source", "extract_archive", str(error)) from error
    archive.unlink()


def validate_tool(path: Path, expected_hash: str, name: str) -> dict[str, str]:
    require(path.is_file(), "tool", "missing", f"{name}: {path}")
    actual = sha256_file(path.resolve())
    require(actual == expected_hash, "tool", "hash", f"{name}: {actual}")
    version = command([str(path), "--version"], stage="tool", kind="version").stdout
    first = next((line.strip() for line in version.splitlines() if line.strip()), "")
    require(bool(first), "tool", "version", f"{name}: empty version")
    return {"path": str(path), "realpath": str(path.resolve()), "sha256": actual, "version": first}


def rust_tools(toolchain: str) -> dict[str, str]:
    rustc = command(["rustc", f"+{toolchain}", "-Vv"], stage="tool", kind="rustc").stdout
    cargo = command(["cargo", f"+{toolchain}", "-V"], stage="tool", kind="cargo").stdout.strip()
    commit = next((line.split(":", 1)[1].strip() for line in rustc.splitlines()
                   if line.startswith("commit-hash:")), "")
    llvm = next((line.split(":", 1)[1].strip() for line in rustc.splitlines()
                 if line.startswith("LLVM version:")), "")
    require(bool(commit) and bool(llvm), "tool", "rustc_identity", rustc)
    return {"cargo": cargo, "rustc_commit": commit, "rustc_llvm": llvm}


def fixed_env(target_dir: Path, epoch: str) -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        {
            "CARGO_BUILD_JOBS": "1",
            "CARGO_INCREMENTAL": "0",
            "CARGO_PROFILE_RELEASE_DEBUG": "0",
            "CARGO_TARGET_DIR": str(target_dir),
            "SOURCE_DATE_EPOCH": epoch,
        }
    )
    return env


def prepare_cache(root: Path, registration: dict[str, Any]) -> None:
    toolchain = registration["build"]["toolchain"]
    command(
        [
            "cargo",
            f"+{toolchain}",
            "fetch",
            "--locked",
            "--target",
            "arch/x86_64/x86_64.json",
        ],
        cwd=root / "kernel",
        stage="prepare",
        kind="cargo_fetch",
    )


def parse_time_report(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", text)
    require(match is not None, "build", "rss_report", str(path))
    return int(match.group(1))


def build_module(root: Path, target_dir: Path, registration: dict[str, Any]) -> tuple[Path, dict[str, int]]:
    kernel = root / "kernel"
    (kernel / "target/x86_64/release").mkdir(parents=True, exist_ok=True)
    target_dir.mkdir(parents=True)
    timing = target_dir / "time.txt"
    toolchain = registration["build"]["toolchain"]
    cargo = [
        "cargo",
        f"+{toolchain}",
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
        "-Ccodegen-units=1",
        "-Clink-dead-code",
        f"--remap-path-prefix={root}=/axeyum-external/maestro",
        "--emit=llvm-ir",
    ]
    wrapped = [
        "systemd-run", "--user", "--scope", "--quiet",
        "-p", "MemoryHigh=2500M", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=512M",
        "choom", "-n", "200", "--", "/usr/bin/time", "-v", "-o", str(timing), *cargo,
    ]
    started = time.monotonic_ns()
    command(
        wrapped,
        cwd=kernel,
        env=fixed_env(target_dir, registration["build"]["source_date_epoch"]),
        stage="build",
        kind="cargo_rustc",
    )
    wall_ms = (time.monotonic_ns() - started) // 1_000_000
    modules = sorted((target_dir / "x86_64/release/deps").glob("kernel-*.ll"))
    require(len(modules) == 1, "build", "module_count", f"found {len(modules)} modules")
    return modules[0], {"wall_ms": wall_ms, "peak_rss_kib": parse_time_report(timing)}


def assemble(llvm_as: Path, source: Path) -> None:
    command(
        [str(llvm_as), str(source), "-o", "/dev/null"],
        stage="llvm_as",
        kind="rejected",
    )


def definition_count(module: bytes, symbol: str) -> int:
    pattern = re.compile(br"^define\s+[^\r\n]*@" + re.escape(symbol.encode()) + br"\(", re.M)
    return len(pattern.findall(module))


def moduleid_agnostic(data: bytes) -> bytes:
    lines = data.splitlines(keepends=True)
    matches = [index for index, line in enumerate(lines) if MODULE_ID.fullmatch(line)]
    require(matches == [0], "extract", "module_id", f"ModuleID lines: {matches}")
    return b"".join(lines[1:])


def parse_admission(stdout: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in stdout.splitlines():
        require("=" in line, "admission", "output", line)
        key, value = line.split("=", 1)
        require(key not in result, "admission", "output", f"duplicate {key}")
        result[key] = value
    require(set(result) == ADMISSION_KEYS, "admission", "output", f"keys {sorted(result)}")
    require(result["stage"] == "accepted" and result["kind"] == "straight_line_scalar",
            "admission", "declined", stdout)
    return result


def identity_projection(result: dict[str, Any]) -> dict[str, Any]:
    projected = json.loads(json.dumps(result))
    projected.pop("observations", None)
    projected.pop("identity_sha256", None)
    return projected


def run_capture(args: argparse.Namespace) -> dict[str, Any]:
    registration_path = args.registration.resolve()
    registration = read_json(registration_path)
    validate_registration(registration)
    validate_producers(registration)
    validate_source(args.maestro_repo.resolve(), registration)

    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)

    tools = registration["tools"]
    llvm_as = Path(tools["llvm_as"]["path"])
    llvm_extract = Path(tools["llvm_extract"]["path"])
    tool_report = {
        "llvm_as": validate_tool(llvm_as, tools["llvm_as"]["sha256"], "llvm_as"),
        "llvm_extract": validate_tool(
            llvm_extract, tools["llvm_extract"]["sha256"], "llvm_extract"
        ),
    }
    admitter = args.admitter.resolve()
    require(admitter.is_file(), "admission", "missing_binary", str(admitter))
    admitter_hash = sha256_file(admitter)
    rust_report = rust_tools(registration["build"]["toolchain"])
    require(rust_report["rustc_commit"] == registration["build"]["rustc_commit"],
            "tool", "rustc_commit", rust_report["rustc_commit"])
    require(rust_report["rustc_llvm"] == registration["build"]["rustc_llvm"],
            "tool", "rustc_llvm", rust_report["rustc_llvm"])

    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    require(not partial.exists(), "output", "partial_exists", str(partial))
    partial.mkdir()
    try:
        with tempfile.TemporaryDirectory(prefix="maestro-source-", dir=target_root) as raw_temp:
            temp = Path(raw_temp)
            roots = [temp / "root-a", temp / "root-b"]
            for root in roots:
                materialize(args.maestro_repo.resolve(), registration["upstream"]["commit"], root)
            if args.prepare_cache:
                prepare_cache(roots[0], registration)

            build_rows: list[dict[str, Any]] = []
            modules: list[Path] = []
            for label, root in zip(("a", "b"), roots):
                module, observation = build_module(root, temp / f"cargo-{label}", registration)
                retained = partial / "runs" / label / "kernel.ll"
                retained.parent.mkdir(parents=True)
                shutil.copyfile(module, retained)
                assemble(llvm_as, retained)
                modules.append(retained)
                build_rows.append(
                    {
                        "root": label,
                        "module_bytes": retained.stat().st_size,
                        "module_sha256": sha256_file(retained),
                        **observation,
                    }
                )

            require(build_rows[0]["module_bytes"] == build_rows[1]["module_bytes"],
                    "build", "module_size_drift", str(build_rows))
            require(build_rows[0]["module_sha256"] == build_rows[1]["module_sha256"],
                    "build", "module_hash_drift", str(build_rows))

            module_bytes = [path.read_bytes() for path in modules]
            targets: list[dict[str, Any]] = []
            canonical_hashes: set[str] = set()
            for target in registration["targets"]:
                symbol = target["symbol"]
                counts = [definition_count(data, symbol) for data in module_bytes]
                require(counts == [1, 1], "symbols", "definition_count", f"{symbol}: {counts}")
                per_root: list[dict[str, Any]] = []
                for label, module in zip(("a", "b"), modules):
                    extracted = partial / "runs" / label / f"{target['name']}.ll"
                    command(
                        [str(llvm_extract), f"--func={symbol}", "-S", str(module), "-o", str(extracted)],
                        stage="extract",
                        kind="llvm_extract",
                    )
                    assemble(llvm_as, extracted)
                    raw = extracted.read_bytes()
                    agnostic = moduleid_agnostic(raw)
                    frontend = partial / "runs" / label / f"{target['name']}.canonical.ll"
                    admitted = parse_admission(
                        command(
                            [str(admitter), str(extracted), str(frontend)],
                            stage="admission",
                            kind="classifier",
                        ).stdout
                    )
                    assemble(llvm_as, frontend)
                    expected_widths = ",".join(str(v) for v in target["parameter_widths"])
                    require(admitted["function"] == symbol, "admission", "function", symbol)
                    require(admitted["parameter_widths"] == expected_widths,
                            "admission", "parameter_widths", admitted["parameter_widths"])
                    require(int(admitted["return_width"]) == target["return_width"],
                            "admission", "return_width", admitted["return_width"])
                    require(admitted["blocks"] == "1" and admitted["phis"] == "0",
                            "admission", "profile", str(admitted))
                    per_root.append(
                        {
                            "root": label,
                            "raw_bytes": len(raw),
                            "raw_sha256": sha256_bytes(raw),
                            "moduleid_agnostic_sha256": sha256_bytes(agnostic),
                            "frontend_canonical_bytes": frontend.stat().st_size,
                            "frontend_canonical_sha256": sha256_file(frontend),
                            "admission": admitted,
                        }
                    )
                require(per_root[0]["moduleid_agnostic_sha256"] ==
                        per_root[1]["moduleid_agnostic_sha256"],
                        "extract", "canonical_drift", target["name"])
                require(per_root[0]["frontend_canonical_sha256"] ==
                        per_root[1]["frontend_canonical_sha256"],
                        "admission", "canonical_drift", target["name"])
                canonical_hashes.add(per_root[0]["moduleid_agnostic_sha256"])
                targets.append({"name": target["name"], "symbol": symbol, "roots": per_root})
            require(len(canonical_hashes) == 3, "extract", "cross_symbol_collision", "hashes")

        result: dict[str, Any] = {
            "schema": RESULT_SCHEMA,
            "status": "accepted",
            "registration_sha256": sha256_file(registration_path),
            "upstream": registration["upstream"],
            "tools": {**tool_report, **rust_report, "admitter_sha256": admitter_hash},
            "full_module": {
                "bytes": build_rows[0]["module_bytes"],
                "sha256": build_rows[0]["module_sha256"],
                "root_count": 2,
                "byte_identical": True,
            },
            "targets": targets,
            "summary": {"builds": 2, "targets": 3, "accepted": 3, "dropped": 0},
            "observations": {"builds": build_rows},
        }
        result["identity_sha256"] = sha256_bytes(
            (json.dumps(identity_projection(result), sort_keys=True, separators=(",", ":")) + "\n")
            .encode()
        )
        (partial / "capture-result.json").write_text(
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
    parser.add_argument("--maestro-repo", type=Path, default=DEFAULT_MAESTRO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--admitter", type=Path, default=DEFAULT_ADMITTER)
    parser.add_argument("--prepare-cache", action="store_true")
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
