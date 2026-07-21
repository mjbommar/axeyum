#!/usr/bin/env python3
"""Run ADR-0335's authenticated Tock log2 proof scoreboard."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
from pathlib import Path, PurePosixPath
from typing import Any, Sequence


def load_support(path: Path):
    spec = importlib.util.spec_from_file_location("tock_proof_support", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load support module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REPO = Path(__file__).resolve().parents[1]
SUPPORT = load_support(REPO / "scripts/capture-tock-log2.py")
DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-tock-log2-20260721/proof-v1-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/tock-log2-20260721/proof-v1"
LOCAL_CAPTURE = REPO / "target/tock-log2-20260721/capture-v3"
LOCAL_RESULT = LOCAL_CAPTURE / "capture-result.json"
CANONICAL_DIR = LOCAL_CAPTURE / "canonical"
REGISTRATION_SCHEMA = "axeyum.tock-log2-proof-v1-registration.v1"
RESULT_SCHEMA = "axeyum.tock-log2-proof-v1-result.v1"
EXPECTED_RESOURCE_SCOPE = {
    "memory_high_bytes": 2_621_440_000,
    "memory_max_bytes": 4_294_967_296,
    "swap_max_bytes": 536_870_912,
}
EXPECTED_COMMAND = [
    "test",
    "--locked",
    "--offline",
    "-p",
    "axeyum-verify",
    "--test",
    "tock_log2_external",
    "authenticated_tock_log2_scoreboard",
    "--",
    "--ignored",
    "--exact",
    "--nocapture",
    "--test-threads=1",
]
EXPECTED_SOLVER = {
    "backend": "pure-rust-qfbv",
    "cnf_clause_budget": 5_000_000,
    "cnf_variable_budget": 1_000_000,
    "memory_limit_mb": 2_048,
    "node_budget": 250_000,
    "policy_toggles": {
        "bit_lowering_mode": "eager",
        "cnf_inprocessing": False,
        "cnf_vivify": False,
        "lazy_bv": False,
        "lazy_bv_abstract_ite": False,
        "native_cdcl": False,
        "preprocess": False,
        "xor_cdcl_fallback": False,
    },
    "prove_unsat": True,
    "resource_limit": 5_000_000,
    "timeout_seconds": 30,
}
EXPECTED_ROWS = {
    "functions": 2,
    "proofs": 8,
    "controls": 6,
    "unknown": 0,
    "disagree": 0,
}
EXPECTED_PROPERTIES = {
    (target, property_name)
    for target in ("log_base_two", "log_base_two_u64")
    for property_name in ("defined", "zero", "floor_log2", "msb")
}
EXPECTED_CONTROLS = {
    (target, mutation)
    for target in ("log_base_two", "log_base_two_u64")
    for mutation in ("wrong_index", "inverted_zero", "high_partition")
}
TOTAL_TIMEOUT_SECONDS = 600


CaptureError = SUPPORT.CaptureError
fail = SUPPORT.fail
require = SUPPORT.require


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return SUPPORT.sha256_file(path)


def read_registration(path: Path) -> dict[str, Any]:
    registration = SUPPORT.read_json(path)
    required = {
        "schema",
        "capture",
        "canonical",
        "source_files",
        "producer_files",
        "tools",
        "command",
        "solver",
        "expected_rows",
        "resource_scope",
    }
    require(
        set(registration) == required,
        "registration",
        "fields",
        str(sorted(registration)),
    )
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "registration",
        "schema",
        str(registration.get("schema")),
    )
    require(
        registration.get("command") == EXPECTED_COMMAND,
        "registration",
        "command",
        str(registration.get("command")),
    )
    require(
        registration.get("solver") == EXPECTED_SOLVER,
        "registration",
        "solver",
        str(registration.get("solver")),
    )
    require(
        registration.get("expected_rows") == EXPECTED_ROWS,
        "registration",
        "expected_rows",
        str(registration.get("expected_rows")),
    )
    require(
        registration.get("resource_scope") == EXPECTED_RESOURCE_SCOPE,
        "registration",
        "resource_scope",
        str(registration.get("resource_scope")),
    )
    for field in ("producer_files", "source_files"):
        rows = registration.get(field)
        require(isinstance(rows, list) and rows, "registration", "shape", field)
        paths = [row.get("path") for row in rows]
        require(paths == sorted(set(paths)), "registration", f"{field}_order", str(paths))
        for row in rows:
            path_value = row.get("path")
            digest = row.get("sha256")
            require(isinstance(path_value, str), "registration", "shape", field)
            require(isinstance(digest, str), "registration", "shape", field)
            if field == "producer_files":
                SUPPORT.validate_file(REPO / path_value, digest, "registration", field)
    tools = registration.get("tools")
    require(
        isinstance(tools, dict) and set(tools) == {"cargo", "git", "gnu_time", "rustc"},
        "registration",
        "tools",
        str(tools),
    )
    for name, entry in tools.items():
        SUPPORT.tool_report(entry, name)
    return registration


def validate_capture(registration: dict[str, Any]) -> dict[str, Any]:
    capture = registration["capture"]
    committed = REPO / capture["committed_result"]["path"]
    SUPPORT.validate_file(
        committed,
        capture["committed_result"]["sha256"],
        "capture",
        "committed_result",
    )
    SUPPORT.validate_file(
        LOCAL_RESULT,
        capture["local_result_sha256"],
        "capture",
        "local_result",
    )
    committed_result = SUPPORT.read_json(committed)
    local_result = SUPPORT.read_json(LOCAL_RESULT)
    require(
        committed_result.get("capture_identity_sha256") == capture["identity_sha256"]
        and local_result.get("identity_sha256") == capture["identity_sha256"],
        "capture",
        "identity",
        str(capture),
    )
    require(
        committed_result.get("module", {}).get("sha256") == capture["module_sha256"],
        "capture",
        "module",
        str(committed_result.get("module")),
    )
    canonical = registration["canonical"]
    require(
        isinstance(canonical, list) and len(canonical) == 2,
        "capture",
        "canonical_shape",
        str(canonical),
    )
    for entry in canonical:
        path = CANONICAL_DIR / entry["file"]
        SUPPORT.validate_file(path, entry["sha256"], "capture", "canonical")
        require(path.stat().st_size == entry["bytes"], "capture", "canonical_size", str(path))
        match = next(
            (row for row in committed_result["targets"] if row["name"] == entry["name"]),
            None,
        )
        require(
            match is not None
            and match["canonical_sha256"] == entry["sha256"]
            and match["canonical_bytes"] == entry["bytes"]
            and match["instructions"] == entry["instructions"]
            and match["parameter_widths"] == [entry["width"]],
            "capture",
            "canonical_metadata",
            str(entry),
        )
    return committed_result


def git_output(registration: dict[str, Any], *args: str) -> str:
    result = SUPPORT.command(
        [registration["tools"]["git"]["path"], *args],
        stage="source",
        kind="git",
        cwd=REPO,
    )
    return result.stdout.strip()


def validate_pushed_head(
    registration: dict[str, Any], registration_path: Path
) -> dict[str, str]:
    head = git_output(registration, "rev-parse", "HEAD")
    tracking = git_output(registration, "rev-parse", "@{u}")
    tree = git_output(registration, "rev-parse", "HEAD^{tree}")
    require(len(head) == 40 and head == tracking, "source", "tracking", f"{head} {tracking}")
    require(len(tree) == 40, "source", "tree", tree)
    resolved_registration = registration_path.resolve()
    require(
        resolved_registration.is_relative_to(REPO),
        "source",
        "registration_path",
        str(resolved_registration),
    )
    registration_relative = resolved_registration.relative_to(REPO).as_posix()
    committed_registration = subprocess.run(
        [
            registration["tools"]["git"]["path"],
            "show",
            f"HEAD:{registration_relative}",
        ],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(
        committed_registration.returncode == 0
        and committed_registration.stdout == resolved_registration.read_bytes(),
        "source",
        "registration_head_drift",
        registration_relative,
    )
    for field in ("producer_files", "source_files"):
        for row in registration[field]:
            result = subprocess.run(
                [
                    registration["tools"]["git"]["path"],
                    "show",
                    f"HEAD:{row['path']}",
                ],
                cwd=REPO,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            require(result.returncode == 0, "source", "head_file", row["path"])
            require(
                sha256_bytes(result.stdout) == row["sha256"],
                "source",
                "head_file_hash",
                row["path"],
            )
    return {"commit": head, "tree": tree, "tracking": tracking}


def safe_extract(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, mode="r:") as stream:
        members = stream.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            require(
                not path.is_absolute() and ".." not in path.parts,
                "source",
                "archive_path",
                member.name,
            )
        stream.extractall(destination, members=members, filter="data")


def materialize_head(registration: dict[str, Any], destination: Path) -> None:
    archive = destination.parent / "axeyum-head.tar"
    with archive.open("wb") as output:
        result = subprocess.run(
            [
                registration["tools"]["git"]["path"],
                "archive",
                "--format=tar",
                "HEAD",
            ],
            cwd=REPO,
            stdout=output,
            stderr=subprocess.PIPE,
            check=False,
        )
    require(result.returncode == 0, "source", "archive", result.stderr.decode(errors="replace"))
    destination.mkdir()
    safe_extract(archive, destination)
    for field in ("producer_files", "source_files"):
        for row in registration[field]:
            SUPPORT.validate_file(
                destination / row["path"],
                row["sha256"],
                "source",
                "archive_file",
            )


def parse_fields(line: str, prefix: str) -> dict[str, str]:
    require(line.startswith(prefix + "|"), "result", "row_prefix", line)
    fields: dict[str, str] = {}
    for component in line.split("|")[1:]:
        key, separator, value = component.partition("=")
        require(bool(separator) and bool(key) and bool(value), "result", "row_field", component)
        require(key not in fields, "result", "row_duplicate_field", key)
        fields[key] = value
    return fields


def numeric(row: dict[str, str], field: str, *, positive: bool) -> int:
    try:
        value = int(row[field])
    except (KeyError, ValueError) as error:
        fail("result", "numeric", f"{field}: {error}")
    require(value > 0 if positive else value >= 0, "result", "numeric", f"{field}={value}")
    return value


def parse_runner_output(stdout: str) -> dict[str, Any]:
    proof_rows = [parse_fields(line, "TOCK_PROOF") for line in stdout.splitlines() if line.startswith("TOCK_PROOF|")]
    control_rows = [parse_fields(line, "TOCK_CONTROL") for line in stdout.splitlines() if line.startswith("TOCK_CONTROL|")]
    score_rows = [parse_fields(line, "TOCK_SCOREBOARD") for line in stdout.splitlines() if line.startswith("TOCK_SCOREBOARD|")]
    require(len(proof_rows) == 8, "result", "proof_count", str(len(proof_rows)))
    require(len(control_rows) == 6, "result", "control_count", str(len(control_rows)))
    require(len(score_rows) == 1, "result", "score_count", str(len(score_rows)))
    proof_keys = {(row.get("target"), row.get("property")) for row in proof_rows}
    control_keys = {(row.get("target"), row.get("mutation")) for row in control_rows}
    require(proof_keys == EXPECTED_PROPERTIES, "result", "proof_keys", str(proof_keys))
    require(control_keys == EXPECTED_CONTROLS, "result", "control_keys", str(control_keys))
    for row in proof_rows:
        require(row.get("outcome") == "proved", "result", "proof_outcome", str(row))
        require(
            row.get("evidence") in {"alethe_bitblast_resolution", "drat"},
            "result",
            "proof_evidence",
            str(row),
        )
        trust = row.get("trust", "").split(",")
        require(trust and all(value.endswith(":certified") for value in trust), "result", "proof_trust", str(row))
        for field in ("width", "terms", "wall_us"):
            numeric(row, field, positive=True)
    for row in control_rows:
        require(
            row.get("outcome") == "disproved" and row.get("replay") == "pass",
            "result",
            "control_outcome",
            str(row),
        )
        require(row.get("reflected") == row.get("native"), "result", "control_disagree", str(row))
        require(row.get("mutated") != row.get("native"), "result", "control_nondiscriminating", str(row))
        numeric(row, "width", positive=True)
        numeric(row, "wall_us", positive=True)
        for field in ("witness", "reflected", "native", "mutated"):
            numeric(row, field, positive=False)
    score = score_rows[0]
    expected_score = {
        "functions": "2",
        "proved": "8",
        "refuted_replayed": "6",
        "unknown": "0",
        "disagree": "0",
    }
    require(
        all(score.get(key) == value for key, value in expected_score.items()),
        "result",
        "scoreboard",
        str(score),
    )
    numeric(score, "query_wall_us", positive=True)
    numeric(score, "runner_wall_us", positive=True)
    proof_rows.sort(key=lambda row: (row["target"], row["property"]))
    control_rows.sort(key=lambda row: (row["target"], row["mutation"]))
    return {"proofs": proof_rows, "controls": control_rows, "scoreboard": score}


def parse_time(path: Path) -> dict[str, int]:
    values: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        key, separator, value = line.partition("=")
        require(bool(separator), "result", "time_format", line)
        if key == "wall_seconds":
            values["wall_ms"] = round(float(value) * 1000)
        elif key == "peak_rss_kib":
            values["peak_rss_kib"] = int(value)
    require(set(values) == {"wall_ms", "peak_rss_kib"}, "result", "time_fields", str(values))
    return values


def result_identity(result: dict[str, Any]) -> str:
    projected = json.loads(json.dumps(result))
    projected.pop("observations", None)
    projected.pop("identity_sha256", None)
    for field in ("proofs", "controls"):
        for row in projected.get(field, []):
            row.pop("wall_us", None)
    return sha256_bytes((json.dumps(projected, sort_keys=True, separators=(",", ":")) + "\n").encode())


def run_scoreboard(args: argparse.Namespace) -> dict[str, Any]:
    registration = read_registration(args.registration.resolve())
    validate_capture(registration)
    source = validate_pushed_head(registration, args.registration.resolve())
    output = args.output.resolve()
    target_root = (REPO / "target/tock-log2-20260721").resolve()
    require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    require(not output.exists(), "output", "exists", str(output))
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    require(not partial.exists(), "output", "partial_exists", str(partial))
    resource_before = SUPPORT.resource_snapshot()
    partial.mkdir(parents=True)
    try:
        with tempfile.TemporaryDirectory(prefix="tock-log2-proof-") as raw:
            temporary = Path(raw)
            source_root = temporary / "source"
            materialize_head(registration, source_root)
            build_root = partial / "build"
            build_root.mkdir()
            timing_path = partial / "time.txt"
            stdout_path = partial / "stdout.log"
            stderr_path = partial / "stderr.log"
            environment = {
                "CARGO_BUILD_JOBS": "1",
                "CARGO_HOME": "/home/mjbommar/.cargo",
                "CARGO_INCREMENTAL": "0",
                "CARGO_NET_OFFLINE": "true",
                "CARGO_PROFILE_DEV_DEBUG": "0",
                "CARGO_PROFILE_TEST_DEBUG": "0",
                "CARGO_TARGET_DIR": str(build_root),
                "HOME": "/home/mjbommar",
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "PATH": "/home/mjbommar/.rustup/toolchains/nightly-2026-04-21-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin",
                "RUSTC": registration["tools"]["rustc"]["path"],
                "RUSTUP_HOME": "/home/mjbommar/.rustup",
                "AXEYUM_TOCK_CANONICAL_DIR": str(CANONICAL_DIR.resolve()),
            }
            command = [
                registration["tools"]["gnu_time"]["path"],
                "-f",
                "wall_seconds=%e\npeak_rss_kib=%M",
                "-o",
                str(timing_path),
                registration["tools"]["cargo"]["path"],
                *EXPECTED_COMMAND,
            ]
            started = time.monotonic_ns()
            try:
                completed = subprocess.run(
                    command,
                    cwd=source_root,
                    env=environment,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=TOTAL_TIMEOUT_SECONDS,
                    check=False,
                )
            except subprocess.TimeoutExpired as error:
                fail("runner", "timeout", str(error))
            total_wall_ms = (time.monotonic_ns() - started) // 1_000_000
            stdout_path.write_text(completed.stdout, encoding="utf-8")
            stderr_path.write_text(completed.stderr, encoding="utf-8")
            require(
                completed.returncode == 0,
                "runner",
                "cargo_test",
                completed.stderr.strip() or completed.stdout.strip(),
            )
            parsed = parse_runner_output(completed.stdout)
            timing = parse_time(timing_path)
            resource_after = SUPPORT.resource_snapshot()
            oom_deltas = SUPPORT.resource_delta(resource_before, resource_after)
            result: dict[str, Any] = {
                "schema": RESULT_SCHEMA,
                "status": "accepted",
                "capture": registration["capture"],
                "canonical": registration["canonical"],
                "runner": source,
                "solver": registration["solver"],
                "proofs": parsed["proofs"],
                "controls": parsed["controls"],
                "scoreboard": {
                    "functions": 2,
                    "proved": 8,
                    "refuted_replayed": 6,
                    "unknown": 0,
                    "disagree": 0,
                },
                "tools": {
                    name: {"path": entry["path"], "sha256": entry["sha256"], "version": entry["version"]}
                    for name, entry in registration["tools"].items()
                },
                "observations": {
                    "cargo_wall_ms": timing["wall_ms"],
                    "outer_wall_ms": total_wall_ms,
                    "peak_rss_kib": timing["peak_rss_kib"],
                    "query_wall_us": int(parsed["scoreboard"]["query_wall_us"]),
                    "runner_wall_us": int(parsed["scoreboard"]["runner_wall_us"]),
                    "resource": {
                        "before": resource_before,
                        "after": resource_after,
                        "oom_deltas": oom_deltas,
                    },
                },
            }
            result["identity_sha256"] = result_identity(result)
            (partial / "proof-result.json").write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
        partial.rename(output)
        return result
    except BaseException as error:
        shutil.rmtree(partial, ignore_errors=True)
        try:
            SUPPORT.resource_delta(resource_before, SUPPORT.resource_snapshot())
        except CaptureError as resource_error:
            if resource_error.stage == "resource" and resource_error.kind == "oom_delta":
                raise resource_error from error
        raise


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
