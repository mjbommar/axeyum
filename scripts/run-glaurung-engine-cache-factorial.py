#!/usr/bin/env python3
"""Run ADR-0303's frozen six-mode engine-cache/warm-state factorial."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import pathlib
import subprocess
import sys
from typing import Any, Sequence


REGISTRATION_SCHEMA = "axeyum-glaurung-engine-cache-factorial-registration-v1"
CAMPAIGN_SCHEMA = "axeyum-glaurung-engine-cache-factorial-campaign-v1"
REPORT_SCHEMA = "glaurung-native-ordered-replay-report-v2"
MODES = (
    "cold-off",
    "warm-off",
    "cold-exact",
    "warm-exact",
    "cold-structural",
    "warm-structural",
)
MODE_POLICY = {
    "cold-off": ("off", "off"),
    "warm-off": ("adaptive", "off"),
    "cold-exact": ("off", "exact"),
    "warm-exact": ("adaptive", "exact"),
    "cold-structural": ("off", "structural"),
    "warm-structural": ("adaptive", "structural"),
}


class CampaignError(RuntimeError):
    """The registered campaign cannot proceed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CampaignError(message)


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_output(command: Sequence[str], cwd: pathlib.Path) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return completed.stdout.strip()


def read_object(path: pathlib.Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_bytes())
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CampaignError(f"cannot read {label} {path}: {error}") from error
    require(isinstance(value, dict), f"{label} must be a JSON object")
    return value


def write_json(path: pathlib.Path, value: Any) -> None:
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def verify_file(row: dict[str, Any], root: pathlib.Path, label: str) -> pathlib.Path:
    raw_path = row.get("path")
    expected = row.get("sha256")
    require(isinstance(raw_path, str) and raw_path, f"{label}.path is invalid")
    require(isinstance(expected, str) and len(expected) == 64, f"{label}.sha256 is invalid")
    path = pathlib.Path(raw_path)
    if not path.is_absolute():
        path = root / path
    require(path.is_file(), f"{label} is absent: {path}")
    require(sha256_file(path) == expected, f"{label} SHA-256 differs: {path}")
    return path.resolve()


def verify_git_source(row: dict[str, Any], root: pathlib.Path, label: str) -> None:
    expected = row.get("revision")
    require(isinstance(expected, str) and len(expected) == 40, f"{label} revision is invalid")
    require(
        command_output(["git", "rev-parse", "HEAD"], root) == expected,
        f"{label} revision differs",
    )
    require(
        not command_output(["git", "status", "--short"], root),
        f"{label} worktree is dirty",
    )


def sanitize_environment(
    base: dict[str, str], mode: str, axeyum_root: pathlib.Path
) -> dict[str, str]:
    environment = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith(("GLAURUNG_", "AXEYUM_", "IOCTLANCE_", "BITWUZLA_"))
        and key != "LD_LIBRARY_PATH"
    }
    warm, cache = MODE_POLICY[mode]
    environment.update(base)
    environment.update(
        {
            "GLAURUNG_ENGINE_CACHE_FACTORIAL_MODE": mode,
            "GLAURUNG_ENGINE_CONSTRAINT_CACHE": cache,
            "GLAURUNG_AXEYUM_WARM_REUSE": warm,
            "GLAURUNG_AXEYUM_SOURCE_REPO": str(axeyum_root),
        }
    )
    return environment


def input_identity(row: dict[str, Any], axeyum_root: pathlib.Path) -> dict[str, Any]:
    trace = pathlib.Path(str(row.get("trace_path", "")))
    require(trace.is_dir(), f"trace is absent: {trace}")
    manifest = verify_file(
        {
            "path": str(trace / "trace-manifest-v1.json"),
            "sha256": row.get("manifest_sha256"),
        },
        pathlib.Path("/"),
        "trace manifest",
    )
    manifest_value = read_object(manifest, "trace manifest")
    require(manifest_value.get("schema") == "glaurung-ordered-trace-v1", "trace schema differs")
    events = trace / "events-v1.ndjson"
    index = trace / "query-index-v1.json"
    require(events.is_file() and index.is_file(), f"trace payload is incomplete: {trace}")
    require(
        sha256_file(events) == manifest_value.get("events_sha256"),
        f"event hash differs: {trace}",
    )
    require(
        sha256_file(index) == manifest_value.get("query_index_sha256"),
        f"query-index hash differs: {trace}",
    )
    finding = verify_file(row.get("finding_artifact", {}), axeyum_root, "finding artifact")
    offline = verify_file(row.get("offline_replay", {}), axeyum_root, "offline replay")
    return {
        "driver": row.get("driver"),
        "repetition": row.get("repetition"),
        "trace_path": str(trace.resolve()),
        "manifest_sha256": row.get("manifest_sha256"),
        "events_sha256": manifest_value.get("events_sha256"),
        "query_index_sha256": manifest_value.get("query_index_sha256"),
        "finding_path": str(finding),
        "finding_sha256": row["finding_artifact"]["sha256"],
        "offline_replay_path": str(offline),
        "offline_replay_sha256": row["offline_replay"]["sha256"],
        "expected_cache": row.get("expected_cache"),
    }


def preflight(
    registration_path: pathlib.Path,
    axeyum_root: pathlib.Path,
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    output_root: pathlib.Path | None,
    *,
    require_output: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    registration = read_object(registration_path, "registration")
    require(registration.get("schema") == REGISTRATION_SCHEMA, "registration schema differs")
    require(registration.get("zero_result_rows") is True, "registration already contains observations")
    sources = registration.get("sources")
    require(isinstance(sources, dict), "registration.sources is invalid")
    verify_git_source(sources.get("axeyum", {}), axeyum_root, "Axeyum")
    verify_git_source(sources.get("glaurung", {}), glaurung_root, "Glaurung")
    verify_file(sources.get("six_cell_registration", {}), axeyum_root, "ADR-0272 registration")
    verify_file(sources.get("opportunity", {}), axeyum_root, "opportunity result")

    protocol = registration.get("protocol")
    require(isinstance(protocol, dict), "registration.protocol is invalid")
    require(tuple(protocol.get("modes", ())) == MODES, "registered mode order differs")
    require(protocol.get("repetitions_per_driver") == 5, "repetition count differs")
    require(protocol.get("process_count") == 120, "process count differs")
    require(protocol.get("logical_cpu") in os.sched_getaffinity(0), "registered CPU is unavailable")
    verify_file(protocol.get("runner", {}), axeyum_root, "runner")
    verify_file(protocol.get("analyzer", {}), axeyum_root, "analyzer")

    registered_executable = registration.get("executable")
    require(isinstance(registered_executable, dict), "registration.executable is invalid")
    require(executable.is_file(), f"replay executable is absent: {executable}")
    require(
        sha256_file(executable) == registered_executable.get("sha256"),
        "replay executable SHA-256 differs",
    )
    for index, library in enumerate(registered_executable.get("dynamic_libraries", [])):
        verify_file(library, pathlib.Path("/"), f"dynamic library {index}")

    inputs = registration.get("inputs")
    require(isinstance(inputs, list) and len(inputs) == 20, "registration must bind 20 traces")
    identities = [input_identity(row, axeyum_root) for row in inputs]
    expected_pairs = [
        (driver, repetition)
        for driver in protocol.get("driver_order", [])
        for repetition in range(1, 6)
    ]
    require(
        [(row["driver"], row["repetition"]) for row in identities] == expected_pairs,
        "input driver/repetition order differs",
    )
    if require_output:
        require(output_root is not None and output_root.is_dir(), "output root must exist")
        require(not any(output_root.iterdir()), "output root must be empty")
    campaign = {
        "schema": CAMPAIGN_SCHEMA,
        "registration_path": str(registration_path.resolve()),
        "registration_sha256": sha256_file(registration_path),
        "started_utc": utc_now(),
        "sources": sources,
        "executable": {"path": str(executable.resolve()), **registered_executable},
        "protocol": protocol,
        "inputs": identities,
        "runs": [],
        "terminal_status": "preflight",
    }
    return registration, campaign


def run_campaign(
    registration: dict[str, Any],
    campaign: dict[str, Any],
    axeyum_root: pathlib.Path,
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    output_root: pathlib.Path,
) -> None:
    protocol = registration["protocol"]
    campaign_path = output_root / "campaign.json"
    campaign["terminal_status"] = "running"
    write_json(campaign_path, campaign)
    base_environment = protocol["environment"]
    for mode in MODES:
        for input_row in campaign["inputs"]:
            run_name = f"{mode}--{input_row['driver']}--r{input_row['repetition']}"
            run_root = output_root / run_name
            run_root.mkdir()
            report_path = run_root / "report.json"
            time_path = run_root / "time.txt"
            command = [
                "systemd-run",
                "--user",
                "--scope",
                "--quiet",
                "-p",
                f"MemoryHigh={protocol['cgroup']['memory_high']}",
                "-p",
                f"MemoryMax={protocol['cgroup']['memory_max']}",
                "-p",
                f"MemorySwapMax={protocol['cgroup']['memory_swap_max']}",
                "choom",
                "-n",
                str(protocol["oom_score_adjust"]),
                "--",
                "/usr/bin/time",
                "-v",
                "-o",
                str(time_path),
                "taskset",
                "-c",
                str(protocol["logical_cpu"]),
                str(executable),
                input_row["trace_path"],
                input_row["finding_sha256"],
                input_row["offline_replay_sha256"],
                str(report_path),
            ]
            record = {
                "run": run_name,
                "mode": mode,
                "driver": input_row["driver"],
                "repetition": input_row["repetition"],
                "command": command,
                "started_utc": utc_now(),
                "report_path": str(report_path),
                "time_path": str(time_path),
            }
            campaign["runs"].append(record)
            write_json(campaign_path, campaign)
            with (run_root / "stdout.log").open("wb") as stdout, (
                run_root / "stderr.log"
            ).open("wb") as stderr:
                completed = subprocess.run(
                    command,
                    cwd=glaurung_root,
                    env=sanitize_environment(base_environment, mode, axeyum_root),
                    stdout=stdout,
                    stderr=stderr,
                    check=False,
                )
            record["ended_utc"] = utc_now()
            record["return_code"] = completed.returncode
            if completed.returncode == 0 and report_path.is_file():
                report = read_object(report_path, "native replay report")
                record["report_sha256"] = sha256_file(report_path)
                record["report_gate"] = report.get("gate")
                record["report_schema"] = report.get("schema")
                record["reported_mode"] = report.get("configuration", {}).get("factorial_mode")
            valid = (
                completed.returncode == 0
                and record.get("report_schema") == REPORT_SCHEMA
                and record.get("report_gate") == "pass"
                and record.get("reported_mode") == mode
                and time_path.is_file()
            )
            record["validation"] = "accepted" if valid else "failed"
            write_json(run_root / "run-record.json", record)
            write_json(campaign_path, campaign)
            if not valid:
                campaign["terminal_status"] = "failed"
                campaign["ended_utc"] = utc_now()
                write_json(campaign_path, campaign)
                raise CampaignError(f"run failed closed: {run_name}")
    campaign["terminal_status"] = "complete"
    campaign["ended_utc"] = utc_now()
    write_json(campaign_path, campaign)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", required=True, type=pathlib.Path)
    parser.add_argument("--axeyum-root", required=True, type=pathlib.Path)
    parser.add_argument("--glaurung-root", required=True, type=pathlib.Path)
    parser.add_argument("--executable", required=True, type=pathlib.Path)
    parser.add_argument("--output-root", type=pathlib.Path)
    parser.add_argument("--preflight-only", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if not args.preflight_only and args.output_root is None:
        print("factorial campaign failed: --output-root is required", file=sys.stderr)
        return 2
    try:
        registration, campaign = preflight(
            args.registration.resolve(),
            args.axeyum_root.resolve(),
            args.glaurung_root.resolve(),
            args.executable.resolve(),
            args.output_root.resolve() if args.output_root else None,
            require_output=not args.preflight_only,
        )
        if args.preflight_only:
            print(json.dumps(campaign, indent=2, sort_keys=True))
            return 0
        run_campaign(
            registration,
            campaign,
            args.axeyum_root.resolve(),
            args.glaurung_root.resolve(),
            args.executable.resolve(),
            args.output_root.resolve(),
        )
    except (CampaignError, OSError, subprocess.SubprocessError) as error:
        print(f"factorial campaign failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
