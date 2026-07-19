#!/usr/bin/env python3
"""Execute ADR-0273's 14-tier deterministic six-cell calibration."""

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


GLAURUNG_REVISION = "dc06a3740d989f5a71f3a1cef4ba5111c5188f36"
EXECUTABLE_SHA256 = "d96520a04d5dd4825957dc3e07e1fd11a24bad220c55baae539ec9f8a10db5f7"
REGISTERED_DYNAMIC_LIBRARIES = {
    "/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzla.so.0": "4e994b7a527e207dfdde3dcc289133f72e423e54e4ce67ba8ff2211c1b48bb1c",
    "/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlabb.so": "3bc0a9fb5f1d4f5799ba2c71aec40b3616ad04a03942e5d23f639bb96b64a75b",
    "/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlabv.so": "df3ffc2e41e92ff04c017b77b0e5b14b391ae687482542d47162b90aae0bfab3",
    "/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlals.so": "83e70c846dcf33d0c8a3ecdf88e74b9fc7ce48de3aa1fc034c130190ab1365da",
    "/lib64/ld-linux-x86-64.so.2": "223b94a42758f2434da331cc0aa62db1af5b456481762c5caceefa1a2d1eb8fb",
    "/usr/lib/x86_64-linux-gnu/libc.so.6": "d763925433ff9b757390549e1b20c085f5e6de27ae700fe89194178d96a8a2b0",
    "/usr/lib/x86_64-linux-gnu/libgcc_s.so.1": "9d339ecb409578d6a5d587e6c537a8f9589b8a13fefba30d167433a4b5758bee",
    "/usr/lib/x86_64-linux-gnu/libgmp.so.10": "fda9699eef15deda5f1c626e9140377a7f5d88c41516a54278ac02429cb20fa5",
    "/usr/lib/x86_64-linux-gnu/libm.so.6": "670fb59bd462ee2f833e2ed7c0a1814e0dcdbec0b8bfa048bec46e2e6fd66334",
    "/usr/lib/x86_64-linux-gnu/libmpfr.so.6": "1aed080b3143049fbe016cd82cdc5fb47db386386556cc1bb37cfccc133c0fae",
    "/usr/lib/x86_64-linux-gnu/libstdc++.so.6": "5bb0d21308f123b6ad46c6f35b42cedfcb8d6d439a53aa3dae04d880aaffdde3",
    "/usr/lib/x86_64-linux-gnu/libz3.so.4": "eff8f0f91482d0809aae7aa0ed54cb52ff5ee9b5fe1ed1d2bfa9153c4a2fcfaf",
}
DRIVER_PATH = pathlib.Path(
    "/nas4/data/workspace-infosec/glaurung/tests/fixtures/msvc-pdb/tcpip.sys"
)
DRIVER_SHA256 = "ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea"
CPU = 2
REPETITIONS = 3
PROCESS_TIMEOUT_SECONDS = 2_700
LADDERS = (
    (3, 1, 1),
    (10, 2, 2),
    (30, 4, 4),
    (100, 8, 8),
    (300, 16, 16),
    (1_000, 32, 32),
    (3_000, 64, 64),
    (10_000, 128, 128),
    (30_000, 256, 256),
    (100_000, 512, 512),
    (300_000, 1_024, 1_024),
    (1_000_000, 2_048, 2_048),
    (3_000_000, 4_096, 4_096),
    (10_000_000, 8_192, 8_192),
)
AXEYUM_TREE_IDENTITIES = {
    "crates/axeyum-solver": "19774056908200a85aa986e3b7da5ceeb386c56a",
    "crates/axeyum-cnf": "8a87bca7490eaf666fbe4fcf9c054101796f5c3c",
    "crates/axeyum-ir": "ed3649e3a52fbd602327ea523db49bac3a883b6a",
    "Cargo.toml": "e1351bec59d6601b6a60c774f1d00a01be1dc3e4",
    "Cargo.lock": "2738bf0d289afea537f444fe0152b040f68278fa",
}
FIXED_ENVIRONMENT = {
    "GLAURUNG_FAIR_SHADOW": "1",
    "GLAURUNG_CHECK_TIMEOUT_MS": "60000",
    "GLAURUNG_AXEYUM_REPLAY_SAT_CACHE": "1",
    "GLAURUNG_AXEYUM_WARM_MAX_LIVE_PATHS": "9",
    "GLAURUNG_AXEYUM_WARM_MAX_ASSERTIONS_PER_PATH": "512",
    "IOCTLANCE_ALL": "1",
    "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
    "IOCTLANCE_DEADLINE_SECS": "2400",
    "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "20",
    "IOCTLANCE_SOLVE_BUDGET": "400000",
    "IOCTLANCE_SOLVE_SECS": "900",
}
MEMORY_GUARD = pathlib.Path(__file__).with_name("mem-run.sh")
AXEYUM_ROOT = pathlib.Path(__file__).resolve().parents[1]


class CampaignError(RuntimeError):
    """The registered calibration cannot proceed."""


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


def resolved_dynamic_libraries(linkage: str) -> dict[str, str]:
    libraries: dict[str, str] = {}
    for line in linkage.splitlines():
        fields = line.strip().split()
        if not fields:
            continue
        candidate = fields[2] if len(fields) >= 3 and fields[1] == "=>" else fields[0]
        if not candidate.startswith("/"):
            continue
        path = pathlib.Path(candidate)
        if not path.is_file():
            raise CampaignError(f"resolved dynamic library is absent: {path}")
        libraries[str(path)] = sha256_file(path)
    if not libraries:
        raise CampaignError("ldd resolved no file-backed dynamic libraries")
    return dict(sorted(libraries.items()))


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def write_json(path: pathlib.Path, value: Any) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def planned_runs() -> list[dict[str, int]]:
    return [
        {
            "tier": tier,
            "repetition": repetition,
            "z3_rlimit": z3,
            "axeyum_progress_checks": axeyum,
            "bitwuzla_termination_polls": bitwuzla,
        }
        for tier, (z3, axeyum, bitwuzla) in enumerate(LADDERS)
        for repetition in range(1, REPETITIONS + 1)
    ]


def sanitize_environment(
    trace_root: pathlib.Path, planned: dict[str, int]
) -> dict[str, str]:
    environment = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith(("GLAURUNG_", "IOCTLANCE_", "BITWUZLA_"))
        and key != "LD_LIBRARY_PATH"
    }
    environment.update(FIXED_ENVIRONMENT)
    environment.update(
        {
            "GLAURUNG_Z3_RLIMIT": str(planned["z3_rlimit"]),
            "GLAURUNG_AXEYUM_PROGRESS_CHECK_LIMIT": str(
                planned["axeyum_progress_checks"]
            ),
            "GLAURUNG_BITWUZLA_TERMINATION_POLL_LIMIT": str(
                planned["bitwuzla_termination_polls"]
            ),
            "GLAURUNG_ORDERED_TRACE_DIR": str(trace_root),
            "MEM_LIMIT_GB": "64",
        }
    )
    return environment


def axeyum_tree_identity() -> dict[str, str]:
    return {
        path: command_output(["git", "rev-parse", f"HEAD:{path}"], AXEYUM_ROOT)
        for path in AXEYUM_TREE_IDENTITIES
    }


def preflight(
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    output_root: pathlib.Path,
) -> dict[str, Any]:
    if command_output(["git", "rev-parse", "HEAD"], glaurung_root) != GLAURUNG_REVISION:
        raise CampaignError("Glaurung revision differs from ADR-0273")
    if command_output(["git", "status", "--short"], glaurung_root):
        raise CampaignError("Glaurung worktree is dirty")
    observed_trees = axeyum_tree_identity()
    if observed_trees != AXEYUM_TREE_IDENTITIES:
        raise CampaignError("Axeyum measured tree identity differs from ADR-0273")
    if not executable.is_file() or sha256_file(executable) != EXECUTABLE_SHA256:
        raise CampaignError("release executable identity differs from registration")
    if not DRIVER_PATH.is_file() or sha256_file(DRIVER_PATH) != DRIVER_SHA256:
        raise CampaignError("tcpip driver identity differs from ADR-0273")
    if not MEMORY_GUARD.is_file():
        raise CampaignError("registered memory guard is absent")
    if CPU not in os.sched_getaffinity(0):
        raise CampaignError(f"registered logical CPU {CPU} is unavailable")
    if not output_root.is_dir() or any(output_root.iterdir()):
        raise CampaignError("output root must exist and be empty")
    linkage = command_output(["ldd", str(executable)], glaurung_root)
    libraries = resolved_dynamic_libraries(linkage)
    if libraries != REGISTERED_DYNAMIC_LIBRARIES:
        raise CampaignError("resolved dynamic libraries differ from registration")
    return {
        "schema": "axeyum-glaurung-six-cell-calibration-campaign-v1",
        "registration": "ADR-0273",
        "started_utc": utc_now(),
        "glaurung_revision": GLAURUNG_REVISION,
        "axeyum_measured_trees": observed_trees,
        "executable": str(executable),
        "executable_sha256": EXECUTABLE_SHA256,
        "dynamic_link_report": linkage,
        "dynamic_link_report_sha256": hashlib.sha256(linkage.encode()).hexdigest(),
        "dynamic_libraries": libraries,
        "driver": {"path": str(DRIVER_PATH), "sha256": DRIVER_SHA256},
        "logical_cpu": CPU,
        "process_timeout_seconds": PROCESS_TIMEOUT_SECONDS,
        "repetitions_per_tier": REPETITIONS,
        "fixed_environment": FIXED_ENVIRONMENT,
        "ladders": [
            {
                "tier": tier,
                "z3_rlimit": row[0],
                "axeyum_progress_checks": row[1],
                "bitwuzla_termination_polls": row[2],
            }
            for tier, row in enumerate(LADDERS)
        ],
        "planned_runs": planned_runs(),
        "runs": [],
        "terminal_status": "preflight",
    }


def validate_trace(
    validator: pathlib.Path,
    trace: pathlib.Path,
    glaurung_root: pathlib.Path,
    run_root: pathlib.Path,
) -> tuple[int, str]:
    completed = subprocess.run(
        [sys.executable, str(validator), str(trace)],
        cwd=glaurung_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    (run_root / "validator.stdout.log").write_text(completed.stdout, encoding="utf-8")
    (run_root / "validator.stderr.log").write_text(completed.stderr, encoding="utf-8")
    return completed.returncode, "accepted" if completed.returncode == 0 else "failed"


def run_campaign(
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    output_root: pathlib.Path,
    campaign: dict[str, Any],
) -> bool:
    campaign_path = output_root / "campaign.json"
    campaign["terminal_status"] = "running"
    write_json(campaign_path, campaign)
    validator = glaurung_root / "docs/axeyum-integration/capture/validate_ordered_trace.py"
    all_valid = True
    for planned in campaign["planned_runs"]:
        run_name = f"tier-{planned['tier']:02d}-r{planned['repetition']}"
        run_root = output_root / run_name
        trace_parent = run_root / "traces"
        trace_parent.mkdir(parents=True)
        command = [
            str(MEMORY_GUARD),
            "taskset",
            "-c",
            str(CPU),
            str(executable),
            str(DRIVER_PATH),
        ]
        record: dict[str, Any] = {
            **planned,
            "run": run_name,
            "command": command,
            "started_utc": utc_now(),
            "trace_parent": str(trace_parent),
            "timed_out": False,
        }
        campaign["runs"].append(record)
        write_json(campaign_path, campaign)
        stdout_path = run_root / "stdout.log"
        stderr_path = run_root / "stderr.log"
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                completed = subprocess.run(
                    command,
                    cwd=glaurung_root,
                    env=sanitize_environment(trace_parent, planned),
                    stdout=stdout,
                    stderr=stderr,
                    check=False,
                    timeout=PROCESS_TIMEOUT_SECONDS,
                )
            record["return_code"] = completed.returncode
        except subprocess.TimeoutExpired:
            record["return_code"] = None
            record["timed_out"] = True
        record["ended_utc"] = utc_now()
        record["stdout_sha256"] = sha256_file(stdout_path)
        record["stderr_sha256"] = sha256_file(stderr_path)
        traces = sorted(path.parent for path in trace_parent.rglob("trace-manifest-v1.json"))
        record["traces"] = [str(path) for path in traces]
        if record["return_code"] == 0 and len(traces) == 1:
            code, status = validate_trace(validator, traces[0], glaurung_root, run_root)
            record["validator_return_code"] = code
            record["validation"] = status
        else:
            record["validator_return_code"] = None
            record["validation"] = "not-run"
        record_valid = (
            record["return_code"] == 0
            and len(traces) == 1
            and record["validation"] == "accepted"
        )
        record["valid"] = record_valid
        all_valid &= record_valid
        write_json(run_root / "run-record.json", record)
        write_json(campaign_path, campaign)
    campaign["terminal_status"] = "complete" if all_valid else "complete-with-failures"
    campaign["ended_utc"] = utc_now()
    write_json(campaign_path, campaign)
    return all_valid


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--glaurung-root", required=True, type=pathlib.Path)
    parser.add_argument("--executable", required=True, type=pathlib.Path)
    parser.add_argument("--output-root", required=True, type=pathlib.Path)
    parser.add_argument("--preflight-only", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        glaurung_root = args.glaurung_root.resolve()
        executable = args.executable.resolve()
        output_root = args.output_root.resolve()
        campaign = preflight(glaurung_root, executable, output_root)
        if args.preflight_only:
            print(json.dumps(campaign, indent=2, sort_keys=True))
            return 0
        return 0 if run_campaign(glaurung_root, executable, output_root, campaign) else 2
    except (CampaignError, OSError, subprocess.SubprocessError) as error:
        print(f"six-cell calibration failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
