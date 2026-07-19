#!/usr/bin/env python3
"""Fail-closed analysis and mechanical selection for ADR-0273."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import pathlib
import re
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
DRIVER_SHA256 = "ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea"
DRIVER_PATH = pathlib.Path(
    "/nas4/data/workspace-infosec/glaurung/tests/fixtures/msvc-pdb/tcpip.sys"
)
CPU = 2
PROCESS_TIMEOUT_SECONDS = 2_700
REPETITIONS = 3
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
CELLS = (
    "z3_cold",
    "z3_warm",
    "axeyum_cold",
    "axeyum_warm",
    "bitwuzla_cold",
    "bitwuzla_warm",
)
BACKEND_CELLS = {
    "z3": ("z3_cold", "z3_warm"),
    "axeyum": ("axeyum_cold", "axeyum_warm"),
    "bitwuzla": ("bitwuzla_cold", "bitwuzla_warm"),
}
LIMIT_FIELDS = {
    "z3": ("z3_rlimit", "z3-rlimit"),
    "axeyum": ("axeyum_progress_checks", "axeyum-progress-checks"),
    "bitwuzla": (
        "bitwuzla_termination_polls",
        "bitwuzla-termination-polls",
    ),
}
DECIDED = {"sat", "unsat"}
DIRECT_WARM = {"warm-created", "warm-retained"}
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
SYMBOLIC_RE = re.compile(
    r"\[symbolic\] \S+\s+raw=(\d+) high-confidence=(\d+) suppressed=(\d+).*"
    r"analyzed=(\d+)/(\d+)(.*)"
)
CONFIDENCE_RE = re.compile(
    r"\[finding-confidence\] schema=(\S+) high=(\d+) diagnostic=(\d+)"
)
EXPLORATION_RE = re.compile(
    r"\[exploration-limits\] runs=(\d+) completed=(\d+) state_budget=(\d+) "
    r"solve_budget=(\d+) timeout_budget=(\d+) deadline=(\d+)"
)


def load_peer_module() -> Any:
    path = pathlib.Path(__file__).with_name("analyze-glaurung-paired-traces.py")
    spec = importlib.util.spec_from_file_location("paired_for_calibration", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load paired trace analyzer")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


PAIRED = load_peer_module()


class CalibrationError(RuntimeError):
    """The campaign cannot support ADR-0273's selection."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CalibrationError(message)


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CalibrationError(f"cannot read {path}: {error}") from error


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_stderr(stderr: str) -> dict[str, Any]:
    symbolic = list(SYMBOLIC_RE.finditer(stderr))
    confidence = list(CONFIDENCE_RE.finditer(stderr))
    exploration = list(EXPLORATION_RE.finditer(stderr))
    require(len(symbolic) == 1, "missing or duplicate symbolic coverage row")
    require(len(confidence) == 1, "missing or duplicate finding-confidence row")
    require(len(exploration) == 1, "missing or duplicate exploration-limits row")
    symbolic_match = symbolic[0]
    confidence_match = confidence[0]
    exploration_match = exploration[0]
    raw = int(symbolic_match.group(1))
    high = int(symbolic_match.group(2))
    diagnostic = int(symbolic_match.group(3))
    analyzed = int(symbolic_match.group(4))
    reachable = int(symbolic_match.group(5))
    boundary = symbolic_match.group(6)
    require(analyzed == 20 and reachable == 338, "calibration coverage is not 20/338")
    require("WORK-LIMIT-HIT" in boundary, "fixed function boundary was not reached")
    require("DEADLINE-HIT" not in boundary, "outer driver deadline was reached")
    require(
        confidence_match.group(1) == "glaurung-ioctlance-confidence-v1",
        "finding-confidence schema mismatch",
    )
    require(
        int(confidence_match.group(2)) == high
        and int(confidence_match.group(3)) == diagnostic,
        "finding-confidence footer mismatch",
    )
    require(raw == high + diagnostic, "raw finding partition is inconsistent")
    names = (
        "runs",
        "completed",
        "state_budget",
        "solve_budget",
        "timeout_budget",
        "deadline",
    )
    limits = {
        name: int(value)
        for name, value in zip(names, exploration_match.groups(), strict=True)
    }
    require(
        limits["timeout_budget"] == 0 and limits["deadline"] == 0,
        "exploration has a timeout/deadline stop",
    )
    require(
        limits["runs"]
        == limits["completed"]
        + limits["state_budget"]
        + limits["solve_budget"]
        + limits["timeout_budget"]
        + limits["deadline"],
        "exploration stop partition is inconsistent",
    )
    return {
        "coverage": {"analyzed": analyzed, "reachable": reachable},
        "findings": {"raw": raw, "high_confidence": high, "diagnostic": diagnostic},
        "exploration_limits": limits,
    }


def parse_stdout(stdout: bytes, expected: dict[str, int]) -> dict[str, Any]:
    try:
        lines = stdout.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise CalibrationError(f"finding output is not UTF-8: {error}") from error
    high = 0
    diagnostic = 0
    normalized = []
    for line in lines:
        if line.endswith("\tconfidence=high"):
            high += 1
            normalized.append(line.removesuffix("\tconfidence=high"))
        elif line.endswith("\tconfidence=diagnostic"):
            diagnostic += 1
            normalized.append(line.removesuffix("\tconfidence=diagnostic"))
        else:
            raise CalibrationError("finding row lacks a known confidence annotation")
    require(len(lines) == expected["raw"], "stdout finding count differs from footer")
    require(high == expected["high_confidence"], "stdout high-confidence count differs")
    require(diagnostic == expected["diagnostic"], "stdout diagnostic count differs")
    return {
        "raw_count": len(lines),
        "high_confidence_count": high,
        "diagnostic_count": diagnostic,
        "ordered_sha256": sha256_bytes(("\n".join(normalized) + "\n").encode()),
        "annotated_stdout_sha256": sha256_bytes(stdout),
    }


def expected_planned_runs() -> list[dict[str, int]]:
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


def trace_vector(trace: Any) -> tuple[Any, ...]:
    return tuple(
        (
            check.identity,
            tuple(
                (
                    getattr(check, f"{cell}_outcome"),
                    check.resource_counters[cell]["stop_reason"],
                )
                for cell in CELLS
            ),
            check.z3_warm_execution,
            check.axeyum_warm_execution,
            check.bitwuzla_warm_execution,
        )
        for check in trace.checks
    )


def summarize_tier(
    tier: int,
    limits: tuple[int, int, int],
    records: Sequence[dict[str, Any]],
) -> dict[str, Any]:
    traces = []
    stderr_summaries = []
    finding_summaries = []
    for record in records:
        require(record.get("valid") is True, f"{record.get('run')} was not validator-clean")
        trace_paths = record.get("traces")
        require(isinstance(trace_paths, list) and len(trace_paths) == 1, "run lacks one trace")
        trace = PAIRED.load_trace(pathlib.Path(trace_paths[0]))
        require(trace.measurement_schema == PAIRED.MEASUREMENT_SCHEMA_V4, "trace is not v4")
        require(trace.driver_sha256 == DRIVER_SHA256, "trace driver identity mismatch")
        traces.append(trace)
        run_root = pathlib.Path(record["trace_parent"]).parent
        stderr = (run_root / "stderr.log").read_text(encoding="utf-8")
        parsed_stderr = parse_stderr(stderr)
        stderr_summaries.append(parsed_stderr)
        stdout = (run_root / "stdout.log").read_bytes()
        finding_summaries.append(parse_stdout(stdout, parsed_stderr["findings"]))

    require(len(traces) == REPETITIONS, "tier repetition count mismatch")
    vectors = [trace_vector(trace) for trace in traces]
    require(all(vector == vectors[0] for vector in vectors[1:]), "ordered outcome drift")
    require(
        all(summary == stderr_summaries[0] for summary in stderr_summaries[1:]),
        "outer work/finding partition drift",
    )
    require(
        all(summary == finding_summaries[0] for summary in finding_summaries[1:]),
        "ordered finding drift",
    )
    check_count = len(traces[0].checks)
    require(check_count > 0, "tier contains no ordered checks")
    expected_limits = {
        "z3": {"unit": "z3-rlimit", "limit": limits[0]},
        "axeyum": {"unit": "axeyum-progress-checks", "limit": limits[1]},
        "bitwuzla": {"unit": "bitwuzla-termination-polls", "limit": limits[2]},
        "cross_backend_unit_equivalence": False,
        "wall_safety_cap_ms": 60_000,
    }
    configuration = json.loads(traces[0].configuration_identity)
    require(
        configuration.get("solver_work_budgets") == expected_limits,
        "tier work-budget identity mismatch",
    )
    require(
        all(trace.configuration_identity == traces[0].configuration_identity for trace in traces),
        "tier configuration identity drift",
    )

    cell_summaries: dict[str, Any] = {}
    decided_disagreement = 0
    for check in traces[0].checks:
        decided = {
            getattr(check, f"{cell}_outcome")
            for cell in CELLS
            if getattr(check, f"{cell}_outcome") in DECIDED
        }
        if len(decided) > 1:
            decided_disagreement += 1
    require(decided_disagreement == 0, "decided six-cell disagreement")
    for cell in CELLS:
        outcomes = [getattr(check, f"{cell}_outcome") for check in traces[0].checks]
        reasons = [
            check.resource_counters[cell]["stop_reason"] for check in traces[0].checks
        ]
        counts = {
            "sat": outcomes.count("sat"),
            "unsat": outcomes.count("unsat"),
            "unknown": outcomes.count("unknown"),
            "resource_limit": reasons.count("resource-limit"),
            "wall_timeout": reasons.count("wall-timeout"),
            "other": reasons.count("other"),
        }
        decided_count = counts["sat"] + counts["unsat"]
        counts["decided"] = decided_count
        counts["decided_fraction"] = decided_count / check_count
        cell_summaries[cell] = counts

    warm_direct = all(
        check.z3_warm_execution in DIRECT_WARM
        and check.axeyum_warm_execution in DIRECT_WARM
        and check.bitwuzla_warm_execution in DIRECT_WARM
        for check in traces[0].checks
    )
    threshold = math.ceil(check_count * 0.95)
    eligibility = {}
    for backend, cells in BACKEND_CELLS.items():
        eligibility[backend] = warm_direct and all(
            cell_summaries[cell]["decided"] >= threshold
            and cell_summaries[cell]["wall_timeout"] == 0
            and cell_summaries[cell]["other"] == 0
            and cell_summaries[cell]["unknown"]
            == cell_summaries[cell]["resource_limit"]
            for cell in cells
        )
    return {
        "tier": tier,
        "limits": {
            "z3_rlimit": limits[0],
            "axeyum_progress_checks": limits[1],
            "bitwuzla_termination_polls": limits[2],
        },
        "repetitions": REPETITIONS,
        "checks_per_repetition": check_count,
        "ordered_outcome_vector_sha256": sha256_bytes(
            json.dumps(vectors[0], sort_keys=True, separators=(",", ":")).encode()
        ),
        "findings": finding_summaries[0],
        "outer_work": stderr_summaries[0],
        "cells": cell_summaries,
        "warm_execution_direct": warm_direct,
        "selection_eligibility": eligibility,
    }


def select_limits(
    tiers: Sequence[dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    selected: dict[str, dict[str, Any]] = {}
    failures = []
    for backend in ("z3", "axeyum", "bitwuzla"):
        field, unit = LIMIT_FIELDS[backend]
        match = next(
            (tier for tier in tiers if tier["selection_eligibility"].get(backend) is True),
            None,
        )
        if match is None:
            failures.append(f"no qualifying limit for {backend}")
            continue
        selected[backend] = {
            "tier": match["tier"],
            "unit": unit,
            "limit": match["limits"][field],
        }
    return selected, failures


def analyze(campaign_path: pathlib.Path) -> dict[str, Any]:
    campaign = load_json(campaign_path)
    campaign_root = campaign_path.parent
    require(isinstance(campaign, dict), "campaign is not an object")
    require(
        campaign.get("schema") == "axeyum-glaurung-six-cell-calibration-campaign-v1",
        "campaign schema mismatch",
    )
    require(campaign.get("registration") == "ADR-0273", "registration mismatch")
    require(campaign.get("glaurung_revision") == GLAURUNG_REVISION, "source mismatch")
    require(
        campaign.get("axeyum_measured_trees") == AXEYUM_TREE_IDENTITIES,
        "Axeyum measured tree mismatch",
    )
    require(campaign.get("executable_sha256") == EXECUTABLE_SHA256, "binary mismatch")
    executable = pathlib.Path(campaign.get("executable", ""))
    require(executable.is_file(), "registered executable is absent")
    require(sha256_file(executable) == EXECUTABLE_SHA256, "executable bytes drifted")
    require(
        campaign.get("dynamic_libraries") == REGISTERED_DYNAMIC_LIBRARIES,
        "dynamic library registration mismatch",
    )
    for path_text, expected_sha256 in REGISTERED_DYNAMIC_LIBRARIES.items():
        path = pathlib.Path(path_text)
        require(path.is_file(), f"registered dynamic library is absent: {path}")
        require(sha256_file(path) == expected_sha256, f"dynamic library drift: {path}")
    linkage = campaign.get("dynamic_link_report")
    require(isinstance(linkage, str) and linkage, "dynamic link report is absent")
    require(
        campaign.get("dynamic_link_report_sha256") == sha256_bytes(linkage.encode()),
        "dynamic link report hash mismatch",
    )
    require(
        campaign.get("driver")
        == {"path": str(DRIVER_PATH), "sha256": DRIVER_SHA256},
        "driver mismatch",
    )
    require(DRIVER_PATH.is_file(), "registered driver is absent")
    require(sha256_file(DRIVER_PATH) == DRIVER_SHA256, "driver bytes drifted")
    require(campaign.get("logical_cpu") == CPU, "CPU registration mismatch")
    require(
        campaign.get("process_timeout_seconds") == PROCESS_TIMEOUT_SECONDS,
        "process timeout registration mismatch",
    )
    require(
        campaign.get("fixed_environment") == FIXED_ENVIRONMENT,
        "fixed environment registration mismatch",
    )
    require(campaign.get("repetitions_per_tier") == REPETITIONS, "repetition mismatch")
    require(campaign.get("planned_runs") == expected_planned_runs(), "planned matrix drift")
    require(campaign.get("terminal_status") == "complete", "campaign did not complete cleanly")
    records = campaign.get("runs")
    require(isinstance(records, list) and len(records) == len(expected_planned_runs()), "run count mismatch")
    for expected, record in zip(expected_planned_runs(), records, strict=True):
        require(
            all(record.get(key) == value for key, value in expected.items()),
            "run order or configured limit drift",
        )
        run_name = f"tier-{expected['tier']:02d}-r{expected['repetition']}"
        run_root = campaign_root / run_name
        require(record.get("run") == run_name, "run name drift")
        require(
            record.get("command")
            == [
                str(MEMORY_GUARD),
                "taskset",
                "-c",
                str(CPU),
                str(executable),
                str(DRIVER_PATH),
            ],
            f"{run_name} command drift",
        )
        require(
            record.get("trace_parent") == str(run_root / "traces"),
            "trace root escaped the campaign",
        )
        require(record.get("timed_out") is False, f"{run_name} timed out")
        require(record.get("return_code") == 0, f"{run_name} failed")
        require(
            record.get("validator_return_code") == 0
            and record.get("validation") == "accepted"
            and record.get("valid") is True,
            f"{run_name} was not validator-clean",
        )
        stdout_path = run_root / "stdout.log"
        stderr_path = run_root / "stderr.log"
        require(
            record.get("stdout_sha256") == sha256_file(stdout_path),
            f"{run_name} stdout hash mismatch",
        )
        require(
            record.get("stderr_sha256") == sha256_file(stderr_path),
            f"{run_name} stderr hash mismatch",
        )
        retained_record = load_json(run_root / "run-record.json")
        require(retained_record == record, f"{run_name} retained record mismatch")
        trace_paths = record.get("traces")
        require(
            isinstance(trace_paths, list) and len(trace_paths) == 1,
            f"{run_name} lacks exactly one trace",
        )
        require(
            pathlib.Path(trace_paths[0]).resolve().is_relative_to(
                (run_root / "traces").resolve()
            ),
            f"{run_name} trace escaped the run root",
        )
    tier_summaries = [
        summarize_tier(
            tier,
            limits,
            records[tier * REPETITIONS : (tier + 1) * REPETITIONS],
        )
        for tier, limits in enumerate(LADDERS)
    ]
    selected, failures = select_limits(tier_summaries)
    return {
        "schema": "axeyum-glaurung-six-cell-calibration-analysis-v1",
        "registration": "ADR-0273",
        "accepted": not failures,
        "failures": failures,
        "campaign": str(campaign_path),
        "campaign_sha256": sha256_bytes(campaign_path.read_bytes()),
        "glaurung_revision": GLAURUNG_REVISION,
        "executable_sha256": EXECUTABLE_SHA256,
        "driver_sha256": DRIVER_SHA256,
        "selection_rule": (
            "smallest backend-specific tier with cold and warm >=95% decided in all "
            "three byte-stable repetitions, only resource-limit nondecisions, zero "
            "fallback/wall/other/error, and no decided disagreement"
        ),
        "cross_backend_unit_equivalence": False,
        "selected": selected,
        "tiers": tier_summaries,
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("campaign", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = analyze(args.campaign.resolve())
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.write_text(rendered, encoding="utf-8")
        return 0 if report["accepted"] else 2
    except (CalibrationError, OSError, PAIRED.AnalysisError) as error:
        print(f"six-cell calibration analysis failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
