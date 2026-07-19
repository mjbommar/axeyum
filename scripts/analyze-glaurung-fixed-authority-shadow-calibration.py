#!/usr/bin/env python3
"""Fail-closed analysis and shadow-limit selection for ADR-0274."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import sys
from typing import Any, Sequence


Z3_RLIMIT = 100_000
EXPECTED_CHECKS = 4_846
SHADOW_LADDERS = (
    (8_192, 1),
    (16_384, 2),
    (32_768, 4),
    (65_536, 8),
    (131_072, 16),
    (262_144, 32),
    (524_288, 64),
    (1_048_576, 128),
    (2_097_152, 256),
    (4_194_304, 512),
)
LADDERS = tuple((Z3_RLIMIT, axeyum, bitwuzla) for axeyum, bitwuzla in SHADOW_LADDERS)
CAMPAIGN_SCHEMA = "axeyum-glaurung-fixed-authority-shadow-calibration-campaign-v1"
ANALYSIS_SCHEMA = "axeyum-glaurung-fixed-authority-shadow-calibration-analysis-v1"
REGISTRATION = "ADR-0274"


def load_base_module() -> Any:
    path = pathlib.Path(__file__).with_name("analyze-glaurung-six-cell-calibration.py")
    spec = importlib.util.spec_from_file_location("six_cell_analysis_for_adr0274", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load ADR-0273 calibration analyzer")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.LADDERS = LADDERS
    return module


BASE = load_base_module()


class ShadowCalibrationError(RuntimeError):
    """The campaign cannot support ADR-0274's selection."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ShadowCalibrationError(message)


def expected_planned_runs() -> list[dict[str, int]]:
    return BASE.expected_planned_runs()


def check_identity_vector(trace: Any) -> tuple[Any, ...]:
    return tuple(check.identity for check in trace.checks)


def authority_vector(trace: Any) -> tuple[Any, ...]:
    return tuple(
        (check.identity, check.z3_cold_outcome, check.z3_warm_outcome)
        for check in trace.checks
    )


def summarize_tier(
    tier: int,
    limits: tuple[int, int, int],
    records: Sequence[dict[str, Any]],
) -> tuple[dict[str, Any], tuple[Any, ...], tuple[Any, ...]]:
    summary = BASE.summarize_tier(tier, limits, records)
    trace = BASE.PAIRED.load_trace(pathlib.Path(records[0]["traces"][0]))
    identities = check_identity_vector(trace)
    authority = authority_vector(trace)
    require(len(identities) == EXPECTED_CHECKS, "authority stream is not 4,846 checks")
    z3_cells = (summary["cells"]["z3_cold"], summary["cells"]["z3_warm"])
    require(
        all(cell["decided"] == EXPECTED_CHECKS for cell in z3_cells),
        "fixed Z3 authority did not decide every check",
    )
    summary["authority_identity_sha256"] = BASE.sha256_bytes(
        json.dumps(identities, separators=(",", ":")).encode()
    )
    summary["authority_outcome_sha256"] = BASE.sha256_bytes(
        json.dumps(authority, separators=(",", ":")).encode()
    )
    return summary, identities, authority


def select_shadow_limits(
    tiers: Sequence[dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    selected: dict[str, dict[str, Any]] = {}
    failures = []
    for backend, field, unit in (
        ("axeyum", "axeyum_progress_checks", "axeyum-progress-checks"),
        ("bitwuzla", "bitwuzla_termination_polls", "bitwuzla-termination-polls"),
    ):
        match = next(
            (tier for tier in tiers if tier["selection_eligibility"][backend]),
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


def validate_campaign_metadata(
    campaign_path: pathlib.Path, campaign: dict[str, Any]
) -> list[dict[str, Any]]:
    root = campaign_path.parent
    require(campaign.get("schema") == CAMPAIGN_SCHEMA, "campaign schema mismatch")
    require(campaign.get("registration") == REGISTRATION, "registration mismatch")
    require(campaign.get("glaurung_revision") == BASE.GLAURUNG_REVISION, "source mismatch")
    require(
        campaign.get("axeyum_measured_trees") == BASE.AXEYUM_TREE_IDENTITIES,
        "Axeyum measured tree mismatch",
    )
    require(campaign.get("executable_sha256") == BASE.EXECUTABLE_SHA256, "binary mismatch")
    executable = pathlib.Path(campaign.get("executable", ""))
    require(executable.is_file(), "registered executable is absent")
    require(BASE.sha256_file(executable) == BASE.EXECUTABLE_SHA256, "executable drift")
    require(
        campaign.get("dynamic_libraries") == BASE.REGISTERED_DYNAMIC_LIBRARIES,
        "dynamic library registration mismatch",
    )
    for path_text, expected_hash in BASE.REGISTERED_DYNAMIC_LIBRARIES.items():
        path = pathlib.Path(path_text)
        require(path.is_file(), f"registered dynamic library is absent: {path}")
        require(BASE.sha256_file(path) == expected_hash, f"dynamic library drift: {path}")
    linkage = campaign.get("dynamic_link_report")
    require(isinstance(linkage, str) and linkage, "dynamic link report is absent")
    require(
        campaign.get("dynamic_link_report_sha256")
        == BASE.sha256_bytes(linkage.encode()),
        "dynamic link report hash mismatch",
    )
    require(
        campaign.get("driver")
        == {"path": str(BASE.DRIVER_PATH), "sha256": BASE.DRIVER_SHA256},
        "driver mismatch",
    )
    require(BASE.sha256_file(BASE.DRIVER_PATH) == BASE.DRIVER_SHA256, "driver drift")
    require(campaign.get("logical_cpu") == BASE.CPU, "CPU registration mismatch")
    require(
        campaign.get("process_timeout_seconds") == BASE.PROCESS_TIMEOUT_SECONDS,
        "process timeout registration mismatch",
    )
    require(campaign.get("fixed_environment") == BASE.FIXED_ENVIRONMENT, "environment drift")
    require(
        campaign.get("authority")
        == {
            "backend": "z3",
            "unit": "z3-rlimit",
            "limit": Z3_RLIMIT,
            "concretization_policy": "glaurung-any-model-v1",
        },
        "authority registration mismatch",
    )
    require(campaign.get("cross_backend_unit_equivalence") is False, "unit equivalence drift")
    require(
        campaign.get("repetitions_per_tier") == BASE.REPETITIONS,
        "repetition registration mismatch",
    )
    require(campaign.get("planned_runs") == expected_planned_runs(), "planned matrix drift")
    require(campaign.get("terminal_status") == "complete", "campaign did not complete")
    records = campaign.get("runs")
    require(
        isinstance(records, list) and len(records) == len(expected_planned_runs()),
        "run count mismatch",
    )
    for expected, record in zip(expected_planned_runs(), records, strict=True):
        require(
            all(record.get(key) == value for key, value in expected.items()),
            "run order or configured limit drift",
        )
        run_name = f"tier-{expected['tier']:02d}-r{expected['repetition']}"
        run_root = root / run_name
        require(record.get("run") == run_name, "run name drift")
        require(
            record.get("command")
            == [
                str(BASE.MEMORY_GUARD),
                "taskset",
                "-c",
                str(BASE.CPU),
                str(executable),
                str(BASE.DRIVER_PATH),
            ],
            f"{run_name} command drift",
        )
        require(record.get("trace_parent") == str(run_root / "traces"), "trace root drift")
        require(record.get("timed_out") is False, f"{run_name} timed out")
        require(record.get("return_code") == 0, f"{run_name} failed")
        require(
            record.get("validator_return_code") == 0
            and record.get("validation") == "accepted"
            and record.get("valid") is True,
            f"{run_name} was not validator-clean",
        )
        require(
            record.get("stdout_sha256") == BASE.sha256_file(run_root / "stdout.log"),
            f"{run_name} stdout hash mismatch",
        )
        require(
            record.get("stderr_sha256") == BASE.sha256_file(run_root / "stderr.log"),
            f"{run_name} stderr hash mismatch",
        )
        require(
            BASE.load_json(run_root / "run-record.json") == record,
            f"{run_name} retained record mismatch",
        )
        traces = record.get("traces")
        require(isinstance(traces, list) and len(traces) == 1, f"{run_name} trace count")
        require(
            pathlib.Path(traces[0]).resolve().is_relative_to((run_root / "traces").resolve()),
            f"{run_name} trace escaped the run root",
        )
    return records


def analyze(campaign_path: pathlib.Path) -> dict[str, Any]:
    campaign = BASE.load_json(campaign_path)
    require(isinstance(campaign, dict), "campaign is not an object")
    records = validate_campaign_metadata(campaign_path, campaign)
    tier_data = [
        summarize_tier(
            tier,
            limits,
            records[tier * BASE.REPETITIONS : (tier + 1) * BASE.REPETITIONS],
        )
        for tier, limits in enumerate(LADDERS)
    ]
    tiers = [row[0] for row in tier_data]
    identities = [row[1] for row in tier_data]
    authority = [row[2] for row in tier_data]
    require(all(value == identities[0] for value in identities[1:]), "authority stream drift")
    require(all(value == authority[0] for value in authority[1:]), "authority outcome drift")
    require(
        all(tier["findings"] == tiers[0]["findings"] for tier in tiers[1:]),
        "finding output drift across tiers",
    )
    require(
        all(tier["outer_work"] == tiers[0]["outer_work"] for tier in tiers[1:]),
        "outer work drift across tiers",
    )
    selected, failures = select_shadow_limits(tiers)
    if not failures:
        selected = {
            "z3": {"unit": "z3-rlimit", "limit": Z3_RLIMIT},
            **selected,
        }
    return {
        "schema": ANALYSIS_SCHEMA,
        "registration": REGISTRATION,
        "accepted": not failures,
        "failures": failures,
        "campaign": str(campaign_path),
        "campaign_sha256": BASE.sha256_bytes(campaign_path.read_bytes()),
        "glaurung_revision": BASE.GLAURUNG_REVISION,
        "executable_sha256": BASE.EXECUTABLE_SHA256,
        "driver_sha256": BASE.DRIVER_SHA256,
        "authority_stream_checks": EXPECTED_CHECKS,
        "authority_identity_sha256": tiers[0]["authority_identity_sha256"],
        "authority_outcome_sha256": tiers[0]["authority_outcome_sha256"],
        "cross_backend_unit_equivalence": False,
        "selected": selected,
        "tiers": tiers,
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
    except (ShadowCalibrationError, OSError, BASE.CalibrationError, BASE.PAIRED.AnalysisError) as error:
        print(f"fixed-authority shadow analysis failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
