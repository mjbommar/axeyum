#!/usr/bin/env python3
"""Analyze ADR-0275 Phase A reproduction or Phase B census."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import sys
from typing import Any, Sequence


TRIPLET = (100_000, 32_768, 512)
REGISTRATION = "ADR-0275"
SCHEMAS = {
    "phase-a": "axeyum-glaurung-joint-triplet-reproduction-campaign-v1",
    "phase-b": "axeyum-glaurung-joint-triplet-census-campaign-v1",
}
EXPECTED_IDENTITY = "89d28a2978e4d9fc1bbba78bb1413a80fffc408c0bbc4dcef51b1eb6b5e1e928"
EXPECTED_AUTHORITY = "f0b5580fcc6bba0accd6a91fc76a1373a60835af84c5982394ca9d6b3312fafa"
EXPECTED_FINDINGS = {
    "raw_count": 235,
    "high_confidence_count": 0,
    "diagnostic_count": 235,
    "ordered_sha256": "dcdefa04c27247ab2c5e0510e35fdf4f65919f049827cd8e96aaaebb2657a472",
    "annotated_stdout_sha256": "08116a53471ea3d59f2b69aba287c475944dc5edc2e90e0ba28f854e8164f96b",
}


def load_fixed() -> Any:
    path = pathlib.Path(__file__).with_name(
        "analyze-glaurung-fixed-authority-shadow-calibration.py"
    )
    spec = importlib.util.spec_from_file_location("fixed_analysis_for_adr0275", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load fixed-authority analyzer")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


FIXED = load_fixed()


def configure(phase: str) -> None:
    FIXED.LADDERS = (TRIPLET,)
    FIXED.BASE.LADDERS = (TRIPLET,)
    FIXED.CAMPAIGN_SCHEMA = SCHEMAS[phase]
    FIXED.REGISTRATION = REGISTRATION
    FIXED.BASE.FIXED_ENVIRONMENT = {
        **FIXED.BASE.FIXED_ENVIRONMENT,
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "20" if phase == "phase-a" else "338",
    }


def analyze(phase: str, campaign_path: pathlib.Path) -> dict[str, Any]:
    configure(phase)
    campaign = FIXED.BASE.load_json(campaign_path)
    FIXED.require(isinstance(campaign, dict), "campaign is not an object")
    FIXED.require(campaign.get("phase") == phase, "phase identity mismatch")
    records = FIXED.validate_campaign_metadata(campaign_path, campaign)
    if phase == "phase-a":
        summary, identities, authority = FIXED.summarize_tier(0, TRIPLET, records)
        FIXED.require(len(identities) == 4_846, "Phase A check count mismatch")
        FIXED.require(
            summary["authority_identity_sha256"] == EXPECTED_IDENTITY,
            "Phase A authority identity mismatch",
        )
        FIXED.require(
            summary["authority_outcome_sha256"] == EXPECTED_AUTHORITY,
            "Phase A authority outcome mismatch",
        )
        FIXED.require(
            all(summary["cells"][cell]["decided"] == 4_846 for cell in FIXED.BASE.CELLS),
            "Phase A has a nondecision",
        )
        FIXED.require(summary["warm_execution_direct"], "Phase A warm fallback")
        FIXED.require(summary["findings"] == EXPECTED_FINDINGS, "Phase A finding drift")
        FIXED.require(
            summary["outer_work"]["exploration_limits"]
            == {
                "runs": 21,
                "completed": 20,
                "state_budget": 1,
                "solve_budget": 0,
                "timeout_budget": 0,
                "deadline": 0,
            },
            "Phase A outer-work drift",
        )
    else:
        original = FIXED.BASE.parse_stderr
        FIXED.BASE.parse_stderr = lambda stderr: original(
            stderr,
            expected_analyzed=338,
            expected_reachable=338,
            require_work_limit=False,
        )
        summary = FIXED.BASE.summarize_tier(0, TRIPLET, records)
        FIXED.require(
            summary["outer_work"]["coverage"] == {"analyzed": 338, "reachable": 338},
            "Phase B census coverage mismatch",
        )
        FIXED.require(
            all(summary["selection_eligibility"].values()),
            "Phase B decision/fallback gate failed",
        )
    return {
        "schema": f"axeyum-glaurung-adr0275-{phase}-analysis-v1",
        "registration": REGISTRATION,
        "phase": phase,
        "accepted": True,
        "campaign": str(campaign_path),
        "campaign_sha256": FIXED.BASE.sha256_bytes(campaign_path.read_bytes()),
        "triplet": {
            "z3_rlimit": TRIPLET[0],
            "axeyum_progress_checks": TRIPLET[1],
            "bitwuzla_termination_polls": TRIPLET[2],
        },
        "summary": summary,
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", choices=tuple(SCHEMAS), required=True)
    parser.add_argument("campaign", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report = analyze(args.phase, args.campaign.resolve())
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        return 0
    except (
        OSError,
        FIXED.ShadowCalibrationError,
        FIXED.BASE.CalibrationError,
        FIXED.BASE.PAIRED.AnalysisError,
    ) as error:
        print(f"ADR-0275 analysis failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
