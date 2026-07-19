#!/usr/bin/env python3
"""Execute ADR-0275's gated joint-triplet reproduction and census."""

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
MAX_FUNCTIONS = {"phase-a": 20, "phase-b": 338}


def load_base() -> Any:
    path = pathlib.Path(__file__).with_name("run-glaurung-six-cell-calibration.py")
    spec = importlib.util.spec_from_file_location("six_cell_runner_for_adr0275", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load six-cell runner")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.LADDERS = (TRIPLET,)
    return module


BASE = load_base()


def configure_phase(phase: str) -> None:
    BASE.LADDERS = (TRIPLET,)
    BASE.FIXED_ENVIRONMENT = {
        **BASE.FIXED_ENVIRONMENT,
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": str(MAX_FUNCTIONS[phase]),
    }


def require_phase_a(root: pathlib.Path) -> None:
    report_path = root / "phase-a-analysis.json"
    campaign_path = root / "phase-a" / "campaign.json"
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if (
        report.get("schema") != "axeyum-glaurung-adr0275-phase-a-analysis-v1"
        or report.get("phase") != "phase-a"
        or report.get("triplet")
        != {
            "z3_rlimit": TRIPLET[0],
            "axeyum_progress_checks": TRIPLET[1],
            "bitwuzla_termination_polls": TRIPLET[2],
        }
        or report.get("accepted") is not True
    ):
        raise BASE.CampaignError("Phase A analysis is not accepted")
    if report.get("campaign_sha256") != BASE.sha256_file(campaign_path):
        raise BASE.CampaignError("Phase A campaign changed after acceptance")


def run_phase(
    phase: str,
    root: pathlib.Path,
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    preflight_only: bool,
) -> int:
    if phase == "phase-a":
        if not root.is_dir() or any(root.iterdir()):
            raise BASE.CampaignError("Phase A root must exist and be empty")
    else:
        require_phase_a(root)
    output = root / phase
    if output.exists():
        raise BASE.CampaignError(f"{phase} output already exists")
    output.mkdir()
    configure_phase(phase)
    campaign = BASE.preflight(glaurung_root, executable, output)
    campaign["schema"] = SCHEMAS[phase]
    campaign["registration"] = REGISTRATION
    campaign["phase"] = phase
    campaign["authority"] = {
        "backend": "z3",
        "unit": "z3-rlimit",
        "limit": TRIPLET[0],
        "concretization_policy": "glaurung-any-model-v1",
    }
    campaign["cross_backend_unit_equivalence"] = False
    if preflight_only:
        output.rmdir()
        print(json.dumps(campaign, indent=2, sort_keys=True))
        return 0
    return 0 if BASE.run_campaign(glaurung_root, executable, output, campaign) else 2


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", choices=tuple(SCHEMAS), required=True)
    parser.add_argument("--root", type=pathlib.Path, required=True)
    parser.add_argument("--glaurung-root", type=pathlib.Path, required=True)
    parser.add_argument("--executable", type=pathlib.Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return run_phase(
            args.phase,
            args.root.resolve(),
            args.glaurung_root.resolve(),
            args.executable.resolve(),
            args.preflight_only,
        )
    except (BASE.CampaignError, OSError, json.JSONDecodeError) as error:
        print(f"ADR-0275 runner failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
