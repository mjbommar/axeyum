#!/usr/bin/env python3
"""Execute ADR-0274's fixed-Z3-authority shadow-limit calibration."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import subprocess
import sys
from typing import Any, Sequence


Z3_RLIMIT = 100_000
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
REGISTRATION = "ADR-0274"


def load_base_module() -> Any:
    path = pathlib.Path(__file__).with_name("run-glaurung-six-cell-calibration.py")
    spec = importlib.util.spec_from_file_location("six_cell_runner_for_adr0274", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load ADR-0273 calibration runner")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.LADDERS = LADDERS
    return module


BASE = load_base_module()


def planned_runs() -> list[dict[str, int]]:
    return BASE.planned_runs()


def preflight(
    glaurung_root: pathlib.Path,
    executable: pathlib.Path,
    output_root: pathlib.Path,
) -> dict[str, Any]:
    campaign = BASE.preflight(glaurung_root, executable, output_root)
    campaign["schema"] = CAMPAIGN_SCHEMA
    campaign["registration"] = REGISTRATION
    campaign["authority"] = {
        "backend": "z3",
        "unit": "z3-rlimit",
        "limit": Z3_RLIMIT,
        "concretization_policy": "glaurung-any-model-v1",
    }
    campaign["cross_backend_unit_equivalence"] = False
    return campaign


def parse_args(argv: Sequence[str]) -> Any:
    return BASE.parse_args(argv)


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
        return (
            0
            if BASE.run_campaign(glaurung_root, executable, output_root, campaign)
            else 2
        )
    except (BASE.CampaignError, OSError, subprocess.SubprocessError) as error:
        print(f"fixed-authority shadow calibration failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
