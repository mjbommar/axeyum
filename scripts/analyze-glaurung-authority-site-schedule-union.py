#!/usr/bin/env python3
"""Validate a deterministic four-schedule Glaurung finding-coverage union."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
from typing import Any


BASE_SCRIPT = Path(__file__).with_name(
    "analyze-glaurung-authority-coverage-union.py"
)
BASE_SPEC = importlib.util.spec_from_file_location(
    "glaurung_authority_coverage_union_base", BASE_SCRIPT
)
if BASE_SPEC is None or BASE_SPEC.loader is None:
    raise RuntimeError(f"cannot load base authority analyzer: {BASE_SCRIPT}")
BASE = importlib.util.module_from_spec(BASE_SPEC)
BASE_SPEC.loader.exec_module(BASE)

UNION_SCHEMA = "axeyum.glaurung-authority-site-schedule-union.v1"
POLICY_LABELS = (
    "min-unsigned",
    "max-unsigned",
    "site-hash-0",
    "site-hash-1",
)


def set_summary(findings: set[str]) -> dict[str, Any]:
    ordered = sorted(findings)
    return {
        "finding_count": len(ordered),
        "findings_sha256": BASE.text_sha256(ordered),
        "ordered_findings": ordered,
    }


def analyze_reports(
    any_model_report: dict[str, Any],
    minimum_report: dict[str, Any],
    maximum_report: dict[str, Any],
    site_hash_zero_report: dict[str, Any],
    site_hash_one_report: dict[str, Any],
) -> dict[str, Any]:
    cells = BASE.validate_cells(
        {
            "any-model": (any_model_report, None),
            "min-unsigned": (minimum_report, "min-unsigned"),
            "max-unsigned": (maximum_report, "max-unsigned"),
            "site-hash-0": (site_hash_zero_report, "site-hash-0"),
            "site-hash-1": (site_hash_one_report, "site-hash-1"),
        }
    )

    policy_findings = {
        label: {
            backend: set(cells[label]["findings"][backend])
            for backend in ("z3", "axeyum")
        }
        for label in POLICY_LABELS
    }
    authority_unions = {
        backend: set().union(
            *(policy_findings[label][backend] for label in POLICY_LABELS)
        )
        for backend in ("z3", "axeyum")
    }
    BASE.require(
        authority_unions["z3"] == authority_unions["axeyum"],
        "four-schedule union authority findings differ",
    )

    canonical_sets = {
        label: policy_findings[label]["z3"] for label in POLICY_LABELS
    }
    two_extrema = canonical_sets["min-unsigned"] | canonical_sets["max-unsigned"]
    site_pair = canonical_sets["site-hash-0"] | canonical_sets["site-hash-1"]
    four_schedule = authority_unions["z3"]

    policy_unique: dict[str, list[str]] = {}
    for label in POLICY_LABELS:
        other_union = set().union(
            *(canonical_sets[other] for other in POLICY_LABELS if other != label)
        )
        policy_unique[label] = sorted(canonical_sets[label] - other_union)

    membership: dict[str, list[str]] = {}
    for count in range(1, len(POLICY_LABELS) + 1):
        membership[str(count)] = sorted(
            finding
            for finding in four_schedule
            if sum(finding in canonical_sets[label] for label in POLICY_LABELS)
            == count
        )

    any_findings = cells["any-model"]["findings"]
    any_z3 = set(any_findings["z3"])
    any_axeyum = set(any_findings["axeyum"])
    any_union = any_z3 | any_axeyum

    representative = cells["min-unsigned"]
    return {
        "schema": UNION_SCHEMA,
        "accepted": True,
        "claim": "bounded deterministic four-schedule mixed-extremum authority parity",
        "glaurung": representative["report"]["glaurung"],
        "axeyum": representative["report"]["axeyum"],
        "binaries": representative["report"]["binaries"],
        "driver": representative["driver"],
        "coverage": representative["summary"]["coverage"],
        "repetitions_per_policy_authority": representative["report"]["repetitions"],
        "check_timeout_ms": representative["report"]["check_timeout_ms_required"],
        "schedule": {
            "policies": list(POLICY_LABELS),
            "site_hash": "FNV-1a-64(purpose || location_le), high-bit selection",
            "complement": "site-hash-1 flips every site-hash-0 extremum",
        },
        "policies": {
            label: BASE.policy_summary(cells[label]) for label in POLICY_LABELS
        },
        "two_extremum_union": set_summary(two_extrema),
        "site_schedule_union": set_summary(site_pair),
        "four_schedule_union": {
            "exact_authority_parity": True,
            **set_summary(four_schedule),
            "policy_unique": policy_unique,
            "membership_by_policy_count": membership,
        },
        "extension_over_two_extrema": {
            "shared": sorted(four_schedule & two_extrema),
            "site_schedule_only": sorted(four_schedule - two_extrema),
            "two_extrema_only": sorted(two_extrema - four_schedule),
        },
        "any_model_baseline": {
            "accepted": False,
            "z3_finding_count": len(any_findings["z3"]),
            "axeyum_finding_count": len(any_findings["axeyum"]),
            "stable_intersection": sorted(any_z3 & any_axeyum),
            "z3_only": sorted(any_z3 - any_axeyum),
            "axeyum_only": sorted(any_axeyum - any_z3),
            "combined_union_count": len(any_union),
            "combined_union": sorted(any_union),
        },
        "four_schedule_vs_any_model_combined_union": {
            "shared": sorted(four_schedule & any_union),
            "four_schedule_only": sorted(four_schedule - any_union),
            "any_model_only": sorted(any_union - four_schedule),
        },
        "claim_limits": [
            "Four deterministic schedules do not enumerate every satisfying model.",
            "Equal authority unions do not prove exhaustive path or vulnerability coverage.",
            "A favorable overlap with arbitrary-model rows is not an acceptance criterion.",
            "Standalone process times include schedule-dependent probe counts and are not solver-speed evidence.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--any-model-report", type=Path, required=True)
    parser.add_argument("--min-report", type=Path, required=True)
    parser.add_argument("--max-report", type=Path, required=True)
    parser.add_argument("--site-hash-zero-report", type=Path, required=True)
    parser.add_argument("--site-hash-one-report", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    report = analyze_reports(
        BASE.load_json(args.any_model_report),
        BASE.load_json(args.min_report),
        BASE.load_json(args.max_report),
        BASE.load_json(args.site_hash_zero_report),
        BASE.load_json(args.site_hash_one_report),
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
