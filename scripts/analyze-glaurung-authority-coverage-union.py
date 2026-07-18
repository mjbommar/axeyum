#!/usr/bin/env python3
"""Validate a deterministic min/max Glaurung finding-coverage union."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPORT_SCHEMA = "axeyum.glaurung-authoritative-finding-parity.v4"
UNION_SCHEMA = "axeyum.glaurung-authority-coverage-union.v1"
POLICIES = {
    "min-unsigned": "glaurung-min-unsigned-v1",
    "max-unsigned": "glaurung-max-unsigned-v1",
}


def text_sha256(lines: list[str]) -> str:
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def stable_backend_findings(
    report: dict[str, Any], *, label: str
) -> dict[str, list[str]]:
    drivers = report.get("drivers")
    require(isinstance(drivers, list) and len(drivers) == 1, f"{label} must have one driver")
    runs = drivers[0].get("runs")
    require(isinstance(runs, list) and runs, f"{label} has no runs")
    populations: dict[str, list[dict[str, Any]]] = {"z3": [], "axeyum": []}
    for run in runs:
        require("run_error" not in run, f"{label} contains a process failure")
        backend = run.get("backend")
        require(backend in populations, f"{label} has an unexpected backend")
        populations[backend].append(run)
    expected_repetitions = int(report["repetitions"])
    findings: dict[str, list[str]] = {}
    for backend, population in populations.items():
        require(
            len(population) == expected_repetitions,
            f"{label} {backend} repetition population is incomplete",
        )
        candidates = [run.get("findings") for run in population]
        require(
            all(isinstance(candidate, list) for candidate in candidates),
            f"{label} {backend} has no exact finding list",
        )
        first = candidates[0]
        require(
            all(candidate == first for candidate in candidates[1:]),
            f"{label} {backend} finding output is unstable",
        )
        require(
            len(first) == len(set(first)),
            f"{label} {backend} emitted duplicate finding rows",
        )
        require(
            all(run.get("finding_count") == len(first) for run in population),
            f"{label} {backend} finding counts do not match output",
        )
        findings[backend] = first
    return findings


def validate_report(
    report: dict[str, Any], *, label: str, policy: str | None
) -> dict[str, Any]:
    require(report.get("schema") == REPORT_SCHEMA, f"{label} schema mismatch")
    require(
        report.get("post_run_source_identity", {}).get("stable") is True,
        f"{label} source identity changed during measurement",
    )
    require(report.get("glaurung", {}).get("tracked_dirty") is False, f"{label} Glaurung source is dirty")
    require(report.get("axeyum", {}).get("tracked_dirty") is False, f"{label} Axeyum source is dirty")
    require(int(report.get("repetitions", 0)) >= 3, f"{label} requires at least three repetitions")
    drivers = report["drivers"]
    summary = drivers[0].get("summary")
    require(isinstance(summary, dict), f"{label} has no driver summary")
    require(summary.get("within_backend_stable") is True, f"{label} is not stable within each backend")
    findings = stable_backend_findings(report, label=label)

    if policy is None:
        require(report.get("canonical_model_choice_required") is False, f"{label} unexpectedly requires a canonical policy")
        require(report.get("canonical_model_choice_policy") is None, f"{label} unexpectedly names a canonical policy")
        require(report.get("accepted") is False, f"{label} must preserve a stable divergence")
        require(summary.get("exact_finding_parity") is False, f"{label} must preserve a stable divergence")
        require(findings["z3"] != findings["axeyum"], f"{label} must preserve a stable divergence")
    else:
        policy_name = POLICIES[policy]
        require(summary.get("exact_finding_parity") is True, f"{policy} authority findings differ")
        require(findings["z3"] == findings["axeyum"], f"{policy} authority findings differ")
        require(report.get("accepted") is True, f"{policy} report was not accepted")
        require(report.get("failures") == [], f"{policy} report contains failures")
        require(report.get("all_drivers_exact_finding_parity") is True, f"{policy} report lacks exact parity")
        require(report.get("canonical_model_choice_required") is True, f"{policy} report did not require its policy")
        require(report.get("canonical_model_choice_policy") == policy_name, f"{policy} report policy mismatch")
        canonical = summary.get("canonical_model_choice")
        require(isinstance(canonical, dict), f"{policy} report lacks canonical telemetry")
        require(canonical.get("policy") == policy_name, f"{policy} telemetry policy mismatch")
        canonical_backends = canonical.get("backends")
        require(isinstance(canonical_backends, dict), f"{policy} report lacks per-backend canonical telemetry")
        require(
            canonical_backends.get("z3") == canonical_backends.get("axeyum"),
            f"{policy} canonical telemetry differs by authority",
        )
        backend_rows = summary.get("backends")
        require(isinstance(backend_rows, dict), f"{policy} report lacks backend work rows")
        z3_solves = backend_rows.get("z3", {}).get("solves")
        axeyum_solves = backend_rows.get("axeyum", {}).get("solves")
        require(
            isinstance(z3_solves, list)
            and z3_solves
            and z3_solves == axeyum_solves
            and len(set(z3_solves)) == 1,
            f"{policy} solve counts differ or drift",
        )
        for run in drivers[0]["runs"]:
            telemetry = run.get("canonical_model_choice")
            require(isinstance(telemetry, dict), f"{policy} run lacks canonical telemetry")
            require(telemetry.get("policy") == policy_name, f"{policy} run policy drift")
            require(telemetry.get("inconclusive") == 0, f"{policy} run has inconclusive choices")
    return {
        "report": report,
        "driver": drivers[0]["driver"],
        "summary": summary,
        "findings": findings,
    }


def require_same_control(
    cells: dict[str, dict[str, Any]], key: str, *, message: str
) -> None:
    values = [cell["report"].get(key) for cell in cells.values()]
    require(all(value == values[0] for value in values[1:]), message)


def environment_without_policy(report: dict[str, Any]) -> dict[str, str]:
    environment = dict(report["environment"])
    environment.pop("GLAURUNG_CANONICAL_MODEL_CHOICE", None)
    return environment


def analyze_reports(
    any_model_report: dict[str, Any],
    minimum_report: dict[str, Any],
    maximum_report: dict[str, Any],
) -> dict[str, Any]:
    cells = {
        "any-model": validate_report(any_model_report, label="any-model", policy=None),
        "min-unsigned": validate_report(
            minimum_report, label="min-unsigned", policy="min-unsigned"
        ),
        "max-unsigned": validate_report(
            maximum_report, label="max-unsigned", policy="max-unsigned"
        ),
    }
    require_same_control(cells, "glaurung", message="glaurung identity drift")
    require_same_control(cells, "axeyum", message="axeyum identity drift")
    require_same_control(cells, "binaries", message="authority binary identity drift")
    require_same_control(cells, "repetitions", message="repetition count drift")
    require_same_control(cells, "order", message="execution order drift")
    require_same_control(cells, "process_timeout_seconds", message="process timeout drift")
    require_same_control(cells, "check_timeout_ms_required", message="check timeout drift")
    driver_rows = [cell["driver"] for cell in cells.values()]
    require(all(row == driver_rows[0] for row in driver_rows[1:]), "driver identity drift")
    coverage_rows = [cell["summary"]["coverage"] for cell in cells.values()]
    require(all(row == coverage_rows[0] for row in coverage_rows[1:]), "coverage population drift")
    environments = [environment_without_policy(cell["report"]) for cell in cells.values()]
    require(all(row == environments[0] for row in environments[1:]), "environment drift outside model policy")

    minimum = cells["min-unsigned"]["findings"]
    maximum = cells["max-unsigned"]["findings"]
    unions = {
        backend: set(minimum[backend]) | set(maximum[backend])
        for backend in ("z3", "axeyum")
    }
    require(unions["z3"] == unions["axeyum"], "coverage-union authority findings differ")
    union_findings = sorted(unions["z3"])
    minimum_set = set(minimum["z3"])
    maximum_set = set(maximum["z3"])

    any_findings = cells["any-model"]["findings"]
    any_z3 = set(any_findings["z3"])
    any_axeyum = set(any_findings["axeyum"])
    any_union = any_z3 | any_axeyum
    canonical_union = set(union_findings)

    def policy_summary(cell: dict[str, Any]) -> dict[str, Any]:
        findings = cell["findings"]["z3"]
        canonical = cell["summary"]["canonical_model_choice"]
        return {
            "policy": canonical["policy"],
            "finding_count": len(findings),
            "findings_sha256": text_sha256(findings),
            "ordered_findings": findings,
            "canonical_model_choice": canonical,
            "backend_solves": {
                backend: cell["summary"]["backends"][backend]["solves"]
                for backend in ("z3", "axeyum")
            },
        }

    return {
        "schema": UNION_SCHEMA,
        "accepted": True,
        "claim": "bounded deterministic two-extremum coverage-union authority parity",
        "glaurung": cells["min-unsigned"]["report"]["glaurung"],
        "axeyum": cells["min-unsigned"]["report"]["axeyum"],
        "binaries": cells["min-unsigned"]["report"]["binaries"],
        "driver": driver_rows[0],
        "coverage": coverage_rows[0],
        "repetitions_per_policy_authority": cells["min-unsigned"]["report"]["repetitions"],
        "check_timeout_ms": cells["min-unsigned"]["report"]["check_timeout_ms_required"],
        "policies": {
            "min-unsigned": policy_summary(cells["min-unsigned"]),
            "max-unsigned": policy_summary(cells["max-unsigned"]),
        },
        "coverage_union": {
            "exact_authority_parity": True,
            "finding_count": len(union_findings),
            "findings_sha256": text_sha256(union_findings),
            "ordered_findings": union_findings,
            "shared_by_both_policies": sorted(minimum_set & maximum_set),
            "min_only": sorted(minimum_set - maximum_set),
            "max_only": sorted(maximum_set - minimum_set),
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
        "canonical_union_vs_any_model_combined_union": {
            "shared": sorted(canonical_union & any_union),
            "canonical_only": sorted(canonical_union - any_union),
            "any_model_only": sorted(any_union - canonical_union),
        },
        "claim_limits": [
            "The union contains two deterministic extremal policies, not every satisfying model.",
            "Equal authority unions do not prove exhaustive path or vulnerability coverage.",
            "Standalone process times include policy-dependent probe counts and are not solver-speed evidence.",
        ],
    }


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--any-model-report", type=Path, required=True)
    parser.add_argument("--min-report", type=Path, required=True)
    parser.add_argument("--max-report", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    report = analyze_reports(
        load_json(args.any_model_report),
        load_json(args.min_report),
        load_json(args.max_report),
    )
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
