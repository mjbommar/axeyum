#!/usr/bin/env python3
"""Freeze the exact source-backed raw rows that vary across A0 policies."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any


OUTPUT_SCHEMA = "axeyum.glaurung-policy-difference-population.v1"
EXPECTED_POLICIES = [
    "any-model",
    "min-unsigned",
    "max-unsigned",
    "site-hash-0",
    "site-hash-1",
]
FINDING_PATTERN = re.compile(
    r"^\s*(?P<kind>[a-z][a-z-]*)\s+va=(?P<va>0x[0-9a-f]+).*taint=(?P<taint>\[.*\])$"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"JSON root is not an object: {path}")
    return value


def stable_report_rows(report: dict[str, Any], policy: str) -> dict[str, set[str]]:
    require(report.get("accepted") is True, f"{policy} authority report rejected")
    require(
        report.get("all_drivers_exact_finding_parity") is True,
        f"{policy} lacks exact raw authority parity",
    )
    drivers = report.get("drivers")
    require(isinstance(drivers, list) and drivers, f"{policy} has no drivers")
    result: dict[str, set[str]] = {}
    for driver in drivers:
        require(isinstance(driver, dict), f"{policy} driver is malformed")
        identity = driver.get("driver")
        runs = driver.get("runs")
        require(isinstance(identity, dict), f"{policy} driver identity is malformed")
        require(isinstance(runs, list) and runs, f"{policy} driver has no runs")
        path = identity.get("path")
        require(isinstance(path, str) and path, f"{policy} driver has no path")
        name = Path(path).name
        require(name not in result, f"{policy} repeats driver {name}")
        observed: set[frozenset[str]] = set()
        backends: set[str] = set()
        for run in runs:
            require(isinstance(run, dict), f"{policy}/{name} run is malformed")
            findings = run.get("findings")
            backend = run.get("backend")
            require(
                isinstance(findings, list)
                and all(isinstance(row, str) and row for row in findings),
                f"{policy}/{name} findings are malformed",
            )
            require(backend in {"z3", "axeyum"}, f"{policy}/{name} backend is invalid")
            observed.add(frozenset(findings))
            backends.add(backend)
        require(backends == {"z3", "axeyum"}, f"{policy}/{name} lacks both authorities")
        require(len(observed) == 1, f"{policy}/{name} raw rows are unstable")
        result[name] = set(next(iter(observed)))
    return result


def freeze_population(
    *,
    reports: dict[str, dict[str, Any]],
    report_hashes: dict[str, str],
    source_manifest: dict[str, Any],
    source_manifest_sha256: str,
    analysis_sha256: str,
) -> dict[str, Any]:
    require(list(reports) == EXPECTED_POLICIES, "policy order differs")
    rows = {policy: stable_report_rows(report, policy) for policy, report in reports.items()}
    driver_names = set(rows[EXPECTED_POLICIES[0]])
    require(driver_names, "empty driver population")
    for policy in EXPECTED_POLICIES[1:]:
        require(set(rows[policy]) == driver_names, f"{policy} driver population differs")

    manifest_drivers = source_manifest.get("drivers")
    require(isinstance(manifest_drivers, list), "source manifest has no drivers")
    source_by_name = {
        row.get("name"): row
        for row in manifest_drivers
        if isinstance(row, dict) and isinstance(row.get("name"), str)
    }
    require(driver_names <= set(source_by_name), "source manifest misses a driver")

    output_drivers: list[dict[str, Any]] = []
    kinds: dict[str, int] = {}
    taints: dict[str, int] = {}
    varying_count = 0
    site_keys: set[tuple[str, str]] = set()
    for name in sorted(driver_names):
        policy_sets = [rows[policy][name] for policy in EXPECTED_POLICIES]
        varying = set.union(*policy_sets) - set.intersection(*policy_sets)
        if not varying:
            continue
        frozen_rows: list[dict[str, Any]] = []
        for finding in sorted(varying):
            match = FINDING_PATTERN.match(finding)
            require(match is not None, f"cannot parse finding: {finding}")
            taint_value = json.loads(match.group("taint"))
            require(
                isinstance(taint_value, list)
                and all(isinstance(value, str) for value in taint_value),
                f"invalid taint list: {finding}",
            )
            kind = match.group("kind")
            va = match.group("va")
            kinds[kind] = kinds.get(kind, 0) + 1
            taint_key = json.dumps(taint_value, separators=(",", ":"))
            taints[taint_key] = taints.get(taint_key, 0) + 1
            site_keys.add((name, va))
            varying_count += 1
            frozen_rows.append(
                {
                    "finding": finding,
                    "kind": kind,
                    "va": va,
                    "taint": taint_value,
                    "present_policies": [
                        policy for policy in EXPECTED_POLICIES if finding in rows[policy][name]
                    ],
                    "adjudication": {
                        "status": "pending",
                        "classification": None,
                        "source_lines": None,
                        "machine_evidence": None,
                    },
                }
            )
        manifest_driver = source_by_name[name]
        output_drivers.append(
            {
                "name": name,
                "binary_path": manifest_driver.get("binary_path"),
                "sha256": manifest_driver.get("sha256"),
                "source": manifest_driver.get("source"),
                "varying_finding_count": len(frozen_rows),
                "rows": frozen_rows,
            }
        )

    return {
        "schema": OUTPUT_SCHEMA,
        "name": "glaurung-a0-source-backed-policy-differences-v1",
        "population_definition": "union minus intersection of stable raw findings across all five corrected v3 policies",
        "adjudication_policy": "exhaustive exact-row source-and-machine review; no sampling",
        "source_analysis_sha256": analysis_sha256,
        "source_manifest_sha256": source_manifest_sha256,
        "authority_report_sha256": report_hashes,
        "policy_order": EXPECTED_POLICIES,
        "finding_count": varying_count,
        "site_count": len(site_keys),
        "driver_count": len(output_drivers),
        "kind_counts": dict(sorted(kinds.items())),
        "taint_counts": dict(sorted(taints.items())),
        "drivers": output_drivers,
    }


def parse_report_args(values: list[str]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        require("=" in value, f"report must be POLICY=PATH: {value}")
        policy, path = value.split("=", 1)
        require(policy not in result, f"duplicate report policy: {policy}")
        result[policy] = Path(path)
    require(list(result) == EXPECTED_POLICIES, "report policy order differs")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--analysis", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--report", action="append", default=[])
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    report_paths = parse_report_args(args.report)
    reports = {policy: load_json(path) for policy, path in report_paths.items()}
    result = freeze_population(
        reports=reports,
        report_hashes={policy: file_sha256(path) for policy, path in report_paths.items()},
        source_manifest=load_json(args.source_manifest),
        source_manifest_sha256=file_sha256(args.source_manifest),
        analysis_sha256=file_sha256(args.analysis),
    )
    require(not args.out.exists(), f"refusing to overwrite {args.out}")
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
