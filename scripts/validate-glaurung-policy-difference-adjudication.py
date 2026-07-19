#!/usr/bin/env python3
"""Validate an exhaustive review of the frozen Glaurung policy differences."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any


FROZEN_SCHEMA = "axeyum.glaurung-policy-difference-population.v1"
REVIEW_SCHEMA = "axeyum.glaurung-policy-difference-adjudication-review.v1"
OUTPUT_SCHEMA = "axeyum.glaurung-policy-difference-adjudication-result.v1"
EXPECTED_POLICIES = [
    "any-model",
    "min-unsigned",
    "max-unsigned",
    "site-hash-0",
    "site-hash-1",
]
CLASSIFICATIONS = {
    "real-vulnerability-primitive",
    "ordinary-irp-request-plumbing",
    "duplicate-presentation-of-validated-sink",
    "indeterminate",
}
SOURCE_LINES_PATTERN = re.compile(r"^\d+(?:-\d+)?(?:,\s*\d+(?:-\d+)?)*$")
DISASSEMBLY_PATTERN = re.compile(
    r"^\s*(?P<address>[0-9a-f]+):(?:\s+[0-9a-f]{2})+\s+(?P<instruction>.+?)\s*$"
)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return value


def _safe_relative_path(value: Any) -> str | None:
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        return None
    return value


def _source_line_numbers(specification: str, line_count: int) -> list[int]:
    if not SOURCE_LINES_PATTERN.fullmatch(specification):
        raise ValueError(f"invalid source-line range: {specification!r}")
    result: list[int] = []
    for component in specification.split(","):
        component = component.strip()
        if "-" in component:
            start_text, end_text = component.split("-", 1)
            start, end = int(start_text), int(end_text)
        else:
            start = end = int(component)
        if start < 1 or end < start or end > line_count:
            raise ValueError(f"source-line range is out of bounds: {specification!r}")
        result.extend(range(start, end + 1))
    if len(result) != len(set(result)):
        raise ValueError(f"source-line range overlaps: {specification!r}")
    return result


def _source_excerpt(path: Path, specification: str) -> str:
    lines = path.read_text().splitlines()
    numbers = _source_line_numbers(specification, len(lines))
    return "\n".join(f"{number}:{lines[number - 1]}" for number in numbers)


def _disassemble(binary: Path, objdump: str) -> dict[str, str]:
    completed = subprocess.run(
        [objdump, "-d", "--x86-asm-syntax=intel", str(binary)],
        check=True,
        capture_output=True,
        text=True,
    )
    instructions: dict[str, str] = {}
    for line in completed.stdout.splitlines():
        match = DISASSEMBLY_PATTERN.match(line)
        if match is None:
            continue
        address = f"0x{match.group('address').lower()}"
        instructions[address] = match.group("instruction").strip()
    return instructions


def collect_repository_evidence(
    frozen: dict[str, Any], review: dict[str, Any], repository: Path, objdump: str
) -> tuple[dict[tuple[str, str], dict[str, str]], dict[str, Any]]:
    """Re-read exact source lines and instructions from the pinned repository."""

    repository = repository.resolve()
    failures: list[str] = []
    try:
        revision = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repository,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        return {}, {
            "accepted": False,
            "observed_revision": None,
            "verified_file_count": 0,
            "files": [],
            "failures": [f"cannot identify source repository: {error}"],
        }

    expected_revision = review.get("source_repository_revision")
    if revision != expected_revision:
        failures.append(
            f"source repository revision differs: expected {expected_revision}, observed {revision}"
        )

    drivers = frozen.get("drivers")
    if not isinstance(drivers, list):
        drivers = []
    file_expectations: dict[str, str] = {}
    driver_by_name: dict[str, dict[str, Any]] = {}
    for index, driver in enumerate(drivers):
        if not isinstance(driver, dict):
            failures.append(f"frozen driver {index} is malformed")
            continue
        name = driver.get("name")
        if not isinstance(name, str) or not name or name in driver_by_name:
            failures.append(f"frozen driver {index} has an invalid or repeated name")
            continue
        driver_by_name[name] = driver
        for label, path_value, sha_value in (
            ("binary", driver.get("binary_path"), driver.get("sha256")),
            (
                "source",
                driver.get("source", {}).get("path")
                if isinstance(driver.get("source"), dict)
                else None,
                driver.get("source", {}).get("sha256")
                if isinstance(driver.get("source"), dict)
                else None,
            ),
        ):
            relative = _safe_relative_path(path_value)
            if relative is None:
                failures.append(f"{name} has an unsafe {label} path")
            elif not isinstance(sha_value, str) or not sha_value:
                failures.append(f"{name} lacks a {label} SHA-256")
            elif relative in file_expectations and file_expectations[relative] != sha_value:
                failures.append(f"conflicting file identity for {relative}")
            else:
                file_expectations[relative] = sha_value

    paths = sorted(file_expectations)
    if paths:
        try:
            status = subprocess.run(
                ["git", "status", "--porcelain", "--untracked-files=all", "--", *paths],
                cwd=repository,
                check=True,
                capture_output=True,
                text=True,
            ).stdout
        except (OSError, subprocess.CalledProcessError) as error:
            failures.append(f"cannot inspect source fixture status: {error}")
            status = ""
        if status:
            failures.append("source repository tracked fixture population is dirty")

    verified_files: list[dict[str, Any]] = []
    for relative in paths:
        candidate = repository / relative
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", "--", relative],
            cwd=repository,
            capture_output=True,
            text=True,
        ).returncode == 0
        observed = file_sha256(candidate) if candidate.is_file() else None
        expected = file_expectations[relative]
        if not tracked:
            failures.append(f"source fixture is not tracked: {relative}")
        if observed is None:
            failures.append(f"source fixture is missing: {relative}")
        elif observed != expected:
            failures.append(f"source fixture SHA-256 mismatch: {relative}")
        verified_files.append(
            {
                "path": relative,
                "tracked": tracked,
                "expected_sha256": expected,
                "observed_sha256": observed,
            }
        )

    evidence: dict[tuple[str, str], dict[str, str]] = {}
    disassembly_by_driver: dict[str, dict[str, str]] = {}
    sites = review.get("sites")
    if not isinstance(sites, list):
        sites = []
    for index, site in enumerate(sites):
        if not isinstance(site, dict):
            continue
        name, va = site.get("driver"), site.get("va")
        driver = driver_by_name.get(name) if isinstance(name, str) else None
        if driver is None or not isinstance(va, str):
            continue
        source = driver.get("source")
        source_path = (
            repository / source["path"]
            if isinstance(source, dict) and isinstance(source.get("path"), str)
            else None
        )
        binary_path = repository / driver["binary_path"]
        try:
            excerpt = _source_excerpt(source_path, site.get("source_lines"))  # type: ignore[arg-type]
        except (OSError, TypeError, ValueError) as error:
            failures.append(f"review site {index} source evidence is invalid: {error}")
            excerpt = ""
        if name not in disassembly_by_driver:
            try:
                disassembly_by_driver[name] = _disassemble(binary_path, objdump)
            except (OSError, subprocess.CalledProcessError) as error:
                failures.append(f"cannot disassemble {name}: {error}")
                disassembly_by_driver[name] = {}
        instruction = disassembly_by_driver[name].get(va)
        if instruction is None:
            failures.append(f"review site {index} has no instruction at {name}/{va}")
            instruction = ""
        evidence[(name, va)] = {
            "instruction": instruction,
            "source_excerpt": excerpt,
        }

    return evidence, {
        "accepted": not failures,
        "expected_revision": expected_revision,
        "observed_revision": revision,
        "verified_file_count": len(verified_files),
        "files": verified_files,
        "failures": failures,
    }


def validate_adjudication(
    frozen: dict[str, Any],
    review: dict[str, Any],
    *,
    frozen_sha256: str,
    evidence: dict[tuple[str, str], dict[str, str]],
) -> dict[str, Any]:
    """Require an exact row-complete review and summarize policy consequences."""

    failures: list[str] = []
    if frozen.get("schema") != FROZEN_SCHEMA:
        failures.append("unsupported frozen population schema")
    if review.get("schema") != REVIEW_SCHEMA:
        failures.append("unsupported adjudication review schema")
    if review.get("frozen_population_sha256") != frozen_sha256:
        failures.append("review frozen population SHA-256 differs")
    if frozen.get("policy_order") != EXPECTED_POLICIES:
        failures.append("frozen policy order differs")

    drivers = frozen.get("drivers")
    if not isinstance(drivers, list):
        failures.append("frozen population has no drivers")
        drivers = []
    frozen_rows: dict[str, dict[str, Any]] = {}
    frozen_sites: set[tuple[str, str]] = set()
    source_revisions: set[str] = set()
    for driver_index, driver in enumerate(drivers):
        if not isinstance(driver, dict):
            failures.append(f"frozen driver {driver_index} is malformed")
            continue
        name = driver.get("name")
        source = driver.get("source")
        if isinstance(source, dict) and isinstance(source.get("repository_revision"), str):
            source_revisions.add(source["repository_revision"])
        rows = driver.get("rows")
        if not isinstance(name, str) or not isinstance(rows, list):
            failures.append(f"frozen driver {driver_index} identity or rows are malformed")
            continue
        for row_index, row in enumerate(rows):
            if not isinstance(row, dict) or not isinstance(row.get("finding"), str):
                failures.append(f"frozen row {driver_index}/{row_index} is malformed")
                continue
            finding, va = row["finding"], row.get("va")
            if finding in frozen_rows:
                failures.append(f"frozen population repeats finding {finding}")
                continue
            if not isinstance(va, str):
                failures.append(f"frozen finding has no VA: {finding}")
                continue
            if row.get("adjudication", {}).get("status") != "pending":
                failures.append(f"frozen finding is not preregistered pending: {finding}")
            policies = row.get("present_policies")
            if (
                not isinstance(policies, list)
                or not policies
                or any(policy not in EXPECTED_POLICIES for policy in policies)
                or len(policies) != len(set(policies))
            ):
                failures.append(f"frozen finding has invalid policy membership: {finding}")
            frozen_rows[finding] = {**row, "driver": name}
            frozen_sites.add((name, va))

    if len(frozen_rows) != frozen.get("finding_count"):
        failures.append("frozen finding count is inconsistent")
    if len(frozen_sites) != frozen.get("site_count"):
        failures.append("frozen site count is inconsistent")
    if len(drivers) != frozen.get("driver_count"):
        failures.append("frozen driver count is inconsistent")
    review_revision = review.get("source_repository_revision")
    if len(source_revisions) != 1 or review_revision not in source_revisions:
        failures.append("review source revision differs from frozen population")

    reviewed_rows: dict[str, dict[str, Any]] = {}
    reviewed_sites: set[tuple[str, str]] = set()
    sites = review.get("sites")
    if not isinstance(sites, list):
        failures.append("review has no sites")
        sites = []
    for index, site in enumerate(sites):
        if not isinstance(site, dict):
            failures.append(f"review site {index} is malformed")
            continue
        driver, va = site.get("driver"), site.get("va")
        key = (driver, va)
        if not isinstance(driver, str) or not isinstance(va, str) or key in reviewed_sites:
            failures.append(f"review site {index} has invalid or repeated identity")
            continue
        reviewed_sites.add(key)
        classification = site.get("classification")
        if classification not in CLASSIFICATIONS:
            failures.append(f"review site {index} has an invalid classification")
        source_lines = site.get("source_lines")
        if not isinstance(source_lines, str) or not source_lines:
            failures.append(f"review site {index} lacks source lines")
        machine_evidence = site.get("machine_evidence")
        if not isinstance(machine_evidence, str) or not machine_evidence:
            failures.append(f"review site {index} lacks machine evidence")
        observed = evidence.get(key)
        if (
            not isinstance(observed, dict)
            or not isinstance(observed.get("instruction"), str)
            or not observed["instruction"]
            or not isinstance(observed.get("source_excerpt"), str)
            or not observed["source_excerpt"]
        ):
            failures.append(f"review site {index} lacks re-read instruction evidence")
            observed = {"instruction": None, "source_excerpt": None}
        if site.get("applies_to_all_frozen_rows_at_site") is True:
            findings = [
                finding
                for finding, frozen_row in frozen_rows.items()
                if (frozen_row["driver"], frozen_row["va"]) == key
            ]
        else:
            findings = site.get("findings")
        if not isinstance(findings, list) or not findings or any(
            not isinstance(finding, str) or not finding for finding in findings
        ):
            failures.append(f"review site {index} has malformed findings")
            continue
        if len(findings) != len(set(findings)):
            failures.append(f"review site {index} repeats a finding")
        for finding in findings:
            if finding in reviewed_rows:
                failures.append(f"review repeats finding {finding}")
                continue
            reviewed_rows[finding] = {
                "driver": driver,
                "va": va,
                "classification": classification,
                "source_lines": source_lines,
                "source_excerpt": observed.get("source_excerpt"),
                "instruction": observed.get("instruction"),
                "machine_evidence": machine_evidence,
            }

    if set(reviewed_rows) != set(frozen_rows):
        failures.append("review does not exactly cover the frozen finding population")
    if reviewed_sites != frozen_sites:
        failures.append("review does not exactly cover the frozen site population")
    for finding in set(reviewed_rows) & set(frozen_rows):
        expected = frozen_rows[finding]
        observed = reviewed_rows[finding]
        if (observed["driver"], observed["va"]) != (expected["driver"], expected["va"]):
            failures.append(f"review moves frozen finding to a different site: {finding}")

    rows: list[dict[str, Any]] = []
    classification_counts: dict[str, int] = {}
    real_by_policy = {policy: 0 for policy in EXPECTED_POLICIES}
    real_sets_by_policy = {policy: set() for policy in EXPECTED_POLICIES}
    indeterminate_count = 0
    for finding in sorted(set(reviewed_rows) & set(frozen_rows)):
        frozen_row = frozen_rows[finding]
        review_row = reviewed_rows[finding]
        classification = review_row["classification"]
        if classification in CLASSIFICATIONS:
            classification_counts[classification] = classification_counts.get(classification, 0) + 1
        if classification == "indeterminate":
            indeterminate_count += 1
        if classification == "real-vulnerability-primitive":
            for policy in frozen_row["present_policies"]:
                real_by_policy[policy] += 1
                real_sets_by_policy[policy].add(finding)
        rows.append(
            {
                "finding": finding,
                "driver": frozen_row["driver"],
                "va": frozen_row["va"],
                "kind": frozen_row.get("kind"),
                "taint": frozen_row.get("taint"),
                "present_policies": frozen_row.get("present_policies"),
                **review_row,
            }
        )

    real_populations = {frozenset(rows) for rows in real_sets_by_policy.values()}
    validated_policy_difference = len(real_populations) > 1
    validated_residual_gap = validated_policy_difference and any(real_sets_by_policy.values())
    return {
        "schema": OUTPUT_SCHEMA,
        "accepted": not failures,
        "frozen_population_sha256": frozen_sha256,
        "source_repository_revision": review_revision,
        "adjudicated_finding_count": len(rows),
        "adjudicated_site_count": len(reviewed_sites & frozen_sites),
        "classification_counts": dict(sorted(classification_counts.items())),
        "indeterminate_count": indeterminate_count,
        "real_primitive_counts_by_policy": real_by_policy,
        "validated_policy_difference": validated_policy_difference,
        "validated_residual_gap": validated_residual_gap,
        "symbolic_memory_gate": "open" if validated_residual_gap and indeterminate_count == 0 else "closed",
        "rows": rows,
        "failures": failures,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frozen", type=Path, required=True)
    parser.add_argument("--review", type=Path, required=True)
    parser.add_argument("--source-repository", type=Path, required=True)
    parser.add_argument("--objdump", default="llvm-objdump")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    frozen = load_json(args.frozen)
    review = load_json(args.review)
    frozen_sha256 = file_sha256(args.frozen)
    evidence, repository_result = collect_repository_evidence(
        frozen, review, args.source_repository, args.objdump
    )
    result = validate_adjudication(
        frozen, review, frozen_sha256=frozen_sha256, evidence=evidence
    )
    result["source_repository_verification"] = repository_result
    if not repository_result["accepted"]:
        result["failures"].extend(repository_result["failures"])
        result["accepted"] = False
    if args.out.exists():
        raise ValueError(f"refusing to overwrite {args.out}")
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
