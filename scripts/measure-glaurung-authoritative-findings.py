#!/usr/bin/env python3
"""Compare stable findings under Z3- and Axeyum-authoritative exploration."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import statistics
import subprocess
from pathlib import Path
from typing import Any


TIME_PREFIX = "__AXEYUM_AUTH_TIME__"
CANONICAL_MODEL_POLICIES = {
    "min-unsigned": "glaurung-min-unsigned-v1",
    "max-unsigned": "glaurung-max-unsigned-v1",
    "site-hash-0": "glaurung-site-hash-0-v1",
    "site-hash-1": "glaurung-site-hash-1-v1",
}
CONCRETIZATION_POLICY_ENV = "GLAURUNG_CONCRETIZATION_POLICY"
LEGACY_CANONICAL_MODEL_CHOICE_ENV = "GLAURUNG_CANONICAL_MODEL_CHOICE"
SYMBOLIC_RE = re.compile(
    r"\[symbolic\] \S+\s+raw=(\d+) high-confidence=(\d+) suppressed=(\d+).*"
    r"analyzed=(\d+)/(\d+)(.*)"
)
SOLVER_RE = re.compile(
    r"\[solver\] backend=(\S+) solves=(\d+) solver_time=([0-9.]+)ms "
    r"avg=([0-9.]+)us/solve"
)
CANONICAL_MODEL_CHOICE_RE = re.compile(
    r"\[canonical-model-choice\] policy=(\S+) attempts=(\d+) completed=(\d+) "
    r"infeasible=(\d+) probes=(\d+) inconclusive=(\d+) unsupported_width=(\d+) "
    r"unknown=(\d+) no_solver=(\d+) error=(\d+) final_unsat=(\d+)"
)
EXPLORATION_LIMITS_RE = re.compile(
    r"\[exploration-limits\] runs=(\d+) completed=(\d+) state_budget=(\d+) "
    r"solve_budget=(\d+) timeout_budget=(\d+) deadline=(\d+)"
)
CHECK_TIMEOUT_RE = re.compile(r"\[solver\][^\n]* check_timeout_ms=(\d+)")
TIME_RE = re.compile(
    rf"{TIME_PREFIX} elapsed_seconds=([0-9.]+) max_rss_kib=(\d+) exit=(\d+)"
)
FINDING_CONFIDENCE_RE = re.compile(
    r"\[finding-confidence\] schema=(\S+) high=(\d+) diagnostic=(\d+)"
)
FINDING_CONFIDENCE_SUFFIX_RE = re.compile(r"\tconfidence=([^\t]+)$")
FINDING_CONFIDENCE_SCHEMA = "glaurung-ioctlance-confidence-v1"
AUTHORITY_SCHEMA_V5 = "axeyum.glaurung-authoritative-finding-parity.v5"
AUTHORITY_SCHEMA_V6 = "axeyum.glaurung-authoritative-finding-parity.v6"


def resolve_policy_configuration(
    preferred: str | None, legacy: str | None
) -> dict[str, Any]:
    """Resolve one explicit deterministic policy surface without ambiguity."""

    if preferred is not None and legacy is not None:
        raise RuntimeError(
            f"both {CONCRETIZATION_POLICY_ENV} and "
            f"{LEGACY_CANONICAL_MODEL_CHOICE_ENV} were requested; configure exactly one"
        )
    if preferred is not None:
        if preferred not in CANONICAL_MODEL_POLICIES:
            raise RuntimeError(f"unsupported concretization policy: {preferred}")
        return {
            "environment": {CONCRETIZATION_POLICY_ENV: preferred},
            "label": preferred,
            "policy_id": CANONICAL_MODEL_POLICIES[preferred],
            "source": "preferred",
        }
    if legacy is not None:
        if legacy not in CANONICAL_MODEL_POLICIES:
            raise RuntimeError(f"unsupported legacy canonical policy: {legacy}")
        return {
            "environment": {LEGACY_CANONICAL_MODEL_CHOICE_ENV: legacy},
            "label": legacy,
            "policy_id": CANONICAL_MODEL_POLICIES[legacy],
            "source": "legacy",
        }
    return {
        "environment": {},
        "label": None,
        "policy_id": None,
        "source": "default",
    }


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def text_sha256(lines: list[str]) -> str:
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


def parse_annotated_findings(
    stdout: str, *, annotation_active: bool | None = None
) -> dict[str, Any]:
    findings: list[str] = []
    high_confidence: list[str] = []
    diagnostic: list[str] = []
    annotated = 0
    legacy = 0
    for row in (line for line in stdout.splitlines() if line):
        match = FINDING_CONFIDENCE_SUFFIX_RE.search(row)
        if match is None:
            legacy += 1
            findings.append(row)
            continue
        confidence = match.group(1)
        finding = row[: match.start()]
        if confidence == "high":
            high_confidence.append(finding)
        elif confidence == "diagnostic":
            diagnostic.append(finding)
        else:
            raise RuntimeError(f"unknown finding confidence annotation: {confidence}")
        annotated += 1
        findings.append(finding)
    if annotated and legacy:
        raise RuntimeError("mixed annotated and legacy finding rows")
    inferred_active = annotated > 0
    if annotation_active is None:
        annotation_active = inferred_active
    elif annotation_active and legacy:
        raise RuntimeError("confidence footer present with legacy finding rows")
    elif not annotation_active and annotated:
        raise RuntimeError("annotated finding rows missing confidence footer")
    result: dict[str, Any] = {
        "findings": findings,
        "confidence_partition_available": annotation_active,
    }
    if annotation_active:
        result.update(
            {
                "high_confidence_findings": high_confidence,
                "diagnostic_findings": diagnostic,
            }
        )
    return result


def parse_finding_confidence_footer(stderr: str) -> dict[str, int | str] | None:
    match = FINDING_CONFIDENCE_RE.search(stderr)
    if match is None:
        return None
    schema = match.group(1)
    if schema != FINDING_CONFIDENCE_SCHEMA:
        raise RuntimeError(f"unsupported finding confidence schema: {schema}")
    return {
        "schema": schema,
        "high": int(match.group(2)),
        "diagnostic": int(match.group(3)),
    }


def git_identity(repository: Path) -> dict[str, Any]:
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return {
        "path": str(repository),
        "revision": revision,
        "tracked_dirty": bool(status),
        "tracked_status_sha256": hashlib.sha256(status.encode()).hexdigest(),
    }


def require_match(pattern: re.Pattern[str], text: str, label: str) -> re.Match[str]:
    match = pattern.search(text)
    if match is None:
        raise RuntimeError(f"missing {label} row")
    return match


def parse_key_values(line: str) -> dict[str, int | str]:
    values: dict[str, int | str] = {}
    for key, value in re.findall(r"([a-z][a-z0-9-]*)=([^ ]+)", line):
        values[key] = int(value) if value.isdecimal() else value
    return values


def parse_canonical_model_choice(
    stderr: str, *, required_policy: str | None
) -> dict[str, int | str] | None:
    match = CANONICAL_MODEL_CHOICE_RE.search(stderr)
    if match is None:
        if required_policy is not None:
            raise RuntimeError("missing canonical-model-choice row")
        return None
    telemetry: dict[str, int | str] = {
        "policy": match.group(1),
        "attempts": int(match.group(2)),
        "completed": int(match.group(3)),
        "infeasible": int(match.group(4)),
        "probes": int(match.group(5)),
        "inconclusive": int(match.group(6)),
        "unsupported_width": int(match.group(7)),
        "unknown": int(match.group(8)),
        "no_solver": int(match.group(9)),
        "error": int(match.group(10)),
        "final_unsat": int(match.group(11)),
    }
    if required_policy is None:
        return telemetry
    if telemetry["policy"] != required_policy:
        raise RuntimeError(
            "unexpected canonical model policy: "
            f"expected {required_policy}, observed {telemetry['policy']}"
        )
    attempts = int(telemetry["attempts"])
    completed = int(telemetry["completed"])
    infeasible = int(telemetry["infeasible"])
    probes = int(telemetry["probes"])
    inconclusive = int(telemetry["inconclusive"])
    reasons = sum(
        int(telemetry[key])
        for key in (
            "unsupported_width",
            "unknown",
            "no_solver",
            "error",
            "final_unsat",
        )
    )
    if attempts == 0 or completed == 0:
        raise RuntimeError("canonical model policy was not exercised")
    if completed + infeasible + inconclusive != attempts:
        raise RuntimeError("canonical model attempt accounting is inconsistent")
    if reasons != inconclusive:
        raise RuntimeError("canonical model failure accounting is inconsistent")
    if inconclusive != 0:
        raise RuntimeError("canonical model policy did not complete every attempt")
    if probes < completed + infeasible:
        raise RuntimeError("canonical model probe accounting is inconsistent")
    return telemetry


def parse_check_timeout_ms(stderr: str, *, expected: int | None) -> int | None:
    match = CHECK_TIMEOUT_RE.search(stderr)
    if match is None:
        if expected is not None:
            raise RuntimeError("missing solver check-timeout telemetry")
        return None
    observed = int(match.group(1))
    if expected is not None and observed != expected:
        raise RuntimeError(
            f"solver check-timeout mismatch: expected {expected}, observed {observed}"
        )
    return observed


def parse_exploration_limits(
    stderr: str, *, require_deterministic_worklists: bool
) -> dict[str, int] | None:
    matches = list(EXPLORATION_LIMITS_RE.finditer(stderr))
    if not matches:
        if require_deterministic_worklists:
            raise RuntimeError("missing exploration-limits row")
        return None
    if len(matches) != 1:
        raise RuntimeError("multiple exploration-limits rows")
    match = matches[0]
    keys = (
        "runs",
        "completed",
        "state_budget",
        "solve_budget",
        "timeout_budget",
        "deadline",
    )
    telemetry = {key: int(match.group(index)) for index, key in enumerate(keys, 1)}
    classified = sum(telemetry[key] for key in keys[1:])
    if classified != telemetry["runs"]:
        raise RuntimeError("exploration-limit accounting is inconsistent")
    if require_deterministic_worklists and (
        telemetry["timeout_budget"] != 0 or telemetry["deadline"] != 0
    ):
        raise RuntimeError("exploration has a deadline/timeout stop")
    return telemetry


def validate_coverage_boundary(
    *,
    tail: str,
    analyzed: int,
    reachable: int,
    max_analyzed_functions: int | None,
) -> str:
    deadline_hit = "DEADLINE-HIT" in tail
    work_limit_hit = "WORK-LIMIT-HIT" in tail
    if deadline_hit:
        raise RuntimeError("analysis hit the wall-clock safety deadline")
    if work_limit_hit:
        if max_analyzed_functions is None:
            raise RuntimeError("analysis hit an undeclared fixed-work boundary")
        if analyzed != max_analyzed_functions:
            raise RuntimeError(
                "fixed-work boundary count mismatch: "
                f"expected {max_analyzed_functions}, observed {analyzed}"
            )
        return "fixed-work-limit"
    if max_analyzed_functions is not None and analyzed >= max_analyzed_functions:
        raise RuntimeError("analysis reached the fixed-work count without reporting it")
    if analyzed > reachable:
        raise RuntimeError("analyzed count exceeds reachable-function count")
    return "complete"


def run_one(
    repository: Path,
    binary: Path,
    driver: Path,
    backend: str,
    repetition: int,
    position: int,
    common_environment: dict[str, str],
    process_timeout_seconds: int,
    max_analyzed_functions: int | None,
    required_canonical_model_policy: str | None,
    expected_check_timeout_ms: int | None,
    require_deterministic_worklists: bool,
) -> dict[str, Any]:
    environment = os.environ.copy()
    for inherited in (
        "GLAURUNG_SHADOW_DIFF",
        "GLAURUNG_FAIR_SHADOW",
        "GLAURUNG_AXEYUM_PROFILE_DIR",
        "GLAURUNG_ORDERED_TRACE_DIR",
        CONCRETIZATION_POLICY_ENV,
        LEGACY_CANONICAL_MODEL_CHOICE_ENV,
        "GLAURUNG_CHECK_TIMEOUT_MS",
    ):
        environment.pop(inherited, None)
    environment.update(common_environment)
    if backend == "axeyum":
        environment.update(
            {
                "GLAURUNG_AXEYUM_WARM_REUSE": "adaptive",
                "GLAURUNG_AXEYUM_DIRECT_DELTA": "1",
                "GLAURUNG_AXEYUM_WARM_SERIAL_SIBLING_REUSE": "1",
                "GLAURUNG_AXEYUM_WARM_OWNER_TRANSFER": "0",
                "GLAURUNG_AXEYUM_WARM_TIMEOUT_COLD_RETRY": "0",
                "GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE": "0",
                "GLAURUNG_AXEYUM_REPLAY_SAT_CACHE": "1",
                "GLAURUNG_AXEYUM_WARM_MAX_LIVE_PATHS": "9",
                "GLAURUNG_AXEYUM_WARM_MAX_ASSERTIONS_PER_PATH": "512",
            }
        )
    else:
        environment["GLAURUNG_AXEYUM_WARM_REUSE"] = "off"

    command = [
        "/usr/bin/time",
        "-f",
        f"{TIME_PREFIX} elapsed_seconds=%e max_rss_kib=%M exit=%x",
        str(binary),
        str(driver),
    ]
    result = subprocess.run(
        command,
        cwd=repository,
        env=environment,
        capture_output=True,
        text=True,
        timeout=process_timeout_seconds,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"{backend} repetition {repetition} exited {result.returncode}:\n"
            + "\n".join(result.stderr.splitlines()[-30:])
        )

    symbolic = require_match(SYMBOLIC_RE, result.stderr, "symbolic")
    solver = require_match(SOLVER_RE, result.stderr, "solver")
    timing = require_match(TIME_RE, result.stderr, "time")
    canonical_model_choice = parse_canonical_model_choice(
        result.stderr, required_policy=required_canonical_model_policy
    )
    check_timeout_ms = parse_check_timeout_ms(
        result.stderr, expected=expected_check_timeout_ms
    )
    exploration_limits = parse_exploration_limits(
        result.stderr,
        require_deterministic_worklists=require_deterministic_worklists,
    )
    if solver.group(1) != backend:
        raise RuntimeError(f"expected {backend} binary, observed {solver.group(1)}")
    analyzed = int(symbolic.group(4))
    reachable = int(symbolic.group(5))
    coverage_boundary = validate_coverage_boundary(
        tail=symbolic.group(6),
        analyzed=analyzed,
        reachable=reachable,
        max_analyzed_functions=max_analyzed_functions,
    )

    confidence_footer = parse_finding_confidence_footer(result.stderr)
    parsed_findings = parse_annotated_findings(
        result.stdout, annotation_active=confidence_footer is not None
    )
    findings = parsed_findings["findings"]
    if len(findings) != int(symbolic.group(1)):
        raise RuntimeError("IOCTLANCE_ALL output does not match raw finding count")
    run: dict[str, Any] = {
        "backend": backend,
        "repetition": repetition,
        "position": position,
        "finding_count": len(findings),
        "findings_sha256": text_sha256(findings),
        "findings": findings,
        "reported_raw": int(symbolic.group(1)),
        "reported_lines": len(findings),
        "reported_suppressed": int(symbolic.group(3)),
        "confidence_partition_available": parsed_findings[
            "confidence_partition_available"
        ],
        "analyzed": analyzed,
        "analysis_roots": reachable,
        "coverage_boundary": coverage_boundary,
        "solves": int(solver.group(2)),
        "solver_time_ms": float(solver.group(3)),
        "average_us_per_solve": float(solver.group(4)),
        "elapsed_seconds": float(timing.group(1)),
        "max_rss_kib": int(timing.group(2)),
        "time_exit": int(timing.group(3)),
    }
    if confidence_footer is not None:
        high_confidence_findings = parsed_findings["high_confidence_findings"]
        diagnostic_findings = parsed_findings["diagnostic_findings"]
        reported_high_confidence = int(symbolic.group(2))
        if reported_high_confidence != int(confidence_footer["high"]):
            raise RuntimeError("high-confidence footer count mismatch")
        if int(symbolic.group(3)) != int(confidence_footer["diagnostic"]):
            raise RuntimeError("diagnostic footer count mismatch")
        if len(high_confidence_findings) != reported_high_confidence:
            raise RuntimeError("annotated high-confidence finding count mismatch")
        if len(diagnostic_findings) != int(symbolic.group(3)):
            raise RuntimeError("annotated diagnostic finding count mismatch")
        if len(findings) != len(high_confidence_findings) + len(diagnostic_findings):
            raise RuntimeError("finding confidence partition is not exhaustive")
        run.update(
            {
                "finding_confidence_schema": confidence_footer["schema"],
                "reported_high_confidence": reported_high_confidence,
                "high_confidence_finding_count": len(high_confidence_findings),
                "high_confidence_findings_sha256": text_sha256(
                    high_confidence_findings
                ),
                "high_confidence_findings": high_confidence_findings,
                "diagnostic_finding_count": len(diagnostic_findings),
                "diagnostic_findings_sha256": text_sha256(diagnostic_findings),
                "diagnostic_findings": diagnostic_findings,
            }
        )
    if canonical_model_choice is not None:
        run["canonical_model_choice"] = canonical_model_choice
    if check_timeout_ms is not None:
        run["check_timeout_ms"] = check_timeout_ms
    if exploration_limits is not None:
        run["exploration_limits"] = exploration_limits
    if backend == "axeyum":
        for prefix, key in (
            ("[axeyum-warm]", "warm"),
            ("[axeyum-sat-cache]", "sat_cache"),
            ("[axeyum-serial-owner]", "serial_owner"),
        ):
            line = next(
                (row for row in result.stderr.splitlines() if row.startswith(prefix)),
                None,
            )
            if line is not None:
                run[key] = parse_key_values(line)
    return run


def summarize_finding_population(
    populations: dict[str, list[dict[str, Any]]],
    *,
    findings_key: str,
    hash_key: str,
) -> dict[str, Any]:
    stability: dict[str, dict[str, Any]] = {}
    for backend, population in populations.items():
        finding_sets = [set(run[findings_key]) for run in population]
        if any(
            len(candidate) != len(run[findings_key])
            for candidate, run in zip(finding_sets, population)
        ):
            raise RuntimeError(f"{backend} emitted duplicate {findings_key} rows")
        stable_findings = set.intersection(*finding_sets)
        union_findings = set.union(*finding_sets)
        hashes = sorted({run[hash_key] for run in population})
        stability[backend] = {
            "output_stable": len(hashes) == 1,
            "distinct_hashes": hashes,
            "stable_finding_count": len(stable_findings),
            "union_finding_count": len(union_findings),
            "unstable_findings": sorted(union_findings - stable_findings),
            "stable_findings": stable_findings,
            "union_findings": union_findings,
        }
    z3_findings = populations["z3"][0][findings_key]
    axeyum_findings = populations["axeyum"][0][findings_key]
    z3_stable = stability["z3"]["stable_findings"]
    z3_union = stability["z3"]["union_findings"]
    axeyum_stable = stability["axeyum"]["stable_findings"]
    axeyum_union = stability["axeyum"]["union_findings"]
    both_stable = all(row["output_stable"] for row in stability.values())
    return {
        "exact_finding_parity": both_stable and z3_findings == axeyum_findings,
        "within_backend_stable": both_stable,
        "stable_intersection_count": len(z3_stable & axeyum_stable),
        "z3_only": sorted(z3_stable - axeyum_union),
        "axeyum_only": sorted(axeyum_stable - z3_union),
        "stability": {
            backend: {
                key: value
                for key, value in row.items()
                if key not in ("stable_findings", "union_findings")
            }
            for backend, row in stability.items()
        },
    }


def summarize_driver(runs: list[dict[str, Any]]) -> dict[str, Any]:
    process_failures = [run for run in runs if "run_error" in run]
    if process_failures:
        labels = ", ".join(
            f"{run['backend']} repetition {run['repetition']} position {run['position']}"
            for run in process_failures
        )
        raise RuntimeError(f"process failures: {labels}")
    populations = {
        backend: [run for run in runs if run["backend"] == backend]
        for backend in ("z3", "axeyum")
    }
    for backend, population in populations.items():
        if len(population) * 2 != len(runs):
            raise RuntimeError(f"{backend} finding population is unbalanced")
        structural = {
            (
                run["analyzed"],
                run["analysis_roots"],
                run["coverage_boundary"],
            )
            for run in population
        }
        if len(structural) != 1 or any(run["time_exit"] for run in population):
            raise RuntimeError(f"{backend} work population drift")

    authority_coverage = {
        (
            population[0]["analyzed"],
            population[0]["analysis_roots"],
            population[0]["coverage_boundary"],
        )
        for population in populations.values()
    }
    if len(authority_coverage) != 1:
        raise RuntimeError("authority coverage populations differ")

    check_timeout_presence = {"check_timeout_ms" in run for run in runs}
    if len(check_timeout_presence) != 1:
        raise RuntimeError("solver check-timeout telemetry availability drift")
    check_timeout_ms: int | None = None
    if check_timeout_presence.pop():
        check_timeouts = {int(run["check_timeout_ms"]) for run in runs}
        if len(check_timeouts) != 1:
            raise RuntimeError("solver check-timeout population drift")
        check_timeout_ms = check_timeouts.pop()

    exploration_presence = {"exploration_limits" in run for run in runs}
    if len(exploration_presence) != 1:
        raise RuntimeError("exploration-limit telemetry availability drift")
    exploration_available = exploration_presence.pop()
    exploration_summary: dict[str, Any] | None = None
    deterministic_worklists_verified = False
    if exploration_available:
        exploration_keys = (
            "runs",
            "completed",
            "state_budget",
            "solve_budget",
            "timeout_budget",
            "deadline",
        )
        exploration_summary = {"backends": {}}
        for backend, population in populations.items():
            telemetry_rows = {
                tuple(run["exploration_limits"][key] for key in exploration_keys)
                for run in population
            }
            if len(telemetry_rows) != 1:
                raise RuntimeError(f"{backend} exploration-limit telemetry drift")
            values = telemetry_rows.pop()
            exploration_summary["backends"][backend] = dict(
                zip(exploration_keys, values)
            )
        deterministic_worklists_verified = all(
            int(telemetry[stop]) == 0
            for telemetry in exploration_summary["backends"].values()
            for stop in ("timeout_budget", "deadline")
        )

    canonical_presence = {"canonical_model_choice" in run for run in runs}
    if len(canonical_presence) != 1:
        raise RuntimeError("canonical model telemetry availability drift")
    canonical_available = canonical_presence.pop()
    canonical_summary: dict[str, Any] | None = None
    if canonical_available:
        canonical_keys = (
            "policy",
            "attempts",
            "completed",
            "infeasible",
            "probes",
            "inconclusive",
            "unsupported_width",
            "unknown",
            "no_solver",
            "error",
            "final_unsat",
        )
        policies = {str(run["canonical_model_choice"]["policy"]) for run in runs}
        if len(policies) != 1:
            raise RuntimeError("canonical model policy drift")
        canonical_summary = {"policy": policies.pop(), "backends": {}}
        for backend, population in populations.items():
            telemetry_rows = {
                tuple(run["canonical_model_choice"][key] for key in canonical_keys)
                for run in population
            }
            if len(telemetry_rows) != 1:
                raise RuntimeError(f"{backend} canonical model telemetry drift")
            values = telemetry_rows.pop()
            canonical_summary["backends"][backend] = dict(zip(canonical_keys, values))

    telemetry_presence = {
        all(key in run for key in ("warm", "sat_cache", "serial_owner"))
        for run in populations["axeyum"]
    }
    if len(telemetry_presence) != 1:
        raise RuntimeError("Axeyum warm telemetry availability drift")
    telemetry_available = telemetry_presence.pop()
    if telemetry_available:
        for run in populations["axeyum"]:
            warm = run["warm"]
            cache = run["sat_cache"]
            serial = run["serial_owner"]
            if (
                warm.get("resets") != 0
                or warm.get("paths-live") != 0
                or warm.get("path-cap-fallbacks") != 0
                or warm.get("assertion-cap-fallbacks") != 0
                or cache.get("replay-failures") != 0
                or cache.get("entries") != 0
                or serial.get("tracked-owners") != 0
                or serial.get("references") != 0
            ):
                raise RuntimeError("Axeyum lifecycle, fallback, or replay gate failed")

    raw_summary = summarize_finding_population(
        populations, findings_key="findings", hash_key="findings_sha256"
    )
    confidence_presence = {
        bool(run.get("confidence_partition_available")) for run in runs
    }
    if len(confidence_presence) != 1:
        raise RuntimeError("finding confidence partition availability drift")
    confidence_available = confidence_presence.pop()
    high_confidence_summary: dict[str, Any] | None = None
    diagnostic_summary: dict[str, Any] | None = None
    if confidence_available:
        schemas = {str(run["finding_confidence_schema"]) for run in runs}
        if schemas != {FINDING_CONFIDENCE_SCHEMA}:
            raise RuntimeError("finding confidence schema drift")
        for run in runs:
            if run["reported_raw"] != (
                run["high_confidence_finding_count"] + run["diagnostic_finding_count"]
            ):
                raise RuntimeError("finding confidence count partition drift")
            if run["reported_high_confidence"] != run["high_confidence_finding_count"]:
                raise RuntimeError("reported high-confidence count drift")
            if run["reported_suppressed"] != run["diagnostic_finding_count"]:
                raise RuntimeError("reported diagnostic count drift")
        high_confidence_summary = summarize_finding_population(
            populations,
            findings_key="high_confidence_findings",
            hash_key="high_confidence_findings_sha256",
        )
        diagnostic_summary = summarize_finding_population(
            populations,
            findings_key="diagnostic_findings",
            hash_key="diagnostic_findings_sha256",
        )
    result: dict[str, Any] = {
        "exact_finding_parity": raw_summary["exact_finding_parity"],
        "exact_raw_finding_parity": raw_summary["exact_finding_parity"],
        "exact_high_confidence_finding_parity": (
            high_confidence_summary["exact_finding_parity"]
            if high_confidence_summary is not None
            else None
        ),
        "within_backend_stable": raw_summary["within_backend_stable"],
        "stable_intersection_count": raw_summary["stable_intersection_count"],
        "z3_only": raw_summary["z3_only"],
        "axeyum_only": raw_summary["axeyum_only"],
        "stability": raw_summary["stability"],
        "raw": raw_summary,
        "high_confidence": high_confidence_summary,
        "diagnostic": diagnostic_summary,
        "confidence_partition_available": confidence_available,
        "coverage": {
            "analyzed": populations["z3"][0]["analyzed"],
            "reachable": populations["z3"][0]["analysis_roots"],
            "boundary": populations["z3"][0]["coverage_boundary"],
        },
        "backends": {},
        "canonical_model_choice": canonical_summary,
        "check_timeout_ms": check_timeout_ms,
        "exploration_limits": exploration_summary,
        "deterministic_worklists_verified": deterministic_worklists_verified,
    }
    for backend, population in populations.items():
        backend_stability = raw_summary["stability"][backend]
        result["backends"][backend] = {
            "finding_count": (
                population[0]["finding_count"]
                if backend_stability["output_stable"]
                else None
            ),
            "finding_counts": [run["finding_count"] for run in population],
            "findings_sha256": (
                population[0]["findings_sha256"]
                if backend_stability["output_stable"]
                else None
            ),
            "findings_sha256_per_run": [run["findings_sha256"] for run in population],
            "solves": [run["solves"] for run in population],
            "solver_time_ms": [run["solver_time_ms"] for run in population],
            "solver_time_median_ms": statistics.median(
                run["solver_time_ms"] for run in population
            ),
            "elapsed_seconds": [run["elapsed_seconds"] for run in population],
            "max_rss_kib": [run["max_rss_kib"] for run in population],
            "analyzed": population[0]["analyzed"],
            "analysis_roots": population[0]["analysis_roots"],
        }
        if confidence_available:
            high_stability = high_confidence_summary["stability"][backend]
            diagnostic_stability = diagnostic_summary["stability"][backend]
            result["backends"][backend].update(
                {
                    "high_confidence_finding_count": (
                        population[0]["high_confidence_finding_count"]
                        if high_stability["output_stable"]
                        else None
                    ),
                    "high_confidence_finding_counts": [
                        run["high_confidence_finding_count"] for run in population
                    ],
                    "high_confidence_findings_sha256": (
                        population[0]["high_confidence_findings_sha256"]
                        if high_stability["output_stable"]
                        else None
                    ),
                    "diagnostic_finding_count": (
                        population[0]["diagnostic_finding_count"]
                        if diagnostic_stability["output_stable"]
                        else None
                    ),
                    "diagnostic_finding_counts": [
                        run["diagnostic_finding_count"] for run in population
                    ],
                    "diagnostic_findings_sha256": (
                        population[0]["diagnostic_findings_sha256"]
                        if diagnostic_stability["output_stable"]
                        else None
                    ),
                }
            )
    result["axeyum_warm_telemetry_available"] = telemetry_available
    if telemetry_available:
        representative = populations["axeyum"][0]
        checks = int(representative["warm"]["checks"])
        created = int(representative["warm"]["paths-created"])
        result["axeyum_warm_execution"] = {
            "checks": checks,
            "owner_created_checks": created,
            "owner_retained_checks": checks - created,
            "owner_retained_percent": (checks - created) * 100 / checks,
            "replay_cache_hits": int(representative["sat_cache"]["hits"]),
            "fallbacks": 0,
        }
    else:
        result["axeyum_warm_execution"] = None
        result["axeyum_warm_telemetry_note"] = (
            "the Glaurung example prints warm lifecycle rows only when both solver "
            "features are compiled; the Axeyum-only authority binary does not expose them"
        )
    return result


def finding_acceptance_failures(
    driver: Path, summary: dict[str, Any], population: str = "raw"
) -> list[str]:
    if population not in ("raw", "high-confidence"):
        raise ValueError(f"unknown finding acceptance population: {population}")
    selected = summary["raw"] if population == "raw" else summary["high_confidence"]
    if selected is None:
        return [f"{driver}: {population} finding partition unavailable"]
    if selected["exact_finding_parity"]:
        return []
    failures = []
    population_label = "" if population == "raw" else f"{population} "
    for backend in ("z3", "axeyum"):
        stability = selected["stability"][backend]
        if not stability["output_stable"]:
            failures.append(
                f"{driver}: {backend} {population_label}finding output unstable "
                f"(distinct-hashes={len(stability['distinct_hashes'])}, "
                f"stable={stability['stable_finding_count']}, "
                f"union={stability['union_finding_count']})"
            )
    label = (
        "exact finding parity"
        if population == "raw"
        else "exact high-confidence finding parity"
    )
    failures.append(
        f"{driver}: {label} failed "
        f"(z3-only={len(selected['z3_only'])}, "
        f"axeyum-only={len(selected['axeyum_only'])})"
    )
    return failures


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--glaurung-repo", type=Path, required=True)
    parser.add_argument("--z3-binary", type=Path, required=True)
    parser.add_argument("--axeyum-binary", type=Path, required=True)
    parser.add_argument("--driver", type=Path, action="append", required=True)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--deadline-secs", type=int, default=300)
    parser.add_argument("--max-analyzed-functions", type=int)
    parser.add_argument("--solve-budget", type=int, default=20000)
    parser.add_argument("--solve-secs", type=int, default=60)
    parser.add_argument("--process-timeout-secs", type=int, default=600)
    policy_group = parser.add_mutually_exclusive_group()
    policy_group.add_argument(
        "--concretization-policy",
        choices=tuple(CANONICAL_MODEL_POLICIES),
        help=(
            "select and require one first-class deterministic concretization "
            "policy through GLAURUNG_CONCRETIZATION_POLICY"
        ),
    )
    policy_group.add_argument(
        "--canonical-model-choice",
        nargs="?",
        const="min-unsigned",
        choices=tuple(CANONICAL_MODEL_POLICIES),
        help=(
            "enable and require a named backend-independent unsigned-extremum or "
            "stable-site mixed-extremum model-selection policy (omitting the value "
            "preserves the historical min-unsigned behavior)"
        ),
    )
    parser.add_argument(
        "--check-timeout-ms",
        type=int,
        help="explicit shared per-check timeout for both native solver backends",
    )
    parser.add_argument(
        "--acceptance-population",
        choices=("raw", "high-confidence"),
        default="raw",
        help=(
            "finding population whose exact authority parity controls process "
            "acceptance; both populations remain recorded"
        ),
    )
    parser.add_argument(
        "--require-deterministic-worklists",
        action="store_true",
        help=(
            "require Glaurung's exploration-limit stop partition, reject any "
            "deadline/timeout stop, and require stable per-backend partitions"
        ),
    )
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if args.repetitions < 2:
        parser.error("--repetitions must be at least 2")
    for name in (
        "deadline_secs",
        "solve_budget",
        "solve_secs",
        "process_timeout_secs",
    ):
        if getattr(args, name) < 1:
            parser.error(f"--{name.replace('_', '-')} must be positive")
    if args.max_analyzed_functions is not None and args.max_analyzed_functions < 1:
        parser.error("--max-analyzed-functions must be positive")
    if args.check_timeout_ms is not None and not 1 <= args.check_timeout_ms <= 60_000:
        parser.error("--check-timeout-ms must be from 1 to 60000")

    repository = args.glaurung_repo.resolve()
    axeyum_repository = Path(__file__).resolve().parents[1]

    def resolve(path: Path) -> Path:
        return path.resolve() if path.is_absolute() else (repository / path).resolve()

    z3_binary = resolve(args.z3_binary)
    axeyum_binary = resolve(args.axeyum_binary)
    drivers = [resolve(driver) for driver in args.driver]
    for path in (repository, z3_binary, axeyum_binary, *drivers):
        if not path.exists():
            parser.error(f"path does not exist: {path}")

    glaurung_identity = git_identity(repository)
    axeyum_identity = git_identity(axeyum_repository)
    if glaurung_identity["tracked_dirty"] or axeyum_identity["tracked_dirty"]:
        raise RuntimeError("tracked source changes make the measurement inadmissible")

    common_environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
        "IOCTLANCE_DEADLINE_SECS": str(args.deadline_secs),
        "IOCTLANCE_SOLVE_BUDGET": str(args.solve_budget),
        "IOCTLANCE_SOLVE_SECS": str(args.solve_secs),
    }
    policy_configuration = resolve_policy_configuration(
        args.concretization_policy, args.canonical_model_choice
    )
    required_canonical_model_policy = policy_configuration["policy_id"]
    common_environment.update(policy_configuration["environment"])
    if args.check_timeout_ms is not None:
        common_environment["GLAURUNG_CHECK_TIMEOUT_MS"] = str(args.check_timeout_ms)
    if args.max_analyzed_functions is not None:
        common_environment["IOCTLANCE_MAX_ANALYZED_FUNCTIONS"] = str(
            args.max_analyzed_functions
        )
    driver_reports = []
    failures: list[str] = []
    for driver in drivers:
        runs = []
        for repetition in range(1, args.repetitions + 1):
            order = ("z3", "axeyum") if repetition % 2 else ("axeyum", "z3")
            for position, backend in enumerate(order, start=1):
                try:
                    run = run_one(
                        repository,
                        z3_binary if backend == "z3" else axeyum_binary,
                        driver,
                        backend,
                        repetition,
                        position,
                        common_environment,
                        args.process_timeout_secs,
                        args.max_analyzed_functions,
                        required_canonical_model_policy,
                        args.check_timeout_ms,
                        args.require_deterministic_worklists,
                    )
                except (RuntimeError, subprocess.TimeoutExpired) as error:
                    run = {
                        "backend": backend,
                        "repetition": repetition,
                        "position": position,
                        "run_error": str(error),
                    }
                runs.append(run)
        try:
            summary = summarize_driver(runs)
            summary_error = None
            failures.extend(
                finding_acceptance_failures(driver, summary, args.acceptance_population)
            )
        except RuntimeError as error:
            summary = None
            summary_error = str(error)
            failures.append(f"{driver}: {error}")
        driver_reports.append(
            {
                "driver": {"path": str(driver), "sha256": file_sha256(driver)},
                "runs": runs,
                "summary": summary,
                "summary_error": summary_error,
            }
        )

    post_run_glaurung_identity = git_identity(repository)
    post_run_axeyum_identity = git_identity(axeyum_repository)
    source_identity_stable = (
        glaurung_identity == post_run_glaurung_identity
        and axeyum_identity == post_run_axeyum_identity
    )
    if not source_identity_stable:
        failures.append("source identity changed during measurement")

    report = {
        "schema": (
            AUTHORITY_SCHEMA_V6
            if args.require_deterministic_worklists
            else AUTHORITY_SCHEMA_V5
        ),
        "accepted": not failures,
        "failures": failures,
        "glaurung": glaurung_identity,
        "axeyum": axeyum_identity,
        "post_run_source_identity": {
            "glaurung": post_run_glaurung_identity,
            "axeyum": post_run_axeyum_identity,
            "stable": source_identity_stable,
        },
        "binaries": {
            "z3": {"path": str(z3_binary), "sha256": file_sha256(z3_binary)},
            "axeyum": {
                "path": str(axeyum_binary),
                "sha256": file_sha256(axeyum_binary),
            },
        },
        "environment": common_environment,
        "process_timeout_seconds": args.process_timeout_secs,
        "canonical_model_choice_required": required_canonical_model_policy is not None,
        "canonical_model_choice_policy": required_canonical_model_policy,
        "concretization_policy_source": policy_configuration["source"],
        "concretization_policy_label": policy_configuration["label"],
        "concretization_policy_id": policy_configuration["policy_id"],
        "check_timeout_ms_required": args.check_timeout_ms,
        "deterministic_worklists_required": args.require_deterministic_worklists,
        "acceptance_population": args.acceptance_population,
        "repetitions": args.repetitions,
        "order": "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        "drivers": driver_reports,
        "all_drivers_exact_finding_parity": all(
            driver["summary"] is not None and driver["summary"]["exact_finding_parity"]
            for driver in driver_reports
        ),
        "all_drivers_exact_raw_finding_parity": all(
            driver["summary"] is not None
            and driver["summary"]["exact_raw_finding_parity"]
            for driver in driver_reports
        ),
        "all_drivers_exact_high_confidence_finding_parity": all(
            driver["summary"] is not None
            and driver["summary"]["exact_high_confidence_finding_parity"] is True
            for driver in driver_reports
        ),
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")
    if failures:
        raise SystemExit("; ".join(failures))


if __name__ == "__main__":
    main()
