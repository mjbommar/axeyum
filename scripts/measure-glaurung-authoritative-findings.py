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
CHECK_TIMEOUT_RE = re.compile(r"\[solver\][^\n]* check_timeout_ms=(\d+)")
TIME_RE = re.compile(
    rf"{TIME_PREFIX} elapsed_seconds=([0-9.]+) max_rss_kib=(\d+) exit=(\d+)"
)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def text_sha256(lines: list[str]) -> str:
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


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
) -> dict[str, Any]:
    environment = os.environ.copy()
    for inherited in (
        "GLAURUNG_SHADOW_DIFF",
        "GLAURUNG_FAIR_SHADOW",
        "GLAURUNG_AXEYUM_PROFILE_DIR",
        "GLAURUNG_ORDERED_TRACE_DIR",
        "GLAURUNG_CANONICAL_MODEL_CHOICE",
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

    findings = [line for line in result.stdout.splitlines() if line]
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
        "reported_lines": int(symbolic.group(2)),
        "reported_suppressed": int(symbolic.group(3)),
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
    if canonical_model_choice is not None:
        run["canonical_model_choice"] = canonical_model_choice
    if check_timeout_ms is not None:
        run["check_timeout_ms"] = check_timeout_ms
    if backend == "axeyum":
        for prefix, key in (
            ("[axeyum-warm]", "warm"),
            ("[axeyum-sat-cache]", "sat_cache"),
            ("[axeyum-serial-owner]", "serial_owner"),
        ):
            line = next((row for row in result.stderr.splitlines() if row.startswith(prefix)), None)
            if line is not None:
                run[key] = parse_key_values(line)
    return run


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

    canonical_presence = {
        "canonical_model_choice" in run for run in runs
    }
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
        policies = {
            str(run["canonical_model_choice"]["policy"]) for run in runs
        }
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
            canonical_summary["backends"][backend] = dict(
                zip(canonical_keys, values)
            )

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

    z3_findings = populations["z3"][0]["findings"]
    axeyum_findings = populations["axeyum"][0]["findings"]
    stability: dict[str, dict[str, Any]] = {}
    for backend, population in populations.items():
        finding_sets = [set(run["findings"]) for run in population]
        if any(
            len(candidate) != len(run["findings"])
            for candidate, run in zip(finding_sets, population)
        ):
            raise RuntimeError(f"{backend} emitted duplicate finding rows")
        stable_findings = set.intersection(*finding_sets)
        union_findings = set.union(*finding_sets)
        hashes = sorted({run["findings_sha256"] for run in population})
        stability[backend] = {
            "output_stable": len(hashes) == 1,
            "distinct_hashes": hashes,
            "stable_finding_count": len(stable_findings),
            "union_finding_count": len(union_findings),
            "unstable_findings": sorted(union_findings - stable_findings),
            "stable_findings": stable_findings,
            "union_findings": union_findings,
        }
    z3_stable = stability["z3"]["stable_findings"]
    z3_union = stability["z3"]["union_findings"]
    axeyum_stable = stability["axeyum"]["stable_findings"]
    axeyum_union = stability["axeyum"]["union_findings"]
    both_stable = (
        stability["z3"]["output_stable"]
        and stability["axeyum"]["output_stable"]
    )
    result: dict[str, Any] = {
        "exact_finding_parity": both_stable and z3_findings == axeyum_findings,
        "within_backend_stable": both_stable,
        "stable_intersection_count": len(z3_stable & axeyum_stable),
        "z3_only": sorted(z3_stable - axeyum_union),
        "axeyum_only": sorted(axeyum_stable - z3_union),
        "stability": {},
        "coverage": {
            "analyzed": populations["z3"][0]["analyzed"],
            "reachable": populations["z3"][0]["analysis_roots"],
            "boundary": populations["z3"][0]["coverage_boundary"],
        },
        "backends": {},
        "canonical_model_choice": canonical_summary,
        "check_timeout_ms": check_timeout_ms,
    }
    for backend, population in populations.items():
        backend_stability = stability[backend]
        result["stability"][backend] = {
            key: value
            for key, value in backend_stability.items()
            if key not in ("stable_findings", "union_findings")
        }
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
            "findings_sha256_per_run": [
                run["findings_sha256"] for run in population
            ],
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


def finding_acceptance_failures(driver: Path, summary: dict[str, Any]) -> list[str]:
    if summary["exact_finding_parity"]:
        return []
    failures = []
    for backend in ("z3", "axeyum"):
        stability = summary["stability"][backend]
        if not stability["output_stable"]:
            failures.append(
                f"{driver}: {backend} finding output unstable "
                f"(distinct-hashes={len(stability['distinct_hashes'])}, "
                f"stable={stability['stable_finding_count']}, "
                f"union={stability['union_finding_count']})"
            )
    failures.append(
        f"{driver}: exact finding parity failed "
        f"(z3-only={len(summary['z3_only'])}, "
        f"axeyum-only={len(summary['axeyum_only'])})"
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
    parser.add_argument(
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
        "IOCTLANCE_DEADLINE_SECS": str(args.deadline_secs),
        "IOCTLANCE_SOLVE_BUDGET": str(args.solve_budget),
        "IOCTLANCE_SOLVE_SECS": str(args.solve_secs),
    }
    required_canonical_model_policy = (
        CANONICAL_MODEL_POLICIES[args.canonical_model_choice]
        if args.canonical_model_choice is not None
        else None
    )
    if args.canonical_model_choice is not None:
        common_environment["GLAURUNG_CANONICAL_MODEL_CHOICE"] = (
            args.canonical_model_choice
        )
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
            failures.extend(finding_acceptance_failures(driver, summary))
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
        "schema": "axeyum.glaurung-authoritative-finding-parity.v4",
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
            "axeyum": {"path": str(axeyum_binary), "sha256": file_sha256(axeyum_binary)},
        },
        "environment": common_environment,
        "process_timeout_seconds": args.process_timeout_secs,
        "canonical_model_choice_required": required_canonical_model_policy is not None,
        "canonical_model_choice_policy": required_canonical_model_policy,
        "check_timeout_ms_required": args.check_timeout_ms,
        "repetitions": args.repetitions,
        "order": "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        "drivers": driver_reports,
        "all_drivers_exact_finding_parity": all(
            driver["summary"] is not None
            and driver["summary"]["exact_finding_parity"]
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
