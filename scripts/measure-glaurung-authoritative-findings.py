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
SYMBOLIC_RE = re.compile(
    r"\[symbolic\] \S+\s+raw=(\d+) high-confidence=(\d+) suppressed=(\d+).*"
    r"analyzed=(\d+)/(\d+)(.*)"
)
SOLVER_RE = re.compile(
    r"\[solver\] backend=(\S+) solves=(\d+) solver_time=([0-9.]+)ms "
    r"avg=([0-9.]+)us/solve"
)
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


def run_one(
    repository: Path,
    binary: Path,
    driver: Path,
    backend: str,
    repetition: int,
    position: int,
    common_environment: dict[str, str],
) -> dict[str, Any]:
    environment = os.environ.copy()
    for inherited in (
        "GLAURUNG_SHADOW_DIFF",
        "GLAURUNG_FAIR_SHADOW",
        "GLAURUNG_AXEYUM_PROFILE_DIR",
        "GLAURUNG_ORDERED_TRACE_DIR",
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
        timeout=600,
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
    if solver.group(1) != backend:
        raise RuntimeError(f"expected {backend} binary, observed {solver.group(1)}")
    if "DEADLINE-HIT" in symbolic.group(6) or "WORK-LIMIT-HIT" in symbolic.group(6):
        raise RuntimeError(f"{backend} repetition {repetition} hit a coverage bound")

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
        "analyzed": int(symbolic.group(4)),
        "analysis_roots": int(symbolic.group(5)),
        "solves": int(solver.group(2)),
        "solver_time_ms": float(solver.group(3)),
        "average_us_per_solve": float(solver.group(4)),
        "elapsed_seconds": float(timing.group(1)),
        "max_rss_kib": int(timing.group(2)),
        "time_exit": int(timing.group(3)),
    }
    if backend == "axeyum":
        for prefix, key in (
            ("[axeyum-warm]", "warm"),
            ("[axeyum-sat-cache]", "sat_cache"),
            ("[axeyum-serial-owner]", "serial_owner"),
        ):
            line = next((row for row in result.stderr.splitlines() if row.startswith(prefix)), None)
            if line is None:
                raise RuntimeError(f"missing {prefix} row")
            run[key] = parse_key_values(line)
    return run


def summarize_driver(runs: list[dict[str, Any]]) -> dict[str, Any]:
    populations = {
        backend: [run for run in runs if run["backend"] == backend]
        for backend in ("z3", "axeyum")
    }
    for backend, population in populations.items():
        hashes = {run["findings_sha256"] for run in population}
        if len(population) * 2 != len(runs) or len(hashes) != 1:
            raise RuntimeError(f"{backend} finding population is unbalanced or unstable")
        structural = {
            (run["finding_count"], run["analyzed"], run["analysis_roots"])
            for run in population
        }
        if len(structural) != 1 or any(run["time_exit"] for run in population):
            raise RuntimeError(f"{backend} work population drift")

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
    z3_set = set(z3_findings)
    axeyum_set = set(axeyum_findings)
    result: dict[str, Any] = {
        "exact_finding_parity": z3_findings == axeyum_findings,
        "intersection_count": len(z3_set & axeyum_set),
        "z3_only": sorted(z3_set - axeyum_set),
        "axeyum_only": sorted(axeyum_set - z3_set),
        "backends": {},
    }
    for backend, population in populations.items():
        result["backends"][backend] = {
            "finding_count": population[0]["finding_count"],
            "findings_sha256": population[0]["findings_sha256"],
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
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--glaurung-repo", type=Path, required=True)
    parser.add_argument("--z3-binary", type=Path, required=True)
    parser.add_argument("--axeyum-binary", type=Path, required=True)
    parser.add_argument("--driver", type=Path, action="append", required=True)
    parser.add_argument("--repetitions", type=int, default=3)
    args = parser.parse_args()
    if args.repetitions < 2:
        parser.error("--repetitions must be at least 2")

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

    common_environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_DEADLINE_SECS": "300",
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "100000",
        "IOCTLANCE_SOLVE_BUDGET": "20000",
        "IOCTLANCE_SOLVE_SECS": "60",
    }
    driver_reports = []
    for driver in drivers:
        runs = []
        for repetition in range(1, args.repetitions + 1):
            order = ("z3", "axeyum") if repetition % 2 else ("axeyum", "z3")
            for position, backend in enumerate(order, start=1):
                runs.append(
                    run_one(
                        repository,
                        z3_binary if backend == "z3" else axeyum_binary,
                        driver,
                        backend,
                        repetition,
                        position,
                        common_environment,
                    )
                )
        driver_reports.append(
            {
                "driver": {"path": str(driver), "sha256": file_sha256(driver)},
                "runs": runs,
                "summary": summarize_driver(runs),
            }
        )

    report = {
        "schema": "axeyum.glaurung-authoritative-finding-parity.v1",
        "glaurung": git_identity(repository),
        "axeyum": git_identity(axeyum_repository),
        "binaries": {
            "z3": {"path": str(z3_binary), "sha256": file_sha256(z3_binary)},
            "axeyum": {"path": str(axeyum_binary), "sha256": file_sha256(axeyum_binary)},
        },
        "environment": common_environment,
        "repetitions": args.repetitions,
        "order": "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        "drivers": driver_reports,
        "all_drivers_exact_finding_parity": all(
            driver["summary"]["exact_finding_parity"] for driver in driver_reports
        ),
    }
    if report["glaurung"]["tracked_dirty"] or report["axeyum"]["tracked_dirty"]:
        raise RuntimeError("tracked source changes make the measurement inadmissible")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
