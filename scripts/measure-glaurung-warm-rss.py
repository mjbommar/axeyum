#!/usr/bin/env python3
"""Measure exact-stream Glaurung one-shot versus bounded warm Axeyum."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import statistics
import subprocess
from pathlib import Path
from typing import Any


TIME_PREFIX = "__AXEYUM_TIME__"
SHADOW_RE = re.compile(
    r"\[shadow-diff\] queries=(\d+) agree=(\d+) disagree=(\d+) \| "
    r"SAME-STREAM z3=([0-9.]+)ms axeyum=([0-9.]+)ms speedup=([0-9.]+)x"
)
MODEL_RE = re.compile(
    r"\[model-choice\] both-sat=(\d+) different-model=(\d+) \| "
    r"z3-unknown=(\d+) axeyum-unknown=(\d+) unknown-split=(\d+)"
)
SYMBOLIC_RE = re.compile(
    r"\[symbolic\] \S+\s+raw=(\d+) high-confidence=(\d+) suppressed=(\d+).*"
    r"analyzed=(\d+)/(\d+)"
)
TIME_RE = re.compile(
    rf"{TIME_PREFIX} elapsed_seconds=([0-9.]+) max_rss_kib=(\d+) exit=(\d+)"
)


def parse_key_values(line: str) -> dict[str, int | str]:
    values: dict[str, int | str] = {}
    for key, value in re.findall(r"([a-z][a-z0-9-]*)=([^ ]+)", line):
        values[key] = int(value) if value.isdecimal() else value
    return values


def require_match(pattern: re.Pattern[str], text: str, label: str) -> re.Match[str]:
    match = pattern.search(text)
    if match is None:
        raise RuntimeError(f"missing {label} row")
    return match


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


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_one(
    repository: Path,
    binary: Path,
    driver: Path,
    policy: str,
    repetition: int,
    position: int,
    common_environment: dict[str, str],
) -> dict[str, Any]:
    environment = os.environ.copy()
    for inherited in (
        "GLAURUNG_FAIR_SHADOW",
        "GLAURUNG_AXEYUM_PROFILE_DIR",
        "GLAURUNG_ORDERED_TRACE_DIR",
    ):
        environment.pop(inherited, None)
    environment.update(common_environment)
    environment["GLAURUNG_AXEYUM_WARM_REUSE"] = policy

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
    combined = result.stdout + "\n" + result.stderr
    if result.returncode != 0:
        raise RuntimeError(
            f"{policy} repetition {repetition} exited {result.returncode}:\n"
            + "\n".join(combined.splitlines()[-30:])
        )

    shadow = require_match(SHADOW_RE, combined, "shadow-diff")
    model = require_match(MODEL_RE, combined, "model-choice")
    symbolic = require_match(SYMBOLIC_RE, combined, "symbolic")
    timing = require_match(TIME_RE, combined, "time")
    run: dict[str, Any] = {
        "policy": policy,
        "repetition": repetition,
        "position": position,
        "queries": int(shadow.group(1)),
        "agree": int(shadow.group(2)),
        "disagree": int(shadow.group(3)),
        "z3_ms": float(shadow.group(4)),
        "axeyum_ms": float(shadow.group(5)),
        "reported_z3_over_axeyum": float(shadow.group(6)),
        "both_sat": int(model.group(1)),
        "different_model": int(model.group(2)),
        "z3_unknown": int(model.group(3)),
        "axeyum_unknown": int(model.group(4)),
        "unknown_split": int(model.group(5)),
        "findings": {
            "raw": int(symbolic.group(1)),
            "high_confidence": int(symbolic.group(2)),
            "suppressed": int(symbolic.group(3)),
            "analyzed": int(symbolic.group(4)),
            "analysis_roots": int(symbolic.group(5)),
        },
        "elapsed_seconds": float(timing.group(1)),
        "max_rss_kib": int(timing.group(2)),
        "time_exit": int(timing.group(3)),
    }

    if policy != "off":
        rows: dict[str, dict[str, int | str]] = {}
        for prefix, key in (
            ("[axeyum-warm]", "warm"),
            ("[axeyum-sat-cache]", "sat_cache"),
            ("[axeyum-serial-owner]", "serial_owner"),
        ):
            line = next((row for row in combined.splitlines() if row.startswith(prefix)), None)
            if line is None:
                raise RuntimeError(f"missing {prefix} row")
            rows[key] = parse_key_values(line)
        run.update(rows)
    return run


def sample_cv(values: list[float]) -> float:
    return statistics.stdev(values) / statistics.mean(values) if len(values) > 1 else 0.0


def summarize(runs: list[dict[str, Any]]) -> dict[str, Any]:
    by_policy = {policy: [run for run in runs if run["policy"] == policy] for policy in ("off", "adaptive")}
    for policy, population in by_policy.items():
        if len(population) * 2 != len(runs):
            raise RuntimeError(f"unbalanced {policy} population")

    expected_queries = runs[0]["queries"]
    expected_findings = runs[0]["findings"]
    for run in runs:
        if run["queries"] != expected_queries or run["agree"] != expected_queries:
            raise RuntimeError("query/agreement population drift")
        if run["disagree"] or run["unknown_split"] or run["time_exit"]:
            raise RuntimeError("decision or process failure")
        if run["findings"] != expected_findings:
            raise RuntimeError("finding-summary drift")

    for run in by_policy["adaptive"]:
        warm = run["warm"]
        cache = run["sat_cache"]
        serial = run["serial_owner"]
        if (
            warm.get("checks") != expected_queries
            or warm.get("resets") != 0
            or warm.get("paths-live") != 0
            or warm.get("path-cap-fallbacks") != 0
            or warm.get("assertion-cap-fallbacks") != 0
            or cache.get("replay-failures") != 0
            or cache.get("entries") != 0
            or serial.get("tracked-owners") != 0
            or serial.get("references") != 0
        ):
            raise RuntimeError("warm lifecycle, fallback, or replay gate failed")

    policy_summary: dict[str, Any] = {}
    for policy, population in by_policy.items():
        axeyum = [run["axeyum_ms"] for run in population]
        z3 = [run["z3_ms"] for run in population]
        rss = [run["max_rss_kib"] for run in population]
        elapsed = [run["elapsed_seconds"] for run in population]
        policy_summary[policy] = {
            "axeyum_ms": axeyum,
            "axeyum_median_ms": statistics.median(axeyum),
            "axeyum_sample_cv_percent": sample_cv(axeyum) * 100,
            "z3_ms": z3,
            "z3_median_ms": statistics.median(z3),
            "max_rss_kib": rss,
            "max_rss_median_kib": statistics.median(rss),
            "max_rss_sample_cv_percent": sample_cv([float(value) for value in rss]) * 100,
            "elapsed_seconds": elapsed,
            "elapsed_median_seconds": statistics.median(elapsed),
        }

    paired_time = []
    paired_rss = []
    for repetition in sorted({run["repetition"] for run in runs}):
        cold = next(run for run in by_policy["off"] if run["repetition"] == repetition)
        warm = next(run for run in by_policy["adaptive"] if run["repetition"] == repetition)
        paired_time.append(cold["axeyum_ms"] / warm["axeyum_ms"])
        paired_rss.append(warm["max_rss_kib"] / cold["max_rss_kib"])

    representative = by_policy["adaptive"][0]
    warm_checks = int(representative["warm"]["checks"])
    created = int(representative["warm"]["paths-created"])
    cache_hits = int(representative["sat_cache"]["hits"])
    return {
        "fixed_work_queries": expected_queries,
        "findings": expected_findings,
        "policies": policy_summary,
        "paired": {
            "cold_over_warm_axeyum": paired_time,
            "cold_over_warm_axeyum_geomean": math.exp(
                statistics.mean([math.log(value) for value in paired_time])
            ),
            "warm_over_cold_rss": paired_rss,
            "warm_over_cold_rss_median": statistics.median(paired_rss),
            "warm_rss_delta_percent_median": (statistics.median(paired_rss) - 1) * 100,
        },
        "warm_execution": {
            "checks": warm_checks,
            "owner_created_checks": created,
            "owner_retained_checks": warm_checks - created,
            "owner_retained_percent": (warm_checks - created) * 100 / warm_checks,
            "replay_cache_hits": cache_hits,
            "solver_core_calls": warm_checks - cache_hits,
            "fallbacks": 0,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--glaurung-repo", type=Path, required=True)
    parser.add_argument("--driver", type=Path, required=True)
    parser.add_argument("--binary", type=Path, default=Path("target/release/examples/ioctlance"))
    parser.add_argument("--repetitions", type=int, default=5)
    args = parser.parse_args()
    if args.repetitions < 2:
        parser.error("--repetitions must be at least 2")

    repository = args.glaurung_repo.resolve()
    binary = (repository / args.binary).resolve() if not args.binary.is_absolute() else args.binary.resolve()
    driver = (repository / args.driver).resolve() if not args.driver.is_absolute() else args.driver.resolve()
    axeyum_repository = Path(__file__).resolve().parents[1]
    for path, label in ((repository, "Glaurung repository"), (binary, "binary"), (driver, "driver")):
        if not path.exists():
            parser.error(f"{label} does not exist: {path}")

    common_environment = {
        "GLAURUNG_SHADOW_DIFF": "1",
        "GLAURUNG_AXEYUM_DIRECT_DELTA": "1",
        "GLAURUNG_AXEYUM_WARM_SERIAL_SIBLING_REUSE": "1",
        "GLAURUNG_AXEYUM_WARM_OWNER_TRANSFER": "0",
        "GLAURUNG_AXEYUM_WARM_TIMEOUT_COLD_RETRY": "0",
        "GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE": "0",
        "GLAURUNG_AXEYUM_REPLAY_SAT_CACHE": "1",
        "GLAURUNG_AXEYUM_WARM_MAX_LIVE_PATHS": "9",
        "GLAURUNG_AXEYUM_WARM_MAX_ASSERTIONS_PER_PATH": "512",
        "IOCTLANCE_DEADLINE_SECS": "300",
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "100000",
        "IOCTLANCE_SOLVE_BUDGET": "20000",
        "IOCTLANCE_SOLVE_SECS": "60",
    }

    runs = []
    for repetition in range(1, args.repetitions + 1):
        order = ("off", "adaptive") if repetition % 2 else ("adaptive", "off")
        for position, policy in enumerate(order, start=1):
            runs.append(
                run_one(
                    repository,
                    binary,
                    driver,
                    policy,
                    repetition,
                    position,
                    common_environment,
                )
            )

    report = {
        "schema": "axeyum.glaurung-warm-rss-control.v1",
        "glaurung": git_identity(repository),
        "axeyum": git_identity(axeyum_repository),
        "binary": {"path": str(binary), "sha256": file_sha256(binary)},
        "driver": {"path": str(driver), "sha256": file_sha256(driver)},
        "environment": common_environment,
        "repetitions": args.repetitions,
        "order": "odd repetitions off/adaptive; even repetitions adaptive/off",
        "runs": runs,
        "summary": summarize(runs),
    }
    if report["glaurung"]["tracked_dirty"] or report["axeyum"]["tracked_dirty"]:
        raise RuntimeError("tracked source changes make the measurement inadmissible")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
