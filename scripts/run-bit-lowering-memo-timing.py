#!/usr/bin/env python3
"""Run ADR-0300's fixed 12-process unprofiled timing schedule."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


SCHEDULE = ("B", "C", "C", "B", "B", "C", "C", "B", "B", "C", "C", "B")
BASELINE_SOURCE = "d13d1f92446e86113702a7cc27d3e1a5eb67c687"
CANDIDATE_SOURCE = "2c9209fe9c4442cf87b6c121a04997849c05930b"
BASELINE_BINARY_SHA256 = "65d819528f10645042103275e4c79904e47f377326dc9e1159f8c36d8795c515"
CANDIDATE_BINARY_SHA256 = "06d417ef0e0082be87c4a311b5bc92a3a669d5accde5dbd27a349f78f1c93377"
CORPUS = Path(
    "/nas4/data/workspace-infosec/glaurung-captures/"
    "2026-07-16-corrected-wide-v3/representative"
)
MANIFEST = CORPUS / "manifest-v1.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_output(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def validate_source(root: Path, expected_revision: str, label: str) -> None:
    if git_output(root, "rev-parse", "HEAD") != expected_revision:
        raise RuntimeError(f"{label} source revision drift")
    if git_output(root, "status", "--porcelain=v1", "--untracked-files=no"):
        raise RuntimeError(f"{label} tracked source is dirty")


def benchmark_args(artifact: Path) -> list[str]:
    return [
        str(CORPUS),
        "--corpus-manifest",
        str(MANIFEST),
        "--corpus-tier",
        "representative",
        "--backend",
        "sat-bv",
        "--rewrite",
        "off",
        "--compare-z3",
        "--require-in-process-z3",
        "--require-reproducible-run",
        "--require-deterministic-resources",
        "--timeout-ms",
        "10000",
        "--resource-limit",
        "2000000",
        "--node-budget",
        "300000",
        "--cnf-var-budget",
        "3000000",
        "--cnf-clause-budget",
        "8000000",
        "--jobs",
        "1",
        "--min-decided-percent",
        "100",
        "--logic",
        "QF_BV",
        "--out",
        str(artifact),
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-source", type=Path, required=True)
    parser.add_argument("--candidate-source", type=Path, required=True)
    parser.add_argument("--baseline-binary", type=Path, required=True)
    parser.add_argument("--candidate-binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    baseline_source = args.baseline_source.resolve()
    candidate_source = args.candidate_source.resolve()
    baseline_binary = args.baseline_binary.resolve()
    candidate_binary = args.candidate_binary.resolve()
    output = args.out.resolve()

    if output.exists():
        raise RuntimeError(f"refusing existing output directory: {output}")
    validate_source(baseline_source, BASELINE_SOURCE, "baseline")
    validate_source(candidate_source, CANDIDATE_SOURCE, "candidate")
    if sha256(baseline_binary) != BASELINE_BINARY_SHA256:
        raise RuntimeError("baseline binary hash drift")
    if sha256(candidate_binary) != CANDIDATE_BINARY_SHA256:
        raise RuntimeError("candidate binary hash drift")

    output.mkdir(parents=True)
    runs: list[dict[str, Any]] = []
    for index, cell in enumerate(SCHEDULE, start=1):
        run_dir = output / f"run-{index:02d}-{cell}"
        run_dir.mkdir()
        artifact = run_dir / "artifact.json"
        timing = run_dir / "time.json"
        source = baseline_source if cell == "B" else candidate_source
        binary = baseline_binary if cell == "B" else candidate_binary
        command = [
            "/usr/bin/time",
            "-f",
            '{"elapsed_seconds": %e, "max_rss_kib": %M, "exit_status": %x}',
            "-o",
            str(timing),
            str(binary),
            *benchmark_args(artifact),
        ]
        result = subprocess.run(command, cwd=source, capture_output=True, text=True)
        (run_dir / "stdout.log").write_text(result.stdout, encoding="utf-8")
        (run_dir / "stderr.log").write_text(result.stderr, encoding="utf-8")
        if result.returncode != 0:
            raise RuntimeError(f"run {index} ({cell}) failed with {result.returncode}")
        if not artifact.is_file() or not timing.is_file():
            raise RuntimeError(f"run {index} ({cell}) did not produce complete artifacts")
        runs.append(
            {
                "index": index,
                "cell": cell,
                "artifact": str(artifact.relative_to(output)),
                "time": str(timing.relative_to(output)),
            }
        )

    manifest = {
        "schema": "axeyum.bit-lowering-memo-timing-run.v1",
        "schedule": list(SCHEDULE),
        "baseline_source": BASELINE_SOURCE,
        "candidate_source": CANDIDATE_SOURCE,
        "baseline_binary_sha256": BASELINE_BINARY_SHA256,
        "candidate_binary_sha256": CANDIDATE_BINARY_SHA256,
        "runs": runs,
    }
    (output / "run-manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
