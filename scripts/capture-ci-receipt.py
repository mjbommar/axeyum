#!/usr/bin/env python3
"""Capture or online-verify a completed GitHub Actions CI receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "artifacts/runtime/ci-latest-v1.json"
REPOSITORY = "mjbommar/axeyum"


class ReceiptError(RuntimeError):
    """The provider response cannot support a runtime receipt."""


def command(*arguments: str) -> str:
    completed = subprocess.run(
        arguments,
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode:
        raise ReceiptError(
            f"command failed ({completed.returncode}): {' '.join(arguments)}: {completed.stderr.strip()}"
        )
    return completed.stdout


def api(path: str) -> dict[str, Any]:
    value = json.loads(command("gh", "api", path))
    if not isinstance(value, dict):
        raise ReceiptError(f"GitHub response for {path} is not an object")
    return value


def git_blob(commit: str, path: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=False,
        capture_output=True,
    )
    if completed.returncode:
        raise ReceiptError(f"cannot read {path} at tested commit {commit}")
    return completed.stdout


def build(run_id: int) -> dict[str, Any]:
    run = api(f"repos/{REPOSITORY}/actions/runs/{run_id}")
    jobs_response = api(f"repos/{REPOSITORY}/actions/runs/{run_id}/jobs?per_page=100")
    jobs = jobs_response.get("jobs")
    if run.get("status") != "completed" or run.get("conclusion") not in {
        "success",
        "failure",
        "cancelled",
        "timed_out",
        "action_required",
        "neutral",
        "skipped",
        "stale",
    }:
        raise ReceiptError(f"run {run_id} is not complete")
    if not isinstance(jobs, list) or not jobs:
        raise ReceiptError(f"run {run_id} has no jobs")
    if any(job.get("status") != "completed" or not job.get("conclusion") for job in jobs):
        raise ReceiptError(f"run {run_id} still has incomplete jobs")
    workflow_path = run.get("path")
    head_sha = run.get("head_sha")
    if not isinstance(workflow_path, str) or not isinstance(head_sha, str):
        raise ReceiptError("run lacks workflow path or head SHA")
    workflow_sha = hashlib.sha256(git_blob(head_sha, workflow_path)).hexdigest()
    selected_jobs = [
        {
            key: job.get(key)
            for key in (
                "id",
                "name",
                "status",
                "conclusion",
                "started_at",
                "completed_at",
                "html_url",
            )
        }
        for job in jobs
    ]
    selected_jobs.sort(key=lambda job: (str(job["name"]), int(job["id"])))
    return {
        "schema_version": 1,
        "kind": "axeyum-github-actions-runtime-receipt",
        "state": "provider-captured-no-transitive-current-head-claim",
        "authority": "Captured through GitHub's authenticated API. Offline checking binds the workflow bytes, tested commit, and completed job outcomes; --check-online replays the provider response.",
        "repository": REPOSITORY,
        "run": {
            key: run.get(key)
            for key in (
                "id",
                "name",
                "path",
                "event",
                "status",
                "conclusion",
                "head_sha",
                "head_branch",
                "run_attempt",
                "created_at",
                "updated_at",
                "html_url",
            )
        },
        "workflow_definition_sha256": workflow_sha,
        "jobs": selected_jobs,
        "census": {
            "jobs": len(selected_jobs),
            "conclusions": {
                conclusion: sum(job["conclusion"] == conclusion for job in selected_jobs)
                for conclusion in sorted({str(job["conclusion"]) for job in selected_jobs})
            },
        },
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run_id", type=int)
    parser.add_argument("--output", type=pathlib.Path, default=DEFAULT_OUT)
    parser.add_argument("--check-online", action="store_true")
    args = parser.parse_args(argv)
    try:
        document = build(args.run_id)
        rendered = (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()
        output = args.output if args.output.is_absolute() else ROOT / args.output
        if args.check_online:
            if not output.exists() or output.read_bytes() != rendered:
                raise ReceiptError(f"{output.relative_to(ROOT)} differs from live provider state")
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(rendered)
    except (OSError, ReceiptError, json.JSONDecodeError) as error:
        print(f"CI_RECEIPT_ERROR|{error}", file=sys.stderr)
        return 1
    print(
        f"CI_RECEIPT|run={document['run']['id']}|commit={document['run']['head_sha']}|"
        f"conclusion={document['run']['conclusion']}|jobs={document['census']['jobs']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
