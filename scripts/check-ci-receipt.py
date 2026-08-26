#!/usr/bin/env python3
"""Offline fail-closed validation for the latest provider-captured CI receipt."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "artifacts/runtime/ci-latest-v1.json"


def fail(message: str) -> None:
    raise SystemExit(f"ci-receipt: {message}")


def git(*arguments: str) -> bytes:
    completed = subprocess.run(["git", *arguments], cwd=ROOT, check=False, capture_output=True)
    if completed.returncode:
        fail(f"git {' '.join(arguments)} failed")
    return completed.stdout


def main() -> None:
    document = json.loads(RECEIPT.read_text())
    if (
        document.get("schema_version") != 1
        or document.get("kind") != "axeyum-github-actions-runtime-receipt"
    ):
        fail("schema identity changed")
    if document.get("state") != "provider-captured-no-transitive-current-head-claim":
        fail("receipt authority boundary changed")
    run = document.get("run", {})
    if run.get("name") != "CI" or run.get("path") != ".github/workflows/ci.yml":
        fail("receipt is not for the canonical CI workflow")
    if run.get("status") != "completed" or not run.get("conclusion"):
        fail("receipt run is incomplete")
    commit = run.get("head_sha")
    if not isinstance(commit, str) or len(commit) != 40:
        fail("tested commit is invalid")
    git("cat-file", "-e", f"{commit}^{{commit}}")
    completed = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=False
    )
    if completed.returncode:
        fail("tested commit is not an ancestor of the current checkout")
    workflow = git("show", f"{commit}:{run['path']}")
    if hashlib.sha256(workflow).hexdigest() != document.get("workflow_definition_sha256"):
        fail("tested workflow bytes disagree")
    jobs = document.get("jobs")
    if not isinstance(jobs, list) or not jobs:
        fail("receipt has no jobs")
    if len({job.get("id") for job in jobs}) != len(jobs):
        fail("job IDs are not unique")
    if any(job.get("status") != "completed" or not job.get("conclusion") for job in jobs):
        fail("receipt has incomplete jobs")
    conclusions = {
        conclusion: sum(job.get("conclusion") == conclusion for job in jobs)
        for conclusion in sorted({str(job.get("conclusion")) for job in jobs})
    }
    if document.get("census") != {"jobs": len(jobs), "conclusions": conclusions}:
        fail("job census disagrees")
    print(
        f"ci-receipt: ok (run {run['id']}, {run['conclusion']}, {len(jobs)} jobs, commit {commit[:12]})"
    )


if __name__ == "__main__":
    main()
