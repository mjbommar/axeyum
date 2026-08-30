#!/usr/bin/env python3
"""Verify the zero-execution rooted xgcd preflight decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/xgcd-val-rooted-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-rooted-reconstruction-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/9f135d4f0-xgcd-val-rooted-v1"
)
MANIFEST = PACK / "manifest.json"
PREFLIGHT = PACK / "preflight.json"
RESULT_SHA256 = "7b2255dc984e6415b04eb7b41624944c42e6b8275c4864947ee1c8d854f42212"
PLAN_SHA256 = "cc5b32ef86bc407cc3dd4772f0d1dc214cf4abcacc43b3846b2b731eb3c36327"
MANIFEST_SHA256 = "33ae1f917c4156741b408be52faeac070f99814db47275f2ca521b7ff665f788"


class XgcdValRootedResultError(RuntimeError):
    """The preflight baseline, zero-execution result, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValRootedResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise XgcdValRootedResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise XgcdValRootedResultError("measured rooted result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-xgcd-val-rooted-reconstruction-result"
        or result.get("state")
        != "preflight-declined-unbound-three-file-status-baseline-no-execution"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(PREFLIGHT.stat().st_mode) != 0o444
        or PREFLIGHT.stat().st_size != 1_556
        or sha256(PREFLIGHT)
        != "9243912e8beab1303a1a2d44b8eb75f290d65f1e9cd07006ebf8cf3781e7ccdf"
    ):
        raise XgcdValRootedResultError("result producer or pack changed")
    preflight = load(PREFLIGHT)
    projected = [
        {
            "path": row["path"],
            "bytes": row["bytes"],
            "mode": row["mode"],
            "sha256": row["sha256"],
        }
        for row in preflight["status_entries"]
    ]
    if (
        result.get("preexisting_status_baseline") != projected
        or any(row.get("status") != "untracked" for row in preflight["status_entries"])
        or len(preflight.get("planned_temporary_paths", [])) != 3
        or any(row.get("present") is not False for row in preflight["planned_temporary_paths"])
    ):
        raise XgcdValRootedResultError("preflight baseline changed")
    if result.get("outcome") != {
        "precondition_satisfied": False,
        "planned_temporary_paths_present": 0,
        "execution_started": False,
        "source_copied": False,
        "source_compiled": False,
        "exported": False,
        "kernel_imports": 0,
        "projection_equation_accepted": False,
        "decline_reason": "the plan required zero status entries but the full checkout status contained three preexisting untracked files",
    }:
        raise XgcdValRootedResultError("zero-execution outcome changed")
    if result.get("budget") != {
        "source_copies": 0,
        "source_compilations": 0,
        "exporter_invocations": 0,
        "importer_runs": 0,
        "proof_bearing_stream_reads": 0,
        "retries": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "checkout_files_removed": 0,
        "projection_equation_credit": 0,
        "extended_gcd_reconstructions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValRootedResultError("no-execution authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_ROOTED_RESULT_OK|preexisting=3|execution=0|"
            "files_removed=0|projection_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValRootedResultError,
    ) as error:
        print(f"autogenesis-xgcd-val-rooted-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
