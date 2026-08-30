#!/usr/bin/env python3
"""Verify the one-shot Nat.fib iterator-recurrence negative result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-fib-iterate-recurrence-result-v1.json"
MANIFEST_V2 = ROOT / "artifacts/autogenesis/mathlib-nat-fib-iterate-recurrence-result-v2.json"
EXPECTED_RESULT = {
    "target": "Nat.fib_add_two",
    "fact_id": "F:ml430-nat-fib-add-two-b86e0c82",
    "operation": "bounded-iterate-recurrence-v1",
    "helper_schema_kernel_accepted": True,
    "plan_templates_attempted": 2,
    "kernel_submissions_attempted": 2,
    "executor_invocations": 1,
    "producer_retries": 0,
    "kernel_accepted": False,
    "failure_boundary": "recurrence equality-elimination composition",
    "semantic_theorem_receipts_issued": 0,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}
EXPECTED_RESULT_V2 = {
    "target": "Nat.fib_add_two",
    "fact_id": "F:ml430-nat-fib-add-two-b86e0c82",
    "operation": "bounded-iterate-recurrence-v2",
    "preexecution_controls_passed": True,
    "plan_templates_attempted": 2,
    "kernel_submissions_attempted": 2,
    "executor_invocations": 1,
    "producer_retries": 0,
    "kernel_accepted": False,
    "failure_boundary": "target-specific projected-equality composition",
    "semantic_theorem_receipts_issued": 0,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}


class IterateRecurrenceResultError(RuntimeError):
    """The negative result changed, weakened, or claimed forbidden credit."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IterateRecurrenceResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def validate_observation(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise IterateRecurrenceResultError("inner observation identity changed")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-nat-fib-iterate-recurrence-control"
        or observation.get("state")
        != "producer-rejected-no-retry-evaluation-or-ledger-credit"
        or observation.get("policy_version") != "nat-fib-iterate-recurrence-v1"
    ):
        raise IterateRecurrenceResultError("observation contract changed")
    if observation.get("source") != {
        "artifact_file": "r080.ndjson",
        "stream_sha256": "00578e949d71154cf5d9e79005b2a1c8f7fe73d9885ae96b0dd5cb6744c30501",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "target_definition": "Axeyum.Autogenesis.Coverage.r080",
        "fact_id": "F:ml430-nat-fib-add-two-b86e0c82",
    }:
        raise IterateRecurrenceResultError("source identity changed")
    if observation.get("preflight") != {
        "helper_schema_sha256": "5707083f42c94cba87e5eba42e9a022829cbfff95c040ff68dce1554b934b1a4",
        "kernel_accepted": True,
        "target_submissions": 0,
        "target_outcomes": 0,
    }:
        raise IterateRecurrenceResultError("preflight boundary changed")
    if observation.get("execution") != {
        "operation": "bounded-iterate-recurrence-v1",
        "plan_templates_allowed": 2,
        "plan_templates_attempted": 2,
        "kernel_submissions_allowed": 2,
        "kernel_submissions_attempted": 2,
        "executor_invocations": 1,
        "producer_retries": 0,
        "kernel_accepted": False,
        "rejection": "TypeMismatch { expected: ExprId(171), got: ExprId(0) }",
        "failure_boundary": "recurrence equality-elimination composition",
    }:
        raise IterateRecurrenceResultError("negative execution result changed")
    if observation.get("authority") != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "semantic_theorem_receipts_issued": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise IterateRecurrenceResultError("observation authority changed")


def validate_observation_v2(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise IterateRecurrenceResultError("v2 inner observation identity changed")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-nat-fib-iterate-recurrence-control"
        or observation.get("state")
        != "producer-v2-rejected-no-retry-evaluation-or-ledger-credit"
        or observation.get("tooling_commit")
        != "1880e56dbe07c0eb1a8f430d4de983cf4212511a"
        or observation.get("policy_commit") != "1df0eaf8e"
        or observation.get("policy_version") != "nat-fib-iterate-recurrence-v2"
    ):
        raise IterateRecurrenceResultError("v2 observation contract changed")
    if observation.get("source") != {
        "artifact_file": "r080.ndjson",
        "stream_sha256": "00578e949d71154cf5d9e79005b2a1c8f7fe73d9885ae96b0dd5cb6744c30501",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "target_definition": "Axeyum.Autogenesis.Coverage.r080",
        "fact_id": "F:ml430-nat-fib-add-two-b86e0c82",
    }:
        raise IterateRecurrenceResultError("v2 source identity changed")
    if observation.get("preexecution_controls") != {
        "helper_schema_sha256": "5707083f42c94cba87e5eba42e9a022829cbfff95c040ff68dce1554b934b1a4",
        "eq_rec_type_sha256": "0103709339f24495981349289a7912aa10dc1bb7c2e1fe060566a654a7d9b177",
        "transitivity_declaration_sha256": "cc4b8c535ad43a4ff88462ce4a4800ae9b3e7bb29a08b2b894206798d0eae49e",
        "congruence_declaration_sha256": "fff923e8148cfd27c1bfb62f03c334e6d62998e613c2b4735494a84998df0b01",
        "target_submissions": 0,
        "target_outcomes": 0,
    }:
        raise IterateRecurrenceResultError("v2 preexecution controls changed")
    if observation.get("execution") != {
        "operation": "bounded-iterate-recurrence-v2",
        "plan_templates_allowed": 2,
        "plan_templates_attempted": 2,
        "kernel_submissions_allowed": 2,
        "kernel_submissions_attempted": 2,
        "executor_invocations": 1,
        "producer_retries": 0,
        "kernel_accepted": False,
        "rejection": "TypeMismatch { expected: ExprId(4557), got: ExprId(6266) }",
        "failure_boundary": "target-specific projected-equality composition",
    }:
        raise IterateRecurrenceResultError("v2 negative execution result changed")
    if observation.get("authority") != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "semantic_theorem_receipts_issued": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise IterateRecurrenceResultError("v2 observation authority changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-iterate-recurrence-result"
        or manifest.get("state")
        != "producer-rejected-no-retry-evaluation-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT
    ):
        raise IterateRecurrenceResultError("manifest contract changed")
    policy = manifest["frozen_policy"]
    if sha256(ROOT / policy["path"]) != policy["sha256"]:
        raise IterateRecurrenceResultError("frozen policy changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise IterateRecurrenceResultError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise IterateRecurrenceResultError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise IterateRecurrenceResultError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def validate_v2() -> dict[str, Any]:
    manifest = load(MANIFEST_V2)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-iterate-recurrence-result"
        or manifest.get("state")
        != "producer-v2-rejected-no-retry-evaluation-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT_V2
    ):
        raise IterateRecurrenceResultError("v2 manifest contract changed")
    policy = manifest["frozen_policy"]
    if sha256(ROOT / policy["path"]) != policy["sha256"]:
        raise IterateRecurrenceResultError("v2 frozen policy changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise IterateRecurrenceResultError("v2 tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise IterateRecurrenceResultError("v2 observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise IterateRecurrenceResultError("v2 semantic identity changed")
    validate_observation_v2(observation)
    return manifest


def main() -> int:
    try:
        validate()
        manifest = validate_v2()
        print(
            "AUTOGENESIS_NAT_FIB_ITERATE_RECURRENCE_RESULT_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "versions=2|target=Nat.fib_add_two|accepted=0|v2_invocations=1|retries=0|"
            "receipts=0|evaluation=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        IterateRecurrenceResultError,
    ) as error:
        print(f"autogenesis-nat-fib-iterate-recurrence-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
