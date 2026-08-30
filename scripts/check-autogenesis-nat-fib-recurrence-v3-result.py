#!/usr/bin/env python3
"""Verify the one-shot Nat.fib recurrence v3 candidate result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-fib-iterate-recurrence-result-v3.json"


class FibV3ResultError(RuntimeError):
    """The candidate result changed or claimed forbidden authority."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise FibV3ResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def validate_observation(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise FibV3ResultError("inner observation identity changed")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-nat-fib-iterate-recurrence-control"
        or observation.get("state")
        != "candidate-checked-no-receipt-evaluation-or-ledger-credit"
        or observation.get("policy_version") != "nat-fib-iterate-recurrence-v3"
    ):
        raise FibV3ResultError("observation contract changed")
    if observation.get("source") != {
        "artifact_file": "r080.ndjson",
        "fact_id": "F:ml430-nat-fib-add-two-b86e0c82",
        "goal_sha256": "5433b34c4a138d615c488e4c7dfbee5dac8dc253e14680e114f40a55cf5eb16d",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lean_version": "4.30.0",
        "stream_sha256": "00578e949d71154cf5d9e79005b2a1c8f7fe73d9885ae96b0dd5cb6744c30501",
        "target_definition": "Axeyum.Autogenesis.Coverage.r080",
    }:
        raise FibV3ResultError("source identity changed")
    if observation.get("search") != {
        "accepted_plan_rank": 2,
        "direct_normalization_rejection": "DeclarationValueMismatch { declared: ExprId(2816), inferred: ExprId(2842) }",
        "executor_invocations": 1,
        "helper_schema_sha256": "5707083f42c94cba87e5eba42e9a022829cbfff95c040ff68dce1554b934b1a4",
        "helper_schemas_constructed": 1,
        "kernel_submissions": 2,
        "operation": "bounded-iterate-recurrence-v3",
        "plan_templates": 2,
        "retries": 0,
    }:
        raise FibV3ResultError("search contract changed")
    if observation.get("candidate") != {
        "axiom_footprint": [],
        "kernel_accepted": True,
        "name": "Axeyum.Autogenesis.NatFibAddTwo",
        "proof_sha256": "b5965831fd4654e708b03bd3145f9124f02fc57aaa04bc16ded8287b6cee50f2",
        "source_target_dependency": False,
        "theorem_content_sha256": "ad53b80748ad1d3f0a0958277774e36a621ce25f5f1441b6882085349886537a",
        "theorem_dependencies": [],
    }:
        raise FibV3ResultError("candidate contract changed")
    if observation.get("authority") != {
        "evaluation_credit": 0,
        "held_out_inspected": False,
        "ledger_writes": 0,
        "partitions_inspected": ["train"],
        "proof_bodies_inspected": False,
        "semantic_theorem_receipts_issued": 0,
    }:
        raise FibV3ResultError("authority boundary changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("state")
        != "candidate-checked-no-receipt-evaluation-or-ledger-credit"
        or manifest.get("result", {}).get("kernel_accepted") is not True
        or manifest["result"].get("semantic_theorem_receipts_issued") != 0
        or manifest["result"].get("evaluation_credit") != 0
        or manifest["result"].get("ledger_writes") != 0
    ):
        raise FibV3ResultError("manifest authority changed")
    policy = manifest["frozen_policy"]
    if sha256(ROOT / policy["path"]) != policy["sha256"]:
        raise FibV3ResultError("frozen policy changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise FibV3ResultError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise FibV3ResultError("observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise FibV3ResultError("semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_NAT_FIB_RECURRENCE_V3_RESULT_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "accepted=1|axioms=0|theorem_dependencies=0|receipts=0|"
            "evaluation=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, FibV3ResultError) as error:
        print(f"autogenesis-nat-fib-recurrence-v3-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
