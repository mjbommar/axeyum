#!/usr/bin/env python3
"""Execute and replay one machine-selected authoritative Autogenesis operation.

The frontier chooses the fact; the operation registry chooses the executable,
input artifact, budget, and expected evidence label. Callers supply none of
those fields. The normalized receipt binds the clean Git commit, frontier,
registry, fact, input bytes, and independently rechecked evidence observation.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import subprocess
import sys
from collections.abc import Callable
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FRONTIER_SCRIPT = ROOT / "scripts/fact-frontier.py"
REGISTRY_SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
EVIDENCE_RE = re.compile(
    r"^;\s*evidence\s+kind=(\S+)\s+certified=(\S+)\s+"
    r"recheck=(\S+)\s+arena=(\S+)\s+ms=(\d+)\s*$",
    re.MULTILINE,
)


class ExecutionError(RuntimeError):
    """Selection, execution, or receipt replay was not exact and admissible."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ExecutionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def clean_commit() -> str:
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    if status:
        raise ExecutionError("authoritative execution requires a clean checkout")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if not COMMIT_RE.fullmatch(commit):
        raise ExecutionError("checkout HEAD is not a full Git commit identity")
    return commit


def selected_inputs(
    frontier: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    frontier_module = load_module("autogenesis_frontier_for_execution", FRONTIER_SCRIPT)
    registry_module = load_module("autogenesis_registry_for_execution", REGISTRY_SCRIPT)
    facts = frontier_module.load()
    try:
        frontier_module.verify_machine_frontier(frontier, facts)
        registry = registry_module.load_registry(
            ROOT / "artifacts/autogenesis/operations.json", ROOT
        )
    except (frontier_module.FrontierError, registry_module.RegistryError) as error:
        raise ExecutionError(f"frontier or operation registry is invalid: {error}") from error

    selected = (frontier.get("selection") or {}).get("selected_fact_id")
    admissible = (frontier.get("selection") or {}).get("admissible_fact_ids")
    if not isinstance(selected, str) or admissible != [selected]:
        raise ExecutionError("executor requires exactly one admissible selected fact")
    fact = facts.get(selected)
    if not isinstance(fact, dict):
        raise ExecutionError("selected fact is absent from the authoritative ledger")
    matches = [
        operation
        for operation in registry["operations"]
        if operation["scope"] == "authoritative"
        and selected in operation["applicability"]["fact_ids"]
        and fact["formal"]["language"]
        in operation["applicability"]["formal_languages"]
        and fact["formal"]["fragment"] in operation["applicability"]["fragments"]
    ]
    if len(matches) != 1:
        raise ExecutionError(
            f"selected fact has {len(matches)} exact authoritative operations; expected one"
        )
    operation = matches[0]
    entry = next(
        (row for row in frontier["entries"] if row.get("fact_id") == selected), None
    )
    if not isinstance(entry, dict) or entry.get("registered_operation_ids") != [
        operation["id"]
    ]:
        raise ExecutionError("frontier selection does not bind the exact operation")
    return fact, operation, registry


def parse_observation(stdout: str) -> dict[str, Any]:
    matches = list(EVIDENCE_RE.finditer(stdout))
    if len(matches) != 1:
        raise ExecutionError(
            f"executor expected exactly one evidence line, observed {len(matches)}"
        )
    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if not lines:
        raise ExecutionError("executor produced no verdict")
    match = matches[0]
    return {
        "verdict": lines[-1],
        "evidence_label": match.group(1),
        "certified": match.group(2) == "1",
        "recheck": match.group(3),
        "arena": match.group(4),
    }


def run_registered(operation: dict[str, Any]) -> dict[str, Any]:
    executor = operation["executor"]
    if executor["driver"] != "axeyum-bench/smtcomp-evidence-v1":
        raise ExecutionError(f"unsupported execution driver {executor['driver']!r}")
    artifact = executor["input_artifact"]
    override = os.environ.get("AXEYUM_SMTCOMP_CLI")
    command = (
        [override, "--evidence", artifact]
        if override
        else [
            "cargo",
            "run",
            "--release",
            "-q",
            "-p",
            "axeyum-bench",
            "--example",
            "smtcomp_cli",
            "--",
            "--evidence",
            artifact,
        ]
    )
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=executor["timeout_seconds"],
        )
    except subprocess.TimeoutExpired as error:
        raise ExecutionError(
            f"registered operation exceeded {executor['timeout_seconds']} seconds"
        ) from error
    if completed.returncode != 0:
        diagnostic = completed.stderr.strip().splitlines()
        suffix = diagnostic[-1] if diagnostic else "no diagnostic"
        raise ExecutionError(
            f"registered executor exited {completed.returncode}: {suffix}"
        )
    return parse_observation(completed.stdout)


def build_receipt(
    *,
    frontier: dict[str, Any],
    fact: dict[str, Any],
    operation: dict[str, Any],
    registry: dict[str, Any],
    git_commit: str,
    observation: dict[str, Any],
) -> dict[str, Any]:
    if not COMMIT_RE.fullmatch(git_commit):
        raise ExecutionError("execution commit is not a full Git identity")
    executor = operation["executor"]
    expected_observation = {
        "verdict": "unsat",
        "evidence_label": executor["expected_evidence_label"],
        "certified": True,
        "recheck": "na",
        "arena": "ok",
    }
    if observation != expected_observation:
        raise ExecutionError(
            "registered operation observation is not the required certified "
            f"source-bound refutation: observed={observation!r}"
        )
    artifact = ROOT / executor["input_artifact"]
    identity_base = {
        "git_commit": git_commit,
        "frontier_sha256": frontier["frontier_sha256"],
        "operation_registry_sha256": digest(registry),
        "fact_id": fact["id"],
        "fact_sha256": digest(fact),
        "operation_id": operation["id"],
        "input_artifact_sha256": byte_digest(artifact.read_bytes()),
    }
    identity = dict(identity_base)
    identity["execution_id"] = digest(identity_base)
    receipt: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-operation-execution",
        "identity": identity,
        "request": {
            "driver": executor["driver"],
            "implementation": executor["implementation"],
            "input_fact_id": executor["input_fact_id"],
            "input_artifact": executor["input_artifact"],
            "timeout_seconds": executor["timeout_seconds"],
        },
        "result": {
            "outcome": "proved",
            "epistemic_status": operation["admission"]["epistemic_status"],
            "proof_route": operation["admission"]["proof_route"],
            "evidence_kind": operation["admission"]["evidence_kind"],
            "axiom_footprint_policy": operation["admission"][
                "axiom_footprint_policy"
            ],
            "axiom_footprint": operation["admission"]["axiom_footprint"],
            "observation": observation,
        },
        "acceptance": {
            "source_bound": True,
            "fresh_arena_rechecked": True,
            "caller_authored_command": False,
        },
    }
    receipt["execution_sha256"] = digest(receipt)
    return receipt


def derive(
    frontier_path: pathlib.Path,
    runner: Callable[[dict[str, Any]], dict[str, Any]] = run_registered,
) -> dict[str, Any]:
    frontier = json.loads(frontier_path.read_text())
    fact, operation, registry = selected_inputs(frontier)
    commit = clean_commit()
    observation = runner(operation)
    return build_receipt(
        frontier=frontier,
        fact=fact,
        operation=operation,
        registry=registry,
        git_commit=commit,
        observation=observation,
    )


def verify_receipt(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("execution_sha256")
    unsigned = dict(actual)
    unsigned.pop("execution_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ExecutionError("execution receipt digest is missing or invalid")
    if actual != expected:
        raise ExecutionError("execution receipt is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", required=True, type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(args.frontier.resolve())
        if args.verify is not None:
            verify_receipt(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_OPERATION_EXECUTION_OK|{expected['execution_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise ExecutionError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(
                f"AUTOGENESIS_OPERATION_EXECUTION|{expected['execution_sha256']}|"
                f"fact={expected['identity']['fact_id']}|"
                f"operation={expected['identity']['operation_id']}|{output}"
            )
        return 0
    except (
        OSError,
        subprocess.SubprocessError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ExecutionError,
    ) as error:
        print(f"AUTOGENESIS_OPERATION_EXECUTION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
