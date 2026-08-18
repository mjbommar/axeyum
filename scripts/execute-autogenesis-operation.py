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
import tempfile
from collections.abc import Callable
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FRONTIER_SCRIPT = ROOT / "scripts/fact-frontier.py"
REGISTRY_SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
INDUCTION_PROPOSER = ROOT / "scripts/autogenesis-induction-proposer.py"
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
    facts: dict[str, dict[str, Any]] | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    frontier_module = load_module("autogenesis_frontier_for_execution", FRONTIER_SCRIPT)
    registry_module = load_module("autogenesis_registry_for_execution", REGISTRY_SCRIPT)
    if facts is None:
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


def run_smt_registered(operation: dict[str, Any]) -> dict[str, Any]:
    executor = operation["executor"]
    if executor["driver"] != "axeyum-bench/smtcomp-evidence-v1":
        raise ExecutionError(f"unsupported execution driver {executor['driver']!r}")
    artifact = executor["input_artifact"]
    if os.environ.get("AXEYUM_SMTCOMP_CLI"):
        raise ExecutionError(
            "authoritative execution forbids the AXEYUM_SMTCOMP_CLI override"
        )
    command = [
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


def formal_type(fact: dict[str, Any]) -> str:
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or " : " not in statement:
        raise ExecutionError("kernel operation fact has no theorem type")
    return statement.split(" : ", 1)[1]


def parse_kernel_evidence(raw: str) -> dict[str, str]:
    lines = raw.splitlines()
    if not lines or lines[0] != "AXEYUM_AUTOGENESIS_KERNEL_EVIDENCE_V1":
        raise ExecutionError("kernel executor evidence has the wrong kind")
    fields: dict[str, str] = {}
    for line in lines[1:]:
        key, separator, value = line.partition("\t")
        if not separator or not key or key in fields:
            raise ExecutionError("kernel executor evidence fields are malformed")
        fields[key] = value
    required = {
        "candidate",
        "canonical_type",
        "bundle_sha256",
        "catalog_sha256",
        "attempted",
        "budget",
        "accepted_plan_rank",
        "axiom_footprint",
        "retained_answer_dependencies",
    }
    if set(fields) != required:
        raise ExecutionError("kernel executor evidence fields differ from v1")
    return fields


def run_kernel_registered(operation: dict[str, Any]) -> dict[str, Any]:
    executor = operation["executor"]
    frontier_module = load_module("frontier_for_kernel_execution", FRONTIER_SCRIPT)
    fact = frontier_module.load().get(executor["input_fact_id"])
    if not isinstance(fact, dict):
        raise ExecutionError("kernel executor input fact is absent")
    statement = (fact.get("formal") or {}).get("statement")
    if (
        not isinstance(statement, str)
        or not statement.startswith(f"theorem {executor['target_theorem']} : ")
    ):
        raise ExecutionError("kernel executor target theorem differs from formal.statement")
    target_type = formal_type(fact)
    arity = len((fact.get("formal") or {}).get("free_symbols") or [])
    if arity < 1:
        raise ExecutionError("kernel executor target has no formal binder")
    candidate = f"Autogenesis.Authoritative.E{digest(fact)[:16]}.premise"
    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-authoritative-kernel-goal-catalog",
        "phase": "pre_b",
        "proof_bodies_included": False,
        "denied_theorems": executor["denied_theorems"],
        "target": {
            "name": candidate,
            "arity": arity,
            "canonical_type": target_type,
            "source_fact_id": fact["id"],
        },
    }
    catalog["catalog_sha256"] = digest(catalog)
    proposer = load_module("induction_proposer_for_kernel_execution", INDUCTION_PROPOSER)
    try:
        bundle = proposer.build_bundle(catalog)
        projection = proposer.render_tsv(bundle)
    except (KeyError, TypeError, ValueError) as error:
        raise ExecutionError(f"kernel proposal construction failed: {error}") from error
    with tempfile.TemporaryDirectory(prefix="axeyum-authoritative-kernel-") as temporary:
        temporary_root = pathlib.Path(temporary)
        plans = temporary_root / "plans.tsv"
        evidence = temporary_root / "evidence.tsv"
        plans.write_text(projection)
        if os.environ.get("AXEYUM_AUTOGENESIS_INDUCTION_CHECK"):
            raise ExecutionError(
                "authoritative execution forbids the "
                "AXEYUM_AUTOGENESIS_INDUCTION_CHECK override"
            )
        command = [
            "cargo",
            "run",
            "-q",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "autogenesis_induction_plan_check",
            "--",
        ]
        command.extend(
            [
                "--plans",
                str(plans),
                "--candidate",
                candidate,
                "--budget",
                str(executor["budget"]),
                "--expect",
                "proved",
                "--bundle-sha256",
                bundle["bundle_sha256"],
                "--catalog-sha256",
                catalog["catalog_sha256"],
                "--evidence-output",
                str(evidence),
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
            raise ExecutionError("kernel registered operation exceeded its timeout") from error
        if completed.returncode != 0 or not evidence.is_file():
            diagnostic = completed.stderr.strip().splitlines()
            suffix = diagnostic[-1] if diagnostic else "no diagnostic"
            raise ExecutionError(
                f"kernel registered executor exited {completed.returncode}: {suffix}"
            )
        fields = parse_kernel_evidence(evidence.read_text())
    if (
        fields["candidate"] != candidate
        or fields["canonical_type"] != target_type
        or fields["bundle_sha256"] != bundle["bundle_sha256"]
        or fields["catalog_sha256"] != catalog["catalog_sha256"]
        or fields["budget"] != str(executor["budget"])
        or fields["axiom_footprint"] != ""
        or fields["retained_answer_dependencies"] != ""
    ):
        raise ExecutionError("kernel registered evidence differs from the typed request")
    try:
        attempted = int(fields["attempted"])
        accepted_rank = int(fields["accepted_plan_rank"])
    except ValueError as error:
        raise ExecutionError("kernel registered evidence counters are invalid") from error
    return {
        "verdict": "proved",
        "evidence_label": executor["expected_evidence_label"],
        "canonical_type": target_type,
        "axiom_footprint": [],
        "retained_answer_dependencies": [],
        "attempted": attempted,
        "accepted_plan_rank": accepted_rank,
    }


def run_registered(operation: dict[str, Any]) -> dict[str, Any]:
    driver = operation["executor"]["driver"]
    if driver == "axeyum-bench/smtcomp-evidence-v1":
        return run_smt_registered(operation)
    if driver == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        return run_kernel_registered(operation)
    raise ExecutionError(f"unsupported execution driver {driver!r}")


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
    if executor["driver"] == "axeyum-bench/smtcomp-evidence-v1":
        expected_observation = {
            "verdict": "unsat",
            "evidence_label": executor["expected_evidence_label"],
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }
        input_identity = {
            "input_artifact_sha256": byte_digest(
                (ROOT / executor["input_artifact"]).read_bytes()
            )
        }
        request_input = {"input_artifact": executor["input_artifact"]}
    elif executor["driver"] == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        expected_observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "canonical_type": formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "attempted": executor["budget"],
            "accepted_plan_rank": executor["budget"],
        }
        input_identity = {
            "formal_statement_sha256": byte_digest(
                fact["formal"]["statement"].encode()
            )
        }
        request_input = {
            "target_theorem": executor["target_theorem"],
            "denied_theorems": executor["denied_theorems"],
            "budget": executor["budget"],
        }
    else:
        raise ExecutionError(f"unsupported execution driver {executor['driver']!r}")
    if observation != expected_observation:
        raise ExecutionError(
            "registered operation observation is not the required source-bound "
            f"result: observed={observation!r}"
        )
    identity_base = {
        "git_commit": git_commit,
        "frontier_sha256": frontier["frontier_sha256"],
        "operation_registry_sha256": digest(registry),
        "fact_id": fact["id"],
        "fact_sha256": digest(fact),
        "operation_id": operation["id"],
        **input_identity,
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
            **request_input,
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
