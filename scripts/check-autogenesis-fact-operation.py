#!/usr/bin/env python3
"""Replay a settled fact's typed registered Autogenesis operation evidence."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from collections.abc import Callable
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
REGISTRY_SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
EXECUTOR_SCRIPT = ROOT / "scripts/execute-autogenesis-operation.py"


class FactOperationError(RuntimeError):
    """A fact's typed operation evidence is absent, stale, or failed replay."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise FactOperationError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def formal_type(fact: dict[str, Any]) -> str:
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or " : " not in statement:
        raise FactOperationError("kernel fact has no theorem type")
    return statement.split(" : ", 1)[1]


def checker_command(fact_id: str) -> str:
    path = f"artifacts/facts/{fact_id.replace('F:', 'F-')}.json"
    return f"python3 scripts/check-autogenesis-fact-operation.py --fact {path}"


def check_fact(
    fact: dict[str, Any],
    runner: Callable[..., dict[str, Any]],
) -> dict[str, Any]:
    registry_module = load_module("registry_for_fact_operation", REGISTRY_SCRIPT)
    try:
        registry = registry_module.load_registry(
            ROOT / "artifacts/autogenesis/operations.json", ROOT
        )
    except (OSError, json.JSONDecodeError, registry_module.RegistryError) as error:
        raise FactOperationError(f"operation registry is invalid: {error}") from error
    rows = [
        row
        for row in fact.get("evidence") or []
        if isinstance(row.get("checker_operation"), dict)
    ]
    if len(rows) != 1:
        raise FactOperationError(
            f"fact has {len(rows)} typed checker-operation rows; expected exactly one"
        )
    row = rows[0]
    binding = row["checker_operation"]
    operation_id = binding.get("id")
    matches = [
        operation
        for operation in registry["operations"]
        if operation["id"] == operation_id
        and operation["scope"] == "authoritative"
        and fact.get("id") in operation["applicability"]["fact_ids"]
    ]
    if len(matches) != 1:
        raise FactOperationError("fact does not have one matching authoritative operation")
    operation = matches[0]
    admission = operation["admission"]
    executor = operation["executor"]
    expected_binding: dict[str, Any] = {
        "id": operation["id"],
        "operation_sha256": digest(operation),
        "registry_sha256_at_execution": binding.get("registry_sha256_at_execution"),
        "execution_sha256": binding.get("execution_sha256"),
        "frontier_sha256": binding.get("frontier_sha256"),
    }
    if executor["driver"] == "axeyum-bench/smtcomp-evidence-v1":
        expected_binding.update(
            {
                "input_artifact": executor["input_artifact"],
                "input_artifact_sha256": byte_digest(
                    (ROOT / executor["input_artifact"]).read_bytes()
                ),
            }
        )
    elif executor["driver"] == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        expected_binding.update(
            {
                "target_theorem": executor["target_theorem"],
                "formal_statement_sha256": byte_digest(
                    fact["formal"]["statement"].encode()
                ),
                "budget": executor["budget"],
            }
        )
    elif executor["driver"] == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        trigger = binding.get("trigger")
        expected_trigger_keys = {
            "premise_fact_id",
            "premise_operation_id",
            "premise_source_commit",
            "premise_before_fact_sha256",
            "premise_after_fact_sha256",
            "premise_execution_sha256",
            "premise_transaction_sha256",
            "premise_admission_event_sha256",
            "readiness_delta_sha256",
            "frontier_after_sha256",
        }
        if (
            not isinstance(trigger, dict)
            or set(trigger) != expected_trigger_keys
            or trigger.get("premise_fact_id") != executor["premise_fact_id"]
            or trigger.get("premise_operation_id") != executor["premise_operation_id"]
            or not isinstance(trigger.get("premise_source_commit"), str)
            or len(trigger["premise_source_commit"]) != 40
            or trigger.get("frontier_after_sha256") != binding.get("frontier_sha256")
            or any(
                not isinstance(trigger.get(field), str)
                or len(trigger[field]) != 64
                for field in expected_trigger_keys
                if field.endswith("sha256")
            )
        ):
            raise FactOperationError("episode trigger binding is malformed")
        expected_binding.update(
            {
                "target_theorem": executor["target_theorem"],
                "formal_statement_sha256": byte_digest(
                    fact["formal"]["statement"].encode()
                ),
                "premise_fact_id": executor["premise_fact_id"],
                "premise_operation_id": executor["premise_operation_id"],
                "premise_budget": executor["premise_budget"],
                "budget": executor["budget"],
                "trigger": trigger,
            }
        )
    else:
        raise FactOperationError("fact operation uses an unsupported driver")
    if binding != expected_binding:
        raise FactOperationError("fact checker-operation binding is stale or mutated")
    for field in (
        "registry_sha256_at_execution",
        "execution_sha256",
        "frontier_sha256",
    ):
        value = binding[field]
        if not isinstance(value, str) or len(value) != 64:
            raise FactOperationError(f"fact checker-operation {field} is invalid")
    if (
        fact.get("epistemic_status") != admission["epistemic_status"]
        or fact.get("proof_route") != admission["proof_route"]
        or fact.get("axiom_footprint") != admission["axiom_footprint"]
        or row.get("kind") != admission["evidence_kind"]
        or row.get("supports") != fact.get("statement")
        or row.get("check_status") != "checked"
        or row.get("checker_command") != checker_command(fact["id"])
    ):
        raise FactOperationError("fact admission fields differ from the registered operation")
    observation = (
        runner(operation, binding["trigger"])
        if executor["driver"] == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1"
        else runner(operation)
    )
    if executor["driver"] == "axeyum-bench/smtcomp-evidence-v1":
        expected_observation = {
            "verdict": "unsat",
            "evidence_label": executor["expected_evidence_label"],
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }
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
    else:
        premise_candidate = (
            "Autogenesis.Authoritative.E"
            + binding["trigger"]["premise_before_fact_sha256"][:16]
            + ".premise"
        )
        expected_observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "canonical_type": formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "episode_dependency": premise_candidate,
            "attempted": executor["budget"],
            "accepted_plan_rank": executor["budget"],
            "premise_attempted": executor["premise_budget"],
            "premise_plan_rank": executor["premise_budget"],
        }
    if observation != expected_observation:
        raise FactOperationError(
            f"registered operation no longer replays: observed={observation!r}"
        )
    return {
        "fact_id": fact["id"],
        "operation_id": operation["id"],
        "operation_sha256": digest(operation),
        "evidence_label": observation["evidence_label"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fact", required=True, type=pathlib.Path)
    args = parser.parse_args()
    try:
        fact_path = args.fact.resolve()
        if (
            not fact_path.is_relative_to(FACTS.resolve())
            or fact_path.parent != FACTS.resolve()
            or fact_path.suffix != ".json"
        ):
            raise FactOperationError("fact must be one canonical authoritative ledger file")
        fact = json.loads(fact_path.read_text())
        executor = load_module("executor_for_fact_operation", EXECUTOR_SCRIPT)
        result = check_fact(fact, executor.run_registered)
        print(
            f"AUTOGENESIS_FACT_OPERATION_OK|fact={result['fact_id']}|"
            f"operation={result['operation_id']}|label={result['evidence_label']}"
        )
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        FactOperationError,
    ) as error:
        print(f"AUTOGENESIS_FACT_OPERATION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
