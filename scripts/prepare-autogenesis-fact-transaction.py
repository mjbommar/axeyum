#!/usr/bin/env python3
"""Prepare or verify a typed, read-only Autogenesis fact transaction proposal."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
CENSUS = ROOT / "artifacts/autogenesis/open-ranked-proposition-census-v1.json"
OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
EVIDENCE_SCRIPT = ROOT / "scripts/create-autogenesis-premise-evidence.py"
EVENT_SCRIPT = ROOT / "scripts/create-autogenesis-accepted-event.py"
VALIDATOR_SCRIPT = ROOT / "scripts/validate-facts.py"
EXECUTOR_SCRIPT = ROOT / "scripts/execute-autogenesis-operation.py"
FACT_OPERATION_SCRIPT = ROOT / "scripts/check-autogenesis-fact-operation.py"


class TransactionError(RuntimeError):
    """The proposed fact transition is malformed, stale, or unsupported."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise TransactionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def formal_type(fact: dict[str, Any]) -> str:
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or " : " not in statement:
        raise TransactionError("fact formal.statement is not a theorem declaration")
    return statement.split(" : ", 1)[1]


def validate_before(fact: dict[str, Any]) -> None:
    if fact.get("epistemic_status") != "open":
        raise TransactionError("fact precondition is not open")
    if fact.get("evidence") != []:
        raise TransactionError("open fact precondition must have empty evidence")
    for forbidden in ("proof_route", "axiom_footprint"):
        if forbidden in fact:
            raise TransactionError(f"open fact precondition already carries {forbidden}")


def build_proposition_reconciliation_transaction(
    *,
    before_fact: dict[str, Any],
    native_fact: dict[str, Any],
    match: dict[str, Any],
    overlay_link: dict[str, Any],
    census_sha256: str,
) -> dict[str, Any]:
    """Prepare a non-autonomous open-to-proved reconciliation proposal.

    This route registers already-constructed native mathematics. It deliberately
    has no operation identity and cannot receive autonomous-production credit.
    """
    validate_before(before_fact)
    fact_id = before_fact.get("id")
    theorem = match.get("native_theorem")
    if match.get("fact_id") != fact_id or not isinstance(theorem, str):
        raise TransactionError("proposition match does not bind the open fact")
    if not isinstance(census_sha256, str) or len(census_sha256) != 64:
        raise TransactionError("proposition census digest is invalid")
    if (
        native_fact.get("epistemic_status") != "proved"
        or native_fact.get("proof_route") != "kernel-lean"
        or native_fact.get("axiom_footprint") != []
    ):
        raise TransactionError("native fact is not an axiom-free proved kernel fact")
    declarations = {
        evidence.get("kernel_declaration")
        for evidence in native_fact.get("evidence", [])
        if isinstance(evidence, dict)
    }
    if theorem not in declarations:
        raise TransactionError("native fact evidence does not bind the matched theorem")
    source = overlay_link.get("source", {})
    target = overlay_link.get("target", {})
    qualifiers = overlay_link.get("qualifiers", {})
    if (
        overlay_link.get("relation") != "definitionally-matches"
        or overlay_link.get("assurance") != "independently-checked"
        or overlay_link.get("status") != "active"
        or source.get("kind") != "fact"
        or source.get("id") != fact_id
        or target.get("kind") != "kernel-declaration"
        or target.get("id") != theorem
        or qualifiers.get("admission_authority") is not False
        or qualifiers.get("fact_status_unchanged") is not True
    ):
        raise TransactionError("knowledge-overlay link does not bind the qualified match")

    after_fact = json.loads(json.dumps(before_fact))
    after_fact["epistemic_status"] = "proved"
    after_fact["proof_route"] = "kernel-lean"
    after_fact["axiom_footprint"] = []
    after_fact["evidence"] = [
        {
            "id": f"reconciliation-{theorem}",
            "kind": "kernel-term",
            "kernel_declaration": theorem,
            "supports": before_fact["formal"]["statement"],
            "check_status": "checked",
            "checkers": [
                "axeyum-lean-kernel",
                "axeyum-lean-import/checked-proposition-compatibility",
            ],
            "artifact": f"sha256:{census_sha256}",
            "notes": "Registers an independently constructed native theorem whose proposition definitionally matches this proof-free imported goal. No Autogenesis operation produced the theorem.",
        }
    ]
    provenance = dict(after_fact["provenance"])
    provenance["established_by"] = (
        f"non-autonomous reconciliation with native fact {native_fact['id']}"
    )
    after_fact["provenance"] = provenance
    before_sha = digest(before_fact)
    after_sha = digest(after_fact)
    transaction = {
        "schema_version": 1,
        "kind": "axeyum-proposition-reconciliation-transaction-proposal",
        "state": "prepared",
        "identity": {
            "fact_id": fact_id,
            "native_fact_id": native_fact["id"],
            "native_theorem": theorem,
            "before_fact_sha256": before_sha,
            "after_fact_sha256": after_sha,
            "proposition_census_sha256": census_sha256,
            "knowledge_link_id": overlay_link.get("id"),
        },
        "precondition": {
            "epistemic_status": "open",
            "evidence": [],
            "source_is_authoritative": True,
            "native_axiom_footprint": [],
            "definitionally_matches": True,
        },
        "production_credit": {
            "operation_id": None,
            "autonomous": False,
            "classification": "no_operation",
        },
        "authoritative_write": {
            "path": f"artifacts/facts/{fact_id.replace('F:', 'F-')}.json",
            "before_sha256": before_sha,
            "after_sha256": after_sha,
            "after_fact": after_fact,
        },
        "admission_event": None,
    }
    transaction["transaction_sha256"] = digest(transaction)
    return transaction


def derive_proposition_reconciliation(
    transaction: dict[str, Any],
) -> dict[str, Any]:
    """Rebuild one reconciliation proposal from authoritative live inputs."""
    identity = transaction.get("identity", {})
    fact_id = identity.get("fact_id")
    native_fact_id = identity.get("native_fact_id")
    theorem = identity.get("native_theorem")
    link_id = identity.get("knowledge_link_id")
    if not all(isinstance(value, str) for value in (fact_id, native_fact_id, theorem, link_id)):
        raise TransactionError("reconciliation identity is malformed")
    before = json.loads((FACTS / f"{fact_id.replace(':', '-')}.json").read_text())
    native = json.loads((FACTS / f"{native_fact_id.replace(':', '-')}.json").read_text())
    census = json.loads(CENSUS.read_text())
    matches = [
        row
        for row in census.get("matches", [])
        if row.get("fact_id") == fact_id and row.get("native_theorem") == theorem
    ]
    if len(matches) != 1:
        raise TransactionError("live census does not contain one exact proposition match")
    overlay = json.loads(OVERLAY.read_text())
    links = [row for row in overlay.get("links", []) if row.get("id") == link_id]
    if len(links) != 1:
        raise TransactionError("live overlay does not contain one exact knowledge link")
    return build_proposition_reconciliation_transaction(
        before_fact=before,
        native_fact=native,
        match=matches[0],
        overlay_link=links[0],
        census_sha256=hashlib.sha256(CENSUS.read_bytes()).hexdigest(),
    )


def build_transaction(
    *,
    before_fact: dict[str, Any],
    evidence: dict[str, Any],
    transition: dict[str, Any],
    event: dict[str, Any],
    source_is_authoritative: bool,
) -> dict[str, Any]:
    if source_is_authoritative:
        raise TransactionError(
            "counterfactual fixture operation cannot prepare an authoritative write"
        )
    validate_before(before_fact)
    fact_id = before_fact.get("id")
    evidence_identity = evidence.get("identity")
    evidence_result = evidence.get("result")
    acceptance = evidence.get("acceptance")
    route = evidence.get("route")
    if not all(
        isinstance(value, dict)
        for value in (evidence_identity, evidence_result, acceptance, route)
    ):
        raise TransactionError("typed premise evidence is malformed")
    if evidence_identity.get("fact_id") != fact_id:
        raise TransactionError("typed evidence names a different fact")
    if evidence_result.get("outcome") != "proved":
        raise TransactionError("typed evidence does not prove the fact")
    if evidence_result.get("canonical_type") != formal_type(before_fact):
        raise TransactionError("typed evidence theorem type differs from formal.statement")
    if acceptance.get("independent_kernel_checked") is not True:
        raise TransactionError("typed evidence was not independently kernel checked")
    footprint = acceptance.get("axiom_footprint")
    dependencies = acceptance.get("retained_answer_dependencies")
    if footprint != [] or dependencies != []:
        raise TransactionError("fixture route requires an axiom-free isolated result")
    if (
        route.get("operation_id") != "autogenesis-kernel-premise-evidence-v1"
        or not isinstance(route.get("operation_registry_sha256"), str)
        or len(route["operation_registry_sha256"]) != 64
    ):
        raise TransactionError("typed evidence is not bound to the registered operation")
    event_identity = event.get("identity")
    if not isinstance(event_identity, dict):
        raise TransactionError("accepted event identity is malformed")
    if (
        event_identity.get("fact_id") != fact_id
        or event_identity.get("premise_evidence_sha256")
        != evidence.get("evidence_sha256")
        or event_identity.get("transition_sha256")
        != transition.get("transition_sha256")
    ):
        raise TransactionError("accepted event does not bind the fact evidence chain")
    if event.get("authoritative_ledger_writes") != []:
        raise TransactionError("bootstrap accepted event unexpectedly contains ledger writes")

    evidence_sha = evidence["evidence_sha256"]
    after_fact = json.loads(json.dumps(before_fact))
    after_fact["epistemic_status"] = "proved"
    after_fact["proof_route"] = "kernel-lean"
    after_fact["axiom_footprint"] = []
    after_fact["evidence"] = [
        {
            "id": f"autogenesis-kernel-{evidence_sha[:16]}",
            "kind": "kernel-term",
            "supports": before_fact["statement"],
            "check_status": "checked",
            "checkers": [
                "axeyum-lean-kernel/autogenesis-induction-plan-check-v1",
                "autogenesis-typed-premise-evidence-v1",
            ],
            "checker_operation": {
                "id": "autogenesis-kernel-premise-evidence-v1",
                "evidence_sha256": evidence_sha,
                "accepted_event_sha256": event["event_sha256"],
            },
            "artifact": f"sha256:{evidence_sha}",
            "notes": "Derived from a typed registered operation; no caller-authored shell command is accepted.",
        }
    ]
    provenance = dict(after_fact["provenance"])
    provenance["established_by"] = (
        f"axeyum-autogenesis episode {evidence_identity['episode_id']}"
    )
    after_fact["provenance"] = provenance

    before_sha = digest(before_fact)
    after_sha = digest(after_fact)
    transaction: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-fact-transaction-proposal",
        "state": "prepared",
        "identity": {
            "fact_id": fact_id,
            "episode_id": evidence_identity["episode_id"],
            "before_fact_sha256": before_sha,
            "after_fact_sha256": after_sha,
            "premise_evidence_sha256": evidence_sha,
            "premise_transition_sha256": transition["transition_sha256"],
            "accepted_event_sha256": event["event_sha256"],
        },
        "precondition": {
            "epistemic_status": "open",
            "evidence": [],
            "source_is_authoritative": source_is_authoritative,
        },
        "registered_checker_operation": {
            "id": route["operation_id"],
            "registry_sha256": route["operation_registry_sha256"],
            "arguments": {
                "fact_id": fact_id,
                "evidence_sha256": evidence_sha,
            },
        },
        "authoritative_write": {
            "path": f"artifacts/facts/{fact_id.replace('F:', 'F-')}.json",
            "before_sha256": before_sha,
            "after_sha256": after_sha,
            "after_fact": after_fact,
        },
        "admission_event": None,
    }
    transaction["transaction_sha256"] = digest(transaction)
    return transaction


def build_authoritative_transaction(
    *,
    before_fact: dict[str, Any],
    execution: dict[str, Any],
    operation: dict[str, Any],
    registry: dict[str, Any],
) -> dict[str, Any]:
    """Derive a real open-to-proved delta from a replayed operation receipt."""
    validate_before(before_fact)
    fact_id = before_fact.get("id")
    identity = execution.get("identity")
    result = execution.get("result")
    acceptance = execution.get("acceptance")
    if not all(isinstance(value, dict) for value in (identity, result, acceptance)):
        raise TransactionError("typed operation execution is malformed")
    if (
        identity.get("fact_id") != fact_id
        or identity.get("fact_sha256") != digest(before_fact)
        or identity.get("operation_id") != operation.get("id")
        or identity.get("operation_registry_sha256") != digest(registry)
    ):
        raise TransactionError("typed execution does not bind the selected fact operation")
    admission = operation["admission"]
    if (
        result.get("outcome") != "proved"
        or result.get("epistemic_status") != admission["epistemic_status"]
        or result.get("proof_route") != admission["proof_route"]
        or result.get("evidence_kind") != admission["evidence_kind"]
        or result.get("axiom_footprint_policy")
        != admission["axiom_footprint_policy"]
        or result.get("axiom_footprint") != admission["axiom_footprint"]
        or acceptance
        != {
            "source_bound": True,
            "fresh_arena_rechecked": True,
            "caller_authored_command": False,
        }
    ):
        raise TransactionError("typed execution assurance differs from admission policy")

    fact_operation = load_module(
        "autogenesis_fact_operation_for_transaction", FACT_OPERATION_SCRIPT
    )
    execution_sha = execution.get("execution_sha256")
    if not isinstance(execution_sha, str) or len(execution_sha) != 64:
        raise TransactionError("typed execution digest is invalid")
    executor = operation["executor"]
    operation_sha = digest(operation)
    if executor["driver"] == "axeyum-bench/smtcomp-evidence-v1":
        execution_input_binding = {
            "input_artifact": executor["input_artifact"],
            "input_artifact_sha256": identity["input_artifact_sha256"],
        }
        result_description = "source-bound certified refutation"
        replay_description = (
            "exact source artifact and requires its fresh-arena certified result"
        )
    elif executor["driver"] == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        if identity.get("formal_statement_sha256") != expected_statement_sha:
            raise TransactionError("kernel execution does not bind formal.statement")
        execution_input_binding = {
            "target_theorem": executor["target_theorem"],
            "formal_statement_sha256": expected_statement_sha,
            "budget": executor["budget"],
        }
        result_description = "fresh-kernel axiom-free proof"
        replay_description = (
            "formal statement through the registered fresh-kernel operation and "
            "requires an axiom-free result without retained-answer dependencies"
        )
    elif executor["driver"] == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        trigger = identity.get("trigger")
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or not isinstance(trigger, dict)
            or trigger.get("premise_fact_id") != executor["premise_fact_id"]
            or trigger.get("premise_operation_id") != executor["premise_operation_id"]
            or trigger.get("frontier_after_sha256") != identity.get("frontier_sha256")
        ):
            raise TransactionError("episode-local execution trigger is inconsistent")
        execution_input_binding = {
            "target_theorem": executor["target_theorem"],
            "formal_statement_sha256": expected_statement_sha,
            "premise_fact_id": executor["premise_fact_id"],
            "premise_operation_id": executor["premise_operation_id"],
            "premise_budget": executor["premise_budget"],
            "budget": executor["budget"],
            "trigger": trigger,
        }
        result_description = "event-bound episode-local axiom-free apply proof"
        replay_description = (
            "formal statement by reconstructing and applying the event-bound premise "
            "and requires no retained-answer dependency"
        )
    elif executor["driver"] == "axeyum-lean-import/statement-reflexivity-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        observation = result.get("observation")
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or not isinstance(observation, dict)
            or observation.get("verdict") != "proved"
            or observation.get("axiom_footprint") != []
            or observation.get("retained_answer_dependencies") != []
            or observation.get("target_dependency") is not False
            or observation.get("ledger_writes") != 0
        ):
            raise TransactionError(
                "statement-reflexivity execution assurance is inconsistent"
            )
        execution_input_binding = {
            "statement_adapter_manifest": executor["statement_adapter_manifest"],
            "statement_adapter_manifest_sha256": identity[
                "statement_adapter_manifest_sha256"
            ],
            "reflexivity_manifest": executor["reflexivity_manifest"],
            "reflexivity_manifest_sha256": identity["reflexivity_manifest_sha256"],
            "external_artifact_sha256": identity["external_artifact_sha256"],
            "formal_statement_sha256": expected_statement_sha,
            "target_definition": executor["target_definition"],
            "goal_sha256": observation["goal_sha256"],
            "proof_sha256": observation["proof_sha256"],
            "target_content_sha256": observation["target_content_sha256"],
            "max_binders": executor["max_binders"],
            "max_constructed_nodes": executor["max_constructed_nodes"],
        }
        result_description = "fresh-import axiom-free reflexivity proof"
        replay_description = (
            "proof-isolated statement artifact through a fresh importer and "
            "requires the exact kernel-checked proof and dependency-free result"
        )
    elif executor["driver"] == "axeyum-lean-import/checked-theorem-receipt-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        observation = result.get("observation")
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or identity.get("receipt_sha256") != executor["receipt_sha256"]
            or not isinstance(observation, dict)
            or observation.get("verdict") != "proved"
            or observation.get("receipt_sha256") != executor["receipt_sha256"]
            or observation.get("axiom_footprint") != []
            or observation.get("retained_answer_dependencies") != []
            or observation.get("fresh_imports") != 2
            or observation.get("fixed_plan_reconstructions") != 2
            or observation.get("search_invocations") != 0
            or observation.get("ledger_writes") != 0
        ):
            raise TransactionError(
                "checked-theorem receipt execution assurance is inconsistent"
            )
        execution_input_binding = {
            "receipt_manifest": executor["receipt_manifest"],
            "receipt_manifest_sha256": identity["receipt_manifest_sha256"],
            "receipt_sha256": identity["receipt_sha256"],
            "observation_sha256": identity["observation_sha256"],
            "source_artifact_sha256": identity["source_artifact_sha256"],
            "formal_statement_sha256": expected_statement_sha,
            "target_definition": executor["target_definition"],
            "goal_sha256": observation["goal_sha256"],
            "proof_sha256": observation["proof_sha256"],
            "target_content_sha256": observation["target_content_sha256"],
        }
        result_description = "two-fresh-kernel axiom-free semantic theorem receipt"
        replay_description = (
            "immutable source-bound semantic theorem receipt and requires its exact "
            "two-fresh-kernel proof, zero assumptions, and zero direct theorem dependencies"
        )
    elif executor["driver"] == "axeyum-lean-import/dependency-theorem-receipt-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        observation = result.get("observation")
        direct_dependencies = (
            observation.get("retained_answer_dependencies")
            if isinstance(observation, dict)
            else None
        )
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or identity.get("receipt_sha256") != executor["receipt_sha256"]
            or identity.get("dependency_set_sha256")
            != executor["dependency_set_sha256"]
            or identity.get("transitive_dependency_set_sha256")
            != executor["transitive_dependency_set_sha256"]
            or not isinstance(observation, dict)
            or observation.get("verdict") != "proved"
            or observation.get("receipt_sha256") != executor["receipt_sha256"]
            or observation.get("axiom_footprint") != []
            or not isinstance(direct_dependencies, list)
            or len(direct_dependencies) != 8
            or [row.get("name") for row in direct_dependencies]
            != sorted(row.get("name") for row in direct_dependencies)
            or observation.get("dependency_set_sha256")
            != executor["dependency_set_sha256"]
            or observation.get("transitive_theorem_dependencies") != 115
            or observation.get("transitive_dependency_set_sha256")
            != executor["transitive_dependency_set_sha256"]
            or observation.get("fresh_full_reconstructions") != 2
            or observation.get("target_theorem_submissions") != 2
            or observation.get("search_invocations") != 0
            or observation.get("ledger_writes") != 0
        ):
            raise TransactionError(
                "dependency-theorem receipt execution assurance is inconsistent"
            )
        execution_input_binding = {
            "receipt_manifest": executor["receipt_manifest"],
            "receipt_manifest_sha256": identity["receipt_manifest_sha256"],
            "receipt_observation_sha256": identity[
                "receipt_observation_sha256"
            ],
            "receipt_sha256": identity["receipt_sha256"],
            "source_artifact_sha256": identity["source_artifact_sha256"],
            "candidate_observation_sha256": identity[
                "candidate_observation_sha256"
            ],
            "dependency_set_sha256": identity["dependency_set_sha256"],
            "transitive_dependency_set_sha256": identity[
                "transitive_dependency_set_sha256"
            ],
            "formal_statement_sha256": expected_statement_sha,
            "target_definition": executor["target_definition"],
            "goal_sha256": observation["goal_sha256"],
            "proof_sha256": observation["proof_sha256"],
            "target_content_sha256": observation["target_content_sha256"],
            "direct_theorem_dependencies": direct_dependencies,
            "transitive_theorem_dependencies": observation[
                "transitive_theorem_dependencies"
            ],
        }
        result_description = (
            "two-fresh-kernel axiom-free dependency-bound semantic theorem receipt"
        )
        replay_description = (
            "immutable source-bound dependency theorem receipt and requires its "
            "exact two-fresh-kernel proof, empty axiom footprint, eight named direct "
            "premise identities, and replay-bound transitive dependency digest"
        )
    elif executor["driver"] == "axeyum-lean-import/sealed-kernel-capsule-v1":
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        observation = result.get("observation")
        dependencies = (
            observation.get("retained_answer_dependencies")
            if isinstance(observation, dict)
            else None
        )
        is_int_fib_natcast = (
            operation["id"]
            == "authoritative-mathlib-int-fib-natcast-kernel-capsule-v1"
        )
        is_int_fib_add_two = (
            operation["id"]
            == "authoritative-mathlib-int-fib-add-two-kernel-capsule-v1"
        )
        is_int_fib_recurrence_corollary = (
            operation["id"]
            == "authoritative-mathlib-int-fib-recurrence-corollary-kernel-capsule-v1"
        )
        is_int_fib_add_one = (
            operation["id"]
            == "authoritative-mathlib-int-fib-add-one-kernel-capsule-v1"
        )
        is_int_fib_neg = (
            operation["id"]
            == "authoritative-mathlib-int-fib-neg-kernel-capsule-v1"
        )
        is_int_gcd_fib = (
            operation["id"]
            == "authoritative-mathlib-int-gcd-fib-kernel-capsule-v1"
        )
        is_int_fib_gcd = (
            operation["id"]
            == "authoritative-mathlib-int-fib-gcd-kernel-capsule-v1"
        )
        is_int_fib_dvd = (
            operation["id"]
            == "authoritative-mathlib-int-fib-dvd-kernel-capsule-v1"
        )
        is_int_fib_of_nonneg = (
            operation["id"]
            == "authoritative-mathlib-int-fib-of-nonneg-kernel-capsule-v1"
        )
        is_nat_fib_pos = (
            operation["id"]
            == "authoritative-mathlib-nat-fib-pos-kernel-capsule-v1"
        )
        is_nat_fib_eq_zero = (
            operation["id"]
            == "authoritative-mathlib-nat-fib-eq-zero-kernel-capsule-v1"
        )
        is_int_fib_eq_zero = (
            operation["id"]
            == "authoritative-mathlib-int-fib-eq-zero-kernel-capsule-v1"
        )
        expected_dependencies = (
            [
                "Axeyum.Autogenesis.intFibEqZeroResidualV1",
                "Axeyum.Autogenesis.intFibNatAbsV1",
                "Axeyum.Autogenesis.intNatAbsEqZeroV1",
                "Nat.fib_eq_zero",
            ]
            if is_int_fib_eq_zero
            else
            [
                "Axeyum.Autogenesis.natFibEqZeroResidualV1",
                "Axeyum.Autogenesis.natFibZeroV1",
                "Nat.fib_pos",
                "Nat.zero_lt_succ",
            ]
            if is_nat_fib_eq_zero
            else [
                "Axeyum.Autogenesis.natFibOnePositiveV1",
                "Axeyum.Autogenesis.natFibPosResidualV1",
                "Axeyum.Autogenesis.natFibStepPositiveV1",
                "Axeyum.Autogenesis.natFibZeroV1",
                "Nat.zero_lt_succ",
            ]
            if is_nat_fib_pos
            else []
            if is_int_fib_natcast
            else [
                "Axeyum.Autogenesis.fibAddTwo",
                "Axeyum.IntFib.castAdd",
                "Axeyum.IntFib.evenAdd",
                "Axeyum.IntFib.modCases",
                "Axeyum.IntFib.oddAdd",
                "Axeyum.IntFib.succOne",
                "Axeyum.IntFib.succZero",
                "Int.fib_add_two_residual",
            ]
            if is_int_fib_add_two
            else [
                "Axeyum.Autogenesis.intFibEqAddTwoSubAddOneResidualV2",
                "Int.add_neg_cancel_right",
                "Int.fib_add_two",
            ]
            if is_int_fib_recurrence_corollary
            else [
                "Axeyum.Autogenesis.intFibAddOneResidualV3",
                "Int.add_comm",
                "Int.add_neg_cancel_right",
                "Int.fib_add_two",
            ]
            if is_int_fib_add_one
            else [
                "Axeyum.Autogenesis.intFibNegFunctionResidualV1",
                "Axeyum.Autogenesis.intFibNegNegativeBranchV1",
                "Axeyum.Autogenesis.intFibNegPositiveBranchV1",
            ]
            if is_int_fib_neg
            else [
                "Axeyum.Autogenesis.intFibNatAbsV1",
                "Eq.symm",
                "Eq.trans",
                "Int.gcd_def",
                "Nat.fib_gcd",
            ]
            if is_int_gcd_fib
            else ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]
            if is_int_fib_gcd
            else [
                "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
                "Axeyum.Autogenesis.intFibNatAbsV1",
                "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
                "Axeyum.Autogenesis.intNatAbsMulDirectV1",
                "Eq.symm",
                "Nat.fib_dvd",
            ]
            if is_int_fib_dvd
            else [
                "Axeyum.Autogenesis.intFibOfNonnegResidualV1",
                "Int.fib_natCast",
            ]
            if is_int_fib_of_nonneg
            else None
        )
        is_single_construction = (
            is_int_fib_natcast
            or is_int_fib_recurrence_corollary
            or is_int_fib_add_one
            or is_int_fib_neg
            or is_int_gcd_fib
            or is_int_fib_gcd
            or is_int_fib_dvd
            or is_int_fib_of_nonneg
            or is_nat_fib_pos
            or is_nat_fib_eq_zero
            or is_int_fib_eq_zero
        )
        expected_fresh_imports = 2 if is_single_construction else 4
        expected_reconstructions = 1 if is_single_construction else 2
        expected_submissions = 1 if is_single_construction else 2
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or identity.get("receipt_sha256") != executor["receipt_sha256"]
            or identity.get("capsule_sha256") != executor["capsule_sha256"]
            or not isinstance(observation, dict)
            or observation.get("verdict") != "proved"
            or observation.get("receipt_sha256") != executor["receipt_sha256"]
            or observation.get("capsule_sha256") != executor["capsule_sha256"]
            or observation.get("goal_sha256") != executor["goal_sha256"]
            or observation.get("declaration_sha256")
            != executor["declaration_sha256"]
            or observation.get("axiom_footprint") != []
            or not isinstance(dependencies, list)
            or (
                dependencies != expected_dependencies
                if is_int_fib_natcast
                or is_int_fib_add_two
                or is_int_fib_recurrence_corollary
                or is_int_fib_add_one
                or is_int_fib_neg
                or is_int_gcd_fib
                or is_int_fib_gcd
                or is_int_fib_dvd
                or is_int_fib_of_nonneg
                or is_nat_fib_pos
                or is_nat_fib_eq_zero
                or is_int_fib_eq_zero
                else not dependencies
            )
            or len(dependencies) != len(set(dependencies))
            or observation.get("fresh_imports") != expected_fresh_imports
            or observation.get("fixed_plan_reconstructions")
            != expected_reconstructions
            or observation.get("target_theorem_submissions")
            != expected_submissions
            or observation.get("search_invocations") != 0
            or observation.get("ledger_writes") != 0
        ):
            raise TransactionError(
                "sealed kernel capsule execution assurance is inconsistent"
            )
        execution_input_binding = {
            "result_manifest": executor["result_manifest"],
            "result_manifest_sha256": identity["result_manifest_sha256"],
            "capsule_path": executor["capsule_path"],
            "capsule_sha256": identity["capsule_sha256"],
            "receipt_sha256": identity["receipt_sha256"],
            "formal_statement_sha256": expected_statement_sha,
            "target_theorem": executor["target_theorem"],
            "goal_sha256": observation["goal_sha256"],
            "declaration_sha256": observation["declaration_sha256"],
            "direct_theorem_dependencies": dependencies,
        }
        if is_int_fib_eq_zero:
            result_description = (
                "four-link-specialized axiom-free sealed integer Fibonacci zero capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and four named direct theorem dependencies"
            )
        elif is_nat_fib_eq_zero:
            result_description = (
                "four-link-specialized axiom-free sealed natural Fibonacci zero capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and four named direct theorem dependencies"
            )
        elif is_nat_fib_pos:
            result_description = (
                "five-link-specialized axiom-free sealed natural Fibonacci positivity capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and five named direct theorem dependencies"
            )
        elif is_int_fib_natcast:
            result_description = (
                "definitionally reconstructed axiom-free sealed kernel theorem capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and empty direct theorem dependency set"
            )
        elif is_int_fib_add_two:
            result_description = (
                "eight-root-composed axiom-free sealed integer Fibonacci recurrence capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, four fresh imports, empty axiom footprint, "
                "and eight named direct theorem dependencies"
            )
        elif is_int_fib_recurrence_corollary:
            result_description = (
                "three-root-composed axiom-free sealed integer Fibonacci recurrence corollary capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and three named direct theorem dependencies"
            )
        elif is_int_fib_add_one:
            result_description = (
                "four-root-composed axiom-free sealed integer Fibonacci add-one capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and four named direct theorem dependencies"
            )
        elif is_int_fib_neg:
            result_description = (
                "three-root-composed axiom-free sealed integer Fibonacci negation capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and three named direct theorem dependencies"
            )
        elif is_int_gcd_fib:
            result_description = (
                "five-link-composed axiom-free sealed integer Fibonacci gcd capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and five named direct theorem dependencies"
            )
        elif is_int_fib_gcd:
            result_description = (
                "two-link-composed axiom-free sealed integer Fibonacci gcd presentation capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and four named direct theorem dependencies"
            )
        elif is_int_fib_dvd:
            result_description = (
                "six-link-composed axiom-free sealed integer Fibonacci divisibility capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and six named direct theorem dependencies"
            )
        elif is_int_fib_of_nonneg:
            result_description = (
                "two-root-specialized axiom-free sealed nonnegative integer Fibonacci capsule"
            )
            replay_description = (
                "immutable capsule and committed identity manifest and requires its "
                "exact theorem identity, two fresh imports, empty axiom footprint, "
                "and two named direct theorem dependencies"
            )
        else:
            result_description = (
                "twice-reconstructed axiom-free sealed kernel theorem capsule"
            )
            replay_description = (
                "immutable capsule and committed result manifest and requires their "
                "exact twice-reconstructed theorem identity, empty axiom footprint, "
                "and named direct theorem dependencies"
            )
    elif executor["driver"] == "axeyum-lean-import/modeq-family-multi-target-v1":
        # `fact_id` is already bound by the generic check above
        # (`identity.fact_id != fact_id` refuses before this branch ever
        # runs), so this looks up the ONE target row a multi-target
        # operation names for the fact this transaction is FOR -- it does
        # not construct a second, parallel notion of which fact the receipt
        # is about. `resolve_multi_target` is loaded from the executor
        # module and reused verbatim (ADR-0554): never re-implemented here,
        # so this lookup can never disagree with the one `build_receipt`
        # itself used to produce the receipt under test.
        executor_module = load_module(
            "autogenesis_executor_for_modeq_transaction", EXECUTOR_SCRIPT
        )
        try:
            target = executor_module.resolve_multi_target(operation, fact_id)
        except executor_module.ExecutionError as error:
            raise TransactionError(
                f"modeq-family multi-target resolution failed: {error}"
            ) from error
        expected_statement_sha = hashlib.sha256(
            before_fact["formal"]["statement"].encode()
        ).hexdigest()
        observation = result.get("observation")
        if (
            identity.get("formal_statement_sha256") != expected_statement_sha
            or identity.get("target_definition") != target["target_definition"]
            or not isinstance(observation, dict)
            or observation.get("verdict") != "proved"
            or observation.get("target_definition") != target["target_definition"]
            or observation.get("axiom_footprint") != []
            or observation.get("retained_answer_dependencies") != []
            or observation.get("target_dependency") is not False
            or observation.get("ledger_writes") != 0
        ):
            raise TransactionError(
                "modeq-family multi-target execution assurance is inconsistent"
            )
        execution_input_binding = {
            "target_fact_id": fact_id,
            "statement_adapter_manifest": target["statement_adapter_manifest"],
            "statement_adapter_manifest_sha256": identity[
                "statement_adapter_manifest_sha256"
            ],
            "modeq_manifest": target["modeq_manifest"],
            "modeq_manifest_sha256": identity["modeq_manifest_sha256"],
            "external_artifact_sha256": identity["external_artifact_sha256"],
            "formal_statement_sha256": expected_statement_sha,
            "target_definition": target["target_definition"],
            "goal_sha256": observation["goal_sha256"],
            "proof_sha256": observation["proof_sha256"],
            "target_content_sha256": observation["target_content_sha256"],
            "binders_used": observation["binders_used"],
            "max_binders": observation["max_binders"],
            "admitted_declarations": observation["admitted_declarations"],
        }
        result_description = "fresh-import axiom-free modeq-family target proof"
        replay_description = (
            "resolved multi-target statement adapter and candidate manifests "
            "through the operation's own reviewed checker module and requires the "
            "exact kernel-checked proof, dependency-free result, and matching "
            "target definition"
        )
    else:
        raise TransactionError("authoritative operation uses an unsupported driver")
    after_fact = json.loads(json.dumps(before_fact))
    after_fact["epistemic_status"] = admission["epistemic_status"]
    after_fact["proof_route"] = admission["proof_route"]
    after_fact["axiom_footprint"] = admission["axiom_footprint"]
    after_fact["evidence"] = [
        {
            "id": f"autogenesis-operation-{execution_sha[:16]}",
            "kind": admission["evidence_kind"],
            "supports": before_fact["statement"],
            "check_status": "checked",
            "checkers": [
                operation["producer"]["operation"],
                operation["checker"]["operation"],
                executor["driver"],
            ],
            "checker_command": fact_operation.checker_command(fact_id),
            "checker_operation": {
                "id": operation["id"],
                "operation_sha256": operation_sha,
                "registry_sha256_at_execution": identity[
                    "operation_registry_sha256"
                ],
                "execution_sha256": execution_sha,
                "frontier_sha256": identity["frontier_sha256"],
                **execution_input_binding,
            },
            "artifact": f"sha256:{execution_sha}",
            "notes": (
                "Derived from a clean-commit typed execution receipt. The "
                f"registered fact-operation checker replays the {replay_description}; no "
                "caller-authored route, footprint, checker, or shell command "
                "is accepted."
            ),
        }
    ]
    provenance = dict(after_fact["provenance"])
    provenance["established_by"] = (
        f"axeyum-autogenesis execution {identity['execution_id']}"
    )
    after_fact["provenance"] = provenance
    previous_notes = before_fact.get("notes")
    closure_note = (
        "CLOSED BY AXEYUM AUTOGENESIS. The machine frontier selected this exact "
        f"fact for registered operation `{operation['id']}`; execution receipt "
        f"`{execution_sha}` produced a {result_description}, and "
        "the typed transaction derived this status, route, footprint, evidence "
        "row, checker, and provenance without caller-authored admission metadata."
    )
    if isinstance(previous_notes, str) and previous_notes:
        after_fact["notes"] = (
            closure_note
            + "\n\n--- PRE-CLOSURE RECORD, RETAINED AS HISTORY ---\n\n"
            + previous_notes
        )
    else:
        after_fact["notes"] = closure_note

    before_sha = digest(before_fact)
    after_sha = digest(after_fact)
    transaction: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-fact-transaction-proposal",
        "state": "prepared",
        "identity": {
            "fact_id": fact_id,
            "episode_id": identity["execution_id"],
            "before_fact_sha256": before_sha,
            "after_fact_sha256": after_sha,
            "premise_evidence_sha256": execution_sha,
            "execution_sha256": execution_sha,
            "frontier_sha256": identity["frontier_sha256"],
        },
        "precondition": {
            "epistemic_status": "open",
            "evidence": [],
            "source_is_authoritative": True,
        },
        "registered_checker_operation": {
            "id": operation["id"],
            "operation_sha256": operation_sha,
            "registry_sha256": identity["operation_registry_sha256"],
            "arguments": {
                "fact_id": fact_id,
                "execution_sha256": execution_sha,
                **execution_input_binding,
            },
        },
        "authoritative_write": {
            "path": f"artifacts/facts/{fact_id.replace('F:', 'F-')}.json",
            "before_sha256": before_sha,
            "after_sha256": after_sha,
            "after_fact": after_fact,
        },
        "admission_event": None,
    }
    transaction["transaction_sha256"] = digest(transaction)
    return transaction


def verify_transaction(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("transaction_sha256")
    unsigned = dict(actual)
    unsigned.pop("transaction_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise TransactionError("transaction digest is missing or invalid")
    if actual.get("state") != "prepared" or actual.get("admission_event") is not None:
        raise TransactionError("a proposal cannot claim committed admission")
    if actual != expected:
        raise TransactionError("fact transaction proposal is stale or mutated")


def derive_fixture(args: argparse.Namespace) -> dict[str, Any]:
    before_fact = json.loads(args.fact.read_text())
    root = args.bundle.resolve()
    paths = {
        "snapshot": root / "snapshot.json",
        "catalog": root / "pre_b-catalog.json",
        "bundle": root / "pre_b-induction-output/induction-plans.json",
        "plans": root / "pre_b-induction-output/induction-plans.tsv",
        "kernel_evidence": root / "premise-kernel-evidence.tsv",
        "evidence": root / "premise-evidence.json",
        "transition": root / "premise-transition.json",
        "event": root / "premise-accepted-event.json",
    }
    missing = [name for name, path in paths.items() if not path.is_file()]
    if missing:
        raise TransactionError(f"result bundle is missing inputs: {missing}")

    evidence_module = load_module("autogenesis_evidence_for_transaction", EVIDENCE_SCRIPT)
    evidence_args = argparse.Namespace(
        snapshot=paths["snapshot"],
        catalog=paths["catalog"],
        bundle=paths["bundle"],
        plans=paths["plans"],
        kernel_evidence=paths["kernel_evidence"],
    )
    try:
        expected_evidence = evidence_module.derive(evidence_args)
    except evidence_module.EvidenceError as error:
        raise TransactionError(f"typed evidence replay failed: {error}") from error
    evidence = json.loads(paths["evidence"].read_text())
    if evidence != expected_evidence:
        raise TransactionError("retained typed evidence is stale or mutated")

    transition = json.loads(paths["transition"].read_text())
    event = json.loads(paths["event"].read_text())
    event_module = load_module("autogenesis_event_for_transaction", EVENT_SCRIPT)
    try:
        expected_event = event_module.build_event(
            snapshot=json.loads(paths["snapshot"].read_text()),
            evidence=evidence,
            transition=transition,
        )
        event_module.verify_event(event, expected_event)
    except event_module.EventError as error:
        raise TransactionError(f"accepted event replay failed: {error}") from error

    authoritative = FACTS / (before_fact["id"].replace("F:", "F-") + ".json")
    source_is_authoritative = args.fact.resolve() == authoritative.resolve()
    transaction = build_transaction(
        before_fact=before_fact,
        evidence=evidence,
        transition=transition,
        event=event,
        source_is_authoritative=source_is_authoritative,
    )
    validator = load_module("validate_facts_for_transaction", VALIDATOR_SCRIPT)
    errors = validator.validate_one(
        authoritative,
        transaction["authoritative_write"]["after_fact"],
        {json.loads(path.read_text())["id"] for path in FACTS.glob("*.json")},
    )
    if errors:
        raise TransactionError("proposed after-fact fails validation: " + "; ".join(errors))
    return transaction


def derive_authoritative(args: argparse.Namespace) -> dict[str, Any]:
    before_fact = json.loads(args.fact.read_text())
    authoritative = FACTS / (before_fact["id"].replace("F:", "F-") + ".json")
    if args.fact.resolve() != authoritative.resolve():
        raise TransactionError(
            "authoritative transaction preparation requires the canonical fact source"
        )
    executor_module = load_module(
        "autogenesis_executor_for_transaction", EXECUTOR_SCRIPT
    )
    try:
        expected_execution = executor_module.derive(
            args.frontier.resolve(),
            trigger_bundle=(
                args.trigger_bundle.resolve()
                if getattr(args, "trigger_bundle", None) is not None
                else None
            ),
        )
        execution = json.loads(args.execution.read_text())
        executor_module.verify_receipt(execution, expected_execution)
        frontier = json.loads(args.frontier.read_text())
        selected_fact, operation, registry = executor_module.selected_inputs(frontier)
    except executor_module.ExecutionError as error:
        raise TransactionError(f"typed operation execution replay failed: {error}") from error
    if selected_fact != before_fact:
        raise TransactionError("frontier-selected fact differs from authoritative source")
    transaction = build_authoritative_transaction(
        before_fact=before_fact,
        execution=execution,
        operation=operation,
        registry=registry,
    )
    validator = load_module("validate_facts_for_authoritative_transaction", VALIDATOR_SCRIPT)
    errors = validator.validate_one(
        authoritative,
        transaction["authoritative_write"]["after_fact"],
        {json.loads(path.read_text())["id"] for path in FACTS.glob("*.json")},
    )
    if errors:
        raise TransactionError("proposed after-fact fails validation: " + "; ".join(errors))
    return transaction


def derive(args: argparse.Namespace) -> dict[str, Any]:
    bundle = getattr(args, "bundle", None)
    frontier = getattr(args, "frontier", None)
    execution = getattr(args, "execution", None)
    if bundle is not None and frontier is None and execution is None:
        return derive_fixture(args)
    if bundle is None and frontier is not None and execution is not None:
        return derive_authoritative(args)
    raise TransactionError(
        "choose exactly one input mode: --bundle, or --frontier plus --execution"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fact", required=True, type=pathlib.Path)
    parser.add_argument("--bundle", type=pathlib.Path)
    parser.add_argument("--frontier", type=pathlib.Path)
    parser.add_argument("--execution", type=pathlib.Path)
    parser.add_argument("--trigger-bundle", type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(args)
        if args.verify is not None:
            verify_transaction(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_FACT_TRANSACTION_OK|{expected['transaction_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise TransactionError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(
                f"AUTOGENESIS_FACT_TRANSACTION|{expected['transaction_sha256']}|"
                f"source_authoritative={str(expected['precondition']['source_is_authoritative']).lower()}|"
                f"state=prepared|{output}"
            )
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        TransactionError,
    ) as error:
        print(f"AUTOGENESIS_FACT_TRANSACTION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
