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
EVIDENCE_SCRIPT = ROOT / "scripts/create-autogenesis-premise-evidence.py"
EVENT_SCRIPT = ROOT / "scripts/create-autogenesis-accepted-event.py"
VALIDATOR_SCRIPT = ROOT / "scripts/validate-facts.py"


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


def build_transaction(
    *,
    before_fact: dict[str, Any],
    evidence: dict[str, Any],
    transition: dict[str, Any],
    event: dict[str, Any],
    source_is_authoritative: bool,
) -> dict[str, Any]:
    validate_before(before_fact)
    fact_id = before_fact.get("id")
    evidence_identity = evidence.get("identity")
    evidence_result = evidence.get("result")
    acceptance = evidence.get("acceptance")
    if not all(isinstance(value, dict) for value in (evidence_identity, evidence_result, acceptance)):
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
            "id": "autogenesis-kernel-premise-evidence-v1",
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


def derive(args: argparse.Namespace) -> dict[str, Any]:
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fact", required=True, type=pathlib.Path)
    parser.add_argument("--bundle", required=True, type=pathlib.Path)
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
