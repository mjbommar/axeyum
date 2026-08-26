#!/usr/bin/env python3
"""Apply or recover one crash-safe Autogenesis fact transaction."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import pathlib
import tempfile
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
PREPARE_SCRIPT = ROOT / "scripts/prepare-autogenesis-fact-transaction.py"


class ApplyError(RuntimeError):
    """The transaction cannot be applied or recovered without guessing."""


class InjectedFault(RuntimeError):
    """A test-only fault stopped the applicant at a named durable boundary."""


def load_prepare_module():
    spec = importlib.util.spec_from_file_location(
        "prepare_autogenesis_transaction_for_apply", PREPARE_SCRIPT
    )
    if spec is None or spec.loader is None:
        raise ApplyError(f"cannot load {PREPARE_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def object_digest(path: pathlib.Path) -> str:
    return digest(json.loads(path.read_text()))


def fsync_directory(path: pathlib.Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def atomic_write(path: pathlib.Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = pathlib.Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        if temporary.exists():
            temporary.unlink()


def build_admission_event(transaction: dict[str, Any]) -> dict[str, Any]:
    identity = transaction["identity"]
    if transaction.get("kind") == "axeyum-proposition-reconciliation-transaction-proposal":
        event: dict[str, Any] = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-durable-reconciliation-event",
            "event_type": "fact-reconciled",
            "sequence": 1,
            "identity": {
                "fact_id": identity["fact_id"],
                "native_fact_id": identity["native_fact_id"],
                "native_theorem": identity["native_theorem"],
                "transaction_sha256": transaction["transaction_sha256"],
                "before_fact_sha256": identity["before_fact_sha256"],
                "after_fact_sha256": identity["after_fact_sha256"],
                "proposition_census_sha256": identity["proposition_census_sha256"],
            },
            "durable_state": {
                "epistemic_status": transaction["authoritative_write"]["after_fact"][
                    "epistemic_status"
                ],
                "fact_sha256": identity["after_fact_sha256"],
            },
            "production_credit": transaction["production_credit"],
            "publication": {"artifact_archived": False, "git_published": False},
        }
        event["event_sha256"] = digest(event)
        return event
    event: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-durable-admission-event",
        "event_type": "fact-admitted",
        "sequence": 1,
        "identity": {
            "fact_id": identity["fact_id"],
            "episode_id": identity["episode_id"],
            "transaction_sha256": transaction["transaction_sha256"],
            "before_fact_sha256": identity["before_fact_sha256"],
            "after_fact_sha256": identity["after_fact_sha256"],
            "premise_evidence_sha256": identity["premise_evidence_sha256"],
        },
        "durable_state": {
            "epistemic_status": transaction["authoritative_write"]["after_fact"][
                "epistemic_status"
            ],
            "fact_sha256": identity["after_fact_sha256"],
        },
        "publication": {
            "artifact_archived": False,
            "git_published": False,
        },
    }
    event["event_sha256"] = digest(event)
    return event


def build_intent(
    transaction: dict[str, Any], admission_event: dict[str, Any]
) -> dict[str, Any]:
    intent: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-transaction-intent",
        "transaction_sha256": transaction["transaction_sha256"],
        "transaction": transaction,
        "admission_event": admission_event,
    }
    intent["intent_sha256"] = digest(intent)
    return intent


def verify_content_addressed(value: dict[str, Any], field: str, label: str) -> None:
    claimed = value.get(field)
    unsigned = dict(value)
    unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ApplyError(f"{label} digest is missing or invalid")


def authorize_target(
    transaction: dict[str, Any], fixture_fact_root: pathlib.Path | None
) -> pathlib.Path:
    relative = pathlib.Path(transaction["authoritative_write"]["path"])
    if relative.is_absolute() or ".." in relative.parts or len(relative.parts) != 3:
        raise ApplyError("transaction fact path is not the canonical ledger shape")
    expected_name = transaction["identity"]["fact_id"].replace("F:", "F-") + ".json"
    if relative.parts[:2] != ("artifacts", "facts") or relative.name != expected_name:
        raise ApplyError("transaction fact path disagrees with fact identity")
    source_is_authoritative = transaction["precondition"].get(
        "source_is_authoritative"
    )
    if fixture_fact_root is None:
        if source_is_authoritative is not True:
            raise ApplyError("production apply refuses a non-authoritative source proposal")
        return FACTS / relative.name
    if source_is_authoritative is not False:
        raise ApplyError("fixture apply requires an explicitly non-authoritative proposal")
    return fixture_fact_root.resolve() / relative.name


def require_recovery_intent(
    transaction: dict[str, Any], journal_root: pathlib.Path
) -> pathlib.Path:
    """Authorize replay-free recovery only after the checked first phase persisted."""
    verify_content_addressed(transaction, "transaction_sha256", "transaction")
    intent_path = (
        journal_root / transaction["transaction_sha256"] / "intent.json"
    )
    if not intent_path.is_file():
        raise ApplyError("recovery requires an existing durable transaction intent")
    return intent_path


def apply_or_recover(
    *,
    transaction: dict[str, Any],
    target: pathlib.Path,
    journal_root: pathlib.Path,
    fault_after: str | None = None,
) -> dict[str, Any]:
    verify_content_addressed(transaction, "transaction_sha256", "transaction")
    if transaction.get("state") != "prepared" or transaction.get("admission_event") is not None:
        raise ApplyError("applicant requires a prepared proposal with no admission event")
    if not target.is_file():
        raise ApplyError(f"target fact does not exist: {target}")
    journal_root.mkdir(parents=True, exist_ok=True)
    if os.stat(target.parent).st_dev != os.stat(journal_root).st_dev:
        raise ApplyError("journal and fact must be on the same filesystem")

    event = build_admission_event(transaction)
    intent = build_intent(transaction, event)
    transaction_dir = journal_root / transaction["transaction_sha256"]
    intent_path = transaction_dir / "intent.json"
    event_path = transaction_dir / "admission-event.json"
    if intent_path.exists():
        actual_intent = json.loads(intent_path.read_text())
        verify_content_addressed(actual_intent, "intent_sha256", "intent")
        if actual_intent != intent:
            raise ApplyError("journal intent disagrees with the transaction")
    else:
        transaction_dir.mkdir(parents=True, exist_ok=False)
        fsync_directory(journal_root)
        atomic_write(intent_path, json_bytes(intent))
    if fault_after == "intent":
        raise InjectedFault("after-intent")

    before_sha = transaction["identity"]["before_fact_sha256"]
    after_sha = transaction["identity"]["after_fact_sha256"]
    current_sha = object_digest(target)
    if event_path.exists():
        actual_event = json.loads(event_path.read_text())
        verify_content_addressed(actual_event, "event_sha256", "admission event")
        if actual_event != event:
            raise ApplyError("admission event disagrees with the transaction")
        if current_sha != after_sha:
            raise ApplyError("committed event exists but fact is not the admitted after-state")
        return event
    if current_sha == before_sha:
        after_fact = transaction["authoritative_write"]["after_fact"]
        if digest(after_fact) != after_sha:
            raise ApplyError("transaction after-fact digest is invalid")
        atomic_write(target, json_bytes(after_fact))
        if object_digest(target) != after_sha:
            raise ApplyError("fact replacement did not produce the promised after-state")
    elif current_sha != after_sha:
        raise ApplyError("fact compare-and-swap precondition failed")
    if fault_after == "fact":
        raise InjectedFault("after-fact")

    atomic_write(event_path, json_bytes(event))
    if fault_after == "event":
        raise InjectedFault("after-event")
    return event


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transaction", required=True, type=pathlib.Path)
    parser.add_argument("--bundle", type=pathlib.Path)
    parser.add_argument("--frontier", type=pathlib.Path)
    parser.add_argument("--execution", type=pathlib.Path)
    parser.add_argument("--trigger-bundle", type=pathlib.Path)
    parser.add_argument("--before-fact", type=pathlib.Path)
    parser.add_argument("--journal-dir", required=True, type=pathlib.Path)
    parser.add_argument("--fixture-fact-root", type=pathlib.Path)
    parser.add_argument(
        "--recover",
        action="store_true",
        help="recover only from an existing durable intent; do not replay pre-state inputs",
    )
    parser.add_argument(
        "--fault-after", choices=("intent", "fact", "event"), help=argparse.SUPPRESS
    )
    args = parser.parse_args()
    prepare_error = ApplyError
    try:
        prepare = load_prepare_module()
        prepare_error = prepare.TransactionError
        transaction = json.loads(args.transaction.read_text())
        target = authorize_target(transaction, args.fixture_fact_root)
        journal_root = args.journal_dir.resolve()
        if args.recover:
            if any(
                value is not None
                for value in (
                    args.bundle,
                    args.frontier,
                    args.execution,
                    args.before_fact,
                    args.trigger_bundle,
                )
            ):
                raise ApplyError("recovery accepts only transaction, journal, and target mode")
            require_recovery_intent(transaction, journal_root)
        else:
            if args.before_fact is None:
                raise ApplyError("initial apply requires --before-fact")
            derive_args = argparse.Namespace(
                fact=args.before_fact,
                bundle=args.bundle,
                frontier=args.frontier,
                execution=args.execution,
                trigger_bundle=args.trigger_bundle,
            )
            if (
                transaction.get("kind")
                == "axeyum-proposition-reconciliation-transaction-proposal"
            ):
                if any(
                    value is not None
                    for value in (
                        args.bundle,
                        args.frontier,
                        args.execution,
                        args.trigger_bundle,
                    )
                ):
                    raise ApplyError(
                        "reconciliation apply accepts only transaction, before-fact, journal, and target mode"
                    )
                expected = prepare.derive_proposition_reconciliation(transaction)
            else:
                expected = prepare.derive(derive_args)
            prepare.verify_transaction(transaction, expected)
            if (
                args.fixture_fact_root is None
                and args.before_fact.resolve() != target.resolve()
            ):
                raise ApplyError("production before-fact must be the authoritative target")
        event = apply_or_recover(
            transaction=transaction,
            target=target,
            journal_root=journal_root,
            fault_after=args.fault_after,
        )
        print(
            f"AUTOGENESIS_FACT_ADMISSION|transaction={transaction['transaction_sha256']}|"
            f"event={event['event_sha256']}|fact={transaction['identity']['fact_id']}|"
            f"state=committed|artifact_archived=false|git_published=false"
        )
        return 0
    except InjectedFault as error:
        print(f"AUTOGENESIS_FACT_ADMISSION_FAULT|{error}", file=sys.stderr)
        return 75
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ApplyError,
        prepare_error,
    ) as error:
        print(f"AUTOGENESIS_FACT_ADMISSION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
