#!/usr/bin/env python3
"""Derive or verify the frontier change caused by one durable admission event."""

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
APPLY_SCRIPT = ROOT / "scripts/apply-autogenesis-fact-transaction.py"


class ReadinessError(RuntimeError):
    """The durable event cannot justify the claimed readiness change."""


def load_apply_module():
    spec = importlib.util.spec_from_file_location(
        "apply_autogenesis_transaction_for_readiness", APPLY_SCRIPT
    )
    if spec is None or spec.loader is None:
        raise ReadinessError(f"cannot load {APPLY_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        facts[fact["id"]] = fact
    return facts


def build_delta(
    *,
    snapshot: dict[str, Any],
    transaction: dict[str, Any],
    admission_event: dict[str, Any],
    facts: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    snapshot_unsigned = dict(snapshot)
    snapshot_sha = snapshot_unsigned.pop("snapshot_sha256", None)
    if (
        snapshot.get("schema_version") != 1
        or snapshot.get("kind") != "axeyum-autogenesis-counterfactual"
        or not isinstance(snapshot_sha, str)
        or digest(snapshot_unsigned) != snapshot_sha
    ):
        raise ReadinessError("counterfactual snapshot digest or schema is invalid")

    apply_module = load_apply_module()
    try:
        apply_module.verify_content_addressed(
            transaction, "transaction_sha256", "transaction"
        )
    except apply_module.ApplyError as error:
        raise ReadinessError(str(error)) from error
    expected_event = apply_module.build_admission_event(transaction)
    if admission_event != expected_event:
        raise ReadinessError("durable admission event does not match transaction")
    try:
        apply_module.verify_content_addressed(
            admission_event, "event_sha256", "durable admission event"
        )
    except apply_module.ApplyError as error:
        raise ReadinessError(str(error)) from error

    chain = snapshot.get("chain")
    phases = snapshot.get("phases")
    if not isinstance(chain, dict) or not isinstance(phases, dict):
        raise ReadinessError("snapshot lacks chain or phase policy")
    premise_id = chain["premise"]["fact_id"]
    target_id = chain["consequent"]["fact_id"]
    identity = transaction.get("identity")
    event_identity = admission_event.get("identity")
    if not isinstance(identity, dict) or not isinstance(event_identity, dict):
        raise ReadinessError("transaction/event identity is malformed")
    if (
        identity.get("fact_id") != premise_id
        or event_identity.get("fact_id") != premise_id
        or event_identity.get("transaction_sha256")
        != transaction.get("transaction_sha256")
        or event_identity.get("after_fact_sha256")
        != identity.get("after_fact_sha256")
    ):
        raise ReadinessError("durable event admits a fact other than snapshot B")
    if target_id not in facts or premise_id not in facts:
        raise ReadinessError("snapshot chain fact is absent from the ledger")
    target_dependencies = facts[target_id].get("depends_on")
    if not isinstance(target_dependencies, list) or premise_id not in target_dependencies:
        raise ReadinessError("snapshot B is not a ledger dependency of target A")

    visible = phases["pre_a"].get("visible_fact_ids")
    if not isinstance(visible, list) or len(visible) != len(set(visible)):
        raise ReadinessError("pre-A visible fact set is malformed")
    settled_statuses = {"axiom", "proved", "computed", "refuted"}
    invalid_visible = [
        fact_id
        for fact_id in visible
        if fact_id not in facts
        or facts[fact_id].get("epistemic_status") not in settled_statuses
    ]
    if invalid_visible:
        raise ReadinessError(f"visible foundation is not established: {invalid_visible}")
    if premise_id in visible or target_id in visible:
        raise ReadinessError("counterfactual visible set exposes a withheld chain fact")

    before_established = sorted(visible)
    after_established = sorted([*visible, premise_id])
    before_missing = sorted(
        dependency
        for dependency in target_dependencies
        if dependency not in before_established
    )
    after_missing = sorted(
        dependency
        for dependency in target_dependencies
        if dependency not in after_established
    )
    if premise_id not in before_missing:
        raise ReadinessError("target A was already dependency-ready before B")
    if after_missing:
        raise ReadinessError(
            f"admitting B does not make target A dependency-ready: {after_missing}"
        )

    before_state = {
        "episode_id": snapshot["episode_id"],
        "established_fact_ids": before_established,
        "withheld_fact_ids": sorted(snapshot["withheld"]["fact_ids"]),
    }
    after_state = {
        "episode_id": snapshot["episode_id"],
        "established_fact_ids": after_established,
        "withheld_fact_ids": [target_id],
        "trigger_event_sha256": admission_event["event_sha256"],
    }
    delta: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-readiness-delta",
        "mode": "counterfactual-fixture",
        "identity": {
            "episode_id": snapshot["episode_id"],
            "snapshot_sha256": snapshot["snapshot_sha256"],
            "transaction_sha256": transaction["transaction_sha256"],
            "durable_admission_event_sha256": admission_event["event_sha256"],
            "before_state_sha256": digest(before_state),
            "after_state_sha256": digest(after_state),
        },
        "target": {
            "fact_id": target_id,
            "depends_on": target_dependencies,
            "before": {"eligible": False, "missing_dependencies": before_missing},
            "after": {"eligible": True, "missing_dependencies": []},
        },
        "newly_ready": [target_id],
        "cause": {
            "event_type": admission_event["event_type"],
            "admitted_fact_id": premise_id,
            "derived_dependency_edge": f"{premise_id} -> {target_id}",
        },
        "authoritative_ledger_writes": 0,
        "fixture_writes": 1,
    }
    delta["readiness_delta_sha256"] = digest(delta)
    return delta


def verify_delta(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("readiness_delta_sha256")
    unsigned = dict(actual)
    unsigned.pop("readiness_delta_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ReadinessError("readiness delta digest is missing or invalid")
    if actual.get("newly_ready") != [expected["target"]["fact_id"]]:
        raise ReadinessError("readiness delta claims the wrong newly-ready set")
    if actual != expected:
        raise ReadinessError("readiness delta is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--transaction", required=True, type=pathlib.Path)
    parser.add_argument("--durable-admission-event", required=True, type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = build_delta(
            snapshot=json.loads(args.snapshot.read_text()),
            transaction=json.loads(args.transaction.read_text()),
            admission_event=json.loads(args.durable_admission_event.read_text()),
            facts=load_facts(),
        )
        if args.verify is not None:
            verify_delta(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_READINESS_OK|{expected['readiness_delta_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise ReadinessError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_READINESS|{expected['readiness_delta_sha256']}|{output}")
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ReadinessError,
    ) as error:
        print(f"AUTOGENESIS_READINESS_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
