#!/usr/bin/env python3
"""Create or verify the event emitted when an episode-local premise is accepted."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
TRANSITION_SCRIPT = ROOT / "scripts/create-autogenesis-premise-transition.py"


class EventError(RuntimeError):
    """The accepted-transition event is malformed, stale, or unsupported."""


def load_transition_module():
    spec = importlib.util.spec_from_file_location(
        "autogenesis_transition_for_event", TRANSITION_SCRIPT
    )
    if spec is None or spec.loader is None:
        raise EventError(f"cannot load {TRANSITION_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def build_event(
    *,
    snapshot: dict[str, Any],
    evidence: dict[str, Any],
    transition: dict[str, Any],
) -> dict[str, Any]:
    transition_module = load_transition_module()
    try:
        expected_transition = transition_module.build_transition(
            snapshot=snapshot, evidence=evidence
        )
        transition_module.verify_transition(transition, expected_transition)
    except transition_module.TransitionError as error:
        raise EventError(f"premise transition verification failed: {error}") from error

    identity = transition["identity"]
    accepted = transition["after"]["accepted_episode_facts"]
    if len(accepted) != 1:
        raise EventError("accepted transition must contain exactly one episode fact")
    event: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-accepted-transition-event",
        "event_type": "episode-fact-accepted",
        "sequence": 1,
        "identity": {
            "episode_id": identity["episode_id"],
            "snapshot_sha256": identity["snapshot_sha256"],
            "fact_id": identity["fact_id"],
            "premise_evidence_sha256": identity["premise_evidence_sha256"],
            "transition_sha256": transition["transition_sha256"],
        },
        "state_change": {
            "from_phase": transition["before"]["phase"],
            "to_phase": transition["after"]["phase"],
            "accepted_episode_facts": accepted,
        },
        "authoritative_ledger_writes": [],
    }
    event["event_sha256"] = digest(event)
    return event


def verify_event(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("event_sha256")
    unsigned = dict(actual)
    unsigned.pop("event_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise EventError("accepted event digest is missing or invalid")
    if actual.get("authoritative_ledger_writes") != []:
        raise EventError("bootstrap accepted event must contain zero ledger writes")
    if actual != expected:
        raise EventError("accepted event is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--premise-evidence", required=True, type=pathlib.Path)
    parser.add_argument("--premise-transition", required=True, type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        snapshot = json.loads(args.snapshot.read_text())
        evidence = json.loads(args.premise_evidence.read_text())
        transition = json.loads(args.premise_transition.read_text())
        expected = build_event(
            snapshot=snapshot, evidence=evidence, transition=transition
        )
        if args.verify is not None:
            verify_event(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_ACCEPTED_EVENT_OK|{expected['event_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise EventError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_ACCEPTED_EVENT|{expected['event_sha256']}|{output}")
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        EventError,
    ) as error:
        print(f"AUTOGENESIS_ACCEPTED_EVENT_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
