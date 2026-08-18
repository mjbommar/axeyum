#!/usr/bin/env python3
"""Create or verify the episode-local transition that admits generated premise B."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from typing import Any


class TransitionError(RuntimeError):
    """The proposed transition is stale, malformed, or overclaims its effects."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def require_mapping(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise TransitionError(f"{label} must be an object")
    return value


def build_transition(
    *, snapshot: dict[str, Any], evidence: dict[str, Any]
) -> dict[str, Any]:
    if (
        snapshot.get("schema_version") != 1
        or snapshot.get("kind") != "axeyum-autogenesis-counterfactual"
    ):
        raise TransitionError("input is not a version-1 counterfactual snapshot")
    snapshot_unsigned = dict(snapshot)
    snapshot_digest = snapshot_unsigned.pop("snapshot_sha256", None)
    if not isinstance(snapshot_digest, str) or digest(snapshot_unsigned) != snapshot_digest:
        raise TransitionError("snapshot digest is missing or invalid")
    identity = require_mapping(evidence.get("identity"), "evidence identity")
    result = require_mapping(evidence.get("result"), "evidence result")
    acceptance = require_mapping(evidence.get("acceptance"), "evidence acceptance")
    if (
        evidence.get("schema_version") != 1
        or evidence.get("kind") != "axeyum-autogenesis-kernel-premise-evidence"
    ):
        raise TransitionError("input is not kernel premise evidence")
    evidence_unsigned = dict(evidence)
    evidence_digest = evidence_unsigned.pop("evidence_sha256", None)
    if not isinstance(evidence_digest, str) or digest(evidence_unsigned) != evidence_digest:
        raise TransitionError("premise evidence digest is missing or invalid")

    episode_id = snapshot.get("episode_id")
    snapshot_sha256 = snapshot.get("snapshot_sha256")
    premise = require_mapping(
        require_mapping(snapshot.get("chain"), "snapshot chain").get("premise"),
        "snapshot premise",
    )
    fact_id = premise.get("fact_id")
    if identity.get("episode_id") != episode_id:
        raise TransitionError("evidence episode does not match snapshot")
    if identity.get("snapshot_sha256") != snapshot_sha256:
        raise TransitionError("evidence names the wrong snapshot")
    if identity.get("fact_id") != fact_id:
        raise TransitionError("evidence names the wrong premise fact")
    if result.get("outcome") != "proved":
        raise TransitionError("only a proved premise can be admitted")
    if acceptance.get("independent_kernel_checked") is not True:
        raise TransitionError("premise was not independently kernel checked")
    if acceptance.get("axiom_footprint") != []:
        raise TransitionError("premise has a non-empty axiom footprint")
    if acceptance.get("retained_answer_dependencies") != []:
        raise TransitionError("premise depends on a retained answer")

    phases = require_mapping(snapshot.get("phases"), "snapshot phases")
    pre_b = require_mapping(phases.get("pre_b"), "pre_b phase")
    post_b = require_mapping(phases.get("post_b"), "post_b phase")
    if pre_b.get("target_candidate") != result.get("declaration"):
        raise TransitionError("pre_b target does not match proved declaration")
    if pre_b.get("accepted_episode_facts", []) != []:
        raise TransitionError("pre_b already contains an accepted episode fact")
    accepted = post_b.get("accepted_episode_facts")
    if not isinstance(accepted, list) or len(accepted) != 1:
        raise TransitionError("post_b must contain exactly one accepted episode fact")
    accepted_fact = require_mapping(accepted[0], "accepted episode fact")
    expected_fact = {
        "declaration": result.get("declaration"),
        "role": "premise",
        "source_fact_id": fact_id,
    }
    if accepted_fact != expected_fact:
        raise TransitionError("accepted episode fact does not match kernel evidence")
    if post_b.get("required_dependencies") != [result.get("declaration")]:
        raise TransitionError("post_b does not require exactly the admitted premise")

    withheld = require_mapping(snapshot.get("withheld"), "snapshot withheld set")
    denied = withheld.get("retained_theorems")
    if not isinstance(denied, list) or not denied:
        raise TransitionError("snapshot withholds no retained theorem answers")
    for phase_name, phase in (("pre_b", pre_b), ("post_b", post_b)):
        if phase.get("denied_theorems") != denied:
            raise TransitionError(f"{phase_name} denied theorem set drifted")
        visible = phase.get("visible_retained_theorems")
        if not isinstance(visible, list) or set(denied).intersection(visible):
            raise TransitionError(f"{phase_name} exposes a retained theorem answer")

    fact_identity = require_mapping(
        require_mapping(
            require_mapping(snapshot.get("identity"), "snapshot identity").get("facts"),
            "snapshot fact identities",
        ).get("premise"),
        "snapshot premise identity",
    )
    if fact_identity.get("id") != fact_id or not isinstance(
        fact_identity.get("sha256"), str
    ):
        raise TransitionError("snapshot premise content identity is invalid")

    transition: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-episode-premise-transition",
        "identity": {
            "episode_id": episode_id,
            "snapshot_sha256": snapshot_sha256,
            "fact_id": fact_id,
            "premise_evidence_sha256": evidence_digest,
        },
        "before": {
            "phase": "pre_b",
            "premise_available": False,
            "accepted_episode_facts": [],
        },
        "after": {
            "phase": "post_b",
            "premise_available": True,
            "accepted_episode_facts": [accepted_fact],
        },
        "authoritative_ledger": {
            "mode": "unchanged-bootstrap-source",
            "source_fact": fact_identity,
            "writes": [],
        },
        "controls": {
            "denied_retained_theorems": denied,
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
        },
    }
    transition["transition_sha256"] = digest(transition)
    return transition


def verify_transition(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("transition_sha256")
    unsigned = dict(actual)
    unsigned.pop("transition_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise TransitionError("transition digest is missing or invalid")
    ledger = actual.get("authoritative_ledger")
    if not isinstance(ledger, dict) or ledger.get("writes") != []:
        raise TransitionError("bootstrap transition must contain zero ledger writes")
    if actual != expected:
        raise TransitionError("premise transition is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--premise-evidence", required=True, type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        snapshot = json.loads(args.snapshot.read_text())
        evidence = json.loads(args.premise_evidence.read_text())
        expected = build_transition(snapshot=snapshot, evidence=evidence)
        if args.verify is not None:
            verify_transition(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_PREMISE_TRANSITION_OK|{expected['transition_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise TransitionError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_PREMISE_TRANSITION|{expected['transition_sha256']}|{output}")
        return 0
    except (OSError, json.JSONDecodeError, KeyError, TypeError, TransitionError) as error:
        print(f"AUTOGENESIS_PREMISE_TRANSITION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
