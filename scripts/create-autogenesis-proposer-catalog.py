#!/usr/bin/env python3
"""Create or verify a proof-body-free theorem catalog for an Autogenesis phase."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
BASELINE = ROOT / "docs/plan/generated/autogenesis-baseline.json"
SNAPSHOT_SCRIPT = ROOT / "scripts/create-autogenesis-snapshot.py"
EVENT_SCRIPT = ROOT / "scripts/create-autogenesis-accepted-event.py"
READINESS_SCRIPT = ROOT / "scripts/create-autogenesis-readiness-delta.py"


class CatalogError(RuntimeError):
    """The catalog cannot be derived or verified without guessing."""


def load_snapshot_module():
    spec = importlib.util.spec_from_file_location("create_autogenesis_snapshot", SNAPSHOT_SCRIPT)
    if spec is None or spec.loader is None:
        raise CatalogError(f"cannot load {SNAPSHOT_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_event_module():
    spec = importlib.util.spec_from_file_location(
        "create_autogenesis_accepted_event_for_catalog", EVENT_SCRIPT
    )
    if spec is None or spec.loader is None:
        raise CatalogError(f"cannot load {EVENT_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_readiness_module():
    spec = importlib.util.spec_from_file_location(
        "create_autogenesis_readiness_for_catalog", READINESS_SCRIPT
    )
    if spec is None or spec.loader is None:
        raise CatalogError(f"cannot load {READINESS_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def file_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_type_inventory(root: pathlib.Path) -> dict[str, dict[str, Any]]:
    process = subprocess.run(
        [
            "cargo",
            "run",
            "-q",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "nat_theorem_inventory",
        ],
        cwd=root,
        capture_output=True,
        text=True,
        timeout=1800,
        check=True,
    )
    inventory: dict[str, dict[str, Any]] = {}
    for line in process.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) != 3:
            raise CatalogError(f"malformed theorem inventory row: {line!r}")
        name, raw_arity, canonical_type = parts
        if name in inventory:
            raise CatalogError(f"duplicate theorem inventory name {name!r}")
        try:
            arity = int(raw_arity)
        except ValueError as error:
            raise CatalogError(f"invalid theorem arity in row: {line!r}") from error
        inventory[name] = {"arity": arity, "canonical_type": canonical_type}
    if len(inventory) < 100:
        raise CatalogError(
            f"theorem type inventory returned only {len(inventory)} rows; refusing a vacuous catalog"
        )
    return inventory


def statement_type(fact: dict[str, Any]) -> str:
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or " : " not in statement:
        raise CatalogError(f"{fact.get('id')}: formal.statement is not a theorem declaration")
    return statement.split(" : ", 1)[1]


def verify_snapshot_current(
    snapshot: dict[str, Any], root: pathlib.Path
) -> tuple[Any, dict[str, dict[str, Any]]]:
    module = load_snapshot_module()
    claimed = snapshot.get("snapshot_sha256")
    unsigned = dict(snapshot)
    unsigned.pop("snapshot_sha256", None)
    if claimed != module.digest(unsigned):
        raise CatalogError("snapshot_sha256 does not match the snapshot content")
    if snapshot.get("identity", {}).get("baseline_sha256") != file_digest(BASELINE):
        raise CatalogError("snapshot baseline digest is stale")
    try:
        facts, fact_hashes = module.load_facts(root)
        graph = module.dependency_inventory(root)
    except module.SnapshotError as error:
        raise CatalogError(f"cannot rederive snapshot inputs: {error}") from error
    chain = snapshot.get("chain") or {}
    try:
        premise_id = chain["premise"]["fact_id"]
        consequent_id = chain["consequent"]["fact_id"]
    except (KeyError, TypeError) as error:
        raise CatalogError("snapshot has no typed premise/consequent chain") from error
    try:
        expected = module.build_snapshot(
            premise_id=premise_id,
            consequent_id=consequent_id,
            facts=facts,
            fact_hashes=fact_hashes,
            graph=graph,
            baseline=json.loads(BASELINE.read_text()),
            baseline_sha256=file_digest(BASELINE),
        )
    except module.SnapshotError as error:
        raise CatalogError(f"cannot rederive snapshot: {error}") from error
    if snapshot != expected:
        raise CatalogError("snapshot is internally valid but stale against current inputs")
    return module, facts


def build_catalog(
    *,
    snapshot: dict[str, Any],
    phase: str,
    facts: dict[str, dict[str, Any]],
    inventory: dict[str, dict[str, Any]],
    accepted_event: dict[str, Any] | None = None,
    readiness_delta: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if phase not in {"pre_b", "pre_a", "post_b"}:
        raise CatalogError(f"unsupported phase {phase!r}")
    try:
        phase_policy = snapshot["phases"][phase]
        premise = snapshot["chain"]["premise"]
        consequent = snapshot["chain"]["consequent"]
    except (KeyError, TypeError) as error:
        raise CatalogError("snapshot does not contain the requested phase") from error
    visible = phase_policy.get("visible_retained_theorems")
    denied = phase_policy.get("denied_theorems")
    if not isinstance(visible, list) or not isinstance(denied, list):
        raise CatalogError("phase theorem policy is malformed")
    overlap = sorted(set(visible).intersection(denied))
    if overlap:
        raise CatalogError(f"visible and denied theorem sets overlap: {overlap}")
    missing = sorted(set(visible).union(denied).difference(inventory))
    if missing:
        raise CatalogError(f"theorem type inventory is missing policy names: {missing}")

    entries = [
        {
            "name": name,
            "arity": inventory[name]["arity"],
            "canonical_type": inventory[name]["canonical_type"],
            "origin": "retained-visible",
        }
        for name in sorted(visible)
    ]
    if phase != "post_b" and (accepted_event is not None or readiness_delta is not None):
        raise CatalogError("transition/readiness inputs are valid only for post_b")
    if phase == "pre_b":
        target = premise
    elif phase == "pre_a":
        target = consequent
    else:
        if accepted_event is None:
            raise CatalogError("post_b requires a verified accepted-transition event")
        if readiness_delta is None:
            raise CatalogError("post_b requires a durable-event readiness delta")
        verify_event_projection(snapshot, accepted_event)
        verify_readiness_projection(snapshot, readiness_delta)
        accepted = phase_policy.get("accepted_episode_facts")
        if not isinstance(accepted, list) or len(accepted) != 1:
            raise CatalogError("post_b must expose exactly one accepted episode fact")
        episode_premise = accepted[0]
        entries.append(
            {
                "name": episode_premise["declaration"],
                "arity": inventory[premise["retained_theorem"]]["arity"],
                "canonical_type": inventory[premise["retained_theorem"]]["canonical_type"],
                "origin": "accepted-episode",
                "source_fact_id": episode_premise["source_fact_id"],
            }
        )
        target = consequent

    target_fact = facts[target["fact_id"]]
    target_inventory = inventory[target["retained_theorem"]]
    target_type = target_inventory["canonical_type"]
    if statement_type(target_fact) != target_type:
        raise CatalogError(
            f"{target['fact_id']}: ledger formal statement disagrees with kernel type inventory"
        )
    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-proposer-catalog",
        "episode_id": snapshot["episode_id"],
        "phase": phase,
        "snapshot_sha256": snapshot["snapshot_sha256"],
        "theorem_type_inventory_sha256": digest(inventory),
        "proof_bodies_included": False,
        "denied_theorems": sorted(denied),
        "target": {
            "name": phase_policy["target_candidate"],
            "arity": target_inventory["arity"],
            "canonical_type": target_type,
            "source_fact_id": target["fact_id"],
        },
        "entries": sorted(entries, key=lambda entry: entry["name"]),
    }
    if accepted_event is not None:
        catalog["accepted_transition_event_sha256"] = accepted_event["event_sha256"]
        catalog["readiness_delta_sha256"] = readiness_delta["readiness_delta_sha256"]
    catalog["catalog_sha256"] = digest(catalog)
    return catalog


def verify_event_projection(
    snapshot: dict[str, Any], accepted_event: dict[str, Any]
) -> None:
    if (
        accepted_event.get("schema_version") != 1
        or accepted_event.get("kind")
        != "axeyum-autogenesis-accepted-transition-event"
        or accepted_event.get("event_type") != "episode-fact-accepted"
        or accepted_event.get("sequence") != 1
    ):
        raise CatalogError("post_b input is not the first accepted-fact event")
    claimed = accepted_event.get("event_sha256")
    unsigned = dict(accepted_event)
    unsigned.pop("event_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CatalogError("accepted-transition event digest is invalid")
    identity = accepted_event.get("identity")
    state_change = accepted_event.get("state_change")
    if not isinstance(identity, dict) or not isinstance(state_change, dict):
        raise CatalogError("accepted-transition event payload is malformed")
    premise_id = snapshot["chain"]["premise"]["fact_id"]
    if (
        identity.get("episode_id") != snapshot.get("episode_id")
        or identity.get("snapshot_sha256") != snapshot.get("snapshot_sha256")
        or identity.get("fact_id") != premise_id
    ):
        raise CatalogError("accepted-transition event identity does not match snapshot")
    if (
        state_change.get("from_phase") != "pre_b"
        or state_change.get("to_phase") != "post_b"
        or state_change.get("accepted_episode_facts")
        != snapshot["phases"]["post_b"].get("accepted_episode_facts")
    ):
        raise CatalogError("accepted-transition event does not authorize snapshot post_b")
    if accepted_event.get("authoritative_ledger_writes") != []:
        raise CatalogError("bootstrap accepted event contains ledger writes")


def verify_event_chain(
    *,
    snapshot: dict[str, Any],
    evidence: dict[str, Any],
    transition: dict[str, Any],
    accepted_event: dict[str, Any],
) -> None:
    module = load_event_module()
    try:
        expected = module.build_event(
            snapshot=snapshot, evidence=evidence, transition=transition
        )
        module.verify_event(accepted_event, expected)
    except module.EventError as error:
        raise CatalogError(f"accepted-transition event chain failed: {error}") from error
    verify_event_projection(snapshot, accepted_event)


def verify_readiness_projection(
    snapshot: dict[str, Any], readiness_delta: dict[str, Any]
) -> None:
    if (
        readiness_delta.get("schema_version") != 1
        or readiness_delta.get("kind") != "axeyum-autogenesis-readiness-delta"
    ):
        raise CatalogError("post_b input is not a readiness delta")
    claimed = readiness_delta.get("readiness_delta_sha256")
    unsigned = dict(readiness_delta)
    unsigned.pop("readiness_delta_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CatalogError("readiness delta digest is invalid")
    identity = readiness_delta.get("identity")
    target = readiness_delta.get("target")
    target_id = snapshot["chain"]["consequent"]["fact_id"]
    if (
        not isinstance(identity, dict)
        or identity.get("episode_id") != snapshot.get("episode_id")
        or identity.get("snapshot_sha256") != snapshot.get("snapshot_sha256")
        or not isinstance(target, dict)
        or target.get("fact_id") != target_id
        or target.get("after") != {"eligible": True, "missing_dependencies": []}
        or readiness_delta.get("newly_ready") != [target_id]
    ):
        raise CatalogError("readiness delta does not authorize snapshot target A")


def verify_readiness_chain(
    *,
    snapshot: dict[str, Any],
    transaction: dict[str, Any],
    durable_event: dict[str, Any],
    readiness_delta: dict[str, Any],
    facts: dict[str, dict[str, Any]],
) -> None:
    module = load_readiness_module()
    try:
        expected = module.build_delta(
            snapshot=snapshot,
            transaction=transaction,
            admission_event=durable_event,
            facts=facts,
        )
        module.verify_delta(readiness_delta, expected)
    except module.ReadinessError as error:
        raise CatalogError(f"durable readiness chain failed: {error}") from error
    verify_readiness_projection(snapshot, readiness_delta)


def verify_catalog(catalog: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = catalog.get("catalog_sha256")
    unsigned = dict(catalog)
    unsigned.pop("catalog_sha256", None)
    if claimed != digest(unsigned):
        raise CatalogError("catalog_sha256 does not match catalog content")
    forbidden_keys = {"proof", "proof_body", "value", "evidence", "checker_command"}
    entries = catalog.get("entries")
    if not isinstance(entries, list):
        raise CatalogError("catalog entries must be a list")
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise CatalogError(f"catalog entry {index} must be an object")
        leaked = forbidden_keys.intersection(entry)
        if leaked:
            raise CatalogError(f"catalog entry {index} contains proof-bearing keys: {sorted(leaked)}")
    if catalog != expected:
        raise CatalogError("catalog is internally valid but stale against current inputs")


def derive(
    snapshot_path: pathlib.Path,
    phase: str,
    *,
    premise_evidence_path: pathlib.Path | None = None,
    premise_transition_path: pathlib.Path | None = None,
    accepted_event_path: pathlib.Path | None = None,
    fact_transaction_path: pathlib.Path | None = None,
    durable_admission_event_path: pathlib.Path | None = None,
    readiness_delta_path: pathlib.Path | None = None,
) -> dict[str, Any]:
    snapshot = json.loads(snapshot_path.read_text())
    _module, facts = verify_snapshot_current(snapshot, ROOT)
    inventory = theorem_type_inventory(ROOT)
    accepted_event = None
    paths = (
        premise_evidence_path,
        premise_transition_path,
        accepted_event_path,
        fact_transaction_path,
        durable_admission_event_path,
        readiness_delta_path,
    )
    if phase == "post_b":
        if any(path is None for path in paths):
            raise CatalogError(
                "post_b requires evidence, transition, accepted event, transaction, durable event, and readiness delta"
            )
        evidence = json.loads(premise_evidence_path.read_text())
        transition = json.loads(premise_transition_path.read_text())
        accepted_event = json.loads(accepted_event_path.read_text())
        verify_event_chain(
            snapshot=snapshot,
            evidence=evidence,
            transition=transition,
            accepted_event=accepted_event,
        )
        transaction = json.loads(fact_transaction_path.read_text())
        durable_event = json.loads(durable_admission_event_path.read_text())
        readiness_delta = json.loads(readiness_delta_path.read_text())
        verify_readiness_chain(
            snapshot=snapshot,
            transaction=transaction,
            durable_event=durable_event,
            readiness_delta=readiness_delta,
            facts=facts,
        )
    elif any(path is not None for path in paths):
        raise CatalogError("accepted-transition inputs are valid only for post_b")
    return build_catalog(
        snapshot=snapshot,
        phase=phase,
        facts=facts,
        inventory=inventory,
        accepted_event=accepted_event,
        readiness_delta=readiness_delta if phase == "post_b" else None,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--phase", required=True, choices=("pre_b", "pre_a", "post_b"))
    parser.add_argument("--premise-evidence", type=pathlib.Path)
    parser.add_argument("--premise-transition", type=pathlib.Path)
    parser.add_argument("--accepted-transition-event", type=pathlib.Path)
    parser.add_argument("--fact-transaction", type=pathlib.Path)
    parser.add_argument("--durable-admission-event", type=pathlib.Path)
    parser.add_argument("--readiness-delta", type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(
            args.snapshot.resolve(),
            args.phase,
            premise_evidence_path=args.premise_evidence,
            premise_transition_path=args.premise_transition,
            accepted_event_path=args.accepted_transition_event,
            fact_transaction_path=args.fact_transaction,
            durable_admission_event_path=args.durable_admission_event,
            readiness_delta_path=args.readiness_delta,
        )
        if args.verify is not None:
            verify_catalog(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_CATALOG_OK|{expected['catalog_sha256']}|{args.verify.resolve()}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise CatalogError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_CATALOG|{expected['catalog_sha256']}|{output}")
        return 0
    except (OSError, json.JSONDecodeError, subprocess.CalledProcessError, CatalogError) as error:
        print(f"AUTOGENESIS_CATALOG_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
