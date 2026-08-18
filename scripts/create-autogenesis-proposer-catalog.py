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


class CatalogError(RuntimeError):
    """The catalog cannot be derived or verified without guessing."""


def load_snapshot_module():
    spec = importlib.util.spec_from_file_location("create_autogenesis_snapshot", SNAPSHOT_SCRIPT)
    if spec is None or spec.loader is None:
        raise CatalogError(f"cannot load {SNAPSHOT_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def file_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_type_inventory(root: pathlib.Path) -> dict[str, str]:
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
    inventory: dict[str, str] = {}
    for line in process.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) != 3:
            raise CatalogError(f"malformed theorem inventory row: {line!r}")
        name, _arity, canonical_type = parts
        if name in inventory:
            raise CatalogError(f"duplicate theorem inventory name {name!r}")
        inventory[name] = canonical_type
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
    inventory: dict[str, str],
) -> dict[str, Any]:
    if phase not in {"pre_b", "post_b"}:
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
        {"name": name, "canonical_type": inventory[name], "origin": "retained-visible"}
        for name in sorted(visible)
    ]
    if phase == "pre_b":
        target = premise
    else:
        accepted = phase_policy.get("accepted_episode_facts")
        if not isinstance(accepted, list) or len(accepted) != 1:
            raise CatalogError("post_b must expose exactly one accepted episode fact")
        episode_premise = accepted[0]
        entries.append(
            {
                "name": episode_premise["declaration"],
                "canonical_type": inventory[premise["retained_theorem"]],
                "origin": "accepted-episode",
                "source_fact_id": episode_premise["source_fact_id"],
            }
        )
        target = consequent

    target_fact = facts[target["fact_id"]]
    target_type = inventory[target["retained_theorem"]]
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
            "canonical_type": target_type,
            "source_fact_id": target["fact_id"],
        },
        "entries": sorted(entries, key=lambda entry: entry["name"]),
    }
    catalog["catalog_sha256"] = digest(catalog)
    return catalog


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


def derive(snapshot_path: pathlib.Path, phase: str) -> dict[str, Any]:
    snapshot = json.loads(snapshot_path.read_text())
    _module, facts = verify_snapshot_current(snapshot, ROOT)
    inventory = theorem_type_inventory(ROOT)
    return build_catalog(snapshot=snapshot, phase=phase, facts=facts, inventory=inventory)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=pathlib.Path)
    parser.add_argument("--phase", required=True, choices=("pre_b", "post_b"))
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(args.snapshot.resolve(), args.phase)
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
