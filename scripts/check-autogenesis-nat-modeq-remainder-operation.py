#!/usr/bin/env python3
"""Freshly replay the registered 3-target imported Nat.mod operation."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/nat-modeq-remainder-contract-v2.json"
REGISTRY = ROOT / "artifacts/autogenesis/operations.json"
OPERATION_ID = "authoritative-mathlib-nat-modeq-remainder-family-v1"
DRIVER = "axeyum-lean-import/imported-candidate-family-multi-target-v1"


class RemainderOperationError(RuntimeError):
    """The registered operation no longer reproduces its checked receipt."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RemainderOperationError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise RemainderOperationError(f"expected JSON object: {path}")
    return value


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_external(row: dict[str, Any]) -> pathlib.Path:
    path = pathlib.Path(row["path"])
    if (
        not path.is_file()
        or path.stat().st_size != row["bytes"]
        or sha256_file(path) != row["sha256"]
        or sum(1 for _ in path.open("rb")) != row["records"]
        or stat.S_IMODE(path.stat().st_mode) != int(row["mode"], 8)
    ):
        raise RemainderOperationError(f"external input changed or is absent: {path}")
    return path


def parse_receipt(stdout: str) -> dict[str, str]:
    lines = [line for line in stdout.splitlines() if line]
    if len(lines) != 1 or not lines[0].startswith("IMPORTED_CANDIDATE_TRANSPORT|result=accepted|"):
        raise RemainderOperationError("transport probe emitted an invalid receipt shape")
    fields: dict[str, str] = {}
    for item in lines[0].split("|")[1:]:
        if "=" not in item:
            raise RemainderOperationError("receipt field lacks '='")
        key, value = item.split("=", 1)
        if not key or key in fields or not value:
            raise RemainderOperationError("receipt fields are empty or duplicated")
        fields[key] = value
    return fields


def checked_manifest() -> dict[str, Any]:
    checker = load_module(
        "nat_modeq_remainder_contract_v2",
        ROOT / "scripts/check-autogenesis-nat-modeq-remainder-contract-v2.py",
    )
    return checker.validate()


def target_contract(fact_id: str) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    manifest = checked_manifest()
    outcomes = [row for row in manifest["outcomes"] if row["fact_id"] == fact_id]
    targets = [
        row
        for row in manifest["external_inputs"]
        if row.get("role") == "proof-free-target" and row.get("fact_id") == fact_id
    ]
    candidates = [row for row in manifest["external_inputs"] if row.get("role") == "candidate-family"]
    if len(outcomes) != 1 or len(targets) != 1 or len(candidates) != 1:
        raise RemainderOperationError(f"{fact_id}: manifest target resolution is ambiguous")
    return outcomes[0], targets[0], candidates[0]


def check_target(target: dict[str, Any], max_binders: int) -> dict[str, Any]:
    fact_id = target["fact_id"]
    outcome, target_input, candidate_input = target_contract(fact_id)
    if target.get("target_definition") != outcome["target_definition"] or max_binders != 2:
        raise RemainderOperationError(f"{fact_id}: registered target contract changed")
    target_path = validate_external(target_input)
    candidate_path = validate_external(candidate_input)
    roots = checked_manifest()["contract_source"]["candidate_roots"]
    completed = subprocess.run(
        [
            "cargo", "run", "--release", "-q", "-p", "axeyum-lean-import",
            "--example", "imported_candidate_transport_probe", "--",
            str(target_path), target["target_definition"], str(candidate_path), *roots,
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    if completed.returncode != 0:
        raise RemainderOperationError(f"{fact_id}: replay failed: {completed.stderr.strip()}")
    receipt = parse_receipt(completed.stdout)
    expected = {
        "result": "accepted",
        "target": target["target_definition"],
        "roots": "3",
        "transported": "3",
        "added": "2",
        "reused": "1",
        "transport_declines": "0",
        "binders_used": str(outcome["binders_used"]),
        "application_depth": str(outcome["application_depth"]),
        "terms_considered": str(outcome["terms_considered"]),
        "declarations": str(outcome["admitted_declarations"]),
        "axioms": "0",
        "theorem_dependencies": "1",
        "target_dependency": "false",
        "goal_sha256": outcome["goal_sha256"],
        "proof_sha256": outcome["proof_sha256"],
        "target_content_sha256": outcome["target_content_sha256"],
    }
    if receipt != expected:
        raise RemainderOperationError(f"{fact_id}: replayed receipt disagrees")
    return outcome


def load_operation() -> dict[str, Any]:
    validator = load_module(
        "nat_modeq_remainder_operation_registry",
        ROOT / "scripts/validate-autogenesis-operations.py",
    )
    registry = validator.load_registry(REGISTRY, ROOT)
    matches = [row for row in registry["operations"] if row["id"] == OPERATION_ID]
    if len(matches) != 1:
        raise RemainderOperationError("authoritative operation is not registered exactly once")
    return matches[0]


def validate() -> dict[str, Any]:
    operation = load_operation()
    executor = operation["executor"]
    if (
        operation.get("scope") != "authoritative"
        or executor.get("driver") != DRIVER
        or executor.get("receipt_manifest") != MANIFEST.relative_to(ROOT).as_posix()
        or executor.get("max_binders") != 2
    ):
        raise RemainderOperationError("registered operation boundary changed")
    targets = executor.get("targets", [])
    if len(targets) != 3 or {row.get("fact_id") for row in targets} != set(operation["applicability"]["fact_ids"]):
        raise RemainderOperationError("registered target population changed")
    for target in targets:
        check_target(target, executor["max_binders"])
    return operation


def main() -> None:
    validate()
    print("nat-modeq-remainder-operation: ok (3 targets freshly replayed, registration only)")


if __name__ == "__main__":
    main()
