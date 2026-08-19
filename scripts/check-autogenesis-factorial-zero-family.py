#!/usr/bin/env python3
"""Verify the exact two-member proof-free factorial-zero operation family."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import re
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-factorial-zero-family-v1.json"
REGISTRY = ROOT / "artifacts/autogenesis/operations.json"
COVERAGE = ROOT / "artifacts/autogenesis/mathlib-reflexivity-coverage-v1.json"
REGISTRY_CHECKER = ROOT / "scripts/validate-autogenesis-operations.py"
REFLEXIVITY_CHECKER = ROOT / "scripts/check-autogenesis-statement-reflexivity.py"
MEMBER_FIELDS = {
    "fact_id",
    "operation_id",
    "authoritative_adapter_manifest",
    "reflexivity_manifest",
    "family_target_definition",
    "family_external_artifact",
    "goal_sha256",
    "proof_sha256",
    "target_content_sha256",
    "admitted_declarations",
}
EXPECTED_FACTS = [
    "F:ml430-nat-ascfactorial-zero-fd183202",
    "F:ml430-nat-descfactorial-zero-966b01df",
]


class FamilyError(RuntimeError):
    """The family no longer has its exact proof-isolated checked meaning."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise FamilyError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise FamilyError(f"expected JSON object: {path}")
    return value


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def exact_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    if set(value) != expected:
        raise FamilyError(f"{label} fields differ")


def validate_structure(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    exact_keys(
        manifest,
        {
            "schema_version",
            "kind",
            "state",
            "source",
            "population",
            "members",
            "reproduction",
            "limitations",
        },
        "family manifest",
    )
    if (
        manifest["schema_version"] != 1
        or manifest["kind"]
        != "axeyum-autogenesis-mathlib-factorial-zero-family"
        or manifest["state"] != "two-target-proof-isolated-reflexivity-checked"
    ):
        raise FamilyError("family schema identity or state changed")
    source = manifest["source"]
    population = manifest["population"]
    exact_keys(source, {"path", "sha256", "proof_declarations_allowed"}, "source")
    exact_keys(
        population,
        {
            "partition",
            "members",
            "held_out_inspected",
            "proof_bodies_requested",
        },
        "population",
    )
    if (
        source["proof_declarations_allowed"] is not False
        or population
        != {
            "partition": "train",
            "members": 2,
            "held_out_inspected": False,
            "proof_bodies_requested": False,
        }
    ):
        raise FamilyError("family isolation or population boundary changed")
    members = manifest["members"]
    if not isinstance(members, list) or len(members) != 2:
        raise FamilyError("family must contain exactly two members")
    for index, member in enumerate(members):
        if not isinstance(member, dict):
            raise FamilyError(f"member {index} is not an object")
        exact_keys(member, MEMBER_FIELDS, f"member {index}")
    if [member["fact_id"] for member in members] != EXPECTED_FACTS:
        raise FamilyError("family fact membership or order changed")
    if len({member["operation_id"] for member in members}) != 2:
        raise FamilyError("family operations are not independently exact-bound")
    return members


def validate_source(manifest: dict[str, Any]) -> None:
    source = manifest["source"]
    path = ROOT / source["path"]
    if not path.is_file() or sha256(path) != source["sha256"]:
        raise FamilyError("tracked proof-free family source changed")
    text = path.read_text()
    forbidden = re.findall(r"(?m)^\s*(?:axiom|theorem|opaque|example)\b", text)
    definitions = re.findall(r"(?m)^\s*def\s+([A-Za-z0-9_']+)\s*:", text)
    if forbidden or definitions != ["natAscFactorialZero", "natDescFactorialZero"]:
        raise FamilyError("family source is no longer exactly two proof-free definitions")


def validate_external(external: dict[str, Any]) -> pathlib.Path:
    exact_keys(external, {"path", "sha256", "bytes", "records", "mode"}, "external")
    path = pathlib.Path(external["path"])
    if (
        not path.is_file()
        or path.stat().st_size != external["bytes"]
        or sha256(path) != external["sha256"]
        or sum(1 for _ in path.open("rb")) != external["records"]
        or stat.S_IMODE(path.stat().st_mode) != int(external["mode"], 8)
    ):
        raise FamilyError(f"external family stream changed: {path}")
    return path


def expected_receipt(member: dict[str, Any]) -> dict[str, str]:
    return {
        "target": member["family_target_definition"],
        "goal_sha256": member["goal_sha256"],
        "proof_sha256": member["proof_sha256"],
        "target_content_sha256": member["target_content_sha256"],
        "binders": "1",
        "constructed_nodes": "4",
        "max_binders": "8",
        "max_nodes": "16",
        "declarations": str(member["admitted_declarations"]),
        "axioms": "0",
        "theorem_dependencies": "0",
        "target_dependency": "false",
        "ledger_writes": "0",
    }


def validate_member_receipt(member: dict[str, Any], receipt: dict[str, str]) -> None:
    expected = expected_receipt(member)
    if {key: receipt.get(key) for key in expected} != expected:
        raise FamilyError("family reflexivity receipt changed")
    if hashlib.sha256(receipt["goal"].encode()).hexdigest() != member["goal_sha256"]:
        raise FamilyError("family rendered goal changed")
    if hashlib.sha256(receipt["proof"].encode()).hexdigest() != member["proof_sha256"]:
        raise FamilyError("family rendered proof changed")


def validate_credit(member: dict[str, Any], fact: dict[str, Any]) -> str:
    if fact.get("epistemic_status") == "open" and fact.get("evidence") == []:
        if "proof_route" in fact or "axiom_footprint" in fact:
            raise FamilyError("open family fact carries admission fields")
        return "open"
    rows = fact.get("evidence")
    if (
        fact.get("epistemic_status") != "proved"
        or fact.get("proof_route") != "kernel-lean"
        or fact.get("axiom_footprint") != []
        or not isinstance(rows, list)
        or len(rows) != 1
    ):
        raise FamilyError("family fact credit state is malformed")
    binding = rows[0].get("checker_operation")
    if (
        not isinstance(binding, dict)
        or binding.get("id") != member["operation_id"]
        or binding.get("reflexivity_manifest") != member["reflexivity_manifest"]
        or binding.get("proof_sha256") != member["proof_sha256"]
        or rows[0].get("check_status") != "checked"
    ):
        raise FamilyError("settled family fact is not bound to its exact operation")
    return "proved"


def validate() -> tuple[list[dict[str, Any]], list[str]]:
    manifest = load(MANIFEST)
    members = validate_structure(manifest)
    validate_source(manifest)
    registry_checker = load_module("factorial_zero_registry", REGISTRY_CHECKER)
    reflexivity_checker = load_module("factorial_zero_reflexivity", REFLEXIVITY_CHECKER)
    try:
        registry = registry_checker.load_registry(REGISTRY, ROOT)
    except registry_checker.RegistryError as error:
        raise FamilyError(f"operation registry is invalid: {error}") from error
    operations = {operation["id"]: operation for operation in registry["operations"]}
    coverage = load(COVERAGE)
    if coverage.get("population", {}).get("held_out_inspected") is not False:
        raise FamilyError("coverage no longer proves held-out isolation")
    coverage_rows = {
        row["fact_id"]: row for row in coverage.get("admissible_proofs", [])
    }
    credit_states: list[str] = []
    for member in members:
        fact = load(
            ROOT
            / "artifacts/facts"
            / (member["fact_id"].replace("F:", "F-") + ".json")
        )
        credit_states.append(validate_credit(member, fact))
        adapter = load(ROOT / member["authoritative_adapter_manifest"])
        reflexivity = load(ROOT / member["reflexivity_manifest"])
        operation = operations.get(member["operation_id"])
        coverage_row = coverage_rows.get(member["fact_id"])
        if (
            fact.get("id") != member["fact_id"]
            or adapter.get("source_fact_id") != member["fact_id"]
            or reflexivity.get("source_fact_id") != member["fact_id"]
            or reflexivity.get("statement_adapter")
            != member["authoritative_adapter_manifest"]
            or reflexivity.get("operation", {}).get("goal_sha256")
            != member["goal_sha256"]
            or reflexivity.get("operation", {}).get("proof_sha256")
            != member["proof_sha256"]
            or not isinstance(operation, dict)
            or operation.get("scope") != "authoritative"
            or operation.get("applicability", {}).get("fact_ids")
            != [member["fact_id"]]
            or operation.get("executor", {}).get("statement_adapter_manifest")
            != member["authoritative_adapter_manifest"]
            or operation.get("executor", {}).get("reflexivity_manifest")
            != member["reflexivity_manifest"]
            or not isinstance(coverage_row, dict)
            or coverage_row.get("goal_sha256") != member["goal_sha256"]
            or coverage_row.get("proof_sha256") != member["proof_sha256"]
            or coverage_row.get("axioms") != 0
            or coverage_row.get("theorem_dependencies") != 0
            or coverage_row.get("target_dependency") is not False
        ):
            raise FamilyError(f"exact member contract changed: {member['fact_id']}")
        artifact = validate_external(member["family_external_artifact"])
        completed = subprocess.run(
            [
                "cargo",
                "run",
                "-q",
                "-p",
                "axeyum-lean-import",
                "--example",
                "statement_reflexivity_operation",
                "--",
                str(artifact),
                member["family_target_definition"],
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if completed.returncode != 0:
            raise FamilyError(
                f"family member replay failed: {completed.stderr.strip()}"
            )
        receipt = reflexivity_checker.parse_receipt(completed.stdout.rstrip("\n"))
        validate_member_receipt(member, receipt)
    return members, credit_states


def main() -> int:
    try:
        members, credit_states = validate()
        print(
            "AUTOGENESIS_FACTORIAL_ZERO_FAMILY_OK|"
            f"members={len(members)}|credit={','.join(credit_states)}|"
            "held_out=0|proof_bodies=0|axioms=0|theorem_dependencies=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
        FamilyError,
    ) as error:
        print(f"AUTOGENESIS_FACTORIAL_ZERO_FAMILY_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
