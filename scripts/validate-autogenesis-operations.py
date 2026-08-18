#!/usr/bin/env python3
"""Validate the typed Autogenesis producer/checker operation registry."""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "artifacts/autogenesis/operations.json"
ID_RE = re.compile(r"^[a-z0-9]+(?:[a-z0-9./-]*[a-z0-9])?$")
FACT_ID_RE = re.compile(r"^F:[a-z0-9]+(?:-[a-z0-9]+)*$")
SCOPES = {"counterfactual-fixture-only", "authoritative"}
ADMISSION_CONTRACTS = {
    ("proved", "kernel-lean", "kernel-term", "must-be-empty"),
    (
        "proved",
        "smt-term-level",
        "unsat-certificate",
        "must-be-nonempty",
    ),
}


class RegistryError(RuntimeError):
    """The operation registry is malformed or grants ambiguous authority."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def exact_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    missing = sorted(expected.difference(value))
    extra = sorted(set(value).difference(expected))
    if missing or extra:
        raise RegistryError(f"{label} fields differ: missing={missing}, extra={extra}")


def nonempty_strings(value: Any, label: str) -> list[str]:
    if (
        not isinstance(value, list)
        or not value
        or any(not isinstance(item, str) or not item for item in value)
        or len(value) != len(set(value))
    ):
        raise RegistryError(f"{label} must be a nonempty unique string list")
    return value


def validate_endpoint(value: Any, label: str, root: pathlib.Path) -> None:
    if not isinstance(value, dict):
        raise RegistryError(f"{label} must be an object")
    exact_keys(
        value,
        {"operation", "implementation", "input_kind", "output_kind"},
        label,
    )
    for key, item in value.items():
        if not isinstance(item, str) or not item:
            raise RegistryError(f"{label}.{key} must be a nonempty string")
    if not ID_RE.fullmatch(value["operation"]):
        raise RegistryError(f"{label}.operation is not a stable operation id")
    implementation = pathlib.PurePosixPath(value["implementation"])
    if implementation.is_absolute() or ".." in implementation.parts:
        raise RegistryError(f"{label}.implementation must be repository-relative")
    resolved_root = root.resolve()
    resolved = (root / implementation).resolve()
    if not resolved.is_relative_to(resolved_root):
        raise RegistryError(f"{label}.implementation escapes the repository")
    if not resolved.is_file():
        raise RegistryError(f"{label}.implementation does not exist: {implementation}")


def validate_registry(registry: Any, root: pathlib.Path = ROOT) -> None:
    if not isinstance(registry, dict):
        raise RegistryError("registry must be an object")
    exact_keys(registry, {"schema_version", "kind", "operations"}, "registry")
    if (
        registry["schema_version"] != 1
        or registry["kind"] != "axeyum-autogenesis-operation-registry"
    ):
        raise RegistryError("registry schema version or kind is unsupported")
    operations = registry["operations"]
    if not isinstance(operations, list):
        raise RegistryError("operations must be a list")
    seen: set[str] = set()
    for index, operation in enumerate(operations):
        label = f"operations[{index}]"
        if not isinstance(operation, dict):
            raise RegistryError(f"{label} must be an object")
        exact_keys(
            operation,
            {"id", "scope", "applicability", "producer", "checker", "admission"},
            label,
        )
        operation_id = operation["id"]
        if not isinstance(operation_id, str) or not ID_RE.fullmatch(operation_id):
            raise RegistryError(f"{label}.id is not a stable operation id")
        if operation_id in seen:
            raise RegistryError(f"duplicate operation id {operation_id!r}")
        seen.add(operation_id)
        if operation["scope"] not in SCOPES:
            raise RegistryError(f"{label}.scope is unsupported")
        applicability = operation["applicability"]
        if not isinstance(applicability, dict):
            raise RegistryError(f"{label}.applicability must be an object")
        exact_keys(
            applicability,
            {"fact_ids", "formal_languages", "fragments"},
            f"{label}.applicability",
        )
        fact_ids = nonempty_strings(
            applicability["fact_ids"], f"{label}.applicability.fact_ids"
        )
        nonempty_strings(
            applicability["formal_languages"],
            f"{label}.applicability.formal_languages",
        )
        fragments = nonempty_strings(
            applicability["fragments"], f"{label}.applicability.fragments"
        )
        languages = applicability["formal_languages"]
        for fact_id in fact_ids:
            if not FACT_ID_RE.fullmatch(fact_id):
                raise RegistryError(f"{label} has invalid fact id {fact_id!r}")
            fact_path = root / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json")
            if not fact_path.is_file():
                raise RegistryError(f"{label} fact does not exist: {fact_id}")
            fact = json.loads(fact_path.read_text())
            formal = fact.get("formal") or {}
            if formal.get("language") not in languages or formal.get("fragment") not in fragments:
                raise RegistryError(f"{label} applicability does not match {fact_id}")
        validate_endpoint(operation["producer"], f"{label}.producer", root)
        validate_endpoint(operation["checker"], f"{label}.checker", root)
        admission = operation["admission"]
        if not isinstance(admission, dict):
            raise RegistryError(f"{label}.admission must be an object")
        exact_keys(
            admission,
            {"epistemic_status", "proof_route", "evidence_kind", "axiom_footprint_policy"},
            f"{label}.admission",
        )
        admission_contract = (
            admission["epistemic_status"],
            admission["proof_route"],
            admission["evidence_kind"],
            admission["axiom_footprint_policy"],
        )
        if admission_contract not in ADMISSION_CONTRACTS:
            raise RegistryError(f"{label}.admission is outside the v1 contract")
        if operation["scope"] == "authoritative":
            for fact_id in fact_ids:
                fact_path = root / "artifacts/facts" / (
                    fact_id.replace("F:", "F-") + ".json"
                )
                fact = json.loads(fact_path.read_text())
                if fact.get("epistemic_status") not in {
                    "open",
                    "conjectured",
                    "empirical",
                }:
                    raise RegistryError(
                        f"{label} grants authoritative scope to settled fact {fact_id}"
                    )


def load_registry(
    path: pathlib.Path = REGISTRY, root: pathlib.Path = ROOT
) -> dict[str, Any]:
    registry = json.loads(path.read_text())
    validate_registry(registry, root)
    return registry


def main() -> int:
    try:
        registry = load_registry()
        print(
            f"AUTOGENESIS_OPERATIONS_OK|operations={len(registry['operations'])}|"
            f"registry={digest(registry)}"
        )
        return 0
    except (OSError, json.JSONDecodeError, RegistryError) as error:
        print(f"AUTOGENESIS_OPERATIONS_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
