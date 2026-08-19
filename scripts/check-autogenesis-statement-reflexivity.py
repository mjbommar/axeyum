#!/usr/bin/env python3
"""Verify the bounded reflexivity candidate without granting ledger credit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-statement-reflexivity-v1.json"


class ReflexivityError(RuntimeError):
    """The reflexivity evidence no longer matches its checked boundary."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ReflexivityError(f"{path.relative_to(ROOT)} is not an object")
    return value


def load_manifest(path: pathlib.Path = MANIFEST) -> dict[str, Any]:
    value = load(path)
    if (
        value.get("schema_version") != 1
        or value.get("kind") != "axeyum-autogenesis-mathlib-statement-reflexivity"
        or value.get("state") != "candidate-checked-not-admitted"
    ):
        raise ReflexivityError("manifest schema identity or state is invalid")
    return value


def parse_receipt(stdout: str) -> dict[str, str]:
    lines = stdout.splitlines()
    if (
        len(lines) != 3
        or not lines[0].startswith("STATEMENT_REFLEXIVITY_OK|")
        or not lines[1].startswith("GOAL|")
        or not lines[2].startswith("PROOF|")
    ):
        raise ReflexivityError("reflexivity operation emitted an invalid receipt shape")
    fields: dict[str, str] = {}
    for item in lines[0].split("|")[1:]:
        if "=" not in item:
            raise ReflexivityError("receipt field lacks '='")
        key, value = item.split("=", 1)
        if not key or key in fields or not value:
            raise ReflexivityError("receipt fields are empty or duplicated")
        fields[key] = value
    fields["goal"] = lines[1].removeprefix("GOAL|")
    fields["proof"] = lines[2].removeprefix("PROOF|")
    return fields


def validate_receipt(manifest: dict[str, Any], receipt: dict[str, str]) -> None:
    operation = manifest["operation"]
    exact = {
        "target": operation["target_definition"],
        "goal_sha256": operation["goal_sha256"],
        "proof_sha256": operation["proof_sha256"],
        "target_content_sha256": operation["target_content_sha256"],
        "binders": str(operation["binders"]),
        "constructed_nodes": str(operation["constructed_nodes"]),
        "max_binders": str(operation["max_binders"]),
        "max_nodes": str(operation["max_constructed_nodes"]),
        "declarations": str(operation["admitted_declarations"]),
        "axioms": str(operation["axioms"]),
        "theorem_dependencies": str(operation["theorem_dependencies"]),
        "target_dependency": str(operation["target_dependency"]).lower(),
        "ledger_writes": str(operation["ledger_writes"]),
    }
    if {key: receipt.get(key) for key in exact} != exact:
        raise ReflexivityError("reflexivity receipt identity changed")
    if hashlib.sha256(receipt["goal"].encode()).hexdigest() != operation["goal_sha256"]:
        raise ReflexivityError("rendered goal digest changed")
    if hashlib.sha256(receipt["proof"].encode()).hexdigest() != operation["proof_sha256"]:
        raise ReflexivityError("rendered proof digest changed")


def validate(manifest: dict[str, Any]) -> str:
    adapter = load(ROOT / manifest["statement_adapter"])
    operation = manifest["operation"]
    if manifest["source_fact_id"] != adapter["source_fact_id"]:
        raise ReflexivityError("source fact does not match the statement adapter")
    imported = adapter["independent_import"]
    if operation["goal_sha256"] != imported["goal_sha256"]:
        raise ReflexivityError("goal identity does not match the statement adapter")
    if operation["target_content_sha256"] != imported["target_content_sha256"]:
        raise ReflexivityError("target identity does not match the statement adapter")

    fact_path = ROOT / "artifacts/facts" / manifest["source_fact_id"].replace(":", "-")
    fact = load(fact_path.with_suffix(".json"))
    if fact.get("epistemic_status") != "open" or fact.get("evidence") != []:
        raise ReflexivityError("source fact received proof credit")
    if "proof_route" in fact:
        raise ReflexivityError("source fact unexpectedly has a proof route")

    artifact = pathlib.Path(adapter["external_artifact"]["path"])
    if not artifact.exists():
        return "external=unavailable"
    command = [
        "cargo", "run", "-q", "-p", "axeyum-lean-import", "--example",
        "statement_reflexivity_operation", "--", str(artifact), operation["target_definition"],
    ]
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=120)
    if completed.returncode != 0:
        raise ReflexivityError(f"reflexivity replay failed: {completed.stderr.strip()}")
    validate_receipt(manifest, parse_receipt(completed.stdout.rstrip("\n")))
    return "external=verified"


def main() -> int:
    try:
        manifest = load_manifest()
        external = validate(manifest)
        print(
            "AUTOGENESIS_STATEMENT_REFLEXIVITY_OK|"
            f"fact={manifest['source_fact_id']}|{external}|state={manifest['state']}|ledger_writes=0"
        )
    except (OSError, KeyError, json.JSONDecodeError, subprocess.TimeoutExpired, ReflexivityError) as error:
        print(f"autogenesis-statement-reflexivity: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
