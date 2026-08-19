#!/usr/bin/env python3
"""Verify the proof-isolated Mathlib statement-adapter artifact and receipt."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-statement-adapter-v1.json"


class AdapterError(RuntimeError):
    """The statement adapter no longer matches its preregistered identity."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_manifest(path: pathlib.Path = MANIFEST) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AdapterError("manifest is not an object")
    if value.get("schema_version") != 1 or value.get("kind") != "axeyum-autogenesis-mathlib-statement-adapter":
        raise AdapterError("manifest schema identity is invalid")
    if value.get("state") != "independent-kernel-goal-admitted-proof-free":
        raise AdapterError("manifest state is invalid")
    return value


def parse_receipt(stdout: str) -> dict[str, str]:
    lines = stdout.splitlines()
    if len(lines) != 2 or not lines[0].startswith("STATEMENT_ADAPTER_IMPORT|") or not lines[1].startswith("GOAL|"):
        raise AdapterError("adapter emitted an invalid receipt shape")
    fields: dict[str, str] = {}
    for item in lines[0].split("|")[1:]:
        if "=" not in item:
            raise AdapterError("adapter receipt field lacks '='")
        key, value = item.split("=", 1)
        if not key or key in fields or not value:
            raise AdapterError("adapter receipt fields are empty or duplicated")
        fields[key] = value
    fields["goal"] = lines[1].removeprefix("GOAL|")
    return fields


def validate_receipt(manifest: dict[str, Any], receipt: dict[str, str]) -> None:
    expected = manifest["independent_import"]
    source = manifest["adapter_source"]
    exact = {
        "target": source["target_definition"],
        "goal_sha256": expected["goal_sha256"],
        "target_content_sha256": expected["target_content_sha256"],
        "dependencies": str(expected["direct_dependencies"]),
        "declarations": str(expected["admitted_declarations"]),
        "axioms": str(expected["axioms"]),
        "lean": manifest["toolchain"]["lean_version"],
    }
    observed = {key: receipt.get(key) for key in exact}
    if observed != exact:
        raise AdapterError(f"adapter receipt identity changed: {observed!r}")
    if hashlib.sha256(receipt["goal"].encode()).hexdigest() != expected["goal_sha256"]:
        raise AdapterError("rendered goal does not match its claimed digest")


def validate(manifest: dict[str, Any]) -> str:
    source = ROOT / manifest["adapter_source"]["path"]
    if sha256(source) != manifest["adapter_source"]["sha256"]:
        raise AdapterError("tracked Lean adapter source digest changed")
    fact_path = ROOT / "artifacts/facts" / manifest["source_fact_id"].replace(":", "-")
    fact_path = fact_path.with_suffix(".json")
    fact = json.loads(fact_path.read_text())
    statement_digest = hashlib.sha256(fact["formal"]["statement"].encode()).hexdigest()
    if statement_digest != manifest["source_statement_sha256"]:
        raise AdapterError("source fact statement identity changed")

    artifact = pathlib.Path(manifest["external_artifact"]["path"])
    if not artifact.exists():
        return "external=unavailable"
    external = manifest["external_artifact"]
    if artifact.stat().st_size != external["bytes"] or sha256(artifact) != external["sha256"]:
        raise AdapterError("external adapter bytes changed")
    if sum(1 for _ in artifact.open("rb")) != external["records"]:
        raise AdapterError("external adapter record count changed")
    if stat.S_IMODE(artifact.stat().st_mode) != int(external["mode"], 8):
        raise AdapterError("external adapter artifact is not immutable")

    command = [
        "cargo", "run", "-q", "-p", "axeyum-lean-import", "--example",
        "statement_adapter_import", "--", str(artifact),
        manifest["adapter_source"]["target_definition"],
    ]
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=120)
    if completed.returncode != 0:
        raise AdapterError(f"independent adapter import failed: {completed.stderr.strip()}")
    validate_receipt(manifest, parse_receipt(completed.stdout.rstrip("\n")))
    return "external=verified"


def main() -> int:
    try:
        manifest = load_manifest()
        external = validate(manifest)
        print(
            "AUTOGENESIS_STATEMENT_ADAPTER_OK|"
            f"{manifest['independent_import']['goal_sha256']}|{external}|"
            f"fact={manifest['source_fact_id']}|axioms=0"
        )
    except (OSError, KeyError, json.JSONDecodeError, subprocess.TimeoutExpired, AdapterError) as error:
        print(f"autogenesis-statement-adapter: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
