#!/usr/bin/env python3
"""Verify the first durable Mathlib statement-reflexivity admission."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-statement-reflexivity-admission-v1.json"
FACTS = ROOT / "artifacts/facts"
APPLY_SCRIPT = ROOT / "scripts/apply-autogenesis-fact-transaction.py"


class AdmissionResultError(RuntimeError):
    """The retained admission chain is unavailable, stale, or inconsistent."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AdmissionResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def verify_addressed(value: dict[str, Any], field: str, label: str) -> str:
    claimed = value.get(field)
    unsigned = dict(value)
    unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise AdmissionResultError(f"{label} digest is missing or invalid")
    return claimed


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AdmissionResultError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_objects(
    manifest: dict[str, Any], objects: dict[str, dict[str, Any]], current_fact: dict[str, Any]
) -> None:
    before = objects["frontier-before.json"]
    execution = objects["execution.json"]
    transaction = objects["transaction.json"]
    event = objects["admission-event.json"]
    after = objects["frontier-after.json"]
    readiness = objects["readiness.json"]
    before_fact = objects["before-fact.json"]
    after_fact = objects["after-fact.json"]
    identities = manifest["identities"]
    observed = {
        "frontier_before_sha256": verify_addressed(
            before, "frontier_sha256", "before frontier"
        ),
        "execution_sha256": verify_addressed(
            execution, "execution_sha256", "execution"
        ),
        "transaction_sha256": verify_addressed(
            transaction, "transaction_sha256", "transaction"
        ),
        "admission_event_sha256": verify_addressed(
            event, "event_sha256", "admission event"
        ),
        "frontier_after_sha256": verify_addressed(
            after, "frontier_sha256", "after frontier"
        ),
        "readiness_delta_sha256": verify_addressed(
            readiness, "readiness_delta_sha256", "readiness delta"
        ),
        "before_fact_sha256": digest(before_fact),
        "after_fact_sha256": digest(after_fact),
    }
    if observed != identities:
        raise AdmissionResultError("retained object identities changed")
    execution_identity = execution.get("identity") or {}
    transaction_identity = transaction.get("identity") or {}
    readiness_identity = readiness.get("identity") or {}
    if (
        execution_identity.get("git_commit") != manifest["registration_commit"]
        or execution_identity.get("fact_id") != manifest["fact_id"]
        or execution_identity.get("operation_id") != manifest["operation_id"]
        or transaction_identity.get("fact_id") != manifest["fact_id"]
        or transaction_identity.get("execution_sha256") != identities["execution_sha256"]
        or transaction_identity.get("before_fact_sha256")
        != identities["before_fact_sha256"]
        or transaction_identity.get("after_fact_sha256")
        != identities["after_fact_sha256"]
        or readiness_identity.get("transaction_sha256")
        != identities["transaction_sha256"]
        or readiness_identity.get("durable_admission_event_sha256")
        != identities["admission_event_sha256"]
    ):
        raise AdmissionResultError("admission identity chain is inconsistent")
    apply = load_module("apply_for_reflexivity_admission_result", APPLY_SCRIPT)
    if event != apply.build_admission_event(transaction):
        raise AdmissionResultError("durable event does not derive from the transaction")
    if transaction["authoritative_write"]["after_fact"] != after_fact:
        raise AdmissionResultError("transaction after-fact differs from the retained fact")
    if current_fact != after_fact:
        raise AdmissionResultError("authoritative ledger differs from the admitted after-state")
    expected_result = manifest["result"]
    observation = execution["result"]["observation"]
    if (
        readiness.get("authoritative_ledger_writes")
        != expected_result["authoritative_ledger_writes"]
        or readiness.get("fixture_writes") != expected_result["fixture_writes"]
        or readiness.get("newly_ready") != expected_result["newly_ready"]
        or readiness.get("frontier_change", {}).get("no_longer_ready")
        != [manifest["fact_id"]]
        or before.get("selection", {}).get("selected_fact_id")
        != manifest["fact_id"]
        or after.get("selection", {}).get("selected_fact_id") is not None
        or observation.get("axiom_footprint") != expected_result["axiom_footprint"]
        or observation.get("retained_answer_dependencies")
        != expected_result["theorem_dependencies"]
        or observation.get("target_dependency")
        != expected_result["target_dependency"]
    ):
        raise AdmissionResultError("admission result semantics changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-statement-reflexivity-admission"
        or manifest.get("state") != "durably-admitted-and-externally-archived"
    ):
        raise AdmissionResultError("result manifest schema identity or state is invalid")
    root = pathlib.Path(manifest["external_root"])
    if not root.is_dir():
        raise AdmissionResultError("external admission bundle is unavailable")
    if sha256(root / "SHA256SUMS") != manifest["external_index_sha256"]:
        raise AdmissionResultError("external file index changed")
    indexed: dict[str, str] = {}
    for line in (root / "SHA256SUMS").read_text().splitlines():
        claimed, separator, relative = line.partition("  ")
        relative = relative.removeprefix("./")
        if (
            not separator
            or len(claimed) != 64
            or not relative
            or relative in indexed
            or pathlib.PurePosixPath(relative).is_absolute()
            or ".." in pathlib.PurePosixPath(relative).parts
        ):
            raise AdmissionResultError("external file index is malformed")
        indexed[relative] = claimed
    actual_files = {
        str(path.relative_to(root))
        for path in root.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS"
    }
    if set(indexed) != actual_files:
        raise AdmissionResultError("external file index coverage changed")
    for relative, expected in indexed.items():
        if sha256(root / relative) != expected:
            raise AdmissionResultError(f"indexed external artifact changed: {relative}")
    if sha256(root / "source.bundle") != manifest["source_bundle_sha256"]:
        raise AdmissionResultError("source Git bundle changed")
    for relative, expected in manifest["external_files"].items():
        path = root / relative
        if not path.is_file() or sha256(path) != expected:
            raise AdmissionResultError(f"external artifact changed: {relative}")
    objects = {
        relative: load(root / relative)
        for relative in manifest["external_files"]
        if relative.endswith(".json")
    }
    fact_path = FACTS / (manifest["fact_id"].replace("F:", "F-") + ".json")
    validate_objects(manifest, objects, load(fact_path))
    bundle = subprocess.run(
        ["git", "bundle", "verify", str(root / "source.bundle")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if bundle.returncode != 0 or "complete history" not in bundle.stderr + bundle.stdout:
        raise AdmissionResultError("source Git bundle is not a complete verified history")
    fact_check = subprocess.run(
        ["python3", "scripts/check-autogenesis-fact-operation.py", "--fact", str(fact_path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    if fact_check.returncode != 0:
        raise AdmissionResultError(
            f"settled fact operation replay failed: {fact_check.stderr.strip()}"
        )
    return manifest


def main() -> int:
    try:
        manifest = validate()
        identities = manifest["identities"]
        print(
            "AUTOGENESIS_STATEMENT_REFLEXIVITY_ADMISSION_OK|"
            f"fact={manifest['fact_id']}|execution={identities['execution_sha256']}|"
            f"transaction={identities['transaction_sha256']}|"
            f"event={identities['admission_event_sha256']}|writes=1|newly_ready=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
        AdmissionResultError,
    ) as error:
        print(f"AUTOGENESIS_STATEMENT_REFLEXIVITY_ADMISSION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
