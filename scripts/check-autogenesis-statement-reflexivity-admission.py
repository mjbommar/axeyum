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


def validate_external_index(root: pathlib.Path, expected_sha256: str) -> None:
    index = root / "SHA256SUMS"
    if sha256(index) != expected_sha256:
        raise AdmissionResultError("external file index changed")
    indexed: dict[str, str] = {}
    for line in index.read_text().splitlines():
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


def validate_replay_objects(
    manifest: dict[str, Any],
    report: dict[str, Any],
    fresh: dict[str, dict[str, Any]],
    retained: dict[str, dict[str, Any]],
) -> None:
    replay = manifest["clean_replay"]
    if verify_addressed(report, "replay_sha256", "clean replay") != replay[
        "replay_sha256"
    ]:
        raise AdmissionResultError("clean replay identity changed")
    expected_checks = {
        "same_fact",
        "same_registered_operation",
        "same_certified_result",
        "same_acceptance_policy",
        "selected_before",
        "admitted_event",
        "removed_from_ready",
        "honest_leaf_unlock",
        "one_authoritative_write",
        "zero_fixture_writes",
    }
    if set(report.get("checks", {})) != expected_checks or not all(
        report["checks"].values()
    ):
        raise AdmissionResultError("clean replay semantic checks are incomplete")
    if (
        report.get("schema_version") != 1
        or report.get("kind") != "axeyum-autogenesis-authoritative-admission-replay"
        or report.get("mode") != "isolated-clean-worktree-semantic-reproduction"
        or report.get("source_head") != replay["source_commit"]
        or report.get("historical_prestate_commit") != manifest["registration_commit"]
        or report.get("identity")
        != {
            "fact_id": manifest["fact_id"],
            "operation_id": manifest["operation_id"],
        }
        or report.get("fault_injection") != manifest["fault_injection"]
    ):
        raise AdmissionResultError("clean replay contract changed")

    execution = fresh["execution.json"]
    transaction = fresh["transaction.json"]
    event = fresh["admission-event.json"]
    before = fresh["frontier-before.json"]
    after = fresh["frontier-after.json"]
    readiness = fresh["readiness.json"]
    observed = {
        "frontier_before_sha256": verify_addressed(
            before, "frontier_sha256", "fresh before frontier"
        ),
        "execution_sha256": verify_addressed(
            execution, "execution_sha256", "fresh execution"
        ),
        "transaction_sha256": verify_addressed(
            transaction, "transaction_sha256", "fresh transaction"
        ),
        "event_sha256": verify_addressed(event, "event_sha256", "fresh event"),
        "frontier_after_sha256": verify_addressed(
            after, "frontier_sha256", "fresh after frontier"
        ),
        "readiness_delta_sha256": verify_addressed(
            readiness, "readiness_delta_sha256", "fresh readiness delta"
        ),
    }
    if observed != report.get("fresh"):
        raise AdmissionResultError("fresh replay object identities changed")
    if (
        observed["execution_sha256"] != replay["fresh_execution_sha256"]
        or observed["transaction_sha256"] != replay["fresh_transaction_sha256"]
        or observed["event_sha256"] != replay["fresh_event_sha256"]
        or observed["readiness_delta_sha256"]
        != replay["fresh_readiness_delta_sha256"]
    ):
        raise AdmissionResultError("recorded fresh replay identities changed")
    apply = load_module("apply_for_clean_reflexivity_replay", APPLY_SCRIPT)
    if event != apply.build_admission_event(transaction):
        raise AdmissionResultError("fresh replay event does not derive from transaction")
    if (
        transaction.get("identity", {}).get("execution_sha256")
        != observed["execution_sha256"]
        or readiness.get("identity", {}).get("transaction_sha256")
        != observed["transaction_sha256"]
        or readiness.get("identity", {}).get("durable_admission_event_sha256")
        != observed["event_sha256"]
        or execution.get("result") != retained["execution.json"].get("result")
        or execution.get("acceptance")
        != retained["execution.json"].get("acceptance")
    ):
        raise AdmissionResultError("fresh replay chain or certified result changed")
    retained_report = report.get("retained", {})
    if retained_report != {
        "execution_sha256": manifest["identities"]["execution_sha256"],
        "transaction_sha256": manifest["identities"]["transaction_sha256"],
        "event_sha256": manifest["identities"]["admission_event_sha256"],
        "readiness_delta_sha256": manifest["identities"]["readiness_delta_sha256"],
    }:
        raise AdmissionResultError("clean replay retained identities changed")


def validate_clean_replay(
    manifest: dict[str, Any], retained: dict[str, dict[str, Any]]
) -> None:
    replay = manifest["clean_replay"]
    root = pathlib.Path(replay["external_root"])
    if not root.is_dir():
        raise AdmissionResultError("external clean replay is unavailable")
    validate_external_index(root, replay["external_index_sha256"])
    report_path = root / "replay.json"
    if sha256(report_path) != replay["replay_file_sha256"]:
        raise AdmissionResultError("external clean replay report changed")
    fresh = {
        name: load(root / name)
        for name in (
            "frontier-before.json",
            "execution.json",
            "transaction.json",
            "admission-event.json",
            "frontier-after.json",
            "readiness.json",
        )
    }
    validate_replay_objects(manifest, load(report_path), fresh, retained)


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
        or manifest.get("state")
        != "durably-admitted-archived-and-clean-replayed"
    ):
        raise AdmissionResultError("result manifest schema identity or state is invalid")
    root = pathlib.Path(manifest["external_root"])
    if not root.is_dir():
        raise AdmissionResultError("external admission bundle is unavailable")
    validate_external_index(root, manifest["external_index_sha256"])
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
    validate_clean_replay(manifest, objects)
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
            f"event={identities['admission_event_sha256']}|"
            f"replay={manifest['clean_replay']['replay_sha256']}|"
            "writes=1|newly_ready=0"
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
