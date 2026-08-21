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
EXECUTION_DRIVERS = {
    "axeyum-bench/smtcomp-evidence-v1",
    "axeyum-lean-kernel/nat-zero-add-induction-v1",
    "axeyum-lean-kernel/nat-mul-one-episode-apply-v1",
    "axeyum-lean-import/statement-reflexivity-v1",
    "axeyum-lean-import/checked-theorem-receipt-v1",
    "axeyum-lean-import/dependency-theorem-receipt-v1",
    "axeyum-lean-import/sealed-kernel-capsule-v1",
}
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


def repository_file(value: Any, label: str, root: pathlib.Path) -> pathlib.Path:
    if not isinstance(value, str) or not value:
        raise RegistryError(f"{label} must be a nonempty repository-relative path")
    relative = pathlib.PurePosixPath(value)
    if relative.is_absolute() or ".." in relative.parts:
        raise RegistryError(f"{label} must be repository-relative")
    resolved_root = root.resolve()
    resolved = (root / relative).resolve()
    if not resolved.is_relative_to(resolved_root):
        raise RegistryError(f"{label} escapes the repository")
    if not resolved.is_file():
        raise RegistryError(f"{label} does not exist: {relative}")
    return resolved


def validate_executor(value: Any, label: str, root: pathlib.Path) -> None:
    if not isinstance(value, dict):
        raise RegistryError(f"{label} must be an object")
    common = {
            "driver",
            "implementation",
            "input_fact_id",
            "timeout_seconds",
            "expected_evidence_label",
    }
    driver = value.get("driver")
    if driver not in EXECUTION_DRIVERS:
        raise RegistryError(f"{label}.driver is unsupported")
    if driver == "axeyum-bench/smtcomp-evidence-v1":
        expected = common | {"input_artifact"}
    elif driver == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        expected = common | {"target_theorem", "denied_theorems", "budget"}
    elif driver == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        expected = common | {
            "target_theorem",
            "premise_fact_id",
            "premise_operation_id",
            "denied_theorems",
            "premise_budget",
            "budget",
        }
    elif driver == "axeyum-lean-import/statement-reflexivity-v1":
        expected = common | {
            "statement_adapter_manifest",
            "reflexivity_manifest",
            "target_definition",
            "max_binders",
            "max_constructed_nodes",
        }
    elif driver == "axeyum-lean-import/checked-theorem-receipt-v1":
        expected = common | {
            "receipt_manifest",
            "target_definition",
            "receipt_sha256",
        }
    elif driver == "axeyum-lean-import/dependency-theorem-receipt-v1":
        expected = common | {
            "receipt_manifest",
            "target_definition",
            "receipt_sha256",
            "dependency_set_sha256",
            "transitive_dependency_set_sha256",
        }
    elif driver == "axeyum-lean-import/sealed-kernel-capsule-v1":
        expected = common | {
            "result_manifest",
            "capsule_path",
            "capsule_sha256",
            "target_theorem",
            "goal_sha256",
            "declaration_sha256",
            "receipt_sha256",
        }
    else:
        expected = common
    exact_keys(value, expected, label)
    if not isinstance(value["input_fact_id"], str) or not FACT_ID_RE.fullmatch(
        value["input_fact_id"]
    ):
        raise RegistryError(f"{label}.input_fact_id is invalid")
    repository_file(value["implementation"], f"{label}.implementation", root)
    if driver == "axeyum-bench/smtcomp-evidence-v1":
        artifact = repository_file(value["input_artifact"], f"{label}.input_artifact", root)
        expected_artifact_root = (root / "artifacts/facts/smt2").resolve()
        if not artifact.is_relative_to(expected_artifact_root) or artifact.suffix != ".smt2":
            raise RegistryError(f"{label}.input_artifact is not a fact SMT-LIB instance")
    elif driver == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        theorem = value["target_theorem"]
        if not isinstance(theorem, str) or not re.fullmatch(r"Nat\.[A-Za-z0-9_']+", theorem):
            raise RegistryError(f"{label}.target_theorem is invalid")
        denied = nonempty_strings(value["denied_theorems"], f"{label}.denied_theorems")
        if theorem not in denied:
            raise RegistryError(f"{label}.denied_theorems must include the retained target")
        if theorem != "Nat.zero_add" or denied != ["Nat.mul_one", "Nat.zero_add"]:
            raise RegistryError(
                f"{label} exceeds the v1 kernel checker's exact target/deny scope"
            )
        budget = value["budget"]
        if budget != 2:
            raise RegistryError(f"{label}.budget must be exactly 2 for the v1 checker")
    elif driver == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        if value["target_theorem"] != "Nat.mul_one":
            raise RegistryError(f"{label}.target_theorem exceeds the exact A scope")
        if value["premise_fact_id"] != "F:nat-zero-add":
            raise RegistryError(f"{label}.premise_fact_id exceeds the exact A scope")
        if value["premise_operation_id"] != "authoritative-kernel-nat-zero-add-induction-v1":
            raise RegistryError(f"{label}.premise_operation_id exceeds the exact A scope")
        denied = nonempty_strings(value["denied_theorems"], f"{label}.denied_theorems")
        if denied != ["Nat.mul_one", "Nat.zero_add"]:
            raise RegistryError(f"{label}.denied_theorems exceeds the exact A scope")
        if value["premise_budget"] != 2 or value["budget"] != 1:
            raise RegistryError(f"{label} requires premise budget 2 and apply budget 1")
    elif driver == "axeyum-lean-import/statement-reflexivity-v1":
        adapter_path = repository_file(
            value["statement_adapter_manifest"],
            f"{label}.statement_adapter_manifest",
            root,
        )
        reflexivity_path = repository_file(
            value["reflexivity_manifest"],
            f"{label}.reflexivity_manifest",
            root,
        )
        expected_root = (root / "artifacts/autogenesis").resolve()
        if adapter_path.parent != expected_root or reflexivity_path.parent != expected_root:
            raise RegistryError(f"{label} manifests must be canonical autogenesis artifacts")
        adapter = json.loads(adapter_path.read_text())
        reflexivity = json.loads(reflexivity_path.read_text())
        operation = reflexivity.get("operation") or {}
        if (
            adapter.get("kind") != "axeyum-autogenesis-mathlib-statement-adapter"
            or adapter.get("state") != "independent-kernel-goal-admitted-proof-free"
            or reflexivity.get("kind")
            != "axeyum-autogenesis-mathlib-statement-reflexivity"
            or reflexivity.get("state") != "candidate-checked-not-admitted"
            or adapter.get("source_fact_id") != value["input_fact_id"]
            or reflexivity.get("source_fact_id") != value["input_fact_id"]
            or reflexivity.get("statement_adapter")
            != value["statement_adapter_manifest"]
            or operation.get("target_definition") != value["target_definition"]
            or operation.get("max_binders") != value["max_binders"]
            or operation.get("max_constructed_nodes")
            != value["max_constructed_nodes"]
        ):
            raise RegistryError(f"{label} statement-reflexivity manifests disagree")
        fact_path = root / "artifacts/facts" / (
            value["input_fact_id"].replace("F:", "F-") + ".json"
        )
        fact = json.loads(fact_path.read_text())
        statement = (fact.get("formal") or {}).get("statement")
        if (
            not isinstance(statement, str)
            or hashlib.sha256(statement.encode()).hexdigest()
            != adapter.get("source_statement_sha256")
        ):
            raise RegistryError(f"{label} statement identity disagrees with its fact")
    elif driver == "axeyum-lean-import/checked-theorem-receipt-v1":
        manifest_path = repository_file(
            value["receipt_manifest"], f"{label}.receipt_manifest", root
        )
        if manifest_path.parent != (root / "artifacts/autogenesis").resolve():
            raise RegistryError(f"{label}.receipt_manifest must be canonical")
        manifest = json.loads(manifest_path.read_text())
        result = manifest.get("result") or {}
        archive = manifest.get("observation_archive") or {}
        if (
            manifest.get("kind")
            != "axeyum-autogenesis-mathlib-nat-fib-checked-theorem-receipt"
            or manifest.get("state")
            != "semantic-theorem-receipt-issued-no-evaluation-or-ledger-credit"
            or result.get("fact_id") != value["input_fact_id"]
            or result.get("receipt_sha256") != value["receipt_sha256"]
            or result.get("axiom_footprint") != []
            or result.get("direct_theorem_dependencies") != []
            or result.get("fresh_imports") != 2
            or result.get("fixed_plan_reconstructions") != 2
            or result.get("search_invocations") != 0
            or result.get("ledger_writes") != 0
            or not isinstance(archive.get("observation_sha256"), str)
        ):
            raise RegistryError(f"{label} checked-theorem receipt contract disagrees")
        if (
            value["input_fact_id"] != "F:ml430-nat-fib-add-two-b86e0c82"
            or value["target_definition"] != "Axeyum.Autogenesis.Coverage.r080"
            or value["receipt_sha256"]
            != "395f6e80e6addbc69cca8ad560b312dadc31d623fe05f6b1603b5fa523622329"
        ):
            raise RegistryError(f"{label} exceeds the exact checked-theorem receipt scope")
    elif driver == "axeyum-lean-import/sealed-kernel-capsule-v1":
        manifest_path = repository_file(
            value["result_manifest"], f"{label}.result_manifest", root
        )
        expected_manifest = (
            root
            / "artifacts/autogenesis/nat-gcd-fib-add-self-target-native-exact-result-v3.json"
        ).resolve()
        manifest = json.loads(manifest_path.read_text())
        theorem = manifest.get("target") or {}
        execution = manifest.get("execution") or {}
        if (
            manifest_path != expected_manifest
            or manifest.get("state")
            != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
            or value["input_fact_id"]
            != "F:ml430-nat-gcd-fib-add-self-5a92d5e3"
            or value["capsule_path"]
            != "/nas3/data/axeyum/autogenesis/reference-packs/dfa79618c-target-native-exact-v3/target-1.ndjson"
            or value["capsule_sha256"]
            != "279dc4db5daa6dc2f532f9876052500a7e278c54264b32ccbc9d4256907dfc24"
            or value["target_theorem"] != "Nat.gcd_fib_add_self"
            or theorem.get("name") != value["target_theorem"]
            or theorem.get("goal_sha256") != value["goal_sha256"]
            or theorem.get("declaration_sha256") != value["declaration_sha256"]
            or theorem.get("axiom_footprint") != []
            or execution.get("complete_invocations") != 2
            or execution.get("exact_target_submissions") != 2
            or execution.get("fresh_imports") != 4
            or execution.get("outputs_byte_identical") is not True
            or execution.get("receipts_byte_identical") is not True
            or value["receipt_sha256"]
            != "f7f568faf86f908de721b33de3fcbe766e12fae8fab4e1d738eb592eddf9306e"
        ):
            raise RegistryError(f"{label} sealed-kernel capsule contract disagrees")
    else:
        manifest_path = repository_file(
            value["receipt_manifest"], f"{label}.receipt_manifest", root
        )
        if manifest_path != (
            root
            / "artifacts/autogenesis/mathlib-nat-fib-coprime-premise-plan-v1.json"
        ).resolve():
            raise RegistryError(f"{label}.receipt_manifest exceeds the exact dependency receipt scope")
        manifest = json.loads(manifest_path.read_text())
        tracked = manifest.get("fibonacci_semantic_receipt") or {}
        exact = manifest.get("exact_fibonacci_coprimality") or {}
        authority = manifest.get("fibonacci_receipt_authority") or {}
        if (
            manifest.get("state")
            != "exact-official-semantic-receipt-issued-fact-transition-pending"
            or manifest.get("target", {}).get("fact_id") != value["input_fact_id"]
            or tracked.get("schema")
            != "axeyum-checked-dependency-theorem-receipt-v1"
            or tracked.get("receipt_sha256") != value["receipt_sha256"]
            or tracked.get("transitive_dependency_set_sha256")
            != value["transitive_dependency_set_sha256"]
            or authority.get("dependency_set_sha256")
            != value["dependency_set_sha256"]
            or exact.get("target_definition") != value["target_definition"]
            or tracked.get("axiom_footprint") != []
            or tracked.get("fresh_full_reconstructions") != 2
            or tracked.get("kernel_submissions") != 2
            or tracked.get("semantic_theorem_receipts_issued") != 1
            or tracked.get("fact_status_changes") != 0
            or tracked.get("evaluation_credit") != 0
            or tracked.get("ledger_writes") != 0
            or len(authority.get("direct_theorem_dependencies") or []) != 8
        ):
            raise RegistryError(f"{label} dependency-theorem receipt contract disagrees")
        if (
            value["input_fact_id"]
            != "F:ml430-nat-fib-coprime-fib-succ-162fc738"
            or value["target_definition"] != "Axeyum.Autogenesis.Coverage.r082"
            or value["receipt_sha256"]
            != "34b9aad06fc8a640c81df0951b1af37a464f2d9305c048784e4f590b83ff0d0e"
            or value["dependency_set_sha256"]
            != "d407340befc681d6d9abd187bbfead1f6ca1a7395c7dcf908950fd9c4d02e4d5"
            or value["transitive_dependency_set_sha256"]
            != "fa08448a022db2ba1fdd4226979a86854e561888658801d295f4dba0dc3ef84e"
        ):
            raise RegistryError(f"{label} exceeds the exact dependency-theorem receipt scope")
    timeout = value["timeout_seconds"]
    if type(timeout) is not int or not 1 <= timeout <= 900:
        raise RegistryError(f"{label}.timeout_seconds must be an integer in 1..900")
    label_value = value["expected_evidence_label"]
    if not isinstance(label_value, str) or not ID_RE.fullmatch(label_value):
        raise RegistryError(f"{label}.expected_evidence_label is invalid")


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
        scope = operation.get("scope")
        operation_fields = {
            "id",
            "scope",
            "applicability",
            "producer",
            "checker",
            "admission",
        }
        if scope == "authoritative":
            operation_fields.add("executor")
            if "reviewed_gate_mentions" in operation:
                operation_fields.add("reviewed_gate_mentions")
        exact_keys(operation, operation_fields, label)
        operation_id = operation["id"]
        if not isinstance(operation_id, str) or not ID_RE.fullmatch(operation_id):
            raise RegistryError(f"{label}.id is not a stable operation id")
        if operation_id in seen:
            raise RegistryError(f"duplicate operation id {operation_id!r}")
        seen.add(operation_id)
        if scope not in SCOPES:
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
        if scope == "authoritative":
            validate_executor(operation["executor"], f"{label}.executor", root)
            mentions = operation.get("reviewed_gate_mentions", [])
            if not isinstance(mentions, list) or len(mentions) != len(set(mentions)):
                raise RegistryError(f"{label}.reviewed_gate_mentions must be a unique list")
            for mention in mentions:
                if (
                    not isinstance(mention, str)
                    or pathlib.PurePosixPath(mention).name != mention
                    or not (root / "scripts" / mention).is_file()
                ):
                    raise RegistryError(f"{label} has invalid reviewed gate mention")
        admission = operation["admission"]
        if not isinstance(admission, dict):
            raise RegistryError(f"{label}.admission must be an object")
        exact_keys(
            admission,
            {
                "epistemic_status",
                "proof_route",
                "evidence_kind",
                "axiom_footprint_policy",
                "axiom_footprint",
            },
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
        footprint = admission["axiom_footprint"]
        if (
            not isinstance(footprint, list)
            or any(not isinstance(item, str) or not item for item in footprint)
            or len(footprint) != len(set(footprint))
        ):
            raise RegistryError(f"{label}.admission.axiom_footprint is invalid")
        footprint_policy = admission["axiom_footprint_policy"]
        if (footprint_policy == "must-be-empty") != (footprint == []):
            raise RegistryError(f"{label}.admission footprint violates its policy")
        if footprint_policy == "must-be-nonempty" and not footprint:
            raise RegistryError(f"{label}.admission footprint violates its policy")
        if scope == "authoritative":
            executor = operation["executor"]
            if executor["input_fact_id"] not in fact_ids or fact_ids != [
                executor["input_fact_id"]
            ]:
                raise RegistryError(
                    f"{label}.executor must bind the sole applicable fact id"
                )
            if (
                executor["driver"] == "axeyum-bench/smtcomp-evidence-v1"
            ):
                expected_artifact_name = (
                    "neg-" + executor["input_fact_id"].removeprefix("F:") + ".smt2"
                )
                if pathlib.PurePosixPath(executor["input_artifact"]).name != expected_artifact_name:
                    raise RegistryError(
                        f"{label}.executor input artifact does not match its fact id"
                    )
                if (
                    applicability["formal_languages"] != ["smtlib2"]
                    or admission["proof_route"] != "smt-term-level"
                    or admission["evidence_kind"] != "unsat-certificate"
                ):
                    raise RegistryError(
                        f"{label}.executor driver is inconsistent with applicability/admission"
                    )
            elif executor["driver"] == "axeyum-lean-import/statement-reflexivity-v1":
                if (
                    applicability["formal_languages"] != ["lean4-surface"]
                    or applicability["fragments"] != ["Nat"]
                    or admission["proof_route"] != "kernel-lean"
                    or admission["evidence_kind"] != "kernel-term"
                    or admission["axiom_footprint"] != []
                ):
                    raise RegistryError(
                        f"{label}.executor driver is inconsistent with applicability/admission"
                    )
            elif executor["driver"] in {
                "axeyum-lean-import/checked-theorem-receipt-v1",
                "axeyum-lean-import/dependency-theorem-receipt-v1",
                "axeyum-lean-import/sealed-kernel-capsule-v1",
            }:
                if (
                    applicability["formal_languages"] != ["lean4-surface"]
                    or applicability["fragments"] != ["Nat"]
                    or admission["proof_route"] != "kernel-lean"
                    or admission["evidence_kind"] != "kernel-term"
                    or admission["axiom_footprint"] != []
                ):
                    raise RegistryError(
                        f"{label}.executor driver is inconsistent with applicability/admission"
                    )
            elif (
                applicability["formal_languages"] != ["lean4"]
                or applicability["fragments"] != ["Nat"]
                or admission["proof_route"] != "kernel-lean"
                or admission["evidence_kind"] != "kernel-term"
                or admission["axiom_footprint"] != []
            ):
                raise RegistryError(
                    f"{label}.executor driver is inconsistent with applicability/admission"
                )
            if executor["driver"] == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
                premise_matches = [
                    candidate
                    for candidate in registry["operations"]
                    if candidate.get("id") == executor["premise_operation_id"]
                    and candidate.get("scope") == "authoritative"
                    and candidate.get("applicability", {}).get("fact_ids")
                    == [executor["premise_fact_id"]]
                ]
                if len(premise_matches) != 1:
                    raise RegistryError(
                        f"{label}.executor premise operation is absent or ambiguous"
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
