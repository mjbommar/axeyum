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
# A qualified Lean declaration name as this kernel renders it, e.g.
# `Int.add_modEq_left` -- one namespace segment, a dot, then an identifier
# (mixed case and primes are both real in this development's naming).
LEAN_DECLARATION_RE = re.compile(r"^[A-Z][A-Za-z0-9]*\.[A-Za-z_][A-Za-z0-9_']*$")
SCOPES = {"counterfactual-fixture-only", "authoritative"}
EXECUTION_DRIVERS = {
    "axeyum-bench/smtcomp-evidence-v1",
    "axeyum-lean-kernel/nat-zero-add-induction-v1",
    "axeyum-lean-kernel/nat-mul-one-episode-apply-v1",
    "axeyum-lean-kernel/authored-declaration-v1",
    "axeyum-lean-import/statement-reflexivity-v1",
    "axeyum-lean-import/bounded-induction-multi-target-v1",
    "axeyum-lean-import/modeq-family-multi-target-v1",
    "axeyum-lean-import/imported-candidate-family-multi-target-v1",
    "axeyum-lean-import/conclusion-directed-family-multi-target-v1",
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
SEALED_CAPSULE_CONTRACTS = {
    "F:ml430-int-fib-eq-zero-8193c7cb": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-eq-zero-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-eq-zero-exact-v1/root.ndjson",
        "capsule_sha256": "bd36472c8d898066df2c388d30452bd1859a42ffa1b1ae1be184ce5a494a0f73",
        "target_theorem": "Int.fib_eq_zero",
        "receipt_sha256": "e005b5983b5cb2eee4350cba4ece4acee1cd0732582769778e279757d47eb00c",
    },
    "F:ml430-nat-fib-eq-zero-61879073": {
        "result_manifest": "artifacts/autogenesis/mathlib-nat-fib-eq-zero-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/nat-fib-eq-zero-exact-v1/root.ndjson",
        "capsule_sha256": "b25fc8b0db939ace2cbb0a096e86dd79f185398b93ff3c7698bb7b3d9fd796aa",
        "target_theorem": "Nat.fib_eq_zero",
        "receipt_sha256": "c8466767c516d48e0e214aaf7e8a43e88a8bc7fa952a7baa2748eff03d51f3d3",
    },
    "F:ml430-nat-fib-pos-9e67bd8e": {
        "result_manifest": "artifacts/autogenesis/mathlib-nat-fib-pos-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/nat-fib-pos-exact-v1/root.ndjson",
        "capsule_sha256": "ec85c45183bec3c1fe4cbd0d015c76a5ded6dbbfa4be9b279d59870da12566a0",
        "target_theorem": "Nat.fib_pos",
        "receipt_sha256": "60954cc8fbe7d947c08ffca5dbc55e600864151ca5a824c3d950614478c46aff",
    },
    "F:ml430-nat-gcd-fib-add-self-5a92d5e3": {
        "result_manifest": "artifacts/autogenesis/nat-gcd-fib-add-self-target-native-exact-result-v3.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/dfa79618c-target-native-exact-v3/target-1.ndjson",
        "capsule_sha256": "279dc4db5daa6dc2f532f9876052500a7e278c54264b32ccbc9d4256907dfc24",
        "target_theorem": "Nat.gcd_fib_add_self",
        "receipt_sha256": "f7f568faf86f908de721b33de3fcbe766e12fae8fab4e1d738eb592eddf9306e",
    },
    "F:ml430-nat-gcd-greatest-0a04214a": {
        "result_manifest": "artifacts/autogenesis/mathlib-nat-gcd-greatest-result-v3.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/85b9d4243-target-native-gcd-greatest-v4/target-1.ndjson",
        "capsule_sha256": "c233478948b4d4aedc01c839ef9013c3feb2ddb0009d8b57699d7efb755375e6",
        "target_theorem": "Nat.gcd_greatest",
        "receipt_sha256": "7441a7b211212e04f232918abc5026365761e89a922dba763fb90f8a0ad8b8c3",
    },
    "F:ml430-nat-fib-gcd-d1d98407": {
        "result_manifest": "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-result-v3.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/749f30f65-nat-fib-gcd-v3/target-1.ndjson",
        "capsule_sha256": "8ac3c35874540a10e5fa393c65f3ad313a6cf6a06303cec68fec3ec45d0f04cd",
        "target_theorem": "Nat.fib_gcd",
        "receipt_sha256": "1e65caac2183d493f517a9d78dc789b78a530cbaaf90a95fd07cf19dd7940bc8",
    },
    "F:ml430-nat-fib-dvd-f80f3de1": {
        "result_manifest": "artifacts/autogenesis/mathlib-nat-fib-dvd-construction-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/c2266de88-nat-fib-dvd-v1/target-1.ndjson",
        "capsule_sha256": "52acbd5a51f2163ab5b712483c582adb916ab198567c2b0b6c3678f7316d86d7",
        "target_theorem": "Nat.fib_dvd",
        "receipt_sha256": "cefba64b0f9f892400df93bbbfd7be1ba454cc618384cafad3cc3ca72a5472f1",
    },
    "F:ml430-int-fib-natcast-d5886be4": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-natcast-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-clean-definition-v1/int-fib-clean.ndjson",
        "capsule_sha256": "f0e34ecb1dff747938b7f1079c307af5f4e79e7a67e3bc514feee03e4f30656d",
        "target_theorem": "Int.fib_natCast",
        "receipt_sha256": "2ff124525a245094f2715ac2cca99915c023210d3eccde9721b71da21d4cfdfa",
    },
    "F:ml430-int-fib-add-two-739358dd": {
        "result_manifest": "artifacts/autogenesis/int-fib-add-two-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-add-two-exact-composition-v2/int-fib-add-two-1.ndjson",
        "capsule_sha256": "0fbbb4d55ed862f7feb1b8efa3bf45eed24269067b3702c727d05e45c8947219",
        "target_theorem": "Int.fib_add_two",
        "receipt_sha256": "abccdebb1725d2853f204c342f9fd01625c70deefa41963618e41e1bfa2e6a1a",
    },
    "F:ml430-int-fib-neg-b4021d37": {
        "result_manifest": "artifacts/autogenesis/int-fib-neg-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-exact-v1/root.ndjson",
        "capsule_sha256": "d787dc502dff901cab0cab22bf8fd11578bf6e1632892651b1bf67b3d786d257",
        "target_theorem": "Int.fib_neg",
        "receipt_sha256": "6e57d30c732edf80a6a5c5f82c91cb27e6c8d715beca00ff0d5d5d9f2494fbef",
    },
    "F:ml430-int-gcd-fib-73bdafc2": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-gcd-fib-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1/root.ndjson",
        "capsule_sha256": "b1ce136473ead161243e7cdc053f3a8e0dab81a8e253c364171e839f22fd86f6",
        "target_theorem": "Int.gcd_fib",
        "receipt_sha256": "d02db0eee57fb9b6be43c283054b28141a249003acca3eb0fb90f6eecaae3ac1",
    },
    "F:ml430-int-fib-gcd-3a8bfdec": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-gcd-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-gcd-exact-v1/root.ndjson",
        "capsule_sha256": "040f269431f58c8efe69e995c65b25f64952aa9b3d8f552ab0e7faf2711967f1",
        "target_theorem": "Int.fib_gcd",
        "receipt_sha256": "6c5a72c0853beb1136f4934b92ce189427b05e58e2f4af020509b718e8b602cc",
    },
    "F:ml430-int-fib-dvd-ffb3c5c1": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-dvd-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson",
        "capsule_sha256": "f684a4de870734f60f33abe1da468637697c0d27ce988a47d08dfed601ec6af0",
        "target_theorem": "Int.fib_dvd",
        "receipt_sha256": "a39586b5f2cc15a7e6f6b9d2ac189035c6b81df1825ca83a5c864095bf99b897",
    },
    "F:ml430-int-fib-of-nonneg-438018c5": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-of-nonneg-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-nonneg-exact-v1/root.ndjson",
        "capsule_sha256": "efb1875d675810bdf737215b5ebbc2e1afeb1f085c6b1cfccc56d9b779540bd9",
        "target_theorem": "Int.fib_of_nonneg",
        "receipt_sha256": "21be310e9e3e0175d7f79ba8409ea1ebec37a71532c4d0e4a8720e94cb2ed0e2",
    },
    "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-recurrence-corollary-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-recurrence-corollary-composition-v3/int-fib-recurrence-corollary-1.ndjson",
        "capsule_sha256": "d8823373479dce23213aa004b58e9e0c8912fd413b2cb29e52195639f57a7987",
        "target_theorem": "Int.fib_eq_fib_add_two_sub_fib_add_one",
        "receipt_sha256": "90360a5c12c827afcdcd77fc9b02ff2ef2868b74a71010dddc19d67de65fe276",
    },
    "F:ml430-int-fib-add-one-33f1b748": {
        "result_manifest": "artifacts/autogenesis/mathlib-int-fib-add-one-goal-identity-result-v1.json",
        "capsule_path": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-add-one-composition-v1/int-fib-add-one.ndjson",
        "capsule_sha256": "81fb760e78ee25d12fa7b78f8e2d84892809a36db8a4f8d9cc63fda6be66f27c",
        "target_theorem": "Int.fib_add_one",
        "receipt_sha256": "b90147a33567106afe6c5532246d5684637e7ef1f45d93c2fffec47949ee3d9c",
    },
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
    elif driver == "axeyum-lean-kernel/authored-declaration-v1":
        expected = common | {
            "additional_fact_ids",
            "declaration_source",
            "test_path",
            "verifying_tests",
            "targets",
        }
    elif driver == "axeyum-lean-import/statement-reflexivity-v1":
        expected = common | {
            "statement_adapter_manifest",
            "reflexivity_manifest",
            "target_definition",
            "max_binders",
            "max_constructed_nodes",
        }
    elif driver == "axeyum-lean-import/bounded-induction-multi-target-v1":
        expected = common | {
            "additional_fact_ids",
            "targets",
            "max_binders",
            "max_inductions",
        }
    elif driver == "axeyum-lean-import/modeq-family-multi-target-v1":
        expected = common | {
            "additional_fact_ids",
            "targets",
            "max_binders",
        }
    elif driver == "axeyum-lean-import/imported-candidate-family-multi-target-v1":
        expected = common | {
            "additional_fact_ids",
            "targets",
            "receipt_manifest",
            "max_binders",
        }
    elif driver == "axeyum-lean-import/conclusion-directed-family-multi-target-v1":
        expected = common | {
            "additional_fact_ids",
            "targets",
            "receipt_manifest",
            "generalization_train_fact_ids",
            "max_goal_binders",
            "max_holes",
        }
    elif driver == "axeyum-lean-import/conclusion-directed-family-multi-target-v1":
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)) or any(
            not FACT_ID_RE.fullmatch(fid) for fid in all_fact_ids
        ):
            raise RegistryError(f"{label} has duplicate or invalid fact ids")
        manifest_path = repository_file(
            value["receipt_manifest"], f"{label}.receipt_manifest", root
        )
        if manifest_path.parent != (root / "artifacts/autogenesis").resolve():
            raise RegistryError(f"{label}.receipt_manifest must be canonical")
        manifest = json.loads(manifest_path.read_text())
        if (
            manifest.get("schema_version") != 1
            or manifest.get("kind") != "axeyum-autogenesis-nat-modeq-congruence-contract"
            or (manifest.get("contract_source") or {}).get("lean_axiom_footprint") != []
            or (manifest.get("producer") or {}).get("max_goal_binders")
            != value["max_goal_binders"]
            or (manifest.get("producer") or {}).get("max_holes") != value["max_holes"]
        ):
            raise RegistryError(f"{label}.receipt_manifest is not operation-eligible")
        # The train facts this contract's shapes were established on FIRST.
        # `check-development-partition.py` requires an operation that closes a
        # development fact to reference a train fact, because a producer whose
        # whole applicability was authored against the evaluation set no longer
        # measures generalization. This field is that reference, and it is
        # enforced rather than declared: every id must be in the `train`
        # partition of the nursery AND already `proved`, so it cannot be
        # satisfied by naming an open or development fact.
        train_ids = nonempty_strings(
            value["generalization_train_fact_ids"],
            f"{label}.generalization_train_fact_ids",
        )
        nursery = json.loads(
            (root / "artifacts/autogenesis/nursery-v1.json").read_text()
        )
        partitions = {
            entry.get("fact_id"): entry.get("partition")
            for entry in nursery.get("entries", [])
        }
        for train_id in train_ids:
            if partitions.get(train_id) != "train":
                raise RegistryError(
                    f"{label}.generalization_train_fact_ids names {train_id!r}, "
                    "which is not in the nursery's train partition"
                )
            train_path = root / "artifacts/facts" / (
                train_id.replace("F:", "F-") + ".json"
            )
            if not train_path.is_file():
                raise RegistryError(f"{label} train fact does not exist: {train_id}")
            train_fact = json.loads(train_path.read_text())
            if train_fact.get("epistemic_status") not in {"proved", "computed"}:
                raise RegistryError(
                    f"{label}.generalization_train_fact_ids names {train_id!r}, "
                    "which is not established — a generalization source must be "
                    "settled before the development targets are claimed"
                )
        outcomes = {row.get("fact_id"): row for row in manifest.get("outcomes", [])}
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(
                f"{label}.targets must bind every named fact exactly once"
            )
        target_fact_ids = []
        for index, target in enumerate(targets):
            t_label = f"{label}.targets[{index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(target, {"fact_id", "target_definition"}, t_label)
            fid = target["fact_id"]
            target_fact_ids.append(fid)
            outcome = outcomes.get(fid)
            fact_path = root / "artifacts/facts" / (fid.replace("F:", "F-") + ".json")
            if not fact_path.is_file() or not isinstance(outcome, dict):
                raise RegistryError(f"{t_label} has no fact or receipt outcome")
            if (
                outcome.get("target_definition") != target["target_definition"]
                or outcome.get("axiom_footprint") != []
                or outcome.get("theorem_dependencies") != 1
                or outcome.get("target_dependency") is not False
                or outcome.get("independently_admitted") is not True
            ):
                raise RegistryError(f"{t_label} receipt contract disagrees")
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
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
    elif driver == "axeyum-lean-kernel/authored-declaration-v1":
        # A general driver for "an agent read a Mathlib statement and hand-
        # authored a new kernel declaration directly against
        # `Kernel::add_declaration`, with no producer/checker/executor
        # pipeline component running at all" (docs/autogenesis/293, the
        # motivating case: five `Int.ModEq` closures with no adapter authored,
        # no export run, no import-side producer ever invoked). Every field
        # here exists to make the claim RE-CHECKABLE from the repository as it
        # sits today -- the declaration name(s), the source file that must
        # literally mention them, and the exact test functions that fail on
        # their absence -- never a narrative of how the work happened.
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        for fid in additional:
            if not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(
                    f"{label}.additional_fact_ids has invalid fact id {fid!r}"
                )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)):
            raise RegistryError(
                f"{label} names a fact id more than once across "
                "input_fact_id/additional_fact_ids"
            )
        declaration_source = repository_file(
            value["declaration_source"], f"{label}.declaration_source", root
        )
        test_path = repository_file(value["test_path"], f"{label}.test_path", root)
        crate_root = (root / "crates/axeyum-lean-kernel").resolve()
        if not declaration_source.is_relative_to(
            crate_root
        ) or not test_path.is_relative_to(crate_root):
            raise RegistryError(
                f"{label}.declaration_source/test_path must be inside "
                "crates/axeyum-lean-kernel -- this driver names a kernel-lane "
                "authored declaration, not an imported or bench-produced one"
            )
        verifying_tests = nonempty_strings(
            value["verifying_tests"], f"{label}.verifying_tests"
        )
        test_source = test_path.read_text()
        for test_name in verifying_tests:
            if not re.search(rf"fn\s+{re.escape(test_name)}\s*\(", test_source):
                raise RegistryError(
                    f"{label}.verifying_tests names {test_name!r}, which is "
                    f"not a test function declared in {value['test_path']} -- "
                    "a receipt naming a test that does not exist there must "
                    "fail, not silently pass"
                )
        declaration_source_text = declaration_source.read_text()
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(
                f"{label}.targets must have exactly one entry per named fact id"
            )
        target_fact_ids: list[str] = []
        seen_declarations: set[str] = set()
        for t_index, target in enumerate(targets):
            t_label = f"{label}.targets[{t_index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(target, {"fact_id", "declaration"}, t_label)
            fid = target["fact_id"]
            if not isinstance(fid, str) or not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(f"{t_label}.fact_id is invalid")
            target_fact_ids.append(fid)
            declaration = target["declaration"]
            if not isinstance(declaration, str) or not LEAN_DECLARATION_RE.fullmatch(
                declaration
            ):
                raise RegistryError(
                    f"{t_label}.declaration is not a qualified Lean "
                    "declaration name"
                )
            if declaration in seen_declarations:
                raise RegistryError(
                    f"{t_label}.declaration {declaration!r} is bound to more "
                    "than one fact in this operation"
                )
            seen_declarations.add(declaration)
            if declaration not in declaration_source_text:
                raise RegistryError(
                    f"{t_label}.declaration {declaration!r} does not appear "
                    f"in {value['declaration_source']} -- the receipt names a "
                    "declaration the source file never mentions, which is "
                    "exactly the forgery this driver exists to reject"
                )
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
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
    elif driver == "axeyum-lean-import/bounded-induction-multi-target-v1":
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        for fid in additional:
            if not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(
                    f"{label}.additional_fact_ids has invalid fact id {fid!r}"
                )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)):
            raise RegistryError(
                f"{label} names a fact id more than once across "
                "input_fact_id/additional_fact_ids"
            )
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(
                f"{label}.targets must have exactly one entry per named fact id"
            )
        expected_root = (root / "artifacts/autogenesis").resolve()
        target_fact_ids: list[str] = []
        for t_index, target in enumerate(targets):
            t_label = f"{label}.targets[{t_index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(
                target,
                {
                    "fact_id",
                    "statement_adapter_manifest",
                    "induction_manifest",
                    "target_definition",
                },
                t_label,
            )
            fid = target["fact_id"]
            if not isinstance(fid, str) or not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(f"{t_label}.fact_id is invalid")
            target_fact_ids.append(fid)
            adapter_path = repository_file(
                target["statement_adapter_manifest"],
                f"{t_label}.statement_adapter_manifest",
                root,
            )
            induction_path = repository_file(
                target["induction_manifest"], f"{t_label}.induction_manifest", root
            )
            if (
                adapter_path.parent != expected_root
                or induction_path.parent != expected_root
            ):
                raise RegistryError(
                    f"{t_label} manifests must be canonical autogenesis artifacts"
                )
            adapter = json.loads(adapter_path.read_text())
            induction = json.loads(induction_path.read_text())
            induction_op = induction.get("operation") or {}
            if (
                adapter.get("kind") != "axeyum-autogenesis-mathlib-statement-adapter"
                or adapter.get("state") != "independent-kernel-goal-admitted-proof-free"
                or induction.get("kind")
                != "axeyum-autogenesis-mathlib-bounded-induction-candidate"
                or induction.get("state") != "candidate-checked-not-admitted"
                or adapter.get("source_fact_id") != fid
                or induction.get("source_fact_id") != fid
                or induction.get("statement_adapter")
                != target["statement_adapter_manifest"]
                or induction_op.get("target_definition")
                != target["target_definition"]
                or induction_op.get("max_binders") != value["max_binders"]
                or induction_op.get("max_inductions") != value["max_inductions"]
                or induction_op.get("axioms") != 0
                or induction_op.get("theorem_dependencies") != 0
                or induction_op.get("target_dependency") is not False
            ):
                raise RegistryError(
                    f"{t_label} bounded-induction manifests disagree"
                )
            fact_path = root / "artifacts/facts" / (
                fid.replace("F:", "F-") + ".json"
            )
            fact = json.loads(fact_path.read_text())
            statement = (fact.get("formal") or {}).get("statement")
            if (
                not isinstance(statement, str)
                or hashlib.sha256(statement.encode()).hexdigest()
                != adapter.get("source_statement_sha256")
            ):
                raise RegistryError(
                    f"{t_label} statement identity disagrees with its fact"
                )
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
    elif driver == "axeyum-lean-import/modeq-family-multi-target-v1":
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        for fid in additional:
            if not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(
                    f"{label}.additional_fact_ids has invalid fact id {fid!r}"
                )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)):
            raise RegistryError(
                f"{label} names a fact id more than once across "
                "input_fact_id/additional_fact_ids"
            )
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(
                f"{label}.targets must have exactly one entry per named fact id"
            )
        expected_root = (root / "artifacts/autogenesis").resolve()
        target_fact_ids = []
        for t_index, target in enumerate(targets):
            t_label = f"{label}.targets[{t_index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(
                target,
                {
                    "fact_id",
                    "statement_adapter_manifest",
                    "modeq_manifest",
                    "target_definition",
                },
                t_label,
            )
            fid = target["fact_id"]
            if not isinstance(fid, str) or not FACT_ID_RE.fullmatch(fid):
                raise RegistryError(f"{t_label}.fact_id is invalid")
            target_fact_ids.append(fid)
            adapter_path = repository_file(
                target["statement_adapter_manifest"],
                f"{t_label}.statement_adapter_manifest",
                root,
            )
            modeq_path = repository_file(
                target["modeq_manifest"], f"{t_label}.modeq_manifest", root
            )
            if adapter_path.parent != expected_root or modeq_path.parent != expected_root:
                raise RegistryError(
                    f"{t_label} manifests must be canonical autogenesis artifacts"
                )
            adapter = json.loads(adapter_path.read_text())
            modeq = json.loads(modeq_path.read_text())
            modeq_op = modeq.get("operation") or {}
            if (
                adapter.get("kind") != "axeyum-autogenesis-mathlib-statement-adapter"
                or adapter.get("state") != "independent-kernel-goal-admitted-proof-free"
                or modeq.get("kind")
                != "axeyum-autogenesis-mathlib-modeq-family-candidate"
                or modeq.get("state") != "candidate-checked-not-admitted"
                or adapter.get("source_fact_id") != fid
                or modeq.get("source_fact_id") != fid
                or modeq.get("statement_adapter") != target["statement_adapter_manifest"]
                or modeq_op.get("target_definition") != target["target_definition"]
                or modeq_op.get("max_binders") != value["max_binders"]
                or modeq_op.get("axioms") != 0
                or modeq_op.get("theorem_dependencies") != 0
                or modeq_op.get("target_dependency") is not False
            ):
                raise RegistryError(f"{t_label} modeq-family manifests disagree")
            fact_path = root / "artifacts/facts" / (fid.replace("F:", "F-") + ".json")
            fact = json.loads(fact_path.read_text())
            statement = (fact.get("formal") or {}).get("statement")
            if (
                not isinstance(statement, str)
                or hashlib.sha256(statement.encode()).hexdigest()
                != adapter.get("source_statement_sha256")
            ):
                raise RegistryError(
                    f"{t_label} statement identity disagrees with its fact"
                )
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
    elif driver == "axeyum-lean-import/imported-candidate-family-multi-target-v1":
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)) or any(
            not FACT_ID_RE.fullmatch(fid) for fid in all_fact_ids
        ):
            raise RegistryError(f"{label} has duplicate or invalid fact ids")
        manifest_path = repository_file(
            value["receipt_manifest"], f"{label}.receipt_manifest", root
        )
        if manifest_path.parent != (root / "artifacts/autogenesis").resolve():
            raise RegistryError(f"{label}.receipt_manifest must be canonical")
        manifest = json.loads(manifest_path.read_text())
        if (
            manifest.get("schema_version") != 2
            or manifest.get("kind") != "axeyum-autogenesis-nat-modeq-remainder-contract"
            or manifest.get("state") != "three-of-three-operation-contract"
            or (manifest.get("contract_source") or {}).get("lean_axiom_footprint") != []
        ):
            raise RegistryError(f"{label}.receipt_manifest is not operation-eligible")
        outcomes = {row.get("fact_id"): row for row in manifest.get("outcomes", [])}
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(f"{label}.targets must bind every named fact exactly once")
        target_fact_ids = []
        for index, target in enumerate(targets):
            t_label = f"{label}.targets[{index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(target, {"fact_id", "target_definition"}, t_label)
            fid = target["fact_id"]
            target_fact_ids.append(fid)
            outcome = outcomes.get(fid)
            fact_path = root / "artifacts/facts" / (fid.replace("F:", "F-") + ".json")
            if not fact_path.is_file() or not isinstance(outcome, dict):
                raise RegistryError(f"{t_label} has no fact or receipt outcome")
            fact = json.loads(fact_path.read_text())
            statement = (fact.get("formal") or {}).get("statement")
            if (
                outcome.get("target_definition") != target["target_definition"]
                or outcome.get("axiom_footprint") != []
                or outcome.get("theorem_dependencies") != 1
                or outcome.get("target_dependency") is not False
                or outcome.get("independently_admitted") is not True
                or not isinstance(statement, str)
                or hashlib.sha256(statement.encode()).hexdigest()
                != outcome.get("formal_statement_sha256")
            ):
                raise RegistryError(f"{t_label} receipt contract disagrees")
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
    elif driver == "axeyum-lean-import/conclusion-directed-family-multi-target-v1":
        additional = nonempty_strings(
            value["additional_fact_ids"], f"{label}.additional_fact_ids"
        )
        all_fact_ids = [value["input_fact_id"], *additional]
        if len(all_fact_ids) != len(set(all_fact_ids)) or any(
            not FACT_ID_RE.fullmatch(fid) for fid in all_fact_ids
        ):
            raise RegistryError(f"{label} has duplicate or invalid fact ids")
        manifest_path = repository_file(
            value["receipt_manifest"], f"{label}.receipt_manifest", root
        )
        if manifest_path.parent != (root / "artifacts/autogenesis").resolve():
            raise RegistryError(f"{label}.receipt_manifest must be canonical")
        manifest = json.loads(manifest_path.read_text())
        if (
            manifest.get("schema_version") != 1
            or manifest.get("kind") != "axeyum-autogenesis-nat-modeq-congruence-contract"
            or (manifest.get("contract_source") or {}).get("lean_axiom_footprint") != []
            or (manifest.get("producer") or {}).get("max_goal_binders")
            != value["max_goal_binders"]
            or (manifest.get("producer") or {}).get("max_holes") != value["max_holes"]
        ):
            raise RegistryError(f"{label}.receipt_manifest is not operation-eligible")
        # The train facts this contract's shapes were established on FIRST.
        # `check-development-partition.py` requires an operation that closes a
        # development fact to reference a train fact, because a producer whose
        # whole applicability was authored against the evaluation set no longer
        # measures generalization. This field is that reference, and it is
        # enforced rather than declared: every id must be in the `train`
        # partition of the nursery AND already `proved`, so it cannot be
        # satisfied by naming an open or development fact.
        train_ids = nonempty_strings(
            value["generalization_train_fact_ids"],
            f"{label}.generalization_train_fact_ids",
        )
        nursery = json.loads(
            (root / "artifacts/autogenesis/nursery-v1.json").read_text()
        )
        partitions = {
            entry.get("fact_id"): entry.get("partition")
            for entry in nursery.get("entries", [])
        }
        for train_id in train_ids:
            if partitions.get(train_id) != "train":
                raise RegistryError(
                    f"{label}.generalization_train_fact_ids names {train_id!r}, "
                    "which is not in the nursery's train partition"
                )
            train_path = root / "artifacts/facts" / (
                train_id.replace("F:", "F-") + ".json"
            )
            if not train_path.is_file():
                raise RegistryError(f"{label} train fact does not exist: {train_id}")
            train_fact = json.loads(train_path.read_text())
            if train_fact.get("epistemic_status") not in {"proved", "computed"}:
                raise RegistryError(
                    f"{label}.generalization_train_fact_ids names {train_id!r}, "
                    "which is not established — a generalization source must be "
                    "settled before the development targets are claimed"
                )
        outcomes = {row.get("fact_id"): row for row in manifest.get("outcomes", [])}
        targets = value["targets"]
        if not isinstance(targets, list) or len(targets) != len(all_fact_ids):
            raise RegistryError(
                f"{label}.targets must bind every named fact exactly once"
            )
        target_fact_ids = []
        for index, target in enumerate(targets):
            t_label = f"{label}.targets[{index}]"
            if not isinstance(target, dict):
                raise RegistryError(f"{t_label} must be an object")
            exact_keys(target, {"fact_id", "target_definition"}, t_label)
            fid = target["fact_id"]
            target_fact_ids.append(fid)
            outcome = outcomes.get(fid)
            fact_path = root / "artifacts/facts" / (fid.replace("F:", "F-") + ".json")
            if not fact_path.is_file() or not isinstance(outcome, dict):
                raise RegistryError(f"{t_label} has no fact or receipt outcome")
            if (
                outcome.get("target_definition") != target["target_definition"]
                or outcome.get("axiom_footprint") != []
                or outcome.get("theorem_dependencies") != 1
                or outcome.get("target_dependency") is not False
                or outcome.get("independently_admitted") is not True
            ):
                raise RegistryError(f"{t_label} receipt contract disagrees")
        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
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
        contract = SEALED_CAPSULE_CONTRACTS.get(value["input_fact_id"])
        if contract is None:
            raise RegistryError(f"{label} exceeds the exact sealed-capsule scope")
        expected_manifest = (root / contract["result_manifest"]).resolve()
        manifest = json.loads(manifest_path.read_text())
        if value["input_fact_id"] in {
            "F:ml430-int-fib-eq-zero-8193c7cb",
            "F:ml430-nat-fib-eq-zero-61879073",
            "F:ml430-nat-fib-pos-9e67bd8e",
            "F:ml430-int-fib-natcast-d5886be4",
            "F:ml430-int-fib-add-two-739358dd",
            "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d",
            "F:ml430-int-fib-add-one-33f1b748",
            "F:ml430-int-fib-neg-b4021d37",
            "F:ml430-int-gcd-fib-73bdafc2",
            "F:ml430-int-fib-gcd-3a8bfdec",
            "F:ml430-int-fib-dvd-ffb3c5c1",
            "F:ml430-int-fib-of-nonneg-438018c5",
        }:
            theorem = manifest.get("theorem") or {}
            execution = manifest.get("execution") or {}
            is_add_two = (
                value["input_fact_id"] == "F:ml430-int-fib-add-two-739358dd"
            )
            is_corollary = (
                value["input_fact_id"]
                == "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d"
            )
            is_add_one = (
                value["input_fact_id"] == "F:ml430-int-fib-add-one-33f1b748"
            )
            is_neg = value["input_fact_id"] == "F:ml430-int-fib-neg-b4021d37"
            is_gcd_fib = value["input_fact_id"] == "F:ml430-int-gcd-fib-73bdafc2"
            is_fib_gcd = value["input_fact_id"] == "F:ml430-int-fib-gcd-3a8bfdec"
            is_fib_dvd = value["input_fact_id"] == "F:ml430-int-fib-dvd-ffb3c5c1"
            is_fib_of_nonneg = (
                value["input_fact_id"] == "F:ml430-int-fib-of-nonneg-438018c5"
            )
            is_nat_fib_pos = (
                value["input_fact_id"] == "F:ml430-nat-fib-pos-9e67bd8e"
            )
            is_nat_fib_eq_zero = (
                value["input_fact_id"] == "F:ml430-nat-fib-eq-zero-61879073"
            )
            is_int_fib_eq_zero = (
                value["input_fact_id"] == "F:ml430-int-fib-eq-zero-8193c7cb"
            )
            expected_dependencies = (
                [
                    "Axeyum.Autogenesis.intFibEqZeroResidualV1",
                    "Axeyum.Autogenesis.intFibNatAbsV1",
                    "Axeyum.Autogenesis.intNatAbsEqZeroV1",
                    "Nat.fib_eq_zero",
                ]
                if is_int_fib_eq_zero
                else
                [
                    "Axeyum.Autogenesis.natFibEqZeroResidualV1",
                    "Axeyum.Autogenesis.natFibZeroV1",
                    "Nat.fib_pos",
                    "Nat.zero_lt_succ",
                ]
                if is_nat_fib_eq_zero
                else [
                    "Axeyum.Autogenesis.natFibOnePositiveV1",
                    "Axeyum.Autogenesis.natFibPosResidualV1",
                    "Axeyum.Autogenesis.natFibStepPositiveV1",
                    "Axeyum.Autogenesis.natFibZeroV1",
                    "Nat.zero_lt_succ",
                ]
                if is_nat_fib_pos
                else [
                    "Axeyum.Autogenesis.fibAddTwo",
                    "Axeyum.IntFib.castAdd",
                    "Axeyum.IntFib.evenAdd",
                    "Axeyum.IntFib.modCases",
                    "Axeyum.IntFib.oddAdd",
                    "Axeyum.IntFib.succOne",
                    "Axeyum.IntFib.succZero",
                    "Int.fib_add_two_residual",
                ]
                if is_add_two
                else [
                    "Axeyum.Autogenesis.intFibEqAddTwoSubAddOneResidualV2",
                    "Int.add_neg_cancel_right",
                    "Int.fib_add_two",
                ]
                if is_corollary
                else [
                    "Axeyum.Autogenesis.intFibAddOneResidualV3",
                    "Int.add_comm",
                    "Int.add_neg_cancel_right",
                    "Int.fib_add_two",
                ]
                if is_add_one
                else [
                    "Axeyum.Autogenesis.intFibNegFunctionResidualV1",
                    "Axeyum.Autogenesis.intFibNegNegativeBranchV1",
                    "Axeyum.Autogenesis.intFibNegPositiveBranchV1",
                ]
                if is_neg
                else [
                    "Axeyum.Autogenesis.intFibNatAbsV1",
                    "Eq.symm",
                    "Eq.trans",
                    "Int.gcd_def",
                    "Nat.fib_gcd",
                ]
                if is_gcd_fib
                else ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]
                if is_fib_gcd
                else [
                    "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
                    "Axeyum.Autogenesis.intFibNatAbsV1",
                    "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
                    "Axeyum.Autogenesis.intNatAbsMulDirectV1",
                    "Eq.symm",
                    "Nat.fib_dvd",
                ]
                if is_fib_dvd
                else [
                    "Axeyum.Autogenesis.intFibOfNonnegResidualV1",
                    "Int.fib_natCast",
                ]
                if is_fib_of_nonneg
                else []
            )
            if (
                manifest_path != expected_manifest
                or manifest.get("state")
                != (
                    "exact-goal-identity-bound-without-rendering"
                    if is_int_fib_eq_zero or is_nat_fib_eq_zero or is_nat_fib_pos or is_add_two or is_corollary or is_add_one or is_neg or is_gcd_fib or is_fib_gcd or is_fib_dvd or is_fib_of_nonneg
                    else "single-read-hash-only-identity-qualified"
                )
                or value["capsule_path"] != contract["capsule_path"]
                or value["capsule_sha256"] != contract["capsule_sha256"]
                or value["target_theorem"] != contract["target_theorem"]
                or theorem.get("name") != value["target_theorem"]
                or theorem.get("canonical_type_sha256") != value["goal_sha256"]
                or theorem.get("canonical_declaration_sha256")
                != value["declaration_sha256"]
                or theorem.get("axiom_footprint") != []
                or theorem.get("direct_theorem_dependencies")
                != expected_dependencies
                or execution.get("importer_runs") != 1
                or execution.get(
                    "stream_reads"
                    if is_int_fib_eq_zero or is_nat_fib_eq_zero or is_nat_fib_pos or is_add_two or is_corollary or is_add_one or is_neg or is_gcd_fib or is_fib_gcd or is_fib_dvd or is_fib_of_nonneg
                    else "proof_bearing_stream_reads"
                )
                != 1
                or (
                    execution.get("theorem_submissions") != 0
                    if not is_int_fib_eq_zero and not is_nat_fib_eq_zero and not is_nat_fib_pos and not is_add_two and not is_corollary and not is_add_one and not is_neg and not is_gcd_fib and not is_fib_gcd and not is_fib_dvd and not is_fib_of_nonneg
                    else execution.get("ledger_writes") != 0
                )
                or execution.get("retries") != 0
                or value["receipt_sha256"] != contract["receipt_sha256"]
            ):
                raise RegistryError(
                    f"{label} integer Fibonacci capsule contract disagrees"
                )
        theorem = manifest.get("target") or {}
        execution = manifest.get("execution") or {}
        if (
            value["input_fact_id"]
            not in {
                "F:ml430-int-fib-eq-zero-8193c7cb",
                "F:ml430-nat-fib-eq-zero-61879073",
                "F:ml430-nat-fib-pos-9e67bd8e",
                "F:ml430-int-fib-natcast-d5886be4",
                "F:ml430-int-fib-add-two-739358dd",
                "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d",
                "F:ml430-int-fib-add-one-33f1b748",
                "F:ml430-int-fib-neg-b4021d37",
                "F:ml430-int-gcd-fib-73bdafc2",
                "F:ml430-int-fib-gcd-3a8bfdec",
                "F:ml430-int-fib-dvd-ffb3c5c1",
                "F:ml430-int-fib-of-nonneg-438018c5",
            }
            and (
                manifest_path != expected_manifest
                or manifest.get("state")
                != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
                or value["capsule_path"] != contract["capsule_path"]
                or value["capsule_sha256"] != contract["capsule_sha256"]
                or value["target_theorem"] != contract["target_theorem"]
                or theorem.get("name") != value["target_theorem"]
                or theorem.get("goal_sha256") != value["goal_sha256"]
                or theorem.get("declaration_sha256") != value["declaration_sha256"]
                or theorem.get("axiom_footprint") != []
                or execution.get("complete_invocations") != 2
                or (
                    execution.get("exact_target_submissions") != 2
                    and execution.get("target_theorem_submissions") != 2
                )
                or execution.get("fresh_imports") != 4
                or execution.get("outputs_byte_identical") is not True
                or (
                    execution.get("receipts_byte_identical") is not True
                    and execution.get("observations_byte_identical") is not True
                )
                or value["receipt_sha256"] != contract["receipt_sha256"]
            )
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


def check_fact_provenance_is_exclusive(
    root: pathlib.Path, fact_operation_ids: dict[str, list[str]]
) -> None:
    """A fact may be named by several operations; at most one may PROVE it.

    `applicability.fact_ids` is structural coverage -- which operations a
    fact-agnostic producer *could* re-derive -- and more than one operation
    legitimately naming the same fact is by design (a target-agnostic
    bounded-induction family alongside the narrower operation that actually
    produced the fact; see `check-autogenesis-bounded-induction-family.py`'s
    own `SETTLED_FACT_IDS` split for the worked example). What must never
    happen is the fact ITSELF becoming ambiguous about which operation is its
    provenance: two checked evidence rows bound to two different operations,
    or a checked evidence row bound to an operation that does not even name
    the fact. Both are silent forks in every downstream reader that resolves
    a fact to "its" operation (`check-autogenesis-fact-operation.py`,
    `fact-frontier.py`'s dispatch). This only inspects facts named by 2+
    operations; a fact named by exactly one has nothing to be ambiguous about.
    """
    for fact_id, operation_ids in sorted(fact_operation_ids.items()):
        if len(operation_ids) < 2:
            continue
        fact_path = root / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json")
        fact = json.loads(fact_path.read_text())
        bound = sorted(
            {
                row["checker_operation"]["id"]
                for row in fact.get("evidence") or []
                if isinstance(row.get("checker_operation"), dict)
                and isinstance(row["checker_operation"].get("id"), str)
            }
        )
        if len(bound) > 1:
            raise RegistryError(
                f"fact {fact_id} is named by {sorted(operation_ids)} in "
                "applicability.fact_ids and carries checked evidence bound to "
                f"more than one of them ({bound}) -- several operations may "
                "structurally cover one fact, but exactly one may hold its "
                "provenance"
            )
        if bound and bound[0] not in operation_ids:
            raise RegistryError(
                f"fact {fact_id} evidence is bound to operation {bound[0]!r}, "
                "which does not name this fact in its applicability.fact_ids"
            )


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
    fact_operation_ids: dict[str, list[str]] = {}
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
        if scope == "authoritative":
            for fact_id in fact_ids:
                fact_operation_ids.setdefault(fact_id, []).append(operation_id)
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
            if executor["driver"] in {
                "axeyum-lean-kernel/authored-declaration-v1",
                "axeyum-lean-import/bounded-induction-multi-target-v1",
                "axeyum-lean-import/modeq-family-multi-target-v1",
                "axeyum-lean-import/imported-candidate-family-multi-target-v1",
                "axeyum-lean-import/conclusion-directed-family-multi-target-v1",
            }:
                all_ids = [
                    executor["input_fact_id"],
                    *executor.get("additional_fact_ids", []),
                ]
                if fact_ids != all_ids:
                    raise RegistryError(
                        f"{label}.executor must bind exactly its applicable fact "
                        "ids, in order (input_fact_id then additional_fact_ids)"
                    )
            elif executor["input_fact_id"] not in fact_ids or fact_ids != [
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
            elif executor["driver"] == "axeyum-lean-kernel/authored-declaration-v1":
                # Fragment-agnostic like modeq-family-multi-target-v1 (this
                # driver is not tied to Int specifically -- a future
                # hand-authored Nat closure is the same shape), but the proof
                # itself runs entirely inside this repository's own kernel
                # crate, never through the importer.
                if (
                    applicability["formal_languages"] != ["lean4-surface"]
                    or applicability["fragments"]
                    not in (["Int"], ["Nat"], ["Int", "Nat"])
                    or admission["proof_route"] != "kernel-lean"
                    or admission["evidence_kind"] != "kernel-term"
                    or admission["axiom_footprint"] != []
                ):
                    raise RegistryError(
                        f"{label}.executor driver is inconsistent with applicability/admission"
                    )
            elif executor["driver"] in {
                "axeyum-lean-import/statement-reflexivity-v1",
                "axeyum-lean-import/bounded-induction-multi-target-v1",
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
            elif executor["driver"] == "axeyum-lean-import/modeq-family-multi-target-v1":
                # The producer is fragment-agnostic (it never names Int, Nat,
                # ModEq, or %; see producers::modeq_family) and a single
                # operation may legitimately span both -- authored on the Int
                # train facts, generalizing to the Nat development facts. So
                # the closed set of valid values is every nonempty subset of
                # {Int, Nat}, not just the two singletons.
                if (
                    applicability["formal_languages"] != ["lean4-surface"]
                    or applicability["fragments"]
                    not in (["Int"], ["Nat"], ["Int", "Nat"])
                    or admission["proof_route"] != "kernel-lean"
                    or admission["evidence_kind"] != "kernel-term"
                    or admission["axiom_footprint"] != []
                ):
                    raise RegistryError(
                        f"{label}.executor driver is inconsistent with applicability/admission"
                    )
            elif executor["driver"] == "axeyum-lean-import/imported-candidate-family-multi-target-v1":
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
            elif executor["driver"] == "axeyum-lean-import/conclusion-directed-family-multi-target-v1":
                # The producer is theory-agnostic (it never names a carrier, a
                # relation, or a target; see
                # producers::conclusion_directed_application), but the LEAN
                # CANDIDATE CONTRACT it transports is not, and the transport
                # route requires an empty axiom footprint. Measured 2026-08-28,
                # every Lean 4.30 `Int` lemma probed carries `propext` --
                # including `Int.add_comm` and `Int.sub_self` -- so no `Int`
                # target is reachable this way and `Nat` is the only fragment
                # this driver can legitimately claim today. Widen this only
                # against a measurement, not against an intention.
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
                    or applicability["fragments"]
                    not in (
                        [["Nat"], ["Int"]]
                        if executor["driver"]
                        == "axeyum-lean-import/sealed-kernel-capsule-v1"
                        else [["Nat"]]
                    )
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
    check_fact_provenance_is_exclusive(root, fact_operation_ids)


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
