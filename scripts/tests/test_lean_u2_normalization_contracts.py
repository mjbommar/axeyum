from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "lean_u2_normalization_contracts",
    ROOT / "scripts" / "lean_u2_normalization_contracts.py",
)
assert SPEC and SPEC.loader
NORMALIZATION = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = NORMALIZATION
SPEC.loader.exec_module(NORMALIZATION)


class LeanU2NormalizationContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = NORMALIZATION.load_manifest()

    @staticmethod
    def valid_value(field: dict, variant: int = 0):
        kind = field["kind"]
        if kind == "sha256":
            return ("a" if variant == 0 else "b") * 64
        if kind == "enum":
            return field["values"][variant]
        if kind == "nonnegative-integer":
            return 17 + variant
        if kind == "nonempty-string":
            return f"/tmp/root-{'a' if variant == 0 else 'b'}/evidence.json"
        raise AssertionError(f"unknown test schema {kind!r}")

    @classmethod
    def observation(cls, contract: dict, variant: int = 0) -> dict:
        return {
            field["field"]: cls.valid_value(field, variant)
            for field in contract["compared_fields"] + contract["ignored_fields"]
        }

    @staticmethod
    def invalid_value(field: dict):
        return {
            "sha256": "not-a-digest",
            "enum": "not-registered",
            "nonnegative-integer": -1,
            "nonempty-string": "",
        }[field["kind"]]

    def test_committed_registry_is_exact_typed_and_deterministic(self) -> None:
        self.assertEqual(NORMALIZATION.validate_manifest(self.data), [])
        self.assertEqual(
            tuple(contract["id"] for contract in self.data["contracts"]),
            NORMALIZATION.CONTRACT_IDS,
        )
        self.assertEqual(self.data["summary"]["contracts"], 10)
        self.assertEqual(self.data["summary"]["compared_fields"], 76)
        self.assertEqual(self.data["summary"]["ignored_rules"], 20)
        self.assertEqual(self.data["summary"]["covered_axes"], 12)
        self.assertEqual(self.data["summary"]["axis_contract_occurrences"], 15)
        self.assertEqual(self.data["summary"]["typed_field_occurrences"], 96)
        self.assertEqual(
            self.data["summary"]["value_schema_counts"],
            {
                "enum": 3,
                "nonempty-string": 10,
                "nonnegative-integer": 10,
                "sha256": 73,
            },
        )
        self.assertTrue(
            (ROOT / "docs/plan/lean-u2-normalization-contracts-v1.json").is_file()
        )
        self.assertTrue(
            (ROOT / "docs/plan/lean-u2-normalization-contracts-v2.json").is_file()
        )
        self.assertEqual(
            NORMALIZATION.MANIFEST.name, "lean-u2-normalization-contracts-v3.json"
        )
        self.assertEqual(
            tuple(
                NORMALIZATION.load_execution_evidence()["taxonomies"][
                    "termination_classes"
                ]
            ),
            NORMALIZATION.TERMINATION_CLASSES,
        )
        for contract in self.data["contracts"]:
            self.assertEqual(
                contract["contract_sha256"],
                NORMALIZATION.normalization_contract_digest(contract),
            )
        self.assertEqual(
            NORMALIZATION.render_markdown(self.data),
            NORMALIZATION.render_markdown(copy.deepcopy(self.data)),
        )

    def test_every_semantic_field_changes_its_projection_digest(self) -> None:
        mutations = 0
        for contract in self.data["contracts"]:
            baseline = self.observation(contract)
            baseline_digest = NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], baseline
            )
            for field in contract["compared_fields"]:
                mutated = copy.deepcopy(baseline)
                mutated[field["field"]] = self.valid_value(field, 1)
                self.assertNotEqual(
                    NORMALIZATION.normalized_observation_digest(
                        self.data, contract["id"], mutated
                    ),
                    baseline_digest,
                    f"semantic field did not affect digest: {contract['id']}:{field['field']}",
                )
                mutations += 1
        self.assertEqual(mutations, 76)

    def test_every_ignored_rule_preserves_projection_digest(self) -> None:
        mutations = 0
        for contract in self.data["contracts"]:
            baseline = self.observation(contract)
            baseline_digest = NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], baseline
            )
            for rule in contract["ignored_fields"]:
                mutated = copy.deepcopy(baseline)
                mutated[rule["field"]] = self.valid_value(rule, 1)
                self.assertEqual(
                    NORMALIZATION.normalized_observation_digest(
                        self.data, contract["id"], mutated
                    ),
                    baseline_digest,
                    f"ignored field changed digest: {contract['id']}:{rule['field']}",
                )
                mutations += 1
        self.assertEqual(mutations, 20)

    def test_every_field_schema_rejects_a_malformed_value(self) -> None:
        rejected = 0
        for contract in self.data["contracts"]:
            baseline = self.observation(contract)
            for field in contract["compared_fields"] + contract["ignored_fields"]:
                mutated = copy.deepcopy(baseline)
                mutated[field["field"]] = self.invalid_value(field)
                with self.assertRaisesRegex(
                    NORMALIZATION.ObservationError, contract["id"]
                ):
                    NORMALIZATION.normalize_observation(
                        self.data, contract["id"], mutated
                    )
                rejected += 1
        self.assertEqual(rejected, 96)

    def test_projection_is_allowlist_based_and_rejects_wrong_value_shapes(self) -> None:
        contract = self.data["contracts"][0]
        first_field = contract["compared_fields"][0]["field"]
        observation = self.observation(contract)

        missing = copy.deepcopy(observation)
        missing.pop(first_field)
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "missing="):
            NORMALIZATION.normalize_observation(self.data, contract["id"], missing)

        extra = copy.deepcopy(observation)
        extra["unregistered_field"] = "must reject"
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "extra="):
            NORMALIZATION.normalize_observation(self.data, contract["id"], extra)

        for malformed in ({"object": "reject"}, ["array", "reject"], 7, None):
            wrong_shape = copy.deepcopy(observation)
            wrong_shape[first_field] = malformed
            with self.assertRaisesRegex(NORMALIZATION.ObservationError, "SHA-256"):
                NORMALIZATION.normalize_observation(
                    self.data, contract["id"], wrong_shape
                )

        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "unknown"):
            NORMALIZATION.normalize_observation(
                self.data, "lean-process-harness-v1", observation
            )
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "unknown"):
            NORMALIZATION.normalize_observation(
                self.data, "lean-process-harness-v2", observation
            )
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "unknown"):
            NORMALIZATION.normalize_observation(
                self.data, "invented-normalizer-v3", observation
            )

    def test_axis_coverage_and_mathlib_contract_are_exact(self) -> None:
        pairs = {
            (contract["id"], axis)
            for contract in self.data["contracts"]
            for axis in contract["applicable_axes"]
        }
        self.assertEqual(len(pairs), 15)
        self.assertEqual(
            {axis for _, axis in pairs}, set(NORMALIZATION.AXIS_IDS)
        )
        mathlib = next(
            contract
            for contract in self.data["contracts"]
            if contract["layer"] == "mathlib-ecosystem"
        )
        self.assertEqual(mathlib["applicable_axes"], ["A10"])
        self.assertEqual(
            [field["field"] for field in mathlib["compared_fields"]],
            [
                "axiom_trust_closure_sha256",
                "build_outcomes_sha256",
                "declaration_closure_sha256",
                "failure_classification_sha256",
                "module_outcomes_sha256",
                "runtime_tests_sha256",
                "tactic_results_sha256",
                "test_outcomes_sha256",
            ],
        )

        missing_a10 = copy.deepcopy(self.data)
        missing_a10["contracts"][-1]["applicable_axes"] = []
        missing_a10["contracts"][-1]["contract_sha256"] = (
            NORMALIZATION.normalization_contract_digest(
                missing_a10["contracts"][-1]
            )
        )
        self.assertTrue(
            any(
                "cover exactly A0-A11" in failure
                for failure in NORMALIZATION.validate_manifest(missing_a10)
            )
        )

        for axes in (["A0", "A0", "A11"], ["A11", "A0"], ["A0", "A12"]):
            malformed = copy.deepcopy(self.data)
            malformed["contracts"][0]["applicable_axes"] = axes
            malformed["contracts"][0]["contract_sha256"] = (
                NORMALIZATION.normalization_contract_digest(
                    malformed["contracts"][0]
                )
            )
            self.assertTrue(
                any(
                    "known, unique, and sorted" in failure
                    for failure in NORMALIZATION.validate_manifest(malformed)
                )
            )

    def test_digest_integer_and_enum_controls_fail_closed(self) -> None:
        process = self.data["contracts"][0]
        digest_field = process["compared_fields"][0]["field"]
        sequence_field = process["ignored_fields"][0]["field"]
        for malformed in ("A" * 64, "a" * 63, "a" * 65, "g" * 64):
            observation = self.observation(process)
            observation[digest_field] = malformed
            with self.assertRaisesRegex(NORMALIZATION.ObservationError, "SHA-256"):
                NORMALIZATION.normalize_observation(
                    self.data, process["id"], observation
                )
        observation = self.observation(process)
        observation[sequence_field] = True
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "integer"):
            NORMALIZATION.normalize_observation(self.data, process["id"], observation)

        enum_contract = copy.deepcopy(self.data)
        enum = enum_contract["contracts"][0]["compared_fields"][-1]
        controls = ([], ["exited", "exited"], ["signaled", "exited"], [7])
        for malformed in controls:
            mutated = copy.deepcopy(enum_contract)
            mutated["contracts"][0]["compared_fields"][-1]["values"] = malformed
            self.assertTrue(NORMALIZATION.validate_manifest(mutated))

    def test_top_level_object_order_is_canonical(self) -> None:
        contract = self.data["contracts"][0]
        left = self.observation(contract)
        right = dict(reversed(tuple(left.items())))
        self.assertEqual(
            NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], left
            ),
            NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], right
            ),
        )

    def test_contract_schema_mutations_fail_closed(self) -> None:
        stale_seal = copy.deepcopy(self.data)
        stale_seal["contracts"][0]["ignored_fields"][0]["reason"] += " drift"
        self.assertTrue(
            any(
                "contract_sha256 does not match" in failure
                for failure in NORMALIZATION.validate_manifest(stale_seal)
            )
        )

        overlap = copy.deepcopy(self.data)
        overlap["contracts"][0]["ignored_fields"][0]["field"] = overlap[
            "contracts"
        ][0]["compared_fields"][0]["field"]
        self.assertTrue(
            any(
                "ignored field schemas/order drift" in failure or "overlap" in failure
                for failure in NORMALIZATION.validate_manifest(overlap)
            )
        )

        reordered = copy.deepcopy(self.data)
        reordered["contracts"] = list(reversed(reordered["contracts"]))
        self.assertTrue(
            any(
                "contract ids/order" in failure
                for failure in NORMALIZATION.validate_manifest(reordered)
            )
        )

        credited = copy.deepcopy(self.data)
        credited["claims"]["parents_complete"] = True
        self.assertTrue(
            any(
                "offline non-credit boundary" in failure
                for failure in NORMALIZATION.validate_manifest(credited)
            )
        )


if __name__ == "__main__":
    unittest.main()
