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
    def observation(contract: dict) -> dict:
        observation = {
            field: {
                "field": field,
                "ordinal": index,
                "values": [index, f"value-{index}"],
            }
            for index, field in enumerate(contract["compared_fields"])
        }
        observation.update(
            {
                "collector_sequence": 17,
                "evidence_storage_path": "/tmp/root-a/evidence.json",
            }
        )
        return observation

    def test_committed_registry_is_exact_and_deterministic(self) -> None:
        self.assertEqual(NORMALIZATION.validate_manifest(self.data), [])
        self.assertEqual(
            tuple(contract["id"] for contract in self.data["contracts"]),
            NORMALIZATION.CONTRACT_IDS,
        )
        self.assertEqual(
            sum(len(contract["compared_fields"]) for contract in self.data["contracts"]),
            68,
        )
        self.assertEqual(
            sum(len(contract["ignored_fields"]) for contract in self.data["contracts"]),
            18,
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
                mutated[field] = {"semantic_mutation": field}
                self.assertNotEqual(
                    NORMALIZATION.normalized_observation_digest(
                        self.data, contract["id"], mutated
                    ),
                    baseline_digest,
                    f"semantic field did not affect digest: {contract['id']}:{field}",
                )
                mutations += 1
        self.assertEqual(mutations, 68)

    def test_every_ignored_rule_preserves_projection_digest(self) -> None:
        mutations = 0
        for contract in self.data["contracts"]:
            baseline = self.observation(contract)
            baseline_digest = NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], baseline
            )
            for rule in contract["ignored_fields"]:
                mutated = copy.deepcopy(baseline)
                mutated[rule["field"]] = f"ignored-mutation-{contract['id']}"
                self.assertEqual(
                    NORMALIZATION.normalized_observation_digest(
                        self.data, contract["id"], mutated
                    ),
                    baseline_digest,
                    f"ignored field changed digest: {contract['id']}:{rule['field']}",
                )
                mutations += 1
        self.assertEqual(mutations, 18)

    def test_projection_is_allowlist_based_and_rejects_malformed_values(self) -> None:
        contract = self.data["contracts"][0]
        observation = self.observation(contract)

        missing = copy.deepcopy(observation)
        missing.pop(contract["compared_fields"][0])
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "missing="):
            NORMALIZATION.normalize_observation(self.data, contract["id"], missing)

        extra = copy.deepcopy(observation)
        extra["unregistered_field"] = "must reject"
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "extra="):
            NORMALIZATION.normalize_observation(self.data, contract["id"], extra)

        floating = copy.deepcopy(observation)
        floating[contract["compared_fields"][0]] = {"nested": [1, 0.5]}
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "floating-point"):
            NORMALIZATION.normalize_observation(self.data, contract["id"], floating)

        unsupported = copy.deepcopy(observation)
        unsupported[contract["compared_fields"][0]] = ("tuple",)
        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "unsupported"):
            NORMALIZATION.normalize_observation(
                self.data, contract["id"], unsupported
            )

        with self.assertRaisesRegex(NORMALIZATION.ObservationError, "unknown"):
            NORMALIZATION.normalize_observation(
                self.data, "invented-normalizer-v1", observation
            )

    def test_object_key_order_is_canonical_but_array_order_is_semantic(self) -> None:
        contract = self.data["contracts"][0]
        field = contract["compared_fields"][0]
        left = self.observation(contract)
        right = self.observation(contract)
        left[field] = {"outer": {"a": 1, "b": 2}, "array": [1, 2]}
        right[field] = {"array": [1, 2], "outer": {"b": 2, "a": 1}}
        self.assertEqual(
            NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], left
            ),
            NORMALIZATION.normalized_observation_digest(
                self.data, contract["id"], right
            ),
        )
        right[field]["array"] = [2, 1]
        self.assertNotEqual(
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
        ][0]["compared_fields"][0]
        self.assertTrue(
            any(
                "ignored fields/order drift" in failure or "overlap" in failure
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
