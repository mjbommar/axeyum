from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-auto-param-binder-replay.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_auto_param_binder_replay", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def digest(index: int) -> str:
    return f"{index + 1:064x}"


def sign_receipt(receipt):
    receipt["receipt_sha256"] = MODULE.canonical_digest(receipt)


def sign_observation(observation):
    unsigned = {key: value for key, value in observation.items() if key != "observation_sha256"}
    observation["observation_sha256"] = MODULE.canonical_digest(unsigned)


NORMALIZATION_ROWS = {
    14: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
    57: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
    58: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
    64: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
    65: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
    81: (["Preorder.mk", "Preorder.rec"], 4),
    88: (["Preorder.mk", "Preorder.rec"], 4),
    90: (["Preorder.mk", "Preorder.rec"], 4),
    124: (["Monoid.mk", "Monoid.rec"], 8),
    128: (["AddMonoid.mk", "AddMonoid.rec", "Monoid.mk", "Monoid.rec", "Semiring.mk", "Semiring.rec"], 24),
}


class AutoParamBinderReplayTests(unittest.TestCase):
    def inputs(self):
        mapping_rows = []
        observation_rows = []
        for index in range(138):
            common = {
                "artifact_file": f"r{index:03}.ndjson",
                "fact_id": f"F:test-{index:03}",
                "family": "control",
                "partition": "development" if index % 5 == 0 else "train",
                "target_definition": f"Control.r{index:03}",
            }
            mapping_rows.append(dict(common))
            abstractions = []
            for position in range(2 if index < 14 else 1):
                abstractions.append(
                    {
                        "binder_position": position,
                        "source_name": f"Helper.{index}.{position}",
                        "source_occurrences": 1,
                        "instantiated_type_sha256": digest(5000 + index * 2 + position),
                        "source_content_sha256": digest(6000 + index * 2 + position),
                        "universe_sha256": [],
                    }
                )
            receipt = {
                "schema_version": MODULE.V1_SCHEMA,
                "policy_version": MODULE.POLICY_VERSION,
                "specialization_verified": True,
                "fresh_target_content_sha256": digest(1000 + index),
                "sliced_goal_sha256": digest(2000 + index),
                "source": {
                    "stream_sha256": digest(index),
                    "target": common["target_definition"],
                    "goal_sha256": digest(3000 + index),
                    "target_content_sha256": digest(4000 + index),
                },
                "retained": [],
                "abstractions": abstractions,
            }
            if index in NORMALIZATION_ROWS:
                names, rewrites = NORMALIZATION_ROWS[index]
                declarations = []
                for offset, name in enumerate(names):
                    source_hash = digest(10000 + index * 10 + offset)
                    normalized_hash = digest(12000 + index * 10 + offset)
                    dependency_hash = digest(14000 + index * 10 + offset)
                    declarations.append(
                        {
                            "name": name,
                            "source_content_sha256": source_hash,
                            "normalized_content_sha256": normalized_hash,
                            "normalized_dependency_sha256": dependency_hash,
                        }
                    )
                    receipt["retained"].append(
                        {
                            "name": name,
                            "kind": "definition",
                            "content_sha256": normalized_hash,
                            "dependency_sha256": dependency_hash,
                        }
                    )
                receipt["schema_version"] = MODULE.V2_SCHEMA
                receipt["transport_normalization"] = {
                    "kind": MODULE.NORMALIZATION_KIND,
                    "auto_param_source_content_sha256": MODULE.AUTO_PARAM_SHA256,
                    "rewritten_occurrences": rewrites,
                    "declarations": declarations,
                }
            sign_receipt(receipt)
            observation_rows.append(
                {
                    **common,
                    "stream_sha256": digest(index),
                    "outcome": "accepted-receipt",
                    "receipt": receipt,
                }
            )
        mapping = {
            "kind": "axeyum-autogenesis-reflexivity-coverage-input",
            "state": "proof-free-source-input",
            "authority": {
                "nursery_sha256": "f23d76470e29719f5f4303d3e6d34fcd23bf2018692d6fe73fd9f17b85aa497b",
                "partitions_inspected": ["development", "train"],
                "held_out_inspected": False,
                "proof_bodies_accessed": False,
                "target_outcomes_accessed": False,
                "facts_opened": 138,
            },
            "rows": mapping_rows,
        }
        observation = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-checked-type-slice-replay",
            "state": "checked-slice-replay-no-proof-or-ledger-credit",
            "policy_version": MODULE.POLICY_VERSION,
            "authority": {
                "partitions_inspected": ["development", "train"],
                "held_out_inspected": False,
                "proof_producers_executed": False,
                "proof_bodies_requested": False,
                "ledger_writes": 0,
                "targets": 138,
            },
            "mapping_sha256": digest(9000),
            "coverage": {"accepted-receipt": 138},
            "rows": observation_rows,
        }
        sign_observation(observation)
        manifest = {
            "source_archive": {"mapping_sha256": digest(9000)},
            "observation_archive": {"observation_sha256": observation["observation_sha256"]},
            "coverage": {
                "accepted_receipts": 138,
                "declined_selection": 0,
                "exact_v1_receipts": 128,
                "normalized_v2_receipts": 10,
                "abstractions": 152,
                "rewritten_occurrences": 164,
                "normalized_artifacts": sorted(MODULE.NORMALIZED_ARTIFACTS),
            },
        }
        return manifest, observation, mapping

    def resign(self, values, index=14):
        receipt = values[1]["rows"][index]["receipt"]
        receipt.pop("receipt_sha256", None)
        sign_receipt(receipt)
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]

    def validate(self, values):
        MODULE.validate_observation(*values, source_root=None)

    def test_exact_control_is_accepted(self):
        self.validate(self.inputs())

    def test_held_out_mapping_is_rejected(self):
        values = self.inputs()
        values[2]["rows"][0]["partition"] = "held-out"
        with self.assertRaisesRegex(MODULE.BinderReplayError, "held-out"):
            self.validate(values)

    def test_observation_digest_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["family"] = "mutated"
        with self.assertRaisesRegex(MODULE.BinderReplayError, "identity"):
            self.validate(values)

    def test_receipt_digest_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][14]["receipt"]["receipt_sha256"] = digest(99999)
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.BinderReplayError, "receipt digest"):
            self.validate(values)

    def test_v2_downgrade_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][14]["receipt"]["schema_version"] = MODULE.V1_SCHEMA
        self.resign(values)
        with self.assertRaisesRegex(MODULE.BinderReplayError, "transport contract"):
            self.validate(values)

    def test_transport_removal_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][14]["receipt"].pop("transport_normalization")
        self.resign(values)
        with self.assertRaisesRegex(MODULE.BinderReplayError, "transport contract"):
            self.validate(values)

    def test_rewrite_count_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][14]["receipt"]["transport_normalization"]["rewritten_occurrences"] += 1
        self.resign(values)
        with self.assertRaisesRegex(MODULE.BinderReplayError, "coverage"):
            self.validate(values)

    def test_noop_normalization_is_rejected(self):
        values = self.inputs()
        declaration = values[1]["rows"][14]["receipt"]["transport_normalization"]["declarations"][0]
        declaration["source_content_sha256"] = declaration["normalized_content_sha256"]
        self.resign(values)
        with self.assertRaisesRegex(MODULE.BinderReplayError, "did not change"):
            self.validate(values)

    def test_retained_identity_mismatch_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][14]["receipt"]["retained"][0]["content_sha256"] = digest(99998)
        self.resign(values)
        with self.assertRaisesRegex(MODULE.BinderReplayError, "retained identity"):
            self.validate(values)

    def test_coverage_row_change_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["outcome"] = "decline:selection"
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.BinderReplayError, "every row"):
            self.validate(values)


if __name__ == "__main__":
    unittest.main()
