from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-checked-type-slice-replay.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_checked_type_slice_replay", SCRIPT)
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


class CheckedTypeSliceReplayTests(unittest.TestCase):
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
            row = {**common, "stream_sha256": digest(index)}
            if index < 128:
                receipt = {
                    "schema_version": "axeyum-proof-free-type-slice-receipt-v1",
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
                    "abstractions": [
                        {
                            "binder_position": 0,
                            "source_name": f"Helper.{index}",
                            "source_occurrences": 1,
                            "instantiated_type_sha256": digest(5000 + index),
                            "source_content_sha256": digest(6000 + index),
                            "universe_sha256": [],
                        }
                    ],
                }
                sign_receipt(receipt)
                row.update(outcome="accepted-receipt", receipt=receipt)
            else:
                row.update(
                    outcome="decline:selection",
                    decline={
                        "stage": "selection",
                        "reason": "TrustedRetainedClosure { declaration: test }",
                    },
                )
            observation_rows.append(row)
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
            "coverage": {"accepted-receipt": 128, "decline:selection": 10},
            "rows": observation_rows,
        }
        sign_observation(observation)
        manifest = {
            "source_archive": {"mapping_sha256": digest(9000)},
            "observation_archive": {"observation_sha256": observation["observation_sha256"]},
            "coverage": {
                "accepted_receipts": 128,
                "declined_selection": 10,
                "abstractions": 128,
                "accepted_with_abstractions": 128,
                "accepted_without_abstractions": 0,
                "max_abstractions_per_target": 1,
                "declined_artifacts": [f"r{index:03}.ndjson" for index in range(128, 138)],
            },
        }
        return manifest, observation, mapping

    def validate(self, values):
        MODULE.validate_observation(*values, source_root=None)

    def test_exact_control_is_accepted(self):
        self.validate(self.inputs())

    def test_held_out_mapping_is_rejected(self):
        values = self.inputs()
        values[2]["rows"][0]["partition"] = "held-out"
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "held-out"):
            self.validate(values)

    def test_inner_observation_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["family"] = "mutated"
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "identity"):
            self.validate(values)

    def test_receipt_digest_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["receipt"]["receipt_sha256"] = digest(9999)
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "receipt digest"):
            self.validate(values)

    def test_trusted_retained_declaration_is_rejected(self):
        values = self.inputs()
        receipt = values[1]["rows"][0]["receipt"]
        receipt["retained"].append(
            {
                "name": "Hidden.proof",
                "kind": "theorem",
                "content_sha256": digest(7000),
                "dependency_sha256": digest(7001),
            }
        )
        receipt.pop("receipt_sha256")
        sign_receipt(receipt)
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "trusted"):
            self.validate(values)

    def test_duplicate_observation_row_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][1] = copy.deepcopy(values[1]["rows"][0])
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "identity"):
            self.validate(values)

    def test_decline_stage_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][-1]["decline"]["stage"] = "receipt"
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "decline"):
            self.validate(values)

    def test_coverage_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["coverage"]["accepted-receipt"] = 127
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]
        with self.assertRaisesRegex(MODULE.CheckedSliceError, "coverage"):
            self.validate(values)


if __name__ == "__main__":
    unittest.main()
