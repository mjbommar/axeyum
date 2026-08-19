from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import unittest

from scripts.tests.test_check_autogenesis_auto_param_binder_replay import (
    AutoParamBinderReplayTests,
    digest,
    sign_observation,
    sign_receipt,
)


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-type-slice-producer-census.py"
SPEC = importlib.util.spec_from_file_location("check_autogenesis_type_slice_producer_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class TypeSliceProducerCensusTests(unittest.TestCase):
    def inputs(self):
        manifest, observation, mapping = AutoParamBinderReplayTests().inputs()
        exact_indices = {53, 70, *range(100, 122)}
        for index in exact_indices:
            receipt = observation["rows"][index]["receipt"]
            receipt["abstractions"] = []
            receipt.pop("receipt_sha256")
            sign_receipt(receipt)
        for index in range(24):
            receipt = observation["rows"][index]["receipt"]
            position = len(receipt["abstractions"])
            receipt["abstractions"].append(
                {
                    "binder_position": position,
                    "source_name": f"Extra.{index}",
                    "source_occurrences": 1,
                    "instantiated_type_sha256": digest(30000 + index),
                    "source_content_sha256": digest(31000 + index),
                    "universe_sha256": [],
                }
            )
            receipt.pop("receipt_sha256")
            sign_receipt(receipt)
        observation["kind"] = "axeyum-autogenesis-type-slice-producer-census"
        observation["state"] = "diagnostic-fixed-budget-no-ledger-credit"
        observation["producer_policy"] = MODULE.PRODUCER_POLICY
        observation["authority"]["proof_producers_executed"] = True
        observation["budget"] = {
            "producer": MODULE.PRODUCER,
            "max_binders": 8,
            "max_constructed_nodes": 16,
            "producer_invocations": 138,
            "retries": 0,
        }
        kernel_indices = [index for index in range(138) if index not in {53, 70}][:46]
        remaining = [
            index
            for index in range(138)
            if index not in {53, 70} and index not in kernel_indices
        ]
        binder_index = remaining.pop(0)
        constant_indices = set(remaining[:40])
        for index, row in enumerate(observation["rows"]):
            artifact = row["artifact_file"]
            if index in {53, 70}:
                outcome = "admissible-proof"
                search = {
                    "producer": MODULE.PRODUCER,
                    "outcome": outcome,
                    "reason": None,
                    "proof_sha256": MODULE.ADMISSIBLE[artifact],
                    "binders": 1,
                    "constructed_nodes": 4,
                    "max_binders": 8,
                    "max_constructed_nodes": 16,
                    "axioms": 0,
                    "theorem_dependencies": 0,
                    "target_dependency": False,
                }
            elif index in kernel_indices:
                outcome = "kernel-rejection:candidate-typecheck-failed"
                search = {
                    "producer": MODULE.PRODUCER,
                    "outcome": "kernel-rejection",
                    "reason": "candidate-typecheck-failed",
                    "detail": "DeclarationValueMismatch { control }",
                    "proof_sha256": digest(20000 + index),
                    "binders": 1,
                    "constructed_nodes": 4,
                    "max_binders": 8,
                    "max_constructed_nodes": 16,
                }
            else:
                if index == binder_index:
                    reason = "binder-budget-exceeded"
                    detail = "binder budget exceeded: maximum 8"
                elif index in constant_indices:
                    reason = "terminal-not-constant-headed-equality"
                    detail = "terminal goal is not constant-headed equality"
                else:
                    reason = "terminal-not-exact-equality"
                    detail = "terminal goal is not an exact Eq application"
                outcome = f"producer-decline:{reason}"
                search = {
                    "producer": MODULE.PRODUCER,
                    "outcome": "producer-decline",
                    "reason": reason,
                    "detail": detail,
                    "max_binders": 8,
                    "max_constructed_nodes": 16,
                }
            row["outcome"] = outcome
            row["proof_search"] = search
        observation["coverage"] = dict(MODULE.EXPECTED_COVERAGE)
        sign_observation(observation)
        manifest["observation_archive"]["observation_sha256"] = observation["observation_sha256"]
        manifest["coverage"] = dict(MODULE.EXPECTED_COVERAGE)
        return manifest, observation, mapping

    def resign(self, values):
        sign_observation(values[1])
        values[0]["observation_archive"]["observation_sha256"] = values[1]["observation_sha256"]

    def validate(self, values):
        MODULE.validate_observation(*values, source_root=None)

    def test_exact_control_is_accepted(self):
        self.validate(self.inputs())

    def test_held_out_mapping_is_rejected(self):
        values = self.inputs()
        values[2]["rows"][0]["partition"] = "held-out"
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "held-out"):
            self.validate(values)

    def test_observation_digest_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["family"] = "mutated"
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "identity"):
            self.validate(values)

    def test_budget_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["budget"]["max_binders"] = 9
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "contract"):
            self.validate(values)

    def test_row_outcome_mutation_is_rejected(self):
        values = self.inputs()
        values[1]["rows"][0]["outcome"] = "admissible-proof"
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "outcome"):
            self.validate(values)

    def test_structured_reason_mutation_is_rejected(self):
        values = self.inputs()
        row = next(row for row in values[1]["rows"] if row["outcome"].startswith("producer-decline"))
        row["proof_search"]["reason"] = "changed"
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "reason"):
            self.validate(values)

    def test_kernel_rejection_detail_mutation_is_rejected(self):
        values = self.inputs()
        row = next(row for row in values[1]["rows"] if row["outcome"].startswith("kernel-rejection"))
        row["proof_search"]["detail"] = "untyped refusal"
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "typed refusal"):
            self.validate(values)

    def test_admissible_proof_identity_mutation_is_rejected(self):
        values = self.inputs()
        row = values[1]["rows"][53]
        row["proof_search"]["proof_sha256"] = digest(99999)
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "assurance"):
            self.validate(values)

    def test_admissible_axiom_mutation_is_rejected(self):
        values = self.inputs()
        row = values[1]["rows"][53]
        row["proof_search"]["axioms"] = 1
        self.resign(values)
        with self.assertRaisesRegex(MODULE.ProducerCensusError, "assurance"):
            self.validate(values)


if __name__ == "__main__":
    unittest.main()
