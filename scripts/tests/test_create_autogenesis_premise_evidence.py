from __future__ import annotations

import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-premise-evidence.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_premise_evidence", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PremiseEvidenceTests(unittest.TestCase):
    def inputs(self):
        plan = {
            "rank": 2,
            "operation": "induct-nat",
            "target_binder": 0,
            "base": "definitional-reflexivity",
            "step": "successor-congruence-induction-hypothesis",
        }
        snapshot = {
            "episode_id": "episode",
            "snapshot_sha256": "snapshot",
            "chain": {"premise": {"fact_id": "F:nat-zero-add"}},
        }
        catalog = {
            "episode_id": "episode",
            "phase": "pre_b",
            "catalog_sha256": "catalog",
            "target": {"name": "E.B", "canonical_type": "B"},
        }
        bundle = {
            "phase": "pre_b",
            "bundle_sha256": "bundle",
            "plans": [{"rank": 1}, plan],
        }
        kernel = {
            "candidate": "E.B",
            "canonical_type": "B",
            "catalog_sha256": "catalog",
            "bundle_sha256": "bundle",
            "attempted": "2",
            "budget": "2",
            "accepted_plan_rank": "2",
            "axiom_footprint": "",
            "retained_answer_dependencies": "",
        }
        return snapshot, catalog, bundle, kernel

    def build(self):
        snapshot, catalog, bundle, kernel = self.inputs()
        return MODULE.build_evidence(
            snapshot=snapshot,
            catalog=catalog,
            bundle=bundle,
            plans_bytes=b"plans\n",
            kernel_fields=kernel,
        )

    def test_exact_handoff_is_content_addressed(self):
        evidence = self.build()
        unsigned = dict(evidence)
        unsigned.pop("evidence_sha256")
        self.assertEqual(evidence["evidence_sha256"], MODULE.digest(unsigned))
        self.assertEqual(evidence["acceptance"]["axiom_footprint"], [])

    def test_footprint_and_retained_answer_mutations_reject(self):
        for key, value in (
            ("axiom_footprint", "Classical.choice"),
            ("retained_answer_dependencies", "Nat.zero_add"),
        ):
            with self.subTest(key=key):
                snapshot, catalog, bundle, kernel = self.inputs()
                kernel[key] = value
                with self.assertRaisesRegex(MODULE.EvidenceError, "not axiom-free"):
                    MODULE.build_evidence(
                        snapshot=snapshot,
                        catalog=catalog,
                        bundle=bundle,
                        plans_bytes=b"plans\n",
                        kernel_fields=kernel,
                    )

    def test_identity_and_plan_mutations_reject(self):
        mutations = (
            ("candidate", "wrong", "candidate"),
            ("canonical_type", "wrong", "type"),
            ("catalog_sha256", "wrong", "catalog"),
            ("bundle_sha256", "wrong", "bundle"),
            ("accepted_plan_rank", "3", "rank"),
        )
        for key, value, message in mutations:
            with self.subTest(key=key):
                snapshot, catalog, bundle, kernel = self.inputs()
                kernel[key] = value
                with self.assertRaisesRegex(MODULE.EvidenceError, message):
                    MODULE.build_evidence(
                        snapshot=snapshot,
                        catalog=catalog,
                        bundle=bundle,
                        plans_bytes=b"plans\n",
                        kernel_fields=kernel,
                    )

    def test_kernel_wire_rejects_duplicates_and_unknown_fields(self):
        body = "\n".join(
            ["AXEYUM_AUTOGENESIS_KERNEL_EVIDENCE_V1"]
            + [f"{key}\tvalue" for key in sorted(MODULE.KERNEL_FIELDS)]
        )
        with self.assertRaisesRegex(MODULE.EvidenceError, "repeats"):
            MODULE.parse_kernel_evidence(body + "\ncandidate\tagain\n")
        with self.assertRaisesRegex(MODULE.EvidenceError, "field mismatch"):
            MODULE.parse_kernel_evidence(body + "\nunknown\tvalue\n")


if __name__ == "__main__":
    unittest.main()
