import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "kernel_semantic_review_queue",
    ROOT / "scripts/gen-autogenesis-kernel-semantic-review-queue.py",
)
assert SPEC and SPEC.loader
QUEUE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(QUEUE)


class KernelSemanticReviewQueueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = QUEUE.build()

    def test_census_accounts_for_every_empty_footprint_theorem(self):
        census = self.data["census"]
        self.assertEqual(
            census["empty_footprint_theorems"],
            census["reviewed_kernel_semantic_anchors"]
            + census["unreviewed_queue_entries"],
        )

    def test_reviewed_anchors_do_not_reappear_as_unreviewed(self):
        queued = {row["kernel_declaration_id"] for row in self.data["unreviewed_entries"]}
        self.assertFalse(
            queued.intersection(self.data["reviewed_kernel_semantic_anchor_ids"])
        )

    def test_order_is_deterministic_graph_observation(self):
        rows = self.data["unreviewed_entries"]
        keys = [
            (
                -row["direct_reverse_theorem_reference_count"],
                -row["direct_theorem_dependency_count"],
                row["kernel_declaration_id"],
            )
            for row in rows
        ]
        self.assertEqual(keys, sorted(keys))
        self.assertTrue(
            all(row["review_status"] == "unreviewed" for row in rows)
        )

    def test_candidate_anchor_does_not_remove_a_theorem_from_review(self):
        overlay = json.loads((ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text())
        link = next(
            link for link in overlay["links"]
            if link["id"] == "L:kernel-decidable-em-formalizes-excluded-middle"
        )
        link["status"] = "candidate"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "overlay.json"
            path.write_text(json.dumps(overlay))
            old = QUEUE.OVERLAY
            try:
                QUEUE.OVERLAY = path
                data = QUEUE.build()
            finally:
                QUEUE.OVERLAY = old
        self.assertEqual(
            data["census"]["reviewed_kernel_semantic_anchors"],
            self.data["census"]["reviewed_kernel_semantic_anchors"] - 1,
        )
        self.assertIn(
            "Decidable.em",
            {row["kernel_declaration_id"] for row in data["unreviewed_entries"]},
        )


if __name__ == "__main__":
    unittest.main()
