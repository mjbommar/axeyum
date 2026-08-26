from __future__ import annotations

import importlib.util
import pathlib
import unittest
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-next-reusable-family-queue.py"
SPEC = importlib.util.spec_from_file_location("next_reusable_family_queue", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
queue = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(queue)


class NextReusableFamilyQueueTests(unittest.TestCase):
    def test_priority_classes_are_fail_closed_and_reusability_aware(self) -> None:
        self.assertEqual(queue.classify(Counter(), 3, 3)[1], "operation-integration-ready")
        self.assertEqual(queue.classify(Counter(), 1, 1)[1], "expand-unchanged-producer")
        self.assertEqual(
            queue.classify(Counter({"missing-rewrite-or-induction-plan": 3}), 0, 3)[1],
            "shared-proof-composition",
        )
        self.assertEqual(queue.classify(Counter(), 0, 0)[1], "measurement-missing")

    def test_live_queue_excludes_controls_and_registered_facts(self) -> None:
        document = queue.build()
        controls = set(queue.load(queue.FRONTIER)["must_decline_control_fact_ids"])
        all_ready = {fact for row in document["rows"] for fact in row["ready_fact_ids"]}
        self.assertFalse(all_ready.intersection(controls))
        self.assertTrue(document["rows"])
        self.assertEqual(document["rows"][0]["family"], "natural-binomial")
        self.assertEqual(document["rows"][0]["state"], "expand-unchanged-producer")
        self.assertEqual(
            document["rows"][0]["accepted_fact_ids"], ["F:ml430-nat-choose-one-right-7eda8e39"]
        )
        self.assertEqual(document["rows"][0]["measured_fact_count"], 8)
        self.assertEqual(document["rows"][0]["unmeasured_fact_count"], 0)
        self.assertEqual(document["rows"][0]["capability_demands"]["binder-or-generalization"], 2)
        self.assertEqual(
            document["rows"][0]["capability_demands"]["non-equality-terminal-family"], 3
        )
        self.assertTrue(all(not row["already_registered_fact_ids"] for row in document["rows"]))


if __name__ == "__main__":
    unittest.main()
