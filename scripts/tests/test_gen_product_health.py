from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-product-health.py"
SPEC = importlib.util.spec_from_file_location("gen_product_health", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ProductHealthTests(unittest.TestCase):
    def test_live_snapshot_has_an_honest_runtime_boundary(self) -> None:
        document = MODULE.build()
        self.assertIn(
            document["runtime_gate_status"]["state"],
            {"not-recorded", "passed-ancestor", "failed-ancestor"},
        )
        self.assertGreater(document["fact_ledger"]["facts"], 0)
        self.assertGreater(sum(document["fact_ledger"]["proof_route_counts"].values()), 0)
        self.assertGreater(document["semantic_coverage"]["qualified_formalization_facts"], 0)
        self.assertGreater(document["semantic_coverage"]["kernel_semantic_anchors"], 0)
        self.assertGreater(
            document["autonomous_production"]["production_episodes"]["production_episodes"],
            0,
        )

    def test_live_snapshot_reaches_all_named_authorities_in_both_gates(self) -> None:
        document = MODULE.build()
        self.assertTrue(all(row["both"] for row in document["gate_reachability"].values()))

    def test_markdown_does_not_turn_static_wiring_into_green_execution(self) -> None:
        markdown = MODULE.render(MODULE.build())
        self.assertIn("Runtime gate receipt", markdown)
        self.assertIn("not transitive evidence", markdown)
        self.assertIn("Reviewed semantic coverage", markdown)
        self.assertNotIn("all gates pass", markdown.lower())


if __name__ == "__main__":
    unittest.main()
