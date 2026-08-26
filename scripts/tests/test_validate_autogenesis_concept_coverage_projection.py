"""Mutation controls for local, held-out-safe concept coverage."""

from __future__ import annotations

import copy
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "concept_coverage",
    ROOT / "scripts/validate-autogenesis-concept-coverage-projection.py",
)
assert SPEC and SPEC.loader
CC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CC)


class Controls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.data = json.loads(
            (ROOT / "artifacts/autogenesis/concept-coverage-projection-v1.json").read_text()
        )

    def test_current_valid(self) -> None:
        self.assertEqual(CC.validate(self.data), [])

    def test_invented_topic_count_rejected(self) -> None:
        document = copy.deepcopy(self.data)
        row = next(row for row in document["concepts"] if row["family_topic_fact_ids"])
        row["family_topic_fact_count"] += 1
        self.assertTrue(any("family_topic_fact_count" in error for error in CC.validate(document)))

    def test_dropped_formalized_fact_rejected(self) -> None:
        document = copy.deepcopy(self.data)
        row = next(row for row in document["concepts"] if row["qualified_formalization_fact_ids"])
        row["qualified_formalization_fact_ids"].pop()
        row["qualified_formalization_fact_count"] -= 1
        self.assertTrue(any("formalizations disagree" in error for error in CC.validate(document)))

    def test_invented_kernel_anchor_rejected(self) -> None:
        document = copy.deepcopy(self.data)
        row = next(row for row in document["concepts"] if row["kernel_semantic_anchor_ids"])
        row["kernel_semantic_anchor_ids"].append("Kernel.invented")
        row["kernel_semantic_anchor_count"] += 1
        self.assertTrue(any("kernel anchors disagree" in error for error in CC.validate(document)))

    def test_stale_overlay_receipt_rejected(self) -> None:
        document = copy.deepcopy(self.data)
        document["derivation"]["knowledge_overlay_sha256"] = "0" * 64
        self.assertTrue(
            any("stale knowledge_overlay_sha256" in error for error in CC.validate(document))
        )

    def test_projection_never_names_held_out_fact(self) -> None:
        nursery = json.loads((ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
        held = {row["fact_id"] for row in nursery["entries"] if row["partition"] == "held-out"}
        ids = {
            fact_id
            for row in self.data["concepts"]
            for field in ("family_topic_fact_ids", "qualified_formalization_fact_ids")
            for fact_id in row[field]
        }
        self.assertTrue(ids, "vacuity guard: the projection names no facts")
        self.assertFalse(held.intersection(ids))


if __name__ == "__main__":
    unittest.main()
