from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "capability_gap", ROOT / "scripts/validate-autogenesis-capability-gap-projection.py"
)
assert SPEC and SPEC.loader
CG = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CG)


class CapabilityGapProjectionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(
            (ROOT / "artifacts/autogenesis/capability-gap-projection-v1.json").read_text()
        )

    def test_current_projection_is_valid(self):
        self.assertEqual(CG.validate(self.data), [])

    def test_invented_ready_count_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["groups"][0]["ready_fact_count"] += 1
        self.assertTrue(any("count disagrees" in error for error in CG.validate(data)))

    def test_duplicate_ready_fact_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["groups"][0]["ready_fact_ids"].append(data["groups"][0]["ready_fact_ids"][0])
        self.assertTrue(any("sorted and unique" in error for error in CG.validate(data)))

    def test_catalog_coverage_must_partition_ready_facts(self):
        data = copy.deepcopy(self.data)
        data["uncataloged_ready_fact_ids"].append(data["catalog_clusters"][0]["ready_fact_ids"][0])
        data["uncataloged_ready_fact_ids"].sort()
        self.assertTrue(any("partition" in error for error in CG.validate(data)))

    def test_invented_unlock_count_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["catalog_clusters"][0]["direct_unlock_fact_count"] += 1
        self.assertTrue(any("direct unlock count" in error for error in CG.validate(data)))

    def test_projection_never_names_held_out_fact(self):
        nursery = json.loads((ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
        held_out = {row["fact_id"] for row in nursery["entries"] if row["partition"] == "held-out"}
        def strings(value):
            if isinstance(value, dict):
                return [item for child in value.values() for item in strings(child)]
            if isinstance(value, list):
                return [item for child in value for item in strings(child)]
            return [value] if isinstance(value, str) else []
        self.assertFalse(held_out.intersection(strings(self.data)))


if __name__ == "__main__":
    unittest.main()
