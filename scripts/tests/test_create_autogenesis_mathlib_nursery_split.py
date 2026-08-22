from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "create-autogenesis-mathlib-nursery-split.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_mathlib_nursery_split", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MathlibNurserySplitTests(unittest.TestCase):
    def setUp(self) -> None:
        self.catalog = MODULE.load(MODULE.CATALOG)
        self.policy = MODULE.load(MODULE.POLICY)

    def test_repository_split_is_exact_and_balanced(self) -> None:
        nursery = MODULE.build(self.catalog, self.policy)
        counts: dict[str, int] = {}
        for row in nursery["entries"][2:]:
            counts[row["partition"]] = counts.get(row["partition"], 0) + 1
        self.assertEqual(counts, {"development": 79, "held-out": 57, "train": 78})
        self.assertEqual(nursery["state"], "frozen-evaluation")

    def test_mutations_are_bound_to_their_source_group_and_partition(self) -> None:
        nursery = MODULE.build(self.catalog, self.policy)
        by_id = {row["fact_id"]: row for row in nursery["entries"]}
        mutations = [row for row in nursery["entries"] if row["mutation_of"] is not None]
        self.assertEqual(len(mutations), 12)
        for mutation in mutations:
            source = by_id[mutation["mutation_of"]]
            self.assertEqual(mutation["partition"], source["partition"])
            self.assertEqual(mutation["family"], source["family"])
            self.assertEqual(mutation["source_group"], source["source_group"])

    def test_missing_family_policy_fails_closed(self) -> None:
        policy = copy.deepcopy(self.policy)
        del policy["family_partitions"]["natural-primes"]
        with self.assertRaisesRegex(MODULE.SplitError, "cover the catalog families exactly"):
            MODULE.build(self.catalog, policy)

    def test_partition_drift_fails_closed(self) -> None:
        policy = copy.deepcopy(self.policy)
        policy["family_partitions"]["natural-primes"] = "train"
        with self.assertRaisesRegex(MODULE.SplitError, "partition counts changed"):
            MODULE.build(self.catalog, policy)


if __name__ == "__main__":
    unittest.main()
