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
        """The emitted counts, re-derived from the CATALOG and the POLICY.

        This asserted the literal `{"development": 99, "held-out": 37,
        "train": 78}` and had been red since the first held-out family
        amendment moved rows out of held-out (live: 120 / 16 / 78). A literal
        here measures the maintainer's memory, and asserting `PARTITION_COUNTS`
        instead would be vacuous -- that constant is what `build` already
        checks against, so the test would pass by construction.

        So the expectation is computed the third way: count the catalog's 214
        rows by the partition its family is assigned in the split policy. That
        agrees with `build` only if the family mapping, the catalog and the
        emitted entries all say the same thing, and it goes stale for nobody.
        """
        expected: dict[str, int] = {}
        for row in self.catalog["facts"]:
            partition = self.policy["family_partitions"][row["family"]]
            expected[partition] = expected.get(partition, 0) + 1

        nursery = MODULE.build(self.catalog, self.policy)
        counts: dict[str, int] = {}
        for row in nursery["entries"][2:]:
            counts[row["partition"]] = counts.get(row["partition"], 0) + 1
        self.assertEqual(counts, expected)
        self.assertEqual(sum(counts.values()), 214)
        self.assertEqual(nursery["state"], "frozen-evaluation")

    def test_the_partition_roles_reach_the_emitted_policy(self) -> None:
        """ADR-1564. The manifest's `policy` block is what every gate derives
        its evaluated set from, and it is now CARRIED from the split policy
        rather than spelled in `build`."""
        nursery = MODULE.build(self.catalog, self.policy)
        for key in ("required_evaluation_partitions", "training_partitions",
                    "blind_partitions"):
            self.assertEqual(nursery["policy"][key],
                             self.policy["partition_roles"][key], key)

    def test_changed_roles_without_an_amendment_are_refused(self) -> None:
        """The freeze. `required_evaluation_partitions` is part of what was
        frozen `before-target-outcomes`, so a departure from the preregistered
        roles needs a dated `policy_amendments` entry -- otherwise editing the
        list in place is indistinguishable from having always meant it, which
        is ADR-1546's re-scoped exemption at a coarser unit."""
        policy = copy.deepcopy(self.policy)
        policy["policy_amendments"] = []
        with self.assertRaisesRegex(MODULE.SplitError,
                                    "no policy_amendments entry"):
            MODULE.build(self.catalog, policy)

    def test_an_amendment_recorded_against_the_preregistered_roles_is_refused(
        self,
    ) -> None:
        """The other direction, and the one that is easy to leave out: a dated
        amendment beside roles that never changed is a claim about a change
        nobody can check."""
        policy = copy.deepcopy(self.policy)
        policy["partition_roles"].update(MODULE.PREREGISTERED_PARTITION_ROLES)
        with self.assertRaisesRegex(MODULE.SplitError,
                                    "amendment that changes nothing"):
            MODULE.build(self.catalog, policy)

    def test_a_policy_sealing_no_blind_partition_is_refused(self) -> None:
        """Unsealing the blind population must not be reachable by editing a
        data file, so it is refused in the generator too rather than only in
        the gates that read what it emits."""
        policy = copy.deepcopy(self.policy)
        policy["partition_roles"]["blind_partitions"] = []
        with self.assertRaisesRegex(MODULE.SplitError,
                                    "blind_partitions is empty"):
            MODULE.build(self.catalog, policy)

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
