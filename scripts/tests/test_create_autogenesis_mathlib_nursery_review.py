from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-mathlib-nursery-review.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_mathlib_nursery_review", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NurseryReviewTests(unittest.TestCase):
    def inputs(self):
        candidates = {
            "schema_version": 1,
            "candidates": [
                {
                    "candidate_id": "a-id",
                    "domain": "Nat",
                    "module": "Mathlib.A",
                    "name": "Nat.a",
                    "theme": "a",
                    "type": "∀ n : ℕ, n = n",
                },
                {
                    "candidate_id": "b-id",
                    "domain": "Nat",
                    "module": "Mathlib.A",
                    "name": "Nat.b",
                    "theme": "a",
                    "type": "∀ n : ℕ, n ≤ n",
                },
                {
                    "candidate_id": "c-id",
                    "domain": "Int",
                    "module": "Mathlib.C",
                    "name": "Int.c",
                    "theme": "c",
                    "type": "∀ n : ℤ, n = n",
                },
            ],
        }
        candidates["candidates_sha256"] = MODULE.digest(candidates)
        components = {
            "schema_version": 1,
            "components": [
                {
                    "component_id": "component-ab",
                    "members": [{"name": "Nat.a"}, {"name": "Nat.b"}],
                },
                {"component_id": "component-c", "members": [{"name": "Int.c"}]},
            ],
        }
        components["components_sha256"] = MODULE.digest(components)
        policy = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-mathlib-nursery-review-policy",
            "candidate_set_sha256": candidates["candidates_sha256"],
            "dependency_components_sha256": components["components_sha256"],
            "authority": {"forbidden": ["Axeyum outcomes and proofs"]},
            "dispositions": {
                "calibration-only": {"reason": "base", "names": ["Nat.b"]},
            },
            "mutations": [
                {"source": "Nat.a", "class": "boundary", "statement": "∀ n : ℕ, n = 0"},
                {"source": "Int.c", "class": "boundary", "statement": "∀ n : ℤ, n = 0"},
            ],
            "default_disposition": "evaluation-eligible",
            "state": "review-authority-no-splits-no-outcomes",
        }
        policy["policy_sha256"] = MODULE.digest(policy)
        return candidates, components, policy

    def resign(self, policy):
        policy["policy_sha256"] = MODULE.digest(
            {key: value for key, value in policy.items() if key != "policy_sha256"}
        )

    def test_review_is_deterministic_and_mutations_stay_with_source(self) -> None:
        candidates, components, policy = self.inputs()
        first = MODULE.build(candidates, components, policy)
        second = MODULE.build(copy.deepcopy(candidates), copy.deepcopy(components), copy.deepcopy(policy))
        self.assertEqual(first, second)
        self.assertEqual(first["coverage"]["evaluation_eligible_candidates"], 2)
        self.assertEqual(first["coverage"]["future_evaluation_statements"], 4)
        group = next(row for row in first["review_groups"] if row["dependency_component_id"] == "component-ab")
        self.assertEqual(group["candidate_names"], ["Nat.a"])
        self.assertEqual(len(group["mutation_ids"]), 1)
        MODULE.verify(first, second)

    def test_disposition_lists_cannot_overlap(self) -> None:
        candidates, components, policy = self.inputs()
        policy["dispositions"]["excluded-alias"] = {"reason": "alias", "names": ["Nat.b"]}
        self.resign(policy)
        with self.assertRaisesRegex(MODULE.ReviewError, "multiple review dispositions"):
            MODULE.build(candidates, components, policy)

    def test_unknown_review_name_is_rejected(self) -> None:
        candidates, components, policy = self.inputs()
        policy["dispositions"]["calibration-only"]["names"] = ["Nat.unknown"]
        self.resign(policy)
        with self.assertRaisesRegex(MODULE.ReviewError, "unknown candidate"):
            MODULE.build(candidates, components, policy)

    def test_mutation_source_must_be_evaluation_eligible(self) -> None:
        candidates, components, policy = self.inputs()
        policy["mutations"][0]["source"] = "Nat.b"
        self.resign(policy)
        with self.assertRaisesRegex(MODULE.ReviewError, "not evaluation-eligible"):
            MODULE.build(candidates, components, policy)

    def test_every_family_requires_exactly_one_mutation(self) -> None:
        candidates, components, policy = self.inputs()
        policy["mutations"] = policy["mutations"][:1]
        self.resign(policy)
        with self.assertRaisesRegex(MODULE.ReviewError, "every candidate family exactly once"):
            MODULE.build(candidates, components, policy)

    def test_axeyum_outcome_authority_cannot_be_added_silently(self) -> None:
        candidates, components, policy = self.inputs()
        policy["authority"]["forbidden"] = ["proof values"]
        self.resign(policy)
        with self.assertRaisesRegex(MODULE.ReviewError, "outcome-blind"):
            MODULE.build(candidates, components, policy)

    def test_rehashed_statement_mutation_still_fails_exact_verification(self) -> None:
        candidates, components, policy = self.inputs()
        expected = MODULE.build(candidates, components, policy)
        actual = copy.deepcopy(expected)
        actual["mutations"][0]["statement"] = "∀ n : ℤ, n = 1"
        actual["review_sha256"] = MODULE.digest(
            {key: value for key, value in actual.items() if key != "review_sha256"}
        )
        with self.assertRaisesRegex(MODULE.ReviewError, "stale or mutated"):
            MODULE.verify(actual, expected)


if __name__ == "__main__":
    unittest.main()
