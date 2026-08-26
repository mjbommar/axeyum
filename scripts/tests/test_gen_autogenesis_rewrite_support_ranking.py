from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "rewrite_support_ranking",
    ROOT / "scripts" / "gen-autogenesis-rewrite-support-ranking.py",
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RewriteSupportRankingTests(unittest.TestCase):
    def test_second_hop_prefers_simple_axiom_free_connector(self) -> None:
        goal = {
            "fact_id": "F:test",
            "statement_tokens": ["choose", "nat"],
            "candidates": [
                {
                    "kernel_declaration_id": "Nat.choose_step",
                    "score": 10,
                }
            ],
        }
        lemmas = {
            "Nat.choose_step": {
                "kernel_declaration_id": "Nat.choose_step",
                "canonical_type": "Eq.{1} Nat (choose (succ n) k) (add (choose n k) 0)",
                "direct_type_dependencies": ["Eq", "Nat", "Nat.add", "Nat.choose", "Nat.succ"],
                "direct_theorem_dependents": [],
                "axiom_footprint_size": 0,
                "exact_fact_ids": [],
            },
            "Nat.zero_add": {
                "kernel_declaration_id": "Nat.zero_add",
                "canonical_type": "Eq.{1} Nat (add zero n) n",
                "direct_type_dependencies": ["Eq", "Nat", "Nat.add", "Nat.zero"],
                "direct_theorem_dependents": ["Nat.some_user"],
                "axiom_footprint_size": 0,
                "exact_fact_ids": ["F:nat-zero-add"],
            },
            "Nat.unsafe_add": {
                "kernel_declaration_id": "Nat.unsafe_add",
                "canonical_type": "Eq.{1} Nat (add n n) n",
                "direct_type_dependencies": ["Eq", "Nat", "Nat.add"],
                "direct_theorem_dependents": [],
                "axiom_footprint_size": 1,
                "exact_fact_ids": [],
            },
            "Int.zero_add": {
                "kernel_declaration_id": "Int.zero_add",
                "canonical_type": "Eq.{1} Int (add zero n) n",
                "direct_type_dependencies": ["Eq", "Int", "Int.add", "Int.zero"],
                "direct_theorem_dependents": [],
                "axiom_footprint_size": 0,
                "exact_fact_ids": [],
            },
        }

        rows = MODULE.support_rows(goal, lemmas)

        self.assertEqual([row["kernel_declaration_id"] for row in rows], ["Nat.zero_add"])
        self.assertEqual(rows[0]["retrieval_role"], "rewrite-support")

    def test_build_preserves_held_out_exclusion_and_interleaves_support(self) -> None:
        primary = {
            "state": "candidate-only-train-development-held-out-unread",
            "held_out_exclusion": {
                "count": 1,
                "nursery_sha256": "a" * 64,
                "identities_redacted": True,
            },
            "goals": [
                {
                    "fact_id": "F:test",
                    "statement_tokens": ["choose"],
                    "candidate_count": 1,
                    "candidates": [
                        {"kernel_declaration_id": "Nat.choose_step", "score": 10}
                    ],
                }
            ],
        }
        index = {
            "lemmas": [
                {
                    "kernel_declaration_id": "Nat.choose_step",
                    "canonical_type": "Eq.{1} Nat (choose n) (add n zero)",
                    "direct_type_dependencies": ["Eq", "Nat", "Nat.add", "Nat.choose"],
                    "direct_theorem_dependents": [],
                    "axiom_footprint_size": 0,
                    "exact_fact_ids": [],
                },
                {
                    "kernel_declaration_id": "Nat.zero_add",
                    "canonical_type": "Eq.{1} Nat (add zero n) n",
                    "direct_type_dependencies": ["Eq", "Nat", "Nat.add", "Nat.zero"],
                    "direct_theorem_dependents": [],
                    "axiom_footprint_size": 0,
                    "exact_fact_ids": [],
                },
            ]
        }

        result = MODULE.build(primary, index)

        self.assertEqual(result["held_out_exclusion"], primary["held_out_exclusion"])
        self.assertNotIn("F:held-out", str(result))
        self.assertEqual(result["census"]["rewrite_support_candidate_rows"], 1)
        self.assertEqual(
            [row["retrieval_role"] for row in result["goals"][0]["candidates"]],
            ["goal-primary", "rewrite-support"],
        )


if __name__ == "__main__":
    unittest.main()
