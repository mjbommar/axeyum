from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "open_lemma_candidate_ranking",
    ROOT / "scripts/gen-autogenesis-open-lemma-candidate-ranking.py",
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OpenLemmaCandidateRankingTests(unittest.TestCase):
    def test_token_normalization_joins_surface_nat_to_kernel_axnat(self) -> None:
        self.assertEqual(MODULE.tokens("n : ℕ; AxNat.choose n n"), {"nat", "choose"})

    def test_surface_operators_supply_semantic_vocabulary(self) -> None:
        self.assertEqual(
            MODULE.tokens("a + n ≡ a [MOD n]"),
            {"add", "mod"},
        )

    def test_held_out_statement_is_never_returned_for_ranking(self) -> None:
        facts = {
            "F:train": {
                "id": "F:train",
                "epistemic_status": "open",
                "formal": {"language": "lean4", "statement": "True"},
            },
            "F:held": {
                "id": "F:held",
                "epistemic_status": "open",
                "formal": {"language": "lean4", "statement": "SECRET"},
            },
        }
        nursery = {
            "entries": [
                {"fact_id": "F:train", "partition": "train"},
                {"fact_id": "F:held", "partition": "held-out"},
            ]
        }
        eligible, excluded = MODULE.eligible_facts(facts, nursery)
        self.assertEqual([row["id"] for row in eligible], ["F:train"])
        self.assertEqual(excluded, ["F:held"])

    def test_ranking_prefers_name_vocabulary_and_is_candidate_only(self) -> None:
        fact = {
            "formal": {"statement": "∀ n : ℕ, n.choose n = 1", "fragment": "Nat"}
        }
        base = {
            "canonical_type": "AxNat",
            "direct_type_dependencies": ["Nat"],
            "direct_theorem_dependents": [],
            "axiom_footprint_size": 0,
            "exact_fact_ids": [],
        }
        rows = MODULE.rank(
            fact,
            [
                {**base, "kernel_declaration_id": "Nat.add_zero"},
                {**base, "kernel_declaration_id": "Nat.choose_self"},
            ],
        )
        self.assertEqual(rows[0]["kernel_declaration_id"], "Nat.choose_self")

    def test_additive_modeq_goal_prefers_additive_modeq_lemma(self) -> None:
        fact = {
            "formal": {
                "statement": "∀ {n a : ℕ}, n + a ≡ a [MOD n]",
                "fragment": "Nat",
            }
        }
        base = {
            "canonical_type": "AxNat",
            "direct_type_dependencies": ["Nat"],
            "direct_theorem_dependents": [],
            "axiom_footprint_size": 0,
            "exact_fact_ids": [],
        }
        rows = MODULE.rank(
            fact,
            [
                {**base, "kernel_declaration_id": "Nat.mod_lt"},
                {**base, "kernel_declaration_id": "Nat.mod_eq_add_left"},
            ],
        )
        self.assertEqual(rows[0]["kernel_declaration_id"], "Nat.mod_eq_add_left")


if __name__ == "__main__":
    unittest.main()
