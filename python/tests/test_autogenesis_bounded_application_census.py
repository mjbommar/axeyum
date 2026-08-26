"""Controls for the proof-isolated bounded-application census."""

from __future__ import annotations

import unittest

from axeyum import autogenesis_bounded_application_census as CENSUS


class BoundedApplicationCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = CENSUS.build()

    def test_population_and_conversion_are_pinned(self):
        self.assertEqual(
            self.data["census"],
            {
                "population": 111,
                "accepted": 6,
                "declined": 105,
                "conversion_percent": 5.4,
                "decline_reasons": {"NoTypedApplication": 105},
            },
        )

    def test_every_accept_is_kernel_admitted_and_axiom_free(self):
        accepted = self.data["accepted"]
        self.assertTrue(accepted)
        self.assertTrue(all(row["axiom_footprint"] == [] for row in accepted))
        self.assertTrue(all(len(row["proof_sha256"]) == 64 for row in accepted))

    def test_fibonacci_uses_retrieval_without_proof_leakage(self):
        row = next(row for row in self.data["accepted"] if row["theorem"] == "Nat.fib_mono")
        self.assertEqual(row["premise_declarations"], ["Nat.fib_le_succ"])
        self.assertIn("Nat.fib", row["candidate_declarations"])
        self.assertIn("Nat.monotone_of_le_succ", row["candidate_declarations"])
        self.assertEqual(
            row["theorem_dependencies"],
            ["Nat.fib_le_succ", "Nat.monotone_of_le_succ"],
        )

    def test_forbidden_proof_evidence_is_named(self):
        forbidden = self.data["strategy"]["forbidden_inputs"]
        self.assertIn("direct_declaration_dependencies", forbidden)
        self.assertIn("direct_theorem_dependencies", forbidden)


if __name__ == "__main__":
    unittest.main()
