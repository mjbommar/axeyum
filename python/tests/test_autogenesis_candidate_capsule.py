"""Proof-leakage and reproduction controls for native candidate capsules."""

from __future__ import annotations

import unittest

from axeyum import autogenesis_candidate_capsule as CAPSULE


class CandidateCapsuleTests(unittest.TestCase):
    def test_fibonacci_capsule_reproduces_without_target_proof(self):
        names = ["Nat.fib", "Nat.fib_le_succ", "Nat.monotone_of_le_succ"]
        data, receipt = CAPSULE.materialize(
            "Nat.fib_mono",
            "Axeyum.Autogenesis.Statement.Native.fibMono",
            names,
        )
        self.assertNotIn(b'"Nat.fib_mono"', data)
        self.assertEqual(receipt["axiom_footprint"], [])
        self.assertEqual(
            receipt["theorem_dependencies"],
            ["Nat.fib_le_succ", "Nat.monotone_of_le_succ"],
        )

    def test_candidates_must_be_explicit_sorted_and_unique(self):
        with self.assertRaisesRegex(ValueError, "sorted unique"):
            CAPSULE.materialize(
                "Nat.fib_mono",
                "Axeyum.Autogenesis.Statement.Native.fibMono",
                ["Nat.fib_le_succ", "Nat.fib"],
            )


if __name__ == "__main__":
    unittest.main()
