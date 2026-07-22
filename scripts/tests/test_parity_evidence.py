from __future__ import annotations

import unittest

from scripts.parity_evidence import (
    ParityEvidenceError,
    audit_inventory_raw,
    paired_decision_overlap,
)


def raw_result(reported, expected):
    return {"axeyum": {"reported_status": reported, "expected_status": expected}}


def paired_artifact(rows):
    return {"instances": [{"file": file, "outcome": outcome} for file, outcome in rows]}


class InventoryAuditTests(unittest.TestCase):
    def test_separates_adjudicated_and_unadjudicated_decisions(self) -> None:
        raw = {
            "agree-sat": raw_result("sat", "sat"),
            "agree-unsat": raw_result("unsat", "unsat"),
            "wrong": raw_result("sat", "unsat"),
            "unadjudicated-none": raw_result("sat", None),
            "unadjudicated-unknown": raw_result("unsat", "unknown"),
            "decline": raw_result("unknown", "sat"),
            "no-answer": raw_result(None, None),
        }
        self.assertEqual(
            audit_inventory_raw(raw, solver="axeyum"),
            {
                "total": 7,
                "known_status_benchmarks": 4,
                "unknown_status_benchmarks": 3,
                "known_status_agreements": 2,
                "known_status_disagreements": 1,
                "unadjudicated_decisions": 2,
                "declines": 1,
                "no_answers": 1,
                "legacy_decided_correct": 4,
            },
        )

    def test_missing_solver_and_invalid_status_fail_closed(self) -> None:
        with self.assertRaisesRegex(ParityEvidenceError, "missing requested solver"):
            audit_inventory_raw({"x": {}}, solver="axeyum")
        with self.assertRaisesRegex(ParityEvidenceError, "invalid reported status"):
            audit_inventory_raw({"x": raw_result("maybe", "sat")}, solver="axeyum")


class PairedDecisionTests(unittest.TestCase):
    def test_equal_counts_do_not_hide_different_decided_sets(self) -> None:
        left = paired_artifact([("a", "sat"), ("b", "unsat"), ("c", "unknown")])
        right = paired_artifact([("a", "sat"), ("b", "unknown"), ("c", "unsat")])
        self.assertEqual(
            paired_decision_overlap(left, right),
            {
                "total": 3,
                "left_decided": 2,
                "right_decided": 2,
                "both_decided": 1,
                "left_only_decided": 1,
                "right_only_decided": 1,
                "neither_decided": 0,
                "both_decided_disagreements": 0,
            },
        )

    def test_disagreement_and_population_drift_are_visible(self) -> None:
        left = paired_artifact([("a", "sat")])
        right = paired_artifact([("a", "unsat")])
        self.assertEqual(
            paired_decision_overlap(left, right)["both_decided_disagreements"], 1
        )
        with self.assertRaisesRegex(ParityEvidenceError, "paired populations differ"):
            paired_decision_overlap(left, paired_artifact([("b", "sat")]))

    def test_duplicate_identity_fails_closed(self) -> None:
        duplicate = paired_artifact([("a", "sat"), ("a", "unknown")])
        with self.assertRaisesRegex(ParityEvidenceError, "duplicate file"):
            paired_decision_overlap(duplicate, duplicate)


if __name__ == "__main__":
    unittest.main()
