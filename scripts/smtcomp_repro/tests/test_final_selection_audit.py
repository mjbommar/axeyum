"""Focused tests for the independent ADR-0356 S4 publication auditor."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from scripts.smtcomp_repro.final_selection_audit import (
    EXPECTED_MUTATIONS,
    FinalSelectionAuditError,
    merge_decision,
    read_selected,
    run_registered_mutations,
    summarize_reasons,
    terminal_reason,
    validate_logic_summary,
    validate_published_decision,
)


ROOT = Path(__file__).resolve().parents[3]
CONTRACT_PATH = ROOT / "docs/plan/smtcomp-official-selection-contract-v1.json"
BENCHMARK_ID = "non-incremental/QF_BV/2025-fixture/case.smt2"


def fixture_rows(*, eligibility_reason: str = "eligible-new") -> tuple[dict[str, object], dict[str, object]]:
    corpus: dict[str, object] = {
        "archive": "QF_BV.tar.zst",
        "asserts": 1,
        "benchmark_id": BENCHMARK_ID,
        "bytes": 12,
        "family": ["2025-fixture"],
        "logic": "QF_BV",
        "name": "case.smt2",
        "sha256": "a" * 64,
        "status": "unknown",
    }
    eligibility: dict[str, object] = {
        "asserts": 1,
        "benchmark_id": BENCHMARK_ID,
        "family": ["2025-fixture"],
        "historical": {"file_coherent": True, "run": False, "trivial": False, "years": []},
        "is_new": True,
        "logic": "QF_BV",
        "logic_competitive": True,
        "name": "case.smt2",
        "reason": eligibility_reason,
        "status": "unknown",
    }
    return eligibility, corpus


class FinalSelectionAuditTests(unittest.TestCase):
    def test_terminal_reason_is_closed_and_rejects_ineligible_selection(self) -> None:
        self.assertEqual(terminal_reason("eligible-new", True), "selected-new")
        self.assertEqual(terminal_reason("eligible-new", False), "excluded-cap-new")
        self.assertEqual(terminal_reason("eligible-old", True), "selected-old")
        self.assertEqual(terminal_reason("eligible-old", False), "excluded-cap-old")
        for reason in (
            "excluded-explicit-removal",
            "excluded-noncompetitive-logic",
            "excluded-trivial",
        ):
            self.assertEqual(terminal_reason(reason, False), reason)
            with self.assertRaises(FinalSelectionAuditError):
                terminal_reason(reason, True)
        with self.assertRaises(FinalSelectionAuditError):
            terminal_reason("unknown", False)

    def test_merge_and_published_validation_bind_every_cross_stage_field(self) -> None:
        eligibility, corpus = fixture_rows()
        decision = merge_decision(eligibility, corpus, True)
        historical = {"benchmark_id": BENCHMARK_ID, "historical": eligibility["historical"]}
        self.assertEqual(
            validate_published_decision(decision, corpus, historical, True),
            "selected-new",
        )

        mutations = []
        wrong_id = copy.deepcopy(corpus)
        wrong_id["benchmark_id"] = "non-incremental/QF_BV/2025-fixture/other.smt2"
        mutations.append((eligibility, wrong_id))
        wrong_archive = copy.deepcopy(corpus)
        wrong_archive["archive"] = "QF_UF.tar.zst"
        mutations.append((eligibility, wrong_archive))
        wrong_hash = copy.deepcopy(corpus)
        wrong_hash["sha256"] = "z" * 64
        mutations.append((eligibility, wrong_hash))
        extra_field = copy.deepcopy(eligibility)
        extra_field["unexpected"] = True
        mutations.append((extra_field, corpus))
        wrong_new = copy.deepcopy(eligibility)
        wrong_new["is_new"] = False
        mutations.append((wrong_new, corpus))
        for mutated_eligibility, mutated_corpus in mutations:
            with self.subTest(index=mutations.index((mutated_eligibility, mutated_corpus))):
                with self.assertRaises(FinalSelectionAuditError):
                    merge_decision(mutated_eligibility, mutated_corpus, True)

        wrong_decision = copy.deepcopy(decision)
        wrong_decision["selected"] = False
        with self.assertRaises(FinalSelectionAuditError):
            validate_published_decision(wrong_decision, corpus, historical, True)
        wrong_history = copy.deepcopy(historical)
        wrong_history["historical"] = {"file_coherent": False}
        with self.assertRaises(FinalSelectionAuditError):
            validate_published_decision(decision, corpus, wrong_history, True)

    def test_logic_summary_accepts_zero_selected_trivial_logic(self) -> None:
        registered = {
            "cap": 0,
            "eligible_new": 0,
            "eligible_old": 0,
            "explicit_removal": 0,
            "logic": "QF_UFFP",
            "metadata": 2,
            "noncompetitive": 0,
            "selected_new_quota": 0,
            "selected_old_quota": 0,
            "trivial": 2,
        }
        observed = {"metadata": 2, "excluded-trivial": 2}
        validate_logic_summary(registered, observed, None)
        wrong = dict(observed)
        wrong["excluded-trivial"] = 1
        with self.assertRaises(FinalSelectionAuditError):
            validate_logic_summary(registered, wrong, None)
        with self.assertRaises(FinalSelectionAuditError):
            validate_logic_summary(registered, observed, {"new": 0, "old": 1, "selected": 1})

    def test_selected_list_requires_canonical_order_and_lf(self) -> None:
        first = "non-incremental/QF_BV/a/a.smt2"
        second = "non-incremental/QF_BV/b/b.smt2"
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "selected.txt"
            path.write_text(f"{first}\n{second}\n", encoding="utf-8")
            self.assertEqual(read_selected(path), [first, second])
            path.write_text(f"{second}\n{first}\n", encoding="utf-8")
            with self.assertRaises(FinalSelectionAuditError):
                read_selected(path)
            path.write_text(first, encoding="utf-8")
            with self.assertRaises(FinalSelectionAuditError):
                read_selected(path)

    def test_registered_s4_mutations_all_execute_and_reject(self) -> None:
        contract = json.loads(CONTRACT_PATH.read_bytes())
        results = run_registered_mutations(contract)
        self.assertEqual(tuple(row["id"] for row in results), EXPECTED_MUTATIONS)
        self.assertTrue(all(row["result"] == "rejected" for row in results))

    def test_terminal_reason_summary_rejects_duplicate_and_unknown_rows(self) -> None:
        rows = [
            {"benchmark_id": BENCHMARK_ID, "reason": "selected-new"},
            {
                "benchmark_id": "non-incremental/QF_BV/2025-fixture/other.smt2",
                "reason": "excluded-cap-new",
            },
        ]
        self.assertEqual(summarize_reasons(rows), {"selected-new": 1, "excluded-cap-new": 1})
        with self.assertRaises(FinalSelectionAuditError):
            summarize_reasons([rows[0], rows[0]])
        unknown = copy.deepcopy(rows)
        unknown[1]["reason"] = "excluded-magic"
        with self.assertRaises(FinalSelectionAuditError):
            summarize_reasons(unknown)


if __name__ == "__main__":
    unittest.main()
