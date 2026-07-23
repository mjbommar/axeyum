"""Fail-closed gates for the repaired-P0 combined comparison."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

from p0_compare import (  # noqa: E402
    CELL_ORDER,
    build_comparison,
    comparison_json_bytes,
    render_markdown,
    sha256_bytes,
    validate_comparison,
)
from resume_contract import ContractError, digest  # noqa: E402


LOGIC_COUNTS = {
    "axeyum": {"QF_ABVFP": 1, "QF_AUFLIA": 1, "QF_BVFP": 1, "QF_FP": 1},
    "cvc5": {"QF_ABVFP": 1, "QF_AUFLIA": 1, "QF_BVFP": 1, "QF_FP": 1},
    "bitwuzla": {"QF_ABVFP": 1, "QF_BVFP": 1, "QF_FP": 1},
}


def row(
    solver_id: str,
    logic: str,
    suffix: str,
    expected_status: str | None,
    reported_status: str | None,
    termination_class: str = "completed",
) -> dict:
    return {
        "solver_id": solver_id,
        "benchmark_id": f"{logic}/fixture/{suffix}.smt2",
        "benchmark_sha256": suffix * 64,
        "expected_status": expected_status,
        "reported_status": reported_status,
        "termination_class": termination_class,
    }


def fixture() -> dict[str, list[dict]]:
    statuses = {
        "axeyum": {
            "a": ("unsat", "completed"),
            "b": ("unknown", "completed"),
            "c": (None, "wall-timeout"),
            "d": ("unknown", "completed"),
        },
        "cvc5": {
            "a": ("unsat", "completed"),
            "b": ("sat", "completed"),
            "c": ("sat", "completed"),
            "d": (None, "nonzero-exit"),
        },
        "bitwuzla": {
            "a": ("unsat", "completed"),
            "c": ("sat", "completed"),
            "d": ("sat", "completed"),
        },
    }
    definitions = {
        "a": ("QF_ABVFP", "unsat"),
        "b": ("QF_AUFLIA", "sat"),
        "c": ("QF_BVFP", "sat"),
        "d": ("QF_FP", None),
    }
    result = {}
    for solver_id in CELL_ORDER:
        result[solver_id] = [
            row(
                solver_id,
                definitions[suffix][0],
                suffix,
                definitions[suffix][1],
                reported,
                termination,
            )
            for suffix, (reported, termination) in statuses[solver_id].items()
        ]
    return result


def build(records: dict[str, list[dict]] | None = None) -> dict:
    return build_comparison(
        fixture() if records is None else records,
        authority={"fixture": True, "preparation": {"file_sha256": "f" * 64}},
        expected_logic_counts=LOGIC_COUNTS,
    )


class P0ComparisonTests(unittest.TestCase):
    def test_derives_exact_scopes_and_decision_projections(self) -> None:
        result = build()
        self.assertEqual(result["population_contract"]["all_population"], 4)
        self.assertEqual(result["population_contract"]["fp_population"], 3)
        self.assertEqual(result["population_contract"]["qf_auflia_population"], 1)
        self.assertEqual(result["native_cells"]["axeyum"]["decision_count"], 1)
        self.assertEqual(result["native_cells"]["cvc5"]["decision_count"], 3)
        self.assertEqual(result["native_cells"]["bitwuzla"]["decision_count"], 3)
        pair = result["pairwise"]["axeyum_cvc5_all"]["intersection"]
        self.assertEqual(
            pair["decision_projection"],
            {
                "both-decide-agree": 1,
                "disagreement": 0,
                "left-only-decides": 0,
                "neither-decides": 1,
                "right-only-decides": 2,
            },
        )
        three = result["three_solver_fp"]
        self.assertEqual(
            three["decision_projection"],
            {
                "disagreement": 0,
                "none-decide": 0,
                "one-decides": 1,
                "three-decide-agree": 1,
                "two-decide-agree": 1,
            },
        )
        self.assertEqual(three["sole_decider_counts"]["bitwuzla"], 1)
        self.assertEqual(three["sole_non_decider_counts"]["axeyum"], 1)

    def test_unknown_and_no_verdict_are_distinct_non_decisions(self) -> None:
        result = build()
        axeyum = result["native_cells"]["axeyum"]
        self.assertEqual(axeyum["reported_status_counts"]["unknown"], 2)
        self.assertEqual(axeyum["reported_status_counts"]["no-verdict"], 1)
        self.assertEqual(axeyum["decision_expected_status_counts"]["no-decision"], 3)
        bitwuzla = result["native_cells"]["bitwuzla"]
        self.assertEqual(
            bitwuzla["decision_expected_status_counts"]["unadjudicated-decision"],
            1,
        )

    def test_rejects_duplicate_identity(self) -> None:
        records = fixture()
        records["axeyum"].append(copy.deepcopy(records["axeyum"][0]))
        with self.assertRaisesRegex(ContractError, "duplicate comparison benchmark"):
            build(records)

    def test_rejects_missing_fp_row(self) -> None:
        records = fixture()
        records["bitwuzla"].pop()
        with self.assertRaisesRegex(ContractError, "logic population drift"):
            build(records)

    def test_rejects_wrong_bitwuzla_logic_membership(self) -> None:
        records = fixture()
        records["bitwuzla"][-1] = row(
            "bitwuzla", "QF_AUFLIA", "b", "sat", "sat"
        )
        mutated_counts = copy.deepcopy(LOGIC_COUNTS)
        mutated_counts["bitwuzla"] = {
            "QF_ABVFP": 1,
            "QF_AUFLIA": 1,
            "QF_BVFP": 1,
        }
        with self.assertRaisesRegex(ContractError, "exact FP-family subset"):
            build_comparison(
                records,
                authority={"fixture": True},
                expected_logic_counts=mutated_counts,
            )

    def test_rejects_shared_expected_status_drift(self) -> None:
        records = fixture()
        records["cvc5"][0]["expected_status"] = "sat"
        with self.assertRaisesRegex(ContractError, "expected-status drift"):
            build(records)

    def test_rejects_known_status_contradiction(self) -> None:
        records = fixture()
        records["axeyum"][0]["reported_status"] = "sat"
        with self.assertRaisesRegex(ContractError, "known-status contradiction"):
            build(records)

    def test_rejects_cross_solver_disagreement(self) -> None:
        records = fixture()
        records["cvc5"][-1]["reported_status"] = "unsat"
        with self.assertRaisesRegex(ContractError, "cross-solver disagreement"):
            build(records)

    def test_rejects_invalid_status_and_termination(self) -> None:
        records = fixture()
        records["axeyum"][0]["reported_status"] = "timeout"
        with self.assertRaisesRegex(ContractError, "reported status"):
            build(records)
        records = fixture()
        records["axeyum"][0]["termination_class"] = ""
        with self.assertRaisesRegex(ContractError, "termination class"):
            build(records)

    def test_self_seal_and_markdown_are_deterministic(self) -> None:
        first = build()
        second = build()
        self.assertEqual(comparison_json_bytes(first), comparison_json_bytes(second))
        json_bytes = comparison_json_bytes(first)
        markdown = render_markdown(first, sha256_bytes(json_bytes))
        self.assertEqual(markdown, render_markdown(second, sha256_bytes(json_bytes)))
        self.assertIn(b"Bitwuzla's rows are exactly", markdown)
        mutated = copy.deepcopy(first)
        mutated["population_contract"]["all_population"] += 1
        with self.assertRaisesRegex(ContractError, "record hash mismatch"):
            validate_comparison(mutated)

    def test_rejects_resealed_unaccounted_projection(self) -> None:
        mutated = copy.deepcopy(build())
        mutated["pairwise"]["axeyum_cvc5_all"]["intersection_count"] -= 1
        mutated["record_sha256"] = digest(
            {key: value for key, value in mutated.items() if key != "record_sha256"}
        )
        with self.assertRaisesRegex(ContractError, "pairwise projection accounting"):
            validate_comparison(mutated)

    def test_rejects_resealed_external_completion_identity_drift(self) -> None:
        path = (
            ROOT
            / "docs"
            / "plan"
            / "generated"
            / "smtcomp-repaired-p0-comparison.json"
        )
        mutated = json.loads(path.read_text(encoding="utf-8"))
        mutated["authority"]["cells"]["axeyum"][
            "completion_record_sha256"
        ] = "0" * 64
        mutated["record_sha256"] = digest(
            {key: value for key, value in mutated.items() if key != "record_sha256"}
        )
        with self.assertRaisesRegex(ContractError, "cell authority drift"):
            validate_comparison(mutated)


if __name__ == "__main__":
    unittest.main()
