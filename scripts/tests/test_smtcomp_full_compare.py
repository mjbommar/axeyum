"""Fail-closed gates for the credited full-population comparison."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

import full_compare as full_compare_module  # noqa: E402
from full_compare import (  # noqa: E402
    build_full_comparison,
    publish_full_comparison,
    validate_full_comparison,
    validate_full_comparison_publication,
)
from full_population import SOLVER_IDS  # noqa: E402
from resume_contract import ContractError, digest  # noqa: E402


LOGIC_COUNTS = {"QF_ABVFP": 1, "QF_AUFLIA": 1, "QF_BV": 1, "QF_UF": 1}


def seal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def row(
    solver_id: str,
    *,
    sequence: int,
    logic: str,
    suffix: str,
    expected: str | None,
    reported: str | None,
    termination: str = "completed",
) -> dict:
    return seal(
        {
            "solver_id": solver_id,
            "sequence": sequence,
            "benchmark_id": f"{logic}/fixture/{suffix}.smt2",
            "benchmark_sha256": suffix * 64,
            "expected_status": expected,
            "reported_status": reported,
            "termination_class": termination,
        }
    )


def fixture() -> dict[str, list[dict]]:
    definitions = (
        ("QF_ABVFP", "a", "unsat"),
        ("QF_AUFLIA", "b", "sat"),
        ("QF_BV", "c", None),
        ("QF_UF", "d", "unsat"),
    )
    outcomes = {
        "axeyum": (("unsat", "completed"), ("unknown", "completed"), ("sat", "completed"), (None, "wall-timeout")),
        "cvc5": (("unsat", "completed"), ("sat", "completed"), ("unknown", "completed"), ("unknown", "completed")),
        "bitwuzla": (("unknown", "completed"), ("sat", "completed"), ("sat", "completed"), (None, "nonzero-exit")),
    }
    return {
        solver_id: [
            row(
                solver_id,
                sequence=index,
                logic=logic,
                suffix=suffix,
                expected=expected,
                reported=outcomes[solver_id][index][0],
                termination=outcomes[solver_id][index][1],
            )
            for index, (logic, suffix, expected) in enumerate(definitions)
        ]
        for solver_id in SOLVER_IDS
    }


def authority() -> dict:
    return {
        "fixture_only": True,
        "preparation_record_sha256": "e" * 64,
        "selection_record_sha256": "f" * 64,
        "cell_results": [
            {
                "solver_id": solver_id,
                "record_sha256": f"{index + 1:x}" * 64,
                "population_count": 4,
                "safe_to_continue": True,
            }
            for index, solver_id in enumerate(SOLVER_IDS)
        ],
    }


class FullComparisonTests(unittest.TestCase):
    def test_derives_exact_native_pairwise_and_three_way_logic_views(self) -> None:
        result = build_full_comparison(
            fixture(), authority=authority(), expected_logic_counts=LOGIC_COUNTS
        )
        self.assertEqual(result["population_contract"]["population_count"], 4)
        self.assertEqual(result["population_contract"]["logic_count"], 4)
        self.assertTrue(result["population_contract"]["same_population_all_cells"])
        self.assertEqual(result["native_cells"]["axeyum"]["decision_count"], 2)
        self.assertEqual(result["native_cells"]["cvc5"]["decision_count"], 2)
        self.assertEqual(result["native_cells"]["bitwuzla"]["decision_count"], 2)
        self.assertEqual(
            result["pairwise"]["axeyum_cvc5"]["overall"]["decision_projection"],
            {
                "both-decide-agree": 1,
                "disagreement": 0,
                "left-only-decides": 1,
                "neither-decides": 1,
                "right-only-decides": 1,
            },
        )
        self.assertEqual(
            result["three_solver"]["overall"]["decision_projection"],
            {
                "disagreement": 0,
                "none-decide": 1,
                "one-decides": 0,
                "three-decide-agree": 0,
                "two-decide-agree": 3,
            },
        )
        self.assertEqual(
            result["three_solver"]["per_logic"]["QF_BV"]["sole_non_decider_counts"]["cvc5"],
            1,
        )

    def test_rejects_population_duplicate_and_shared_metadata_drift(self) -> None:
        for label, mutate, message in (
            (
                "replacement",
                lambda records: records["bitwuzla"][0].update(
                    benchmark_id="QF_ABVFP/fixture/replacement.smt2"
                ),
                "same-population",
            ),
            (
                "duplicate",
                lambda records: records["cvc5"].__setitem__(
                    1, copy.deepcopy(records["cvc5"][0])
                ),
                "duplicate",
            ),
            (
                "sequence",
                lambda records: records["cvc5"][0].update(sequence=99),
                "sequence coverage",
            ),
            (
                "metadata",
                lambda records: records["cvc5"][2].update(expected_status="sat"),
                "metadata drift",
            ),
            (
                "sequence-coverage",
                lambda records: [
                    records[solver_id][1].update(sequence=0)
                    for solver_id in SOLVER_IDS
                ],
                "sequence coverage",
            ),
        ):
            with self.subTest(label=label):
                records = fixture()
                mutate(records)
                for solver_id in SOLVER_IDS:
                    records[solver_id] = [seal(row) for row in records[solver_id]]
                with self.assertRaisesRegex(ContractError, message):
                    build_full_comparison(
                        records,
                        authority=authority(),
                        expected_logic_counts=LOGIC_COUNTS,
                    )

    def test_rejects_known_contradiction_or_cross_solver_disagreement(self) -> None:
        contradiction = fixture()
        contradiction["axeyum"][0]["reported_status"] = "sat"
        contradiction["axeyum"][0] = seal(contradiction["axeyum"][0])
        with self.assertRaisesRegex(ContractError, "known-status contradiction"):
            build_full_comparison(
                contradiction,
                authority=authority(),
                expected_logic_counts=LOGIC_COUNTS,
            )
        disagreement = fixture()
        disagreement["bitwuzla"][2]["reported_status"] = "unsat"
        disagreement["bitwuzla"][2] = seal(disagreement["bitwuzla"][2])
        with self.assertRaisesRegex(ContractError, "cross-solver disagreement"):
            build_full_comparison(
                disagreement,
                authority=authority(),
                expected_logic_counts=LOGIC_COUNTS,
            )

    def test_resealed_summary_mutation_rejects_against_source_records(self) -> None:
        records = fixture()
        result = build_full_comparison(
            records, authority=authority(), expected_logic_counts=LOGIC_COUNTS
        )
        mutated = copy.deepcopy(result)
        counts = mutated["native_cells"]["axeyum"]["reported_status_counts"]
        counts["sat"] -= 1
        counts["unknown"] += 1
        mutated = seal(mutated)
        with self.assertRaisesRegex(ContractError, "replay drift"):
            validate_full_comparison(
                mutated,
                records_by_solver=records,
                expected_logic_counts=LOGIC_COUNTS,
            )

    def test_publication_is_completion_last_and_rejects_mutation_or_extra_file(self) -> None:
        records = fixture()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "comparison"
            original = full_compare_module.atomic_install_json
            with mock.patch.object(
                full_compare_module, "atomic_install_json", wraps=original
            ) as install:
                completion = publish_full_comparison(
                    root,
                    records_by_solver=records,
                    authority=authority(),
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1234,
                )
            self.assertEqual(install.call_args_list[-1].args[1], "complete.json")
            self.assertEqual(completion["status"], "complete-no-performance-ranking")
            with self.assertRaisesRegex(ContractError, "already complete"):
                publish_full_comparison(
                    root,
                    records_by_solver=records,
                    authority=authority(),
                    expected_logic_counts=LOGIC_COUNTS,
                )
            comparison = root / "comparison.json"
            original_bytes = comparison.read_bytes()
            comparison.chmod(0o644)
            comparison.write_bytes(original_bytes.replace(b'"population":4', b'"population":5', 1))
            with self.assertRaises(ContractError):
                validate_full_comparison_publication(
                    root,
                    records_by_solver=records,
                    expected_logic_counts=LOGIC_COUNTS,
                )
            comparison.write_bytes(original_bytes)
            (root / "unexpected").write_bytes(b"reject\n")
            with self.assertRaisesRegex(ContractError, "inventory"):
                validate_full_comparison_publication(
                    root,
                    records_by_solver=records,
                    expected_logic_counts=LOGIC_COUNTS,
                )

    def test_interrupted_publication_replays_identically_without_completion(self) -> None:
        records = fixture()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "comparison"

            def interrupt(phase: str) -> None:
                if phase == "after_comparison":
                    raise RuntimeError("fixture interruption")

            with self.assertRaisesRegex(RuntimeError, "fixture interruption"):
                publish_full_comparison(
                    root,
                    records_by_solver=records,
                    authority=authority(),
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1234,
                    phase_hook=interrupt,
                )
            self.assertTrue((root / "comparison.json").is_file())
            self.assertFalse((root / "complete.json").exists())
            first = (root / "comparison.json").read_bytes()
            publish_full_comparison(
                root,
                records_by_solver=records,
                authority=authority(),
                expected_logic_counts=LOGIC_COUNTS,
                published_at_ns=1234,
            )
            self.assertEqual((root / "comparison.json").read_bytes(), first)
