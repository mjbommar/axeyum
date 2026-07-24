"""Completion-last external-result gates for credited full execution."""

from __future__ import annotations

import copy
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

import full_result as full_result_module  # noqa: E402
from full_compare import build_full_comparison, summarize_full_cell_records, validate_full_cell_records  # noqa: E402
from full_population import SOLVER_IDS  # noqa: E402
from full_result import (  # noqa: E402
    build_full_execution_authority,
    comparison_authority_from_cell_results,
    load_full_cell_results,
    publish_full_cell_result,
    validate_full_cell_result,
)
from resume_contract import ContractError, digest  # noqa: E402


LOGIC_COUNTS = {"QF_BV": 1, "QF_UF": 1}


def seal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def records(solver_id: str, *, contradiction: bool = False) -> list[dict]:
    return [
        seal(
            {
                "solver_id": solver_id,
                "sequence": 0,
                "benchmark_id": "QF_BV/fixture/a.smt2",
                "benchmark_sha256": "a" * 64,
                "expected_status": "sat",
                "reported_status": "unsat" if contradiction else "sat",
                "termination_class": "completed",
            }
        ),
        seal(
            {
                "solver_id": solver_id,
                "sequence": 1,
                "benchmark_id": "QF_UF/fixture/b.smt2",
                "benchmark_sha256": "b" * 64,
                "expected_status": None,
                "reported_status": "unknown",
                "termination_class": "completed",
            }
        ),
    ]


def authority(
    solver_id: str, material: list[dict], *, disagreements: int = 0
) -> dict:
    indexed = validate_full_cell_records(
        solver_id,
        material,
        expected_logic_counts=LOGIC_COUNTS,
        fixture_only=True,
    )
    summary = summarize_full_cell_records(
        indexed, expected_logic_counts=LOGIC_COUNTS
    )
    return build_full_execution_authority(
        solver_id=solver_id,
        preparation_record_sha256="c" * 64,
        selection_record_sha256="d" * 64,
        run_identity_sha256="e" * 64,
        plan_sha256="f" * 64,
        schedule_record_sha256="1" * 64,
        wave_checkpoint_record_sha256s=["2" * 64],
        resource_completion_record_sha256="3" * 64,
        multi_host_completion_record_sha256="4" * 64,
        prior_cell_result_record_sha256s=[
            f"{10 + index:064x}"
            for index in range(SOLVER_IDS.index(solver_id))
        ],
        cross_solver_disagreement_count=disagreements,
        population_count=summary["population"],
        key_set_sha256=summary["key_set_sha256"],
        record_set_sha256=summary["record_set_sha256"],
        completed_at_ns=1000,
        fixture_only=True,
    )


class FullCellResultTests(unittest.TestCase):
    def test_publishes_completion_last_and_replays_every_artifact(self) -> None:
        material = records("axeyum")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "cell-result"
            original_json = full_result_module.atomic_install_json
            with mock.patch.object(
                full_result_module, "atomic_install_json", wraps=original_json
            ) as install:
                completion = publish_full_cell_result(
                    root,
                    records=material,
                    execution_authority=authority("axeyum", material),
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1100,
                )
            self.assertEqual(install.call_args_list[-1].args[1], "complete.json")
            self.assertTrue(completion["safe_to_continue"])
            self.assertEqual(completion["population_count"], 2)
            self.assertEqual(
                validate_full_cell_result(
                    root, expected_logic_counts=LOGIC_COUNTS
                )["record_sha256"],
                completion["record_sha256"],
            )

    def test_known_contradiction_publishes_but_blocks_comparison_authority(self) -> None:
        material = records("axeyum", contradiction=True)
        with tempfile.TemporaryDirectory() as temp:
            completion = publish_full_cell_result(
                Path(temp) / "cell-result",
                records=material,
                execution_authority=authority("axeyum", material),
                expected_logic_counts=LOGIC_COUNTS,
                published_at_ns=1100,
            )
        self.assertFalse(completion["safe_to_continue"])
        with self.assertRaisesRegex(ContractError, "authority mismatch"):
            comparison_authority_from_cell_results(
                [completion, {**completion, "solver_id": "cvc5"}, {**completion, "solver_id": "bitwuzla"}]
            )

    def test_cross_solver_disagreement_publishes_but_blocks_continuation(self) -> None:
        material = records("cvc5")
        with tempfile.TemporaryDirectory() as temp:
            completion = publish_full_cell_result(
                Path(temp) / "cell-result",
                records=material,
                execution_authority=authority(
                    "cvc5", material, disagreements=1
                ),
                expected_logic_counts=LOGIC_COUNTS,
                published_at_ns=1100,
            )
        self.assertFalse(completion["safe_to_continue"])

    def test_interruption_resumes_without_completion_or_byte_drift(self) -> None:
        material = records("cvc5")
        execution = authority("cvc5", material)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "cell-result"

            def interrupt(phase: str) -> None:
                if phase == "after_records":
                    raise RuntimeError("fixture interruption")

            with self.assertRaisesRegex(RuntimeError, "fixture interruption"):
                publish_full_cell_result(
                    root,
                    records=material,
                    execution_authority=execution,
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1100,
                    phase_hook=interrupt,
                )
            self.assertFalse((root / "complete.json").exists())
            before = (root / "records.jsonl").read_bytes()
            publish_full_cell_result(
                root,
                records=material,
                execution_authority=execution,
                expected_logic_counts=LOGIC_COUNTS,
                published_at_ns=1100,
            )
            self.assertEqual((root / "records.jsonl").read_bytes(), before)

    def test_mutated_record_or_extra_prepublication_file_rejects(self) -> None:
        material = records("bitwuzla")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "cell-result"
            publish_full_cell_result(
                root,
                records=material,
                execution_authority=authority("bitwuzla", material),
                expected_logic_counts=LOGIC_COUNTS,
                published_at_ns=1100,
            )
            record_path = root / "records.jsonl"
            record_path.chmod(0o644)
            record_path.write_bytes(record_path.read_bytes().replace(b'"unknown"', b'"sat"', 1))
            with self.assertRaises(ContractError):
                validate_full_cell_result(root, expected_logic_counts=LOGIC_COUNTS)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "cell-result"
            root.mkdir()
            (root / "unexpected").write_bytes(b"reject\n")
            with self.assertRaisesRegex(ContractError, "prepublication inventory"):
                publish_full_cell_result(
                    root,
                    records=material,
                    execution_authority=authority("bitwuzla", material),
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1100,
                )

    def test_three_safe_cell_results_feed_same_population_comparison(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            roots = {}
            for solver_id in SOLVER_IDS:
                material = records(solver_id)
                roots[solver_id] = Path(temp) / solver_id
                publish_full_cell_result(
                    roots[solver_id],
                    records=material,
                    execution_authority=authority(solver_id, material),
                    expected_logic_counts=LOGIC_COUNTS,
                    published_at_ns=1100,
                )
            comparison_authority, by_solver = load_full_cell_results(
                roots, expected_logic_counts=LOGIC_COUNTS
            )
            comparison = build_full_comparison(
                by_solver,
                authority=comparison_authority,
                expected_logic_counts=LOGIC_COUNTS,
            )
            self.assertEqual(
                comparison["population_contract"]["population_count"], 2
            )
            self.assertTrue(comparison["integrity"]["safe_to_publish"])
