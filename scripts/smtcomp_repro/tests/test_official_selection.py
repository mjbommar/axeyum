"""Contract and mutation tests for ADR-0356's independent selection auditor."""

from __future__ import annotations

import copy
import json
import runpy
import shutil
import tempfile
import unittest
from pathlib import Path

from scripts.smtcomp_repro.official_selection import (
    SelectionAuditError,
    audit_corpus,
    audit_selection,
    canonical_json_bytes,
    division_cap,
    normalize_benchmark,
    validate_decisions,
)


ROOT = Path(__file__).resolve().parents[3]
FIXTURE_ROOT = ROOT / "scripts/smtcomp_repro/fixtures/official_selection"
AUTHORITY_PATH = ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json"
CONTRACT_PATH = ROOT / "docs/plan/smtcomp-official-selection-contract-v1.json"
GENERATOR_PATH = ROOT / "scripts/gen-smtcomp-selection-authority.py"


class OfficialSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = json.loads((FIXTURE_ROOT / "fixture.json").read_bytes())
        cls.authority = json.loads(AUTHORITY_PATH.read_bytes())
        cls.generator = runpy.run_path(str(GENERATOR_PATH))

    def audit_fixture(self, **replacements: object) -> dict[str, object]:
        values = {
            "benchmarks": self.fixture["benchmarks"],
            "submissions": self.fixture["submissions"],
            "historical_results": self.fixture["historical_results"],
            "removed_ids": self.fixture["removed_ids"],
            "selected_ids": self.fixture["selected_ids"],
        }
        values.update(replacements)
        return audit_selection(**values)

    def test_authority_manifest_is_canonical_and_cross_checked(self) -> None:
        self.generator["validate"](self.authority)
        self.assertEqual(AUTHORITY_PATH.read_bytes(), canonical_json_bytes(self.authority))
        self.assertEqual(self.authority["summary"]["submission_count"], 53)
        self.assertEqual(self.authority["summary"]["competitive_submission_count"], 38)
        self.assertEqual(self.authority["policy"]["global_seed"], 22_731_158)
        self.assertEqual(self.authority["benchmark_metadata"]["non_incremental_rows"], 450_472)

    def test_authority_mutations_reject(self) -> None:
        mutations = []

        wrong_source = copy.deepcopy(self.authority)
        next(
            row for row in wrong_source["organizer"]["source_files"]
            if row["path"] == "smtcomp/selection.py"
        )["sha256"] = "0" * 64
        mutations.append(wrong_source)

        wrong_seed = copy.deepcopy(self.authority)
        wrong_seed["policy"]["global_seed"] += 1
        mutations.append(wrong_seed)

        missing_submission = copy.deepcopy(self.authority)
        missing_submission["submissions"].pop()
        mutations.append(missing_submission)

        duplicate_archive = copy.deepcopy(self.authority)
        duplicate_archive["corpus_release"]["archives"][-1] = copy.deepcopy(
            duplicate_archive["corpus_release"]["archives"][0]
        )
        mutations.append(duplicate_archive)

        wrong_release = copy.deepcopy(self.authority)
        wrong_release["corpus_release"]["version"] = "2025.05.22"
        mutations.append(wrong_release)

        for mutation in mutations:
            with self.subTest(mutation=mutations.index(mutation)):
                with self.assertRaises(self.generator["AuthorityError"]):
                    self.generator["validate"](mutation)

    def test_contract_ids_and_frozen_policy_are_unique(self) -> None:
        contract = json.loads(CONTRACT_PATH.read_bytes())
        self.assertEqual(contract["schema"], "axeyum-smtcomp-official-selection-contract-v1")
        self.assertEqual(contract["policy"]["global_seed"], 22_731_158)
        invariant_ids = [row["id"] for row in contract["invariants"]]
        mutation_ids = [row["id"] for row in contract["mutations"]]
        self.assertEqual(len(invariant_ids), 18)
        self.assertEqual(len(invariant_ids), len(set(invariant_ids)))
        self.assertEqual(len(mutation_ids), 18)
        self.assertEqual(len(mutation_ids), len(set(mutation_ids)))

    def test_fixture_selection_reconstructs_all_terminal_reasons(self) -> None:
        result = self.audit_fixture()
        self.assertEqual(result["competitive_logics"], ["QF_BV", "QF_LIA"])
        decisions = {row["benchmark_id"]: row for row in result["decisions"]}
        self.assertEqual(
            decisions["non-incremental/QF_BV/2025-new/nested/new-fast.smt2"]["reason"],
            "excluded-trivial",
        )
        boundary = decisions["non-incremental/QF_BV/2025-new/new-boundary.smt2"]
        self.assertTrue(boundary["historical"]["trivial"])
        self.assertEqual(boundary["reason"], "excluded-trivial")
        incoherent = decisions["non-incremental/QF_BV/2025-new/new-incoherent.smt2"]
        self.assertFalse(incoherent["historical"]["file_coherent"])
        self.assertFalse(incoherent["historical"]["run"])
        self.assertEqual(incoherent["reason"], "selected-new")
        single = decisions["non-incremental/QF_BV/2024-old/old-single-solver.smt2"]
        self.assertFalse(single["historical"]["trivial"])
        self.assertEqual(single["reason"], "selected-old")
        self.assertEqual(
            decisions["non-incremental/QF_BV/2024-old/old-removed.smt2"]["reason"],
            "excluded-explicit-removal",
        )
        self.assertEqual(
            decisions["non-incremental/QF_UF/2024-only-one-entry/noncompetitive.smt2"]["reason"],
            "excluded-noncompetitive-logic",
        )

    def test_fixture_corpus_is_an_exact_byte_bijection(self) -> None:
        expected_ids = {
            normalize_benchmark(row)["benchmark_id"] for row in self.fixture["benchmarks"]
        }
        result = audit_corpus(
            FIXTURE_ROOT,
            self.fixture["file_ledger"],
            expected_ids=expected_ids,
        )
        self.assertEqual(result["files"], 9)
        self.assertEqual(len(result["ledger_sha256"]), 64)

    def test_corpus_missing_extra_symlink_and_byte_drift_reject(self) -> None:
        expected_ids = {
            normalize_benchmark(row)["benchmark_id"] for row in self.fixture["benchmarks"]
        }
        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary) / "fixture"
            shutil.copytree(FIXTURE_ROOT, copied)
            missing = copied / self.fixture["file_ledger"][0]["benchmark_id"]
            missing.unlink()
            with self.assertRaises(SelectionAuditError):
                audit_corpus(copied, self.fixture["file_ledger"], expected_ids=expected_ids)

        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary) / "fixture"
            shutil.copytree(FIXTURE_ROOT, copied)
            extra = copied / "non-incremental/QF_BV/2024-old/extra.smt2"
            extra.write_text("(check-sat)\n", encoding="utf-8")
            with self.assertRaises(SelectionAuditError):
                audit_corpus(copied, self.fixture["file_ledger"], expected_ids=expected_ids)

        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary) / "fixture"
            shutil.copytree(FIXTURE_ROOT, copied)
            target = copied / self.fixture["file_ledger"][0]["benchmark_id"]
            target.unlink()
            target.symlink_to(copied / self.fixture["file_ledger"][1]["benchmark_id"])
            with self.assertRaises(SelectionAuditError):
                audit_corpus(copied, self.fixture["file_ledger"], expected_ids=expected_ids)

        wrong_ledger = copy.deepcopy(self.fixture["file_ledger"])
        wrong_ledger[0]["sha256"] = "0" * 64
        with self.assertRaises(SelectionAuditError):
            audit_corpus(FIXTURE_ROOT, wrong_ledger, expected_ids=expected_ids)

    def test_all_four_cap_regions_and_new_before_old_quotas(self) -> None:
        for population in self.fixture["generated_logic_populations"]:
            logic = population["logic"]
            benchmarks = []
            for index in range(population["count"]):
                benchmarks.append(
                    {
                        "asserts": 1,
                        "family": ["2025-generated" if index < population["new"] else "2024-generated"],
                        "logic": logic,
                        "name": f"case-{index:04d}.smt2",
                        "status": "unknown",
                    }
                )
            ids = [normalize_benchmark(row)["benchmark_id"] for row in benchmarks]
            selected = ids[: population["new"]] + ids[
                population["new"] : population["expected_cap"]
            ]
            submissions = [
                {
                    "competitive": True,
                    "name": f"solver-{suffix}",
                    "participations": [{"logics": [logic], "track": "single-query"}],
                    "seed": seed,
                }
                for suffix, seed in (("a", 1), ("b", 2))
            ]
            with self.subTest(logic=logic):
                self.assertEqual(division_cap(population["count"]), population["expected_cap"])
                result = audit_selection(benchmarks, submissions, [], [], selected)
                self.assertEqual(result["summaries"][0]["cap"], population["expected_cap"])
                self.assertEqual(result["summaries"][0]["selected_new"], population["new"])

                if population["count"] > population["expected_cap"]:
                    wrong = list(selected)
                    wrong[0] = ids[population["expected_cap"]]
                    with self.assertRaises(SelectionAuditError):
                        audit_selection(benchmarks, submissions, [], [], wrong)

    def test_selection_and_decision_mutations_reject(self) -> None:
        duplicate_benchmark = list(self.fixture["benchmarks"]) + [self.fixture["benchmarks"][0]]
        with self.assertRaises(SelectionAuditError):
            self.audit_fixture(benchmarks=duplicate_benchmark)

        traversal = copy.deepcopy(self.fixture["benchmarks"])
        traversal[0]["family"] = [".."]
        with self.assertRaises(SelectionAuditError):
            self.audit_fixture(benchmarks=traversal)

        with self.assertRaises(SelectionAuditError):
            self.audit_fixture(selected_ids=list(self.fixture["selected_ids"]) + ["missing.smt2"])
        with self.assertRaises(SelectionAuditError):
            self.audit_fixture(selected_ids=list(self.fixture["selected_ids"]) * 2)
        with self.assertRaises(SelectionAuditError):
            self.audit_fixture(selected_ids=self.fixture["selected_ids"][:-1])

        result = self.audit_fixture()
        decisions = copy.deepcopy(result["decisions"])
        decisions[0].pop("reason")
        with self.assertRaises(SelectionAuditError):
            validate_decisions(
                decisions,
                expected_ids={row["benchmark_id"] for row in result["decisions"]},
                selected_ids=set(self.fixture["selected_ids"]),
            )

        decisions = copy.deepcopy(result["decisions"])
        decisions[0]["selected"] = not decisions[0]["selected"]
        with self.assertRaises(SelectionAuditError):
            validate_decisions(
                decisions,
                expected_ids={row["benchmark_id"] for row in result["decisions"]},
                selected_ids=set(self.fixture["selected_ids"]),
            )


if __name__ == "__main__":
    unittest.main()
