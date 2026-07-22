"""Contract and mutation tests for ADR-0356's independent selection auditor."""

from __future__ import annotations

import copy
import gzip
import json
import runpy
import shutil
import tempfile
import unittest
from pathlib import Path

from scripts.smtcomp_repro.official_selection import (
    SelectionAuditError,
    HistoricalAccumulator,
    adapt_official_benchmarks,
    adapt_official_results,
    adapt_official_submissions,
    audit_corpus,
    audit_selection,
    canonical_json_bytes,
    division_cap,
    extract_official_logics,
    extract_removed_benchmark_ids,
    extract_single_query_divisions,
    historical_facts,
    normalize_benchmark,
    validate_decisions,
)


ROOT = Path(__file__).resolve().parents[3]
FIXTURE_ROOT = ROOT / "scripts/smtcomp_repro/fixtures/official_selection"
AUTHORITY_PATH = ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json"
CONTRACT_PATH = ROOT / "docs/plan/smtcomp-official-selection-contract-v1.json"
GENERATOR_PATH = ROOT / "scripts/gen-smtcomp-selection-authority.py"
INPUT_AUDIT_PATH = ROOT / "scripts/audit-smtcomp-selection-inputs.py"


class OfficialSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = json.loads((FIXTURE_ROOT / "fixture.json").read_bytes())
        cls.authority = json.loads(AUTHORITY_PATH.read_bytes())
        cls.generator = runpy.run_path(str(GENERATOR_PATH))
        cls.input_audit = runpy.run_path(str(INPUT_AUDIT_PATH))

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
        self.assertEqual(self.authority["summary"]["submission_count"], 51)
        self.assertEqual(self.authority["summary"]["competitive_submission_count"], 36)
        self.assertEqual(self.authority["policy"]["global_seed"], 22_731_074)
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
        self.assertEqual(contract["policy"]["global_seed"], 22_731_074)
        invariant_ids = [row["id"] for row in contract["invariants"]]
        mutation_ids = [row["id"] for row in contract["mutations"]]
        self.assertEqual(len(invariant_ids), 18)
        self.assertEqual(len(invariant_ids), len(set(invariant_ids)))
        self.assertEqual(len(mutation_ids), 18)
        self.assertEqual(len(mutation_ids), len(set(mutation_ids)))

    def test_official_defs_ast_and_submission_adapter(self) -> None:
        defs_source = (FIXTURE_ROOT / "official_defs.py").read_bytes()
        divisions = extract_single_query_divisions(defs_source)
        all_logics = extract_official_logics(defs_source)
        self.assertEqual(
            divisions,
            {
                "QF_Bitvec": ["QF_BV"],
                "QF_LinearIntArith": ["QF_IDL", "QF_LIA"],
            },
        )
        documents = [
            {
                "name": "division-solver",
                "participations": [
                    {"divisions": ["QF_LinearIntArith"], "tracks": ["SingleQuery"]},
                    {"logics": ["QF_BV"], "tracks": ["Parallel"]},
                ],
                "seed": "17",
            },
            {
                "competitive": False,
                "name": "explicit-solver",
                "participations": [
                    {"logics": ["QF_BV"], "tracks": ["SingleQuery"]},
                ],
            },
            {
                "name": "regexp-solver",
                "participations": [
                    {"logics": "QF_(BV|LIA|AUFBVLIA)", "tracks": ["SingleQuery"]},
                ],
                "seed": 23,
            },
        ]
        normalized = adapt_official_submissions(documents, divisions, all_logics)
        self.assertEqual(normalized[0]["seed"], 17)
        self.assertEqual(
            normalized[0]["participations"],
            [{"logics": ["QF_IDL", "QF_LIA"], "track": "single-query"}],
        )
        self.assertFalse(normalized[1]["competitive"])
        self.assertIsNone(normalized[1]["seed"])
        self.assertEqual(
            normalized[2]["participations"],
            [{"logics": ["QF_BV", "QF_LIA"], "track": "single-query"}],
        )
        self.assertEqual(
            extract_removed_benchmark_ids(defs_source),
            {"non-incremental/QF_BV/2024-old/nested/removed.smt2"},
        )

    def test_official_benchmark_and_result_adapters(self) -> None:
        file_identity = {
            "family": ["2025-fixture", "nested"],
            "incremental": False,
            "logic": "QF_BV",
            "name": "case.smt2",
        }
        benchmark_document = {
            "incremental": [],
            "non_incremental": [
                {"asserts": 1, "file": file_identity, "status": "unknown"},
            ],
        }
        benchmarks = adapt_official_benchmarks(gzip.compress(canonical_json_bytes(benchmark_document)))
        self.assertEqual(
            normalize_benchmark(benchmarks[0])["benchmark_id"],
            "non-incremental/QF_BV/2025-fixture/nested/case.smt2",
        )

        result_document = {
            "results": [
                {
                    "cpu_time": 0.25,
                    "file": file_identity,
                    "memory_usage": 10.0,
                    "result": "OutOfMemory",
                    "solver": solver,
                    "track": "SingleQuery",
                    "wallclock_time": 0.3,
                }
                for solver in ("solver-a", "solver-b")
            ]
        }
        results = adapt_official_results(
            gzip.compress(canonical_json_bytes(result_document)),
            year=2024,
        )
        facts = historical_facts(results, {results[0]["benchmark_id"]})
        # This looks odd, but it is the pinned executable criterion:
        # result != Unknown and cpu_time <= 1.0, not the prose comment.
        self.assertTrue(facts[results[0]["benchmark_id"]]["trivial"])

    def test_official_format_mutations_reject(self) -> None:
        defs_source = (FIXTURE_ROOT / "official_defs.py").read_bytes()
        divisions = extract_single_query_divisions(defs_source)
        all_logics = extract_official_logics(defs_source)
        with self.assertRaises(SelectionAuditError):
            adapt_official_submissions(
                [
                    {
                        "name": "bad-division",
                        "participations": [
                            {"divisions": ["missing"], "tracks": ["SingleQuery"]},
                        ],
                        "seed": 1,
                    }
                ],
                divisions,
                all_logics,
            )
        with self.assertRaises(SelectionAuditError):
            adapt_official_submissions(
                [
                    {
                        "name": "bad-regexp",
                        "participations": [
                            {"logics": "[", "tracks": ["SingleQuery"]},
                        ],
                        "seed": 1,
                    }
                ],
                divisions,
                all_logics,
            )
        with self.assertRaises(SelectionAuditError):
            adapt_official_submissions(
                [
                    {
                        "name": "bad-logic",
                        "participations": [
                            {"logics": ["QF_UNKNOWN"], "tracks": ["SingleQuery"]},
                        ],
                        "seed": 1,
                    }
                ],
                divisions,
                all_logics,
            )
        bad_benchmark = {
            "incremental": [],
            "non_incremental": [
                {
                    "asserts": 1,
                    "file": {
                        "family": ["2025-fixture"],
                        "incremental": True,
                        "logic": "QF_BV",
                        "name": "case.smt2",
                    },
                    "status": "unknown",
                }
            ],
        }
        with self.assertRaises(SelectionAuditError):
            adapt_official_benchmarks(gzip.compress(canonical_json_bytes(bad_benchmark)))

        bad_result = {
            "results": [
                {
                    "cpu_time": 0.1,
                    "file": {
                        "family": ["2025-fixture"],
                        "incremental": False,
                        "logic": "QF_BV",
                        "name": "case.smt2",
                    },
                    "memory_usage": 10.0,
                    "result": "new-unregistered-answer",
                    "solver": "solver-a",
                    "track": "SingleQuery",
                    "wallclock_time": 0.1,
                }
            ]
        }
        with self.assertRaises(SelectionAuditError):
            adapt_official_results(gzip.compress(canonical_json_bytes(bad_result)), year=2024)

    def test_streamed_gzip_object_array_handles_target_after_discarded_array(self) -> None:
        document = {
            "discarded": [{"value": index} for index in range(5)],
            "target": [{"id": "a"}, {"id": "b"}],
        }
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "stream.json.gz"
            path.write_bytes(gzip.compress(canonical_json_bytes(document)))
            rows = list(self.input_audit["iter_gzip_object_array"](path, "target"))
        self.assertEqual(rows, [{"id": "a"}, {"id": "b"}])

    def test_streamed_gzip_object_array_mutations_reject(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "stream.json.gz"
            path.write_bytes(gzip.compress(b'{"other":[]}\n'))
            with self.assertRaises(self.input_audit["InputAuditError"]):
                list(self.input_audit["iter_gzip_object_array"](path, "target"))
            path.write_bytes(gzip.compress(b'{"target":[{"id":1}'))
            with self.assertRaises(self.input_audit["InputAuditError"]):
                list(self.input_audit["iter_gzip_object_array"](path, "target"))

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

    def test_streaming_historical_accumulator_matches_batch_result(self) -> None:
        known_ids = {
            normalize_benchmark(row)["benchmark_id"] for row in self.fixture["benchmarks"]
        }
        accumulator = HistoricalAccumulator(known_ids)
        for row in self.fixture["historical_results"]:
            accumulator.add(row)
        self.assertEqual(
            accumulator.facts(),
            historical_facts(self.fixture["historical_results"], known_ids),
        )
        self.assertEqual(accumulator.rows, len(self.fixture["historical_results"]))
        self.assertEqual(accumulator.ignored_rows, 0)

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
