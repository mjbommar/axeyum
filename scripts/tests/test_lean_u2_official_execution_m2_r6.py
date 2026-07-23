from __future__ import annotations

import copy
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2
from scripts import lean_u2_official_execution_m2_r5 as R5
from scripts import lean_u2_official_execution_m2_r6 as R6


ROOT = Path(__file__).resolve().parents[2]


class LeanU2OfficialExecutionM2R6Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        root = R5.DEFAULT_EVIDENCE_ROOT
        cls.junit = BASE.load_canonical(root / "junit.json")
        cls.source = BASE.load_canonical(root / "source.json")
        diagnostic = BASE.load_canonical(root / "diagnostic/post.json")
        cls.all_pass_generated = diagnostic["generated_files"]

    def failing_junit(self) -> dict[str, object]:
        junit = copy.deepcopy(self.junit)
        junit["cases"][0]["outcome"] = "failed"
        junit["summary"] = {
            "official_cases": 64,
            "official_outcomes": 64,
            "official_passes": 63,
            "official_failures": 1,
        }
        junit["cases_sha256"] = BASE.domain_digest(
            "axeyum-lean-u2-official-execution-m2-junit-cases-v1",
            junit["cases"],
        )
        junit["record_sha256"] = ""
        return BASE.seal(junit, M2.JUNIT_SCHEMA)

    def failing_generated(self) -> list[dict[str, object]]:
        rows = copy.deepcopy(self.all_pass_generated)
        template = next(
            row for row in rows if row["path"].endswith("CTestCostData.txt")
        )
        rows.append(
            template
            | {
                "path": R6.FAILURE_LOG,
                "bytes": 12,
                "sha256": BASE.sha256_bytes(b"synthetic\n"),
            }
        )
        return sorted(rows, key=lambda row: row["path"])

    def test_history_spec_and_only_intended_contract_delta_are_exact(self) -> None:
        completion = R6.validate_history()
        self.assertEqual(completion["record_sha256"], R6.R5_COMPLETION_SHA256)
        summary = R6.validate_offline_contract()
        self.assertEqual(summary["cases"], 64)
        self.assertEqual(summary["all_pass_generated"], 123)
        self.assertEqual(summary["failing_generated"], 124)
        self.assertEqual(summary["memory_limit_bytes"], 34_359_738_368)
        spec = R6.build_spec(
            implementation_revision="1" * 40,
            source_root=Path("/r6/source"),
            toolchain_root=Path("/r6/toolchain"),
            harness_build=Path("/r6/harness"),
            junit_path=Path("/r6/attempt/test-results.xml"),
        )
        self.assertEqual(R6.validate_spec(spec), [])
        self.assertEqual(spec["attempt_id"], "attempt-004")
        self.assertEqual(spec["sequence"], 4)
        self.assertTrue(spec["prior_history"]["r5_selected_attempt_consumed"])
        self.assertEqual(spec["prior_history"]["r5_selected_outcome_credit"], 0)

    def test_all_pass_branch_requires_123_rows_and_retains_66(self) -> None:
        post = R6.build_post_record(
            original_files=self.source["files"],
            generated_files=self.all_pass_generated,
            junit=self.junit,
        )
        self.assertFalse(post["conditional_artifact"]["required"])
        self.assertEqual(post["assurance"]["retained_payload_count"], 66)
        projection = R6.result_projection(self.junit, post)
        self.assertEqual(projection["credits"]["official_passes"], 64)
        self.assertEqual(projection["credits"]["official_outcomes"], 64)

    def test_failure_branch_requires_124_rows_and_retains_67(self) -> None:
        junit = self.failing_junit()
        generated = self.failing_generated()
        post = R6.build_post_record(
            original_files=self.source["files"],
            generated_files=generated,
            junit=junit,
        )
        self.assertTrue(post["conditional_artifact"]["required"])
        self.assertEqual(post["assurance"]["retained_payload_count"], 67)
        projection = R6.result_projection(junit, post)
        self.assertEqual(projection["credits"]["official_passes"], 63)
        self.assertEqual(projection["credits"]["official_failures"], 1)

    def test_inverted_conditional_log_presence_rejects_both_directions(self) -> None:
        with self.assertRaisesRegex(R6.R6Error, "disagree with JUnit"):
            R6.build_post_record(
                original_files=self.source["files"],
                generated_files=self.failing_generated(),
                junit=self.junit,
            )
        with self.assertRaisesRegex(R6.R6Error, "disagree with JUnit"):
            R6.build_post_record(
                original_files=self.source["files"],
                generated_files=self.all_pass_generated,
                junit=self.failing_junit(),
            )

    def test_resealed_conditional_predicate_mutation_rejects_projection(self) -> None:
        post = R6.build_post_record(
            original_files=self.source["files"],
            generated_files=self.all_pass_generated,
            junit=self.junit,
        )
        post["conditional_artifact"]["required"] = True
        post["record_sha256"] = ""
        post = BASE.seal(post, M2.POST_SCHEMA)
        with self.assertRaisesRegex(R6.R6Error, "conditional linkage"):
            R6.result_projection(self.junit, post)

    def test_fresh_control_spec_targets_attempt_004_without_credit(self) -> None:
        with R6.r6_control_bindings():
            spec = R5._control_spec(
                implementation_revision="2" * 40,
                control_root=Path(R6.CONTROL_ROOT_PREFIX + "22222222"),
                toolchain_root=Path("/r6/toolchain"),
            )
        self.assertEqual(spec["selected_attempt_id"], "attempt-004")
        self.assertEqual(spec["memory_limit_bytes"], 34_359_738_368)
        self.assertFalse(spec["selected_attempt_consumed"])
        self.assertTrue(all(value == 0 for value in spec["credits"].values()))

    def test_control_preflight_delegates_without_recursion(self) -> None:
        revision = "3" * 40
        with mock.patch.object(R6, "_R5_VALIDATE_REVISION_PREFLIGHT") as gate:
            with R6.r6_control_bindings():
                R5.validate_revision_preflight(revision)
        gate.assert_called_once_with(revision)

    def test_bindings_install_split_and_restore_prior_contract(self) -> None:
        original_run_id = M2.RUN_ID
        with R6.r6_bindings():
            self.assertEqual(M2.RUN_ID, R6.RUN_ID)
            retained, metadata, wrapper = R6.R3._split_generated(
                self.all_pass_generated
            )
            self.assertEqual((len(retained), len(metadata), len(wrapper)), (66, 56, 1))
        self.assertEqual(M2.RUN_ID, original_run_id)

    def test_cli_offline_has_no_implicit_control_or_selected_execution(self) -> None:
        result = subprocess.run(
            [sys.executable, str(Path(R6.__file__).resolve()), "offline-check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"controls=0|selected_processes=0", result.stdout)
        help_result = subprocess.run(
            [sys.executable, str(Path(R6.__file__).resolve()), "--help"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(help_result.returncode, 0)
        self.assertIn(b"run-control", help_result.stdout)
        self.assertIn(b"run-r6", help_result.stdout)


if __name__ == "__main__":
    unittest.main()
