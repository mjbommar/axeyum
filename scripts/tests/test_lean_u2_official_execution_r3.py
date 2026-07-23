from __future__ import annotations

import copy
import subprocess
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_r2 as R2
from scripts import lean_u2_official_execution_r3 as R3


class LeanU2OfficialExecutionR3Tests(unittest.TestCase):
    def spec(self) -> dict:
        with R3.r2_r3_configuration(), R2.base_r2_configuration():
            return BASE.build_spec(
                implementation_revision="a" * 40,
                source_root=Path("/tmp/axeyum-u2-r3-source"),
                toolchain_root=Path("/tmp/axeyum-u2-r3-toolchain"),
                harness_build=Path("/tmp/axeyum-u2-r3-harness"),
                junit_path=Path("/tmp/axeyum-u2-r3-private/test-results.xml"),
            )

    def result_authority(self, outcome: str = "passed") -> dict:
        credits = R3.aggregate_credits(outcome)
        evidence: list[dict] = []
        value = {
            "schema": R3.RESULT_SCHEMA,
            "status": "complete-local-official-case-history",
            "implementation_revision": "a" * 40,
            "r3_preregistration_commit": R3.R3_PREREGISTRATION_COMMIT,
            "r3_plan_sha256": R3.R3_PLAN_SHA256,
            "r2_invocation_bytes_sha256": R3.R2_INVOCATION_BYTES_SHA256,
            "r2_invocation_record_sha256": R3.R2_INVOCATION_RECORD_SHA256,
            "failed_attempt": R3.failed_attempt_dependency(
                live_readonly_validated=True, git_index_validated=True
            ),
            "attempts": [
                {"id": "attempt-001", "sequence": 1, "official_outcomes": 0},
                {
                    "id": "attempt-002",
                    "sequence": 2,
                    "outcome": "failed",
                    "official_outcomes": 1,
                },
                {
                    "id": "attempt-003",
                    "sequence": 3,
                    "status": "failed-before-runner-import",
                    "official_outcomes": 0,
                },
                {
                    "id": R3.ATTEMPT_ID,
                    "sequence": R3.SEQUENCE,
                    "outcome": outcome,
                    "official_outcomes": 1,
                },
            ],
            "case": {"id": BASE.CASE_ID, "outcome": outcome},
            "summary": {
                "process_attempts": 4,
                "incomplete_process_attempts": 2,
                "completed_process_attempts": 2,
                "official_outcomes": 2,
                "official_passes": int(outcome == "passed"),
                "official_failures": 1 + int(outcome == "failed"),
                "parent_profiles_completed": 0,
                "axeyum_outcomes": 0,
                "paired_cells": 0,
                "performance_rows": 0,
            },
            "claims": R3.ZERO_CLAIMS,
            "evidence_files": evidence,
            "evidence_manifest_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
            ),
            "credits": credits,
            "record_sha256": "",
        }
        return BASE.seal(value, R3.RESULT_SCHEMA)

    def test_direct_file_entry_help_passes_without_pythonpath(self) -> None:
        environment = {
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": "/usr/bin:/bin",
            "PYTHONSAFEPATH": "1",
        }
        completed = subprocess.run(
            ["/usr/bin/python3", str(Path(R3.__file__).resolve()), "--help"],
            cwd=BASE.ROOT,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertNotIn("PYTHONPATH", environment)
        self.assertEqual(completed.returncode, 0, completed.stderr.decode())
        self.assertIn(b"run-m0", completed.stdout)

    def test_bootstrap_precedes_repository_import_and_adds_only_root(self) -> None:
        source = Path(R3.__file__).read_text(encoding="utf-8")
        insertion = source.index("sys.path.insert(0, str(REPOSITORY_ROOT))")
        repository_import = source.index("from scripts import lean_u2_official_execution")
        self.assertLess(insertion, repository_import)
        self.assertEqual(R3.REPOSITORY_ROOT, BASE.ROOT)

    def test_r2_invocation_authority_and_prior_history_are_frozen(self) -> None:
        record = R3.validate_r2_invocation(require_git_index=True)
        self.assertEqual(record["record_sha256"], R3.R2_INVOCATION_RECORD_SHA256)
        dependency = R3.validate_failed_attempt(
            require_live_readonly=False, require_git_index=True
        )
        self.assertEqual(dependency["process_attempts"], 3)
        self.assertEqual(dependency["official_outcomes"], 1)
        self.assertEqual(dependency["incomplete_process_attempts"], 2)
        self.assertEqual(
            [row["attempt_id"] for row in dependency["attempts"]],
            ["attempt-001", "attempt-002", "attempt-003"],
        )

    def test_repository_r3_plan_and_frozen_r2_runner_are_current(self) -> None:
        self.assertEqual(R3.validate_repository_inputs(), [])

    def test_r3_spec_freezes_lane_attempt_history_and_forbidden_environment(self) -> None:
        spec = self.spec()
        with R3.r2_r3_configuration(), R2.base_r2_configuration():
            self.assertEqual(BASE.validate_spec(spec), [])
        self.assertEqual(spec["attempt_id"], R3.ATTEMPT_ID)
        self.assertEqual(spec["sequence"], R3.SEQUENCE)
        self.assertEqual(spec["resource_envelope"]["lane_id"], R3.LANE_ID)
        self.assertNotIn("LEAN_CC", spec["environment"])
        self.assertNotIn("PYTHONPATH", spec["environment"])

    def test_r3_spec_rejects_plan_history_lane_and_environment_drift(self) -> None:
        mutations = (
            lambda item: item.__setitem__("r3_plan_sha256", "0" * 64),
            lambda item: item.__setitem__("prior_attempts_sha256", "0" * 64),
            lambda item: item["resource_envelope"].__setitem__("lane_id", "wrong"),
            lambda item: item["environment"].__setitem__("PYTHONPATH", str(BASE.ROOT)),
        )
        for mutate in mutations:
            changed = copy.deepcopy(self.spec())
            mutate(changed)
            changed = BASE.seal(changed, BASE.SPEC_SCHEMA)
            with (
                self.subTest(mutate=mutate),
                R3.r2_r3_configuration(),
                R2.base_r2_configuration(),
            ):
                self.assertTrue(BASE.validate_spec(changed))

    def test_context_restores_r2_and_r1_replay(self) -> None:
        before = (R2.ATTEMPT_ID, R2.SEQUENCE, R2.LANE_ID)
        with R3.r2_r3_configuration():
            self.assertEqual(
                (R2.ATTEMPT_ID, R2.SEQUENCE, R2.LANE_ID),
                (R3.ATTEMPT_ID, R3.SEQUENCE, R3.LANE_ID),
            )
        self.assertEqual((R2.ATTEMPT_ID, R2.SEQUENCE, R2.LANE_ID), before)
        BASE.generate_result(
            root=BASE.DEFAULT_EVIDENCE_ROOT,
            implementation_revision=None,
            check=True,
        )

    def test_result_validator_retains_four_attempts_and_zero_parity(self) -> None:
        authority = self.result_authority()
        self.assertEqual(R3.validate_result_authority(authority), [])
        mutations = (
            lambda item: item["attempts"][2].__setitem__("official_outcomes", 1),
            lambda item: item["credits"].__setitem__("parity_credit", 1),
            lambda item: item["claims"].__setitem__("lean_parity_established", True),
            lambda item: item.__setitem__("claims", {}),
        )
        for mutate in mutations:
            changed = copy.deepcopy(authority)
            mutate(changed)
            changed = BASE.seal(changed, R3.RESULT_SCHEMA)
            with self.subTest(mutate=mutate):
                self.assertTrue(R3.validate_result_authority(changed))


if __name__ == "__main__":
    unittest.main()
