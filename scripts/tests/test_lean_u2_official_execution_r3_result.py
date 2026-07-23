from __future__ import annotations

import copy
import subprocess
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_r3 as R3
from scripts import lean_u2_official_execution_r3_result as RESULT


class LeanU2OfficialExecutionR3ResultTests(unittest.TestCase):
    def authority(self) -> dict:
        return RESULT.build_result_authority(R3.DEFAULT_EVIDENCE_ROOT)

    def test_frozen_pass_evidence_and_old_execution_sources_validate(self) -> None:
        completion, evidence = RESULT.validate_frozen_inputs(R3.DEFAULT_EVIDENCE_ROOT)
        self.assertEqual(completion["projection"]["case_outcome"], "passed")
        self.assertEqual(len(evidence), RESULT.EVIDENCE_FILE_COUNT)
        self.assertEqual(sum(row["bytes"] for row in evidence), RESULT.EVIDENCE_BYTES)

    def test_adapter_has_no_execution_command_and_direct_help_passes(self) -> None:
        environment = {
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": "/usr/bin:/bin",
            "PYTHONSAFEPATH": "1",
        }
        completed = subprocess.run(
            ["/usr/bin/python3", str(Path(RESULT.__file__).resolve()), "--help"],
            cwd=BASE.ROOT,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr.decode())
        self.assertNotIn(b"run-m0", completed.stdout)
        self.assertIn(b"validate", completed.stdout)
        self.assertIn(b"result", completed.stdout)

    def test_amended_authority_accepts_only_two_bounded_positive_claims(self) -> None:
        authority = self.authority()
        self.assertEqual(RESULT.validate_result_authority(authority), [])
        self.assertEqual(authority["claims"], RESULT.RESULT_CLAIMS)
        self.assertTrue(authority["claims"]["official_lean_case_observed"])
        self.assertTrue(authority["claims"]["local_shard_complete"])
        self.assertFalse(authority["claims"]["lean_parity_established"])
        self.assertTrue(R3.validate_result_authority(copy.deepcopy(authority)))

    def test_amended_authority_rejects_attempt_claim_credit_and_evidence_drift(self) -> None:
        authority = self.authority()
        mutations = (
            lambda item: item["attempts"][2].__setitem__("official_outcomes", 1),
            lambda item: item["claims"].__setitem__("local_shard_complete", False),
            lambda item: item["claims"].__setitem__("lean_parity_established", True),
            lambda item: item["credits"].__setitem__("parity_credit", 1),
            lambda item: item.__setitem__("evidence_manifest_sha256", "0" * 64),
        )
        for mutate in mutations:
            changed = copy.deepcopy(authority)
            mutate(changed)
            changed = BASE.seal(changed, RESULT.RESULT_SCHEMA)
            with self.subTest(mutate=mutate):
                self.assertTrue(RESULT.validate_result_authority(changed))


if __name__ == "__main__":
    unittest.main()
