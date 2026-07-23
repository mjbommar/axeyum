from __future__ import annotations

import copy
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2_r6_result as RESULT


ROOT = Path(__file__).resolve().parents[2]


class LeanU2OfficialExecutionM2R6ResultTests(unittest.TestCase):
    def test_committed_authority_rebuilds_exactly(self) -> None:
        committed = BASE.load_json(RESULT.RESULT)
        self.assertEqual(RESULT.validate_result_authority(committed), [])
        self.assertEqual(committed, RESULT.build_result_authority())
        self.assertEqual(committed["summary"]["official_outcomes"], 64)
        self.assertEqual(committed["summary"]["local_physical_shards_completed"], 1)
        self.assertFalse(committed["claims"]["lean_complete_parity"])

    def test_resealed_credit_mutation_rejects(self) -> None:
        data = copy.deepcopy(BASE.load_json(RESULT.RESULT))
        data["credits"]["parity_credit"] = 1
        data["record_sha256"] = ""
        data = BASE.seal(data, RESULT.SCHEMA)
        self.assertIn("field drift", RESULT.validate_result_authority(data)[0])

    def test_portable_validation_accepts_normal_git_modes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r6-result-mode-") as temp:
            root = Path(temp) / "evidence"
            shutil.copytree(RESULT.EVIDENCE_ROOT, root)
            for path in root.rglob("*"):
                if path.is_file():
                    path.chmod(0o644)
            evidence = RESULT.validate_evidence_portable(root)
        self.assertEqual(
            evidence["completion"]["record_sha256"],
            "1f0b9af8997d9cced7bbb141e979ecd169b882b3df57ae02b0cb5f34ff0f3b67",
        )

    def test_cli_check_is_read_only(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                str(Path(RESULT.__file__).resolve()),
                "result",
                "--check",
            ],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"official_outcomes=64|passes=64|local_shards=1", result.stdout)


if __name__ == "__main__":
    unittest.main()
