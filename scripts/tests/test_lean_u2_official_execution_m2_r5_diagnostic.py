from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution_m2_r5_diagnostic as DIAGNOSTIC


ROOT = Path(__file__).resolve().parents[2]


class LeanU2OfficialExecutionM2R5DiagnosticTests(unittest.TestCase):
    def test_offline_contract_is_zero_credit_and_process_free(self) -> None:
        summary = DIAGNOSTIC.validate_offline_contract()
        self.assertIn(
            summary["state"],
            (
                "incomplete-selected-attempt",
                "complete-invalid-selected-attempt-diagnostic",
            ),
        )
        self.assertTrue(summary["selected_attempt_consumed"])
        self.assertEqual(summary["diagnostic_junit_rows"], 64)
        self.assertEqual(summary["official_outcomes"], 0)
        self.assertEqual(summary["parity_credit"], 0)

    def test_raw_validation_is_portable_across_git_checkout_modes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r5-diagnostic-mode-") as temp:
            root = Path(temp) / "evidence"
            shutil.copytree(DIAGNOSTIC.EVIDENCE_ROOT, root)
            diagnostic = root / "diagnostic"
            if diagnostic.exists():
                shutil.rmtree(diagnostic)
            for path in root.rglob("*"):
                if path.is_file():
                    path.chmod(0o644)
            raw = DIAGNOSTIC.validate_raw(root)
            self.assertEqual(len(raw["inventory"]), DIAGNOSTIC.RAW_FILES)
            self.assertEqual(raw["junit"]["summary"]["official_passes"], 64)

    def test_append_refuses_any_existing_diagnostic_namespace(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-r5-diagnostic-conflict-") as temp:
            root = Path(temp)
            (root / "diagnostic").mkdir()
            with self.assertRaisesRegex(
                DIAGNOSTIC.R5DiagnosticError, "namespace already exists"
            ):
                DIAGNOSTIC.append(root)

    def test_cli_offline_check_does_not_require_private_generated_tree(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                str(Path(DIAGNOSTIC.__file__).resolve()),
                "offline-check",
            ],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"processes=0|outcomes=0|parity=0", result.stdout)


if __name__ == "__main__":
    unittest.main()
