#!/usr/bin/env python3
"""Tests for the hash-pinned external certificate replay boundary."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "scripts" / "check-external-certificate.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExternalCertificateCheckTests(unittest.TestCase):
    def make_manifest(self, directory: Path, script: str, required: str = "CERTIFIED") -> Path:
        checker_input = directory / "checker.py"
        checker_input.write_text(script, encoding="utf-8")
        manifest = {
            "schema": "axeyum.external-certificate-check.v1",
            "checker": {"path": sys.executable, "sha256": digest(Path(sys.executable))},
            "artifacts": [
                {"role": "certificate", "path": "checker.py", "sha256": digest(checker_input)}
            ],
            "argv": ["{artifact:certificate}"],
            "timeout_seconds": 2,
            "success": {"exit_codes": [0], "stdout_contains": [required]},
        }
        path = directory / "manifest.json"
        path.write_text(json.dumps(manifest), encoding="utf-8")
        return path

    def run_manifest(self, manifest: Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(RUNNER), str(manifest)],
            text=True,
            capture_output=True,
            check=False,
        )

    def test_verified_receipt_binds_checker_and_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as raw_directory:
            directory = Path(raw_directory)
            result = self.run_manifest(self.make_manifest(directory, "print('CERTIFIED')\n"))
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(result.stdout)
            self.assertEqual(receipt["observation"]["verdict"], "verified")
            self.assertEqual(receipt["artifacts"][0]["sha256"], digest(directory / "checker.py"))

    def test_artifact_mutation_is_rejected_before_execution(self) -> None:
        with tempfile.TemporaryDirectory() as raw_directory:
            directory = Path(raw_directory)
            manifest = self.make_manifest(directory, "print('CERTIFIED')\n")
            (directory / "checker.py").write_text("print('CERTIFIED MUTATED')\n", encoding="utf-8")
            result = self.run_manifest(manifest)
            self.assertEqual(result.returncode, 2)
            self.assertIn("digest mismatch", result.stderr)
            self.assertEqual(result.stdout, "")

    def test_exit_zero_without_required_finding_fails(self) -> None:
        with tempfile.TemporaryDirectory() as raw_directory:
            directory = Path(raw_directory)
            result = self.run_manifest(self.make_manifest(directory, "print('finished')\n"))
            self.assertEqual(result.returncode, 1)
            self.assertEqual(json.loads(result.stdout)["observation"]["verdict"], "failed")

    def test_timeout_is_not_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as raw_directory:
            directory = Path(raw_directory)
            manifest = self.make_manifest(directory, "import time\ntime.sleep(5)\nprint('CERTIFIED')\n")
            manifest_value = json.loads(manifest.read_text(encoding="utf-8"))
            manifest_value["timeout_seconds"] = 1
            manifest.write_text(json.dumps(manifest_value), encoding="utf-8")
            result = self.run_manifest(manifest)
            self.assertEqual(result.returncode, 3)
            self.assertEqual(json.loads(result.stdout)["observation"]["verdict"], "timeout")


if __name__ == "__main__":
    unittest.main()
