"""Focused Git and schema gates for credited full-cell admission."""

from __future__ import annotations

import copy
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

import full_admission as admission_module  # noqa: E402
from full_admission import (  # noqa: E402
    LIVE_ACCEPTANCE_RELATIVE,
    build_full_cell_admission,
    build_full_preparation_acceptance,
    validate_full_cell_admission,
    validate_full_preparation_acceptance,
)
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402


def reseal(value: dict) -> dict:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=root, text=True, stderr=subprocess.STDOUT
    ).strip()


class FullAdmissionTests(unittest.TestCase):
    def test_acceptance_rejects_commit_and_seal_drift(self) -> None:
        acceptance = build_full_preparation_acceptance(
            execution_source_commit="1" * 40,
            preparation_record_sha256="2" * 64,
            selection_record_sha256="3" * 64,
            fixture_only=True,
        )
        self.assertEqual(validate_full_preparation_acceptance(acceptance), acceptance)

        wrong_commit = copy.deepcopy(acceptance)
        wrong_commit["execution_source_commit"] = "1" * 64
        with self.assertRaisesRegex(ContractError, "commit mismatch"):
            validate_full_preparation_acceptance(reseal(wrong_commit))

        wrong_seal = copy.deepcopy(acceptance)
        wrong_seal["record_sha256"] = "0" * 64
        with self.assertRaisesRegex(ContractError, "field/schema/seal"):
            validate_full_preparation_acceptance(wrong_seal)

    def test_live_acceptance_replays_recorded_mainline_git_object(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repository = Path(tmp)
            git(repository, "init", "-b", "main")
            git(repository, "config", "user.email", "fixture@example.invalid")
            git(repository, "config", "user.name", "fixture")
            marker = repository / "source.txt"
            marker.write_text("prepared source\n", encoding="utf-8")
            git(repository, "add", "source.txt")
            git(repository, "commit", "-m", "source")
            source_commit = git(repository, "rev-parse", "HEAD")

            acceptance = build_full_preparation_acceptance(
                execution_source_commit=source_commit,
                preparation_record_sha256="1" * 64,
                selection_record_sha256="2" * 64,
            )
            acceptance_path = repository / LIVE_ACCEPTANCE_RELATIVE
            acceptance_path.parent.mkdir(parents=True)
            acceptance_path.write_bytes(canonical_bytes(acceptance))
            git(repository, "add", LIVE_ACCEPTANCE_RELATIVE.as_posix())
            git(repository, "commit", "-m", "accept preparation")
            acceptance_commit = git(repository, "rev-parse", "HEAD")
            git(
                repository,
                "update-ref",
                "refs/remotes/origin/main",
                acceptance_commit,
            )

            preparation = {
                "fixture_only": False,
                "record_sha256": "1" * 64,
                "prepared_at_ns": 100,
            }
            selection = {"record_sha256": "2" * 64}
            composition = {
                "record_sha256": "3" * 64,
                "cells": [
                    {
                        "solver_id": "axeyum",
                        "run_identity_sha256": "4" * 64,
                        "plan_sha256": "5" * 64,
                        "schedule_record_sha256": "6" * 64,
                    }
                ],
            }
            readiness = {"head_commit": source_commit}
            with (
                mock.patch.object(
                    admission_module,
                    "validate_full_preparation",
                    return_value=preparation,
                ),
                mock.patch.object(
                    admission_module,
                    "_component_records",
                    return_value=(selection, composition, readiness),
                ),
                mock.patch.object(
                    admission_module, "_prior_results", return_value=([], 0)
                ),
            ):
                admission = build_full_cell_admission(
                    repository,
                    repository_root=repository,
                    solver_id="axeyum",
                    expected_logic_counts={},
                    prior_result_roots={},
                    acceptance=acceptance,
                    acceptance_path=acceptance_path,
                    inspect_shared_root=False,
                    admitted_at_ns=101,
                )
                self.assertEqual(
                    admission["mainline_acceptance_commit"], acceptance_commit
                )
                self.assertEqual(
                    admission["mainline_acceptance_path"],
                    LIVE_ACCEPTANCE_RELATIVE.as_posix(),
                )

                marker.write_text("main advanced\n", encoding="utf-8")
                git(repository, "add", "source.txt")
                git(repository, "commit", "-m", "advance main")
                git(
                    repository,
                    "update-ref",
                    "refs/remotes/origin/main",
                    git(repository, "rev-parse", "HEAD"),
                )
                self.assertEqual(
                    validate_full_cell_admission(
                        admission,
                        preparation_root=repository,
                        repository_root=repository,
                        expected_logic_counts={},
                        prior_result_roots={},
                        inspect_shared_root=False,
                    ),
                    admission,
                )

    def test_live_acceptance_rejects_unrelated_execution_revision(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repository = Path(tmp)
            git(repository, "init", "-b", "main")
            git(repository, "config", "user.email", "fixture@example.invalid")
            git(repository, "config", "user.name", "fixture")
            acceptance = build_full_preparation_acceptance(
                execution_source_commit="f" * 40,
                preparation_record_sha256="1" * 64,
                selection_record_sha256="2" * 64,
            )
            path = repository / LIVE_ACCEPTANCE_RELATIVE
            path.parent.mkdir(parents=True)
            path.write_bytes(canonical_bytes(acceptance))
            git(repository, "add", LIVE_ACCEPTANCE_RELATIVE.as_posix())
            git(repository, "commit", "-m", "accept unrelated revision")
            git(
                repository,
                "update-ref",
                "refs/remotes/origin/main",
                git(repository, "rev-parse", "HEAD"),
            )
            with self.assertRaisesRegex(ContractError, "not an ancestor"):
                admission_module._live_acceptance(
                    repository_root=repository,
                    acceptance=acceptance,
                    acceptance_path=path,
                )


if __name__ == "__main__":
    unittest.main()
