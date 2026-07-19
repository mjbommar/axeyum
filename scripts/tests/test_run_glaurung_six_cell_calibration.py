#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import os
import pathlib
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = pathlib.Path(__file__).parents[1] / "run-glaurung-six-cell-calibration.py"
SPEC = importlib.util.spec_from_file_location("six_cell_calibration_runner", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = runner
SPEC.loader.exec_module(runner)


class SixCellCalibrationRunnerTests(unittest.TestCase):
    def test_registered_plan_contains_every_tier_and_repetition_in_order(self) -> None:
        planned = runner.planned_runs()

        self.assertEqual(len(planned), 42)
        self.assertEqual(
            planned[0],
            {
                "tier": 0,
                "repetition": 1,
                "z3_rlimit": 3,
                "axeyum_progress_checks": 1,
                "bitwuzla_termination_polls": 1,
            },
        )
        self.assertEqual(planned[-1]["tier"], 13)
        self.assertEqual(planned[-1]["repetition"], 3)
        self.assertEqual(planned[-1]["z3_rlimit"], 10_000_000)
        self.assertEqual(planned[-1]["axeyum_progress_checks"], 8_192)
        self.assertEqual(planned[-1]["bitwuzla_termination_polls"], 8_192)

    def test_environment_is_sanitized_and_names_each_backend_limit(self) -> None:
        with tempfile.TemporaryDirectory() as directory, mock.patch.dict(
            os.environ,
            {
                "PATH": "/usr/bin",
                "GLAURUNG_STALE": "1",
                "IOCTLANCE_STALE": "1",
                "BITWUZLA_STALE": "1",
                "LD_LIBRARY_PATH": "/stale",
            },
            clear=True,
        ):
            environment = runner.sanitize_environment(
                pathlib.Path(directory), runner.planned_runs()[2]
            )

        self.assertEqual(environment["PATH"], "/usr/bin")
        self.assertNotIn("GLAURUNG_STALE", environment)
        self.assertNotIn("IOCTLANCE_STALE", environment)
        self.assertNotIn("BITWUZLA_STALE", environment)
        self.assertNotIn("LD_LIBRARY_PATH", environment)
        self.assertEqual(environment["GLAURUNG_Z3_RLIMIT"], "3")
        self.assertEqual(environment["GLAURUNG_AXEYUM_PROGRESS_CHECK_LIMIT"], "1")
        self.assertEqual(
            environment["GLAURUNG_BITWUZLA_TERMINATION_POLL_LIMIT"], "1"
        )
        self.assertEqual(environment["IOCTLANCE_ALL"], "1")
        self.assertEqual(environment["IOCTLANCE_MAX_ANALYZED_FUNCTIONS"], "20")

    def test_preflight_rejects_a_dirty_or_wrong_glaurung_source(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            executable = root / "ioctlance"
            executable.write_bytes(b"binary")
            output = root / "output"
            output.mkdir()
            driver = root / "tcpip.sys"
            driver.write_bytes(b"driver")
            with mock.patch.object(
                runner,
                "command_output",
                side_effect=["wrong-revision", ""],
            ), mock.patch.object(runner, "DRIVER_PATH", driver), mock.patch.object(
                runner, "EXECUTABLE_SHA256", runner.sha256_file(executable)
            ), mock.patch.object(
                runner, "DRIVER_SHA256", runner.sha256_file(driver)
            ):
                with self.assertRaisesRegex(runner.CampaignError, "revision"):
                    runner.preflight(root, executable, output)

    def test_resolved_dynamic_libraries_hashes_only_absolute_ldd_targets(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            library = root / "libsolver.so"
            loader = root / "ld-linux.so"
            library.write_bytes(b"solver")
            loader.write_bytes(b"loader")
            linkage = f"""
linux-vdso.so.1 (0x0000)
libsolver.so => {library} (0x0001)
{loader} (0x0002)
"""

            resolved = runner.resolved_dynamic_libraries(linkage)

            self.assertEqual(
                resolved,
                {
                    str(loader): runner.sha256_file(loader),
                    str(library): runner.sha256_file(library),
                },
            )


if __name__ == "__main__":
    unittest.main()
