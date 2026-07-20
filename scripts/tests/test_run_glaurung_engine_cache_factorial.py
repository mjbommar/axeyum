#!/usr/bin/env python3

import importlib.util
import os
import pathlib
import tempfile
import unittest
from unittest import mock


SCRIPT = (
    pathlib.Path(__file__).parents[1]
    / "run-glaurung-engine-cache-factorial.py"
)
SPEC = importlib.util.spec_from_file_location("engine_cache_factorial_runner", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


class EngineCacheFactorialRunnerTests(unittest.TestCase):
    def test_six_modes_map_to_exactly_one_warm_and_cache_policy(self) -> None:
        self.assertEqual(
            RUNNER.MODE_POLICY,
            {
                "cold-off": ("off", "off"),
                "warm-off": ("adaptive", "off"),
                "cold-exact": ("off", "exact"),
                "warm-exact": ("adaptive", "exact"),
                "cold-structural": ("off", "structural"),
                "warm-structural": ("adaptive", "structural"),
            },
        )
        self.assertEqual(len(RUNNER.MODES), 6)

    def test_environment_is_sanitized_and_mode_is_authoritative(self) -> None:
        base = {
            "GLAURUNG_AXEYUM_DIRECT_DELTA": "1",
            "GLAURUNG_AXEYUM_WARM_SERIAL_SIBLING_REUSE": "1",
        }
        with mock.patch.dict(
            os.environ,
            {
                "GLAURUNG_ENGINE_CONSTRAINT_CACHE": "wrong",
                "GLAURUNG_UNREGISTERED": "leak",
                "LD_LIBRARY_PATH": "/unregistered",
                "PATH": "/bin",
            },
            clear=True,
        ):
            environment = RUNNER.sanitize_environment(
                base, "warm-structural", pathlib.Path("/clean/axeyum")
            )
        self.assertNotIn("GLAURUNG_UNREGISTERED", environment)
        self.assertNotIn("LD_LIBRARY_PATH", environment)
        self.assertEqual(environment["PATH"], "/bin")
        self.assertEqual(environment["GLAURUNG_AXEYUM_WARM_REUSE"], "adaptive")
        self.assertEqual(
            environment["GLAURUNG_ENGINE_CONSTRAINT_CACHE"], "structural"
        )
        self.assertEqual(
            environment["GLAURUNG_ENGINE_CACHE_FACTORIAL_MODE"],
            "warm-structural",
        )

    def test_registered_file_hash_is_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            artifact = root / "artifact"
            artifact.write_bytes(b"registered")
            row = {"path": "artifact", "sha256": RUNNER.sha256_file(artifact)}
            self.assertEqual(
                RUNNER.verify_file(row, root, "artifact"), artifact.resolve()
            )
            artifact.write_bytes(b"changed")
            with self.assertRaisesRegex(RUNNER.CampaignError, "SHA-256 differs"):
                RUNNER.verify_file(row, root, "artifact")


if __name__ == "__main__":
    unittest.main()
