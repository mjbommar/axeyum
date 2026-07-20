#!/usr/bin/env python3
"""Fail-closed tests for the ADR-0295 fixture validator."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts/validate-glaurung-llvm-direct-call-fixture.py"
SPEC = importlib.util.spec_from_file_location("direct_call_fixture", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
MANIFEST = REPO / "docs/consumer-track/verify/glaurung-llvm-direct-call-v1.json"


class FixtureValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))

    def validate_mutation(self, mutation) -> None:
        value = json.loads(json.dumps(self.manifest))
        mutation(value)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "manifest.json"
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaises(MODULE.ValidationError):
                MODULE.load_and_validate(path, REPO)

    def test_registered_manifest_passes(self) -> None:
        report = MODULE.load_and_validate(MANIFEST, REPO)
        self.assertEqual(report["schema"], MODULE.SCHEMA)

    def test_hash_and_function_inventory_mutations_fail(self) -> None:
        self.validate_mutation(
            lambda value: value["fixture"]["module"].__setitem__("sha256", "0" * 64)
        )
        self.validate_mutation(
            lambda value: value["fixture"]["functions"].pop()
        )
        self.validate_mutation(
            lambda value: value["fixture"]["functions"][0].__setitem__("name", "missing")
        )

    def test_compile_tool_and_path_mutations_fail(self) -> None:
        self.validate_mutation(lambda value: value["compile"]["args"].append("-O2"))
        self.validate_mutation(
            lambda value: value["toolchain"]["clang"].__setitem__("command", "clang")
        )
        self.validate_mutation(
            lambda value: value["fixture"]["source"].__setitem__("path", "../pac.c")
        )


if __name__ == "__main__":
    unittest.main()
