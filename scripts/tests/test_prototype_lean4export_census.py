#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "prototype_lean4export_census.py"
FIXTURE = ROOT / "docs" / "plan" / "fixtures" / "lean4export-v4.30-axeyum-probe.ndjson"
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)
SPEC = importlib.util.spec_from_file_location("prototype_lean4export_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
CENSUS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CENSUS
SPEC.loader.exec_module(CENSUS)


class CensusTests(unittest.TestCase):
    def test_official_fixture_hash_and_inventory(self) -> None:
        result = CENSUS.census_bytes(FIXTURE.read_bytes(), label="flat")
        self.assertEqual(result["label"], "flat")
        self.assertEqual(
            result["sha256"],
            "c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280",
        )
        self.assertEqual(
            (result["names"], result["levels"], result["exprs"], result["decls"]),
            (14, 2, 43, 5),
        )
        self.assertEqual(result["blockers"], ())

    def test_official_blocker_fixture_hashes_and_inventories(self) -> None:
        cases = [
            (
                "projection",
                "lean4export-v4.30-projection.ndjson",
                "731d9a50659adadf11b2faac18f7c299211f20f85a48371a25a8c79cd4cec5fa",
                (21, 2, 61, 4),
                ("expr-projection",),
            ),
            (
                "nat-literal",
                "lean4export-v4.30-nat-literal.ndjson",
                "8cdb40da9441b77d140f1c794ac04e6dc941fee7466004bf3595ae43c6782603",
                (30, 4, 90, 5),
                ("expr-projection", "literal-nat-typing"),
            ),
            (
                "quotient",
                "lean4export-v4.30-quotient.ndjson",
                "060bb9d132fa6b7917170cd549ded5fb5703935c74ca1f7f32a3b77b6d9903c8",
                (25, 3, 87, 5),
                ("quotient-package",),
            ),
        ]
        fixture_root = ROOT / "docs" / "plan" / "fixtures"
        for label, filename, sha256, inventory, blockers in cases:
            with self.subTest(label=label):
                result = CENSUS.census_bytes((fixture_root / filename).read_bytes(), label=label)
                self.assertEqual(result["sha256"], sha256)
                self.assertEqual(
                    (result["names"], result["levels"], result["exprs"], result["decls"]),
                    inventory,
                )
                self.assertEqual(result["blockers"], blockers)


if __name__ == "__main__":
    unittest.main()
