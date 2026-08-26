"""Negative controls for the generated kernel dependency projection."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("kernel_projection", ROOT / "scripts/validate-autogenesis-kernel-dependency-projection.py")
assert SPEC and SPEC.loader
KP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(KP)


class KernelProjectionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json").read_text())

    def test_current_projection_is_valid(self):
        self.assertEqual(KP.validate(self.data), [])

    def test_characterization_surface_is_in_scope(self):
        rows = {row["id"]: row for row in self.data["declarations"]}
        for theorem in (
            "Nat.Peano.categorical",
            "Nat.Peano.iter_unique",
            "Int.Characterization.categorical",
            "Int.Characterization.iso",
        ):
            self.assertEqual(rows[theorem]["declaration_kind"], "theorem")
            self.assertIn("characterization", rows[theorem]["visible_in"])

    def test_every_declaration_has_a_kernel_rendered_type(self):
        self.assertTrue(
            all(row.get("canonical_type") for row in self.data["declarations"])
        )

    def test_missing_edge_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["direct_theorem_dependency_edges"].pop()
        self.assertTrue(any("does not exactly match" in error for error in KP.validate(data)))

    def test_non_theorem_edge_is_rejected(self):
        data = copy.deepcopy(self.data)
        data["direct_theorem_dependency_edges"][0]["target"] = "Nat"
        self.assertTrue(any("not theorem -> theorem" in error for error in KP.validate(data)))


if __name__ == "__main__":
    unittest.main()
