from __future__ import annotations

import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-mathlib-full-statement-survival-atlas.py"
SPEC = importlib.util.spec_from_file_location("full_statement_survival_atlas", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def source(name: str, module: str, pretty: str, structural: str) -> dict:
    return {
        "name": name,
        "module": module,
        "level_params": [],
        "type": pretty,
        "type_repr": structural,
    }


class FullStatementSurvivalAtlasTests(unittest.TestCase):
    def test_structurally_identical(self) -> None:
        row = source("Nat.same", "M", "p", "Lean.Expr.const `Nat")
        self.assertEqual(MODULE.classify("Nat.same", row, row)["class"], "structurally-identical")

    def test_module_only_drift(self) -> None:
        old = source("Nat.moved", "Old", "p", "Lean.Expr.const `Nat")
        new = source("Nat.moved", "New", "p", "Lean.Expr.const `Nat")
        self.assertEqual(MODULE.classify("Nat.moved", old, new)["class"], "module-only-drift")

    def test_pretty_only_drift(self) -> None:
        old = source("Nat.pretty", "M", "old", "Lean.Expr.const `Nat")
        new = source("Nat.pretty", "M", "new", "Lean.Expr.const `Nat")
        self.assertEqual(MODULE.classify("Nat.pretty", old, new)["class"], "pretty-type-only-drift")

    def test_structural_drift_has_multiset_delta(self) -> None:
        old = source("Int.changed", "M", "p", "Lean.Expr.const `Nat")
        new = source("Int.changed", "M", "p", "Lean.Expr.const `Int")
        row = MODULE.classify("Int.changed", old, new)
        self.assertEqual(row["class"], "structural-type-drift")
        self.assertEqual(row["constant_multiset_delta"], {"removed": ["Nat"], "added": ["Int"]})

    def test_addition_and_removal_are_directional(self) -> None:
        row = source("Nat.edge", "M", "p", "Lean.Expr.const `Nat")
        self.assertEqual(MODULE.classify("Nat.edge", None, row)["class"], "added-by-v4.32.1")
        self.assertEqual(MODULE.classify("Nat.edge", row, None)["class"], "removed-after-v4.30.0")

    def test_structural_row_without_delta_is_rejected(self) -> None:
        row = MODULE.classify(
            "Nat.changed",
            source("Nat.changed", "M", "p", "Lean.Expr.const `Nat"),
            source("Nat.changed", "M", "p", "Lean.Expr.const `Int"),
        )
        row.pop("constant_multiset_delta")
        with self.assertRaisesRegex(MODULE.AtlasError, "constant delta boundary"):
            MODULE.validate_row_shape(row)

    def test_proof_field_in_identity_is_rejected(self) -> None:
        row = MODULE.classify(
            "Nat.same",
            source("Nat.same", "M", "p", "Lean.Expr.const `Nat"),
            source("Nat.same", "M", "p", "Lean.Expr.const `Nat"),
        )
        row["current"]["proof"] = "forbidden"
        with self.assertRaisesRegex(MODULE.AtlasError, "current identity shape"):
            MODULE.validate_row_shape(row)

    def test_unsorted_constant_delta_is_rejected(self) -> None:
        row = MODULE.classify(
            "Nat.changed",
            source("Nat.changed", "M", "p", "Lean.Expr.const `A Lean.Expr.const `B"),
            source("Nat.changed", "M", "p", "Lean.Expr.const `C Lean.Expr.const `D"),
        )
        row["constant_multiset_delta"]["added"] = ["D", "C"]
        with self.assertRaisesRegex(MODULE.AtlasError, "constant delta shape"):
            MODULE.validate_row_shape(row)


if __name__ == "__main__":
    unittest.main()
