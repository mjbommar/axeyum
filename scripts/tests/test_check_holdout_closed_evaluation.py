#!/usr/bin/env python3
"""Controls for `scripts/check-holdout-closed-evaluation.py`.

The case that matters most is `RealPopulationTests`: the gate must FAIL on the
population as it stood before the 2026-08-30 `fermat-numbers` amendment and PASS
on the population as it stands after. Today's committed population contains zero
closed-evaluation rows, so every other test here could pass against a gate that
had quietly stopped working -- which is the exact defect this repository keeps
finding in its own checkers.

Each guard below is mutation-verified to be killed by the case that names it;
the mapping is in the docstring of each test.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-holdout-closed-evaluation.py"

_spec = importlib.util.spec_from_file_location("closed_evaluation", SCRIPT)
assert _spec and _spec.loader
gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gate)


class ClassifierTests(unittest.TestCase):
    """Kills a mutation of `is_closed_evaluation`."""

    def test_the_three_spent_fermat_rows_are_closed_evaluations(self) -> None:
        for statement in ("Nat.fermatNumber 0 = 3",
                          "Nat.fermatNumber 1 = 5",
                          "Nat.fermatNumber 2 = 17"):
            self.assertTrue(gate.is_closed_evaluation(statement), statement)

    def test_a_quantified_sibling_is_not(self) -> None:
        self.assertFalse(gate.is_closed_evaluation("∀ (n : ℕ), n.fermatNumber ≠ 1"))

    def test_a_binder_free_non_equation_is_not(self) -> None:
        """`Monotone Nat.fermatNumber` has no binder and is still not decidable
        by reduction. Kills the mutation that drops the `=` requirement."""
        self.assertFalse(gate.is_closed_evaluation("Monotone Nat.fermatNumber"))

    def test_an_equation_with_free_variables_is_not(self) -> None:
        """Kills the mutation that drops the numeral-side requirement."""
        self.assertFalse(gate.is_closed_evaluation("Nat.gcd m n = Nat.gcd n m"))

    def test_an_unfamiliar_token_is_not_classified(self) -> None:
        """The classifier refuses to guess rather than guessing wrong."""
        self.assertFalse(gate.is_closed_evaluation("Nat.foo 0 ⊕ 1 = 3"))


class SelfTestTests(unittest.TestCase):
    """The gate's own fixture table must discriminate, and must say so."""

    def test_the_shipped_classifier_passes_its_fixtures(self) -> None:
        self.assertEqual(gate.self_test(), [])

    def test_a_broken_classifier_is_caught_by_the_fixtures(self) -> None:
        """Kills any mutation that makes `self_test` vacuous: with the
        classifier stubbed to a constant, the fixtures must report failures."""
        original = gate.is_closed_evaluation
        try:
            gate.is_closed_evaluation = lambda statement: False
            self.assertNotEqual(gate.self_test(), [])
            gate.is_closed_evaluation = lambda statement: True
            self.assertNotEqual(gate.self_test(), [])
        finally:
            gate.is_closed_evaluation = original

    def test_the_fixture_table_carries_both_polarities(self) -> None:
        polarities = {expected for _, expected, _ in gate.CLASSIFIER_FIXTURES}
        self.assertEqual(polarities, {True, False})


class SnakeCaseTests(unittest.TestCase):
    def test_camel_case_becomes_snake_case(self) -> None:
        self.assertEqual(gate.snake("Nat.fermatNumber"), "fermat_number")
        self.assertEqual(gate.snake("Nat.gcd"), "gcd")


class FailClosedTests(unittest.TestCase):
    def test_a_missing_manifest_is_an_error(self) -> None:
        saved = gate.NURSERY
        try:
            gate.NURSERY = pathlib.Path("/nonexistent/nursery.json")
            with self.assertRaises(gate.ClosedEvaluationError):
                gate.held_out_rows()
        finally:
            gate.NURSERY = saved

    def test_a_manifest_with_no_held_out_rows_is_an_error(self) -> None:
        """A population that has quietly become empty must not read as clean."""
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "empty.json"
            path.write_text(json.dumps(
                {"entries": [{"fact_id": "F:x", "partition": "train"}]}))
            saved = gate.NURSERY
            try:
                gate.NURSERY = path
                with self.assertRaises(gate.ClosedEvaluationError):
                    gate.held_out_rows()
            finally:
                gate.NURSERY = saved

    def test_a_missing_snapshot_is_an_error(self) -> None:
        saved = gate.SNAPSHOT
        try:
            gate.SNAPSHOT = pathlib.Path("/nonexistent/snapshot.json")
            with self.assertRaises(gate.ClosedEvaluationError):
                gate.declared_names()
        finally:
            gate.SNAPSHOT = saved


class RealPopulationTests(unittest.TestCase):
    """The discriminating case: FAIL before the amendment, PASS after.

    Without this the whole suite could pass against a gate that never looks at
    a real row, because the committed population is (deliberately) clean.
    """

    def _run_against(self, nursery: pathlib.Path, extension: pathlib.Path):
        saved = (gate.NURSERY, gate.EXTENSION)
        out, err = io.StringIO(), io.StringIO()
        try:
            gate.NURSERY, gate.EXTENSION = nursery, extension
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                code = gate.main()
        finally:
            gate.NURSERY, gate.EXTENSION = saved
        return code, out.getvalue(), err.getvalue()

    def test_the_committed_population_passes(self) -> None:
        code, out, _ = self._run_against(gate.NURSERY, gate.EXTENSION)
        self.assertEqual(code, 0, out)
        self.assertIn("verdict=PASS", out)

    def test_the_pre_amendment_population_fails_on_the_three_fermat_rows(self) -> None:
        """Reads the manifests out of git at the commit before the amendment.

        Skipped rather than failed if that commit is not reachable (a shallow
        clone, or history rewritten), because an unreachable fixture is a
        missing measurement, not a gate regression -- and the skip is loud.
        """
        commit = subprocess.run(
            ["git", "-C", str(ROOT), "rev-list", "-1",
             "--grep=amend two more held-out families", "HEAD"],
            capture_output=True, text=True, check=False).stdout.strip()
        if not commit:
            self.skipTest("the amendment commit is not in this history")
        with tempfile.TemporaryDirectory() as tmp:
            paths = {}
            for key, rel in (("v1", "artifacts/autogenesis/nursery-v1.json"),
                             ("v2", "artifacts/autogenesis/nursery-v2-extension.json")):
                blob = subprocess.run(
                    ["git", "-C", str(ROOT), "show", f"{commit}~1:{rel}"],
                    capture_output=True, text=True, check=False)
                if blob.returncode != 0:
                    self.skipTest(f"cannot read {rel} at {commit}~1")
                p = pathlib.Path(tmp) / f"{key}.json"
                p.write_text(blob.stdout)
                paths[key] = p
            code, out, err = self._run_against(paths["v1"], paths["v2"])
        self.assertEqual(code, 1, out + err)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("violations=3", out)
        for fact_id in ("F:ml430-nat-fermatnumber-zero-ca7aac67",
                        "F:ml430-nat-fermatnumber-one-b1b0798f",
                        "F:ml430-nat-fermatnumber-two-3aa3bfc4"):
            self.assertIn(fact_id, err)


if __name__ == "__main__":
    unittest.main()
