#!/usr/bin/env python3
"""Controls for `scripts/check-l0-gate-enforcement.py` (ADR-1050).

One test per guard, each written so that deleting ITS guard kills exactly it
and leaves the others green -- the property `scripts/tests/mutation_controls.py`
verifies from the `l0-gate-enforcement` suite table.

The acceptance test (`test_committed_tree_passes`) is the one that would catch
a guard rewritten into something that can never fire, which is the failure this
repository cares most about: it asserts the real committed wiring passes, so a
guard mutated to `if True:` breaks it.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts" / "check-l0-gate-enforcement.py"

_spec = importlib.util.spec_from_file_location("l0_gate_enforcement", SUBJECT)
assert _spec and _spec.loader
mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mod)

CI = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
PP = (ROOT / "hooks/pre-push").read_text(encoding="utf-8")


def tags(failures: list[str], prefix: str) -> list[str]:
    return [f for f in failures if f.startswith(prefix)]


class L0GateEnforcementTests(unittest.TestCase):
    def test_committed_tree_passes(self) -> None:
        """The real wiring must be clean, or every guard below is untrusted."""
        self.assertEqual(mod.check(CI, PP), [])

    def test_g1_missing_from_ci_is_refused(self) -> None:
        ci = CI.replace("python3 scripts/check-trust-closure.py --quiet\n", "", 1)
        self.assertNotEqual(ci, CI, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(ci, PP), "G1"))

    def test_g2_continue_on_error_is_refused(self) -> None:
        ci = CI.replace(
            "      - run: python3 scripts/check-proposition-duplication.py",
            "      - run: python3 scripts/check-proposition-duplication.py\n"
            "        continue-on-error: true", 1)
        self.assertNotEqual(ci, CI, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(ci, PP), "G2"))

    def test_g2_allows_continue_on_error_on_non_l0_steps(self) -> None:
        """ci.yml carries two DOCUMENTED lean-parity continue-on-error steps.

        The property is per-step, not per-file. A guard rewritten to reject any
        `continue-on-error` in the file would break the acceptance test; this
        pins the intent explicitly.
        """
        self.assertIn("continue-on-error: true", CI)
        self.assertEqual(tags(mod.check(CI, PP), "G2"), [])

    def test_g3_swallowed_exit_status_is_refused(self) -> None:
        ci = CI.replace(
            "- run: python3 scripts/check-settled-fact-statements.py",
            "- run: python3 scripts/check-settled-fact-statements.py || true", 1)
        self.assertNotEqual(ci, CI, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(ci, PP), "G3"))

    def test_g4_missing_from_pre_push_is_refused(self) -> None:
        pp = PP.replace(
            '  "scripts/check-holdout-closed-evaluation.py" \\\n', "", 1)
        self.assertNotEqual(pp, PP, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(CI, pp), "G4"))

    def test_g4_ignores_a_gate_named_only_in_a_comment(self) -> None:
        """A gate mentioned in prose is not wired to anything.

        The first version of this script matched the whole file, so deleting a
        gate from the loop while leaving it in the block comment above read as
        wired. Comments are stripped now; this pins that.
        """
        pp = PP.replace(
            '  "scripts/check-holdout-closed-evaluation.py" \\\n',
            "  # scripts/check-holdout-closed-evaluation.py\n", 1)
        self.assertNotEqual(pp, PP, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(CI, pp), "G4"))

    def test_g5_block_below_the_early_exit_is_refused(self) -> None:
        """The finding this whole lane exists for.

        Below the Rust/TOML early exit, a push touching only artifacts/ or
        docs/ -- exactly what these gates protect -- is gated by nothing.
        """
        pp = PP + "\npython3 scripts/check-settled-fact-statements.py\n"
        self.assertTrue(tags(mod.check(CI, pp), "G5"))

    def test_g6_missing_failure_path_is_refused(self) -> None:
        pp = PP.replace("L0 gate rejected this push", "all fine", 1)
        self.assertNotEqual(pp, PP, "fixture did not mutate -- test is vacuous")
        self.assertTrue(tags(mod.check(CI, pp), "G6"))

    def test_zero_parsed_ci_steps_is_a_failure_not_a_pass(self) -> None:
        """G1..G3 would all pass vacuously over an empty step list."""
        self.assertTrue(tags(mod.check("", PP), "VACUOUS"))

    def test_self_test_mode_is_clean(self) -> None:
        self.assertEqual(mod.self_test(), [])


if __name__ == "__main__":
    unittest.main()
