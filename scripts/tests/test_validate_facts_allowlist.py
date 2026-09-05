#!/usr/bin/env python3
"""Controls for `validate-facts.py`'s kernel-theorem name allowlist.

WHY THIS FILE EXISTS, AND WHY IT IMPORTS THE REAL MODULE. The two test files
this replaces (`test-allowlist-fix.py`, `mutation-verify-guards.py`) defined
their OWN copies of `KERNEL_THEOREM_RE` and `LOGIC_UNDOTTED` and asserted
against those. They imported nothing from `validate-facts.py`, so they could
not fail when it changed -- measured 2026-08-27 by deleting `Or` from the real
regex in a scratch copy: the validator then rejects `Or.resolve_right`, and the
test still exited 0 and reported "15/15 guards verified".

That is the checker-that-cannot-fail defect this repository audits for, in a
test written to prove an allowlist correct. A test that restates its subject is
testing the restatement.

`validate-facts.py` has a hyphen, so it cannot be imported by name; it is
loaded from its path below. Every assertion here goes through the loaded
module's own `kernel_theorem_is_valid`.
"""

import importlib.util
import unittest
from pathlib import Path

_SRC = Path(__file__).resolve().parents[1] / "validate-facts.py"
_spec = importlib.util.spec_from_file_location("validate_facts_under_test", _SRC)
VF = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(VF)


class AllowlistTests(unittest.TestCase):
    """Names the six-fact quarantine of 2026-08-27 turned on."""

    def test_dotted_names_from_the_quarantine_are_accepted(self):
        for name in ("Or.resolve_right", "Eq.symm"):
            self.assertTrue(
                VF.kernel_theorem_is_valid(name),
                f"{name} is a real kernel declaration and must validate",
            )

    def test_undotted_logic_names_from_the_quarantine_are_accepted(self):
        for name in (
            "not_not_imp",
            "not_not_not_intro",
            "demorgan_or_not_and",
            "congrFun'",
        ):
            self.assertTrue(
                VF.kernel_theorem_is_valid(name),
                f"{name} is a real undotted logic-prelude declaration",
            )

    def test_established_namespaces_still_accepted(self):
        # Positive controls: if these ever fail the harness is misloaded, not
        # the allowlist. A negative result from a misaimed tool is
        # indistinguishable from a real one.
        for name in ("Nat.add_comm", "CReal.integral_abs_le", "Rat.sub_mul"):
            self.assertTrue(VF.kernel_theorem_is_valid(name), name)

    def test_the_geo_namespace_is_accepted(self):
        # ADR-1635 added `Geo` to the dotted allowlist. Both a theorem and a
        # DEFINITION are named through this field (the ledger's
        # `formal.kernel_theorem` is the declaration a fact is about, whatever
        # its kind), so both shapes are pinned.
        for name in ("Geo.Incidence.distinct_lines_meet_once", "Geo.qplane"):
            self.assertTrue(VF.kernel_theorem_is_valid(name), name)

    def test_a_geo_lookalike_namespace_is_still_rejected(self):
        # The negative half of the widening: adding `Geo` must not make every
        # namespace starting with those letters valid.
        self.assertFalse(VF.kernel_theorem_is_valid("Geometry.qplane"))
        self.assertFalse(VF.kernel_theorem_is_valid("Geo"))

    def test_a_typo_in_a_dotted_name_is_still_rejected(self):
        # The whole point of requiring a namespace: catch a fact naming a
        # non-theorem. Widening to accept ANY bare identifier would have
        # destroyed this, which is why bare names are gated on an explicit set.
        self.assertFalse(VF.kernel_theorem_is_valid("Nonsense.no_such_thing"))
        self.assertFalse(VF.kernel_theorem_is_valid("Nat"))

    def test_an_arbitrary_bare_identifier_is_rejected(self):
        # `LOGIC_UNDOTTED` membership, not "looks like an identifier".
        self.assertFalse(VF.kernel_theorem_is_valid("not_not_imp_TYPO"))
        self.assertFalse(VF.kernel_theorem_is_valid("arbitrary_bare_name"))

    def test_str_is_not_in_the_allowlist(self):
        # `Str` matched zero kernel declarations and was removed; it is the
        # original instance of "an allowlist is only tested by the names
        # someone tries".
        self.assertFalse(VF.kernel_theorem_is_valid("Str.append"))


if __name__ == "__main__":
    unittest.main()
