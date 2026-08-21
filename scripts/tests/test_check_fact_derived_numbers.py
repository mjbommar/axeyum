"""Controls for `check-fact-derived-numbers.py`.

The script passes on the committed ledger, which on its own proves nothing --
that is the exact failure mode it exists to prevent. So every guard is driven to
FAIL here, from a fixture that trips **that guard and no other**, which is what
makes `scripts/tests/mutation_controls.py fact-derived-numbers` meaningful: each
deletion there must kill exactly one of these.

The disjointness is not accidental. CLAUDE.md records six of seven guards in one
suite being removable with everything still green, because all six rejected
through one shared check. Here the classifier assigns each anchored slot exactly
one kind, and each test uses a fixture of a different kind.
"""

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_fact_derived_numbers", ROOT / "scripts" / "check-fact-derived-numbers.py"
)
assert SPEC and SPEC.loader
DN = importlib.util.module_from_spec(SPEC)
# Registered before exec: `@dataclass` resolves `cls.__module__` through
# `sys.modules`, and a spec-loaded module that is not there raises on 3.14.
sys.modules["check_fact_derived_numbers"] = DN
SPEC.loader.exec_module(DN)

# Generous by default so a fixture built for one guard cannot trip the ratchets;
# the two ratchet tests pass their own values.
LOOSE = {"floor": 0, "ceiling": 99}


def fact(fid: str, footprint: list[str], evidence: list[dict]) -> dict:
    return {"id": fid, "axiom_footprint": footprint, "evidence": evidence}


def anchored(supports: str, notes: str = "", command: str = "") -> dict:
    return {"supports": supports, "notes": notes, "checker_command": command}


REAL_26 = [f"Real.law_{i}" for i in range(26)]


def check(facts: list[dict], **kw) -> list[str]:
    return DN.evaluate(DN.read(facts), **{**LOOSE, **kw})


class TheReadingIsStructuralNotLexical(unittest.TestCase):
    """A number is bound to the footprint by WHERE it sits, not by what it says."""

    def test_only_a_footprint_anchored_supports_slot_is_read(self) -> None:
        # "the three Peano axioms" and "all seven dependencies" are real prose in
        # this ledger and mean nothing about any footprint. The anchor is what
        # keeps them out; without it a naive `N axioms` regex is 43% wrong.
        r = DN.read([
            fact("F:peano", [], [anchored("The construction satisfies three axioms.")]),
        ])
        self.assertEqual(r.anchored_slots, 0)
        self.assertEqual(r.claims, [])

    def test_route_assumptions_are_not_kernel_declarations(self) -> None:
        footprint = [
            "lean4export-3.1.0-stream-faithfulness",
            "axeyum-lean-import-wire-translation",
            "Classical.choice",
        ]
        self.assertEqual(DN.declaration_count(footprint), 1)

    def test_a_qualified_count_in_notes_is_a_subset_and_is_not_read(self) -> None:
        # "4 variable axioms" is part of a decomposition, not the total. Reading
        # it as the total is how a checker starts inventing disagreements.
        r = DN.read([
            fact("F:x", REAL_26, [anchored(
                "axiom_footprint: the 26 axioms the module rests on.",
                "26 axioms: 17 prelude, 4 variable axioms, 5 hypothesis axioms.",
            )]),
        ])
        notes = [c for c in r.claims if c.where.endswith(".notes")]
        self.assertEqual([c.asserted for c in notes], [26])

    def test_two_cardinals_are_ambiguous_rather_than_guessed(self) -> None:
        r = DN.read([
            fact("F:em", ["Classical.choice"], [anchored(
                "axiom_footprint: reaches six trusted declarations here, three in Lean's"
            )]),
        ])
        self.assertEqual([c.kind for c in r.claims], ["ambiguous"])


class EachGuardCanFailOnItsOwn(unittest.TestCase):
    def test_guard_empty_literal(self) -> None:
        """`axiom_footprint: []` beside a non-empty array -- the headline claim."""
        f = [fact("F:a", ["Real"], [anchored("axiom_footprint: [] -- nothing trusted")])]
        self.assertTrue(any("`axiom_footprint: []`" in m for m in check(f)), check(f))

    def test_guard_no_axiom_prose(self) -> None:
        """"reaches no Lean axiom" while the footprint names one."""
        f = [fact("F:b", ["lean4export-3.1.0-stream-faithfulness", "Classical.choice"],
                  [anchored("axiom_footprint: the imported proof term reaches no Lean "
                            "axiom, opaque or quotient declaration")])]
        self.assertTrue(any("no axiom is reached" in m for m in check(f)), check(f))

    def test_guard_supports_count(self) -> None:
        """The instance this script was built for: prose 30, footprint 26."""
        f = [fact("F:c", REAL_26,
                  [anchored("axiom_footprint: the 30 axioms the kernel module "
                            "actually rests on.")])]
        msgs = check(f)
        self.assertTrue(any("supports: prose asserts 30" in m for m in msgs), msgs)

    def test_guard_notes_count(self) -> None:
        """The same staleness one field over, where `supports` carries no number."""
        f = [fact("F:d", REAL_26,
                  [anchored("axiom_footprint: the axioms the kernel module rests on.",
                            "The rendered module declares 30 axioms: 21 prelude.")])]
        msgs = check(f)
        self.assertTrue(any("notes: notes assert 30" in m for m in msgs), msgs)

    def test_guard_expect_axioms_flag(self) -> None:
        """A number in the COMMAND, derived from the array. No prose involved."""
        f = [fact("F:e", REAL_26, [{"supports": "The five rows are unsatisfiable.",
                                    "checker_command": "cargo run -- --expect-axioms 30"}])]
        msgs = check(f)
        self.assertTrue(any("--expect-axioms 30" in m for m in msgs), msgs)

    def test_guard_unchecked_ceiling(self) -> None:
        """Silence is the failure this script is about, so it is pinned too."""
        f = [fact(f"F:u{i}", [], [anchored("axiom_footprint: the trusted surface.")])
             for i in range(2)]
        msgs = check(f, ceiling=1)
        self.assertTrue(any("could not be bound" in m for m in msgs), msgs)

    def test_guard_anchored_slot_floor(self) -> None:
        """A reader that stops finding slots must not report a healthy zero."""
        msgs = check([], floor=1)
        self.assertTrue(any("floor is 1" in m for m in msgs), msgs)


class TheCommittedLedgerPasses(unittest.TestCase):
    """Last, and worth the least: green here proves nothing on its own."""

    def test_the_real_ledger_has_no_disagreement(self) -> None:
        facts = DN.load()
        reading = DN.read(facts)
        self.assertGreaterEqual(reading.anchored_slots, DN.MIN_ANCHORED_SLOTS)
        self.assertEqual(DN.evaluate(reading), [])

    def test_the_schedule_fact_is_actually_covered(self) -> None:
        """The fact that motivated this must be BOUND, not merely not-failing --
        an empty result from a tool never pointed at your subject is
        indistinguishable from a strong negative one."""
        reading = DN.read(DN.load())
        mine = [c for c in reading.claims
                if c.fact == "F:schedule-critical-chain-infeasible"]
        kinds = {c.where: (c.kind, c.asserted) for c in mine}
        self.assertEqual(kinds["evidence[1].supports"], ("count", 26))
        self.assertEqual(kinds["evidence[1].notes"], ("count", 26))
        self.assertEqual(kinds["evidence[0].checker_command"], ("expect-axioms", 26))


if __name__ == "__main__":
    unittest.main()
