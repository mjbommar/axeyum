#!/usr/bin/env python3
"""Controls for `scripts/check-semantic-control-fixtures.py`.

The subject is a gate whose entire purpose is to refuse checks that cannot
fail, so the way it fails is by being agreeable.  Each case below feeds it a
result set that MUST be refused, and each is aimed at exactly one guard, so
deleting that guard kills exactly this test and no other.  Registered in
`scripts/tests/mutation_controls.py` under `semantic-control-fixtures`; run it
rather than mutating by hand (Python's bytecode cache makes hand loops report
the previous mutant's result).

`test_the_real_pack_passes` is the positive control that stops the whole file
from being a set of negatives against a subject that refuses everything.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location(
    "check_semantic_control_fixtures",
    ROOT / "scripts" / "check-semantic-control-fixtures.py",
)
mod = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(mod)


def result(**over) -> dict:
    """A fixture result that every guard accepts, so a test changes ONE thing."""
    base = {
        "id": "fx",
        "family": "f",
        "expect": "valid",
        "fact_ids": [],
        "executed": 10,
        "discriminating": 5,
        "counterexamples": 0,
        "first_counterexample": "",
        "note": "",
        "mutations": [],
        "killed": 1,
        "also_true": 0,
        "survived": 0,
        "seconds": 0.0,
    }
    base.update(over)
    return base


def numeric(**over) -> dict:
    base = {"script": "s.py", "exit": 0, "negative_controls": 3,
            "stdout_lines": 1, "seconds": 0.0}
    base.update(over)
    return base


class ZeroExecutedTests(unittest.TestCase):
    """Zero executed cases is always failure -- the repository's signature defect."""

    def test_a_fixture_that_executed_nothing_is_refused(self):
        # A SECOND fixture with a nonzero count, deliberately: it keeps the
        # pack total nonzero so only the per-fixture clause can fire here.
        # Without it the total clause covers for a deleted per-fixture clause
        # and the mutation survives.
        bad = mod.guard_zero_executed([result(executed=0), result(id="ok", executed=10)])
        self.assertTrue(bad, "a fixture executing 0 cases was accepted")

    def test_a_pack_whose_total_is_zero_is_refused(self):
        bad = mod.guard_zero_executed([result(executed=0)])
        self.assertTrue(
            any("whole pack executed 0" in b for b in bad),
            f"the pack-total clause did not fire: {bad}",
        )

    def test_an_empty_pack_is_refused(self):
        bad = mod.guard_zero_executed([])
        self.assertTrue(bad, "a pack with no fixtures at all was accepted")


class FalseFixtureTests(unittest.TestCase):
    def test_a_false_statement_with_no_counterexample_is_refused(self):
        bad = mod.guard_false_rejected([result(expect="false", counterexamples=0)])
        self.assertTrue(bad, "a known-FALSE fixture that refuted nothing was accepted")

    def test_a_false_statement_with_a_counterexample_is_accepted(self):
        self.assertEqual(
            mod.guard_false_rejected([result(expect="false", counterexamples=3)]), []
        )


class ValidFixtureTests(unittest.TestCase):
    def test_a_valid_control_that_found_a_counterexample_is_refused(self):
        bad = mod.guard_valid_accepted([result(expect="valid", counterexamples=1)])
        self.assertTrue(bad, "a known-VALID control that failed was accepted")

    def test_a_valid_control_that_discriminates_nothing_is_refused(self):
        bad = mod.guard_valid_discriminates([result(expect="valid", discriminating=0)])
        self.assertTrue(bad, "a vacuous VALID control was accepted")

    def test_a_valid_control_with_no_killed_mutation_is_refused(self):
        bad = mod.guard_valid_load_bearing([result(expect="valid", killed=0)])
        self.assertTrue(bad, "a control with nothing demonstrating it can fail was accepted")


class VacuousFixtureTests(unittest.TestCase):
    def test_a_vacuous_fixture_that_actually_discriminates_is_refused(self):
        bad = mod.guard_vacuous_is_vacuous(
            [result(expect="vacuous", discriminating=4, counterexamples=0)]
        )
        self.assertTrue(
            any("not vacuous" in b for b in bad),
            f"a fixture pinned vacuous that discriminates was accepted: {bad}",
        )

    def test_a_vacuous_fixture_that_is_actually_false_is_refused(self):
        bad = mod.guard_vacuous_is_vacuous(
            [result(expect="vacuous", discriminating=0, counterexamples=2)]
        )
        self.assertTrue(
            any("FALSE" in b for b in bad),
            f"a fixture pinned vacuous whose statement is false was accepted: {bad}",
        )


class NumericsTests(unittest.TestCase):
    def test_a_failing_numerics_script_is_refused(self):
        bad = mod.guard_numerics([numeric(exit=1)])
        self.assertTrue(
            any("exit 1" in b for b in bad), f"a failing numerics script passed: {bad}"
        )

    def test_a_numerics_script_with_no_negative_control_is_refused(self):
        bad = mod.guard_numerics([numeric(negative_controls=0)])
        self.assertTrue(
            any("not load-bearing" in b for b in bad),
            f"a numerics script with no negative control passed: {bad}",
        )

    def test_the_negative_control_detector_matches_both_spellings(self):
        """The first version of this pattern matched only the literal
        `NEGATIVE CONTROL` and reported two in-tree scripts as having none,
        while each carries several spelled `GENUINELY FAILS`."""
        self.assertTrue(mod.NEG_CONTROL.search("    # NEGATIVE CONTROL: ..."))
        self.assertTrue(mod.NEG_CONTROL.search('"5N. ... GENUINELY FAILS at ..."'))
        self.assertTrue(mod.NEG_CONTROL.search("a negative control that must fail"))
        self.assertFalse(mod.NEG_CONTROL.search("ok  everything held"))


class HoldoutTests(unittest.TestCase):
    def test_a_fixture_naming_a_held_out_fact_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            nursery = pathlib.Path(d) / "nursery.json"
            nursery.write_text(
                json.dumps(
                    {"entries": [{"fact_id": "F:secret", "partition": "held-out"},
                                 {"fact_id": "F:open", "partition": "train"}]}
                )
            )
            old = mod.NURSERY
            mod.NURSERY = nursery
            try:
                bad = mod.guard_no_holdout([result(fact_ids=["F:secret"])])
                ok = mod.guard_no_holdout([result(fact_ids=["F:open"])])
            finally:
                mod.NURSERY = old
        self.assertTrue(bad, "a fixture aimed at a HELD-OUT fact was accepted")
        self.assertEqual(ok, [], "a fixture aimed at a train fact was refused")


class FactIdTests(unittest.TestCase):
    def _with_facts(self, files: dict[str, dict], results):
        with tempfile.TemporaryDirectory() as d:
            facts = pathlib.Path(d)
            for name, body in files.items():
                (facts / name).write_text(json.dumps(body))
            old = mod.FACTS
            mod.FACTS = facts
            try:
                return mod.guard_fact_ids_exist(results)
            finally:
                mod.FACTS = old

    def test_a_fixture_naming_a_nonexistent_fact_is_refused(self):
        bad = self._with_facts({}, [result(fact_ids=["F:ghost"])])
        self.assertTrue(
            any("does not exist" in b for b in bad),
            f"a fixture controlling a fact that does not exist was accepted: {bad}",
        )

    def test_a_fixture_naming_an_unproved_fact_is_refused(self):
        bad = self._with_facts(
            {"F-open.json": {"epistemic_status": "open"}},
            [result(fact_ids=["F:open"])],
        )
        self.assertTrue(
            any("whose status is" in b for b in bad),
            f"a fixture controlling an OPEN fact was accepted: {bad}",
        )

    def test_a_fixture_naming_a_proved_fact_is_accepted(self):
        self.assertEqual(
            self._with_facts(
                {"F-good.json": {"epistemic_status": "proved"}},
                [result(fact_ids=["F:good"])],
            ),
            [],
        )


class PinTests(unittest.TestCase):
    def test_a_changed_executed_count_is_drift(self):
        pin = {"fixtures": [{"id": "fx", "expect": "valid", "executed": 999,
                             "discriminating": 5, "counterexamples": 0, "killed": 1}]}
        bad = mod.guard_pin_drift([result()], pin)
        self.assertTrue(bad, "a fixture whose executed count moved was accepted")

    def test_an_unchanged_run_is_not_drift(self):
        pin = {"fixtures": [{"id": "fx", "expect": "valid", "executed": 10,
                             "discriminating": 5, "counterexamples": 0, "killed": 1}]}
        self.assertEqual(mod.guard_pin_drift([result()], pin), [])

    def test_a_deleted_fixture_is_refused(self):
        pin = {"fixtures": [{"id": "fx"}, {"id": "gone"}]}
        bad = mod.guard_pin_coverage([result(id="fx")], pin)
        self.assertTrue(
            any("did not run" in b for b in bad),
            f"deleting a pinned fixture was accepted: {bad}",
        )

    def test_an_unpinned_fixture_is_refused(self):
        pin = {"fixtures": [{"id": "fx"}]}
        bad = mod.guard_pin_coverage([result(id="fx"), result(id="new")], pin)
        self.assertTrue(
            any("not pinned" in b for b in bad),
            f"an unpinned fixture was accepted: {bad}",
        )


class ClassificationTests(unittest.TestCase):
    """A mutation that is not falsified is a REVIEW result, never a failure.

    The roadmap is explicit, and a gate that reds on a true mutation is a gate
    somebody turns off.  This is the one behaviour where the correct outcome is
    to keep going.
    """

    def test_an_unfalsified_mutation_declared_also_true_is_classified_not_failed(self):
        fx = mod.Fixture(
            id="fx",
            family="f",
            expect="valid",
            provenance="control",
            run=lambda: mod.Outcome(4, 2, []),
            mutations=[
                mod.Mutation("kills", "relation", lambda: mod.Outcome(4, 4, ["ce"])),
                mod.Mutation(
                    "true-too", "relation", lambda: mod.Outcome(4, 4, []), also_true=True
                ),
            ],
        )
        r = mod.run_fixture(fx)
        statuses = {m["id"]: m["status"] for m in r["mutations"]}
        self.assertEqual(statuses["true-too"], "also-true")
        self.assertEqual(statuses["kills"], "killed")
        self.assertEqual(r["also_true"], 1)
        self.assertEqual(r["survived"], 0)
        # and it must not make the gate fail
        self.assertEqual(mod.guard_valid_load_bearing([r]), [])

    def test_an_undeclared_unfalsified_mutation_is_reported_as_survived(self):
        fx = mod.Fixture(
            id="fx",
            family="f",
            expect="valid",
            provenance="control",
            run=lambda: mod.Outcome(4, 2, []),
            mutations=[mod.Mutation("quiet", "relation", lambda: mod.Outcome(4, 4, []))],
        )
        r = mod.run_fixture(fx)
        self.assertEqual(r["mutations"][0]["status"], "survived")
        self.assertEqual(r["also_true"], 0)


class CensusTests(unittest.TestCase):
    def test_a_semantic_kind_over_an_axiom_footprint_does_not_become_load_bearing(self):
        """The `kind` inflation, behaviourally.

        S0 measured 1,901 evidence rows declaring `exhaustive-enumeration` or
        `instance-pin` while their `supports` records an axiom footprint --
        reading `kind` at face value turns 91 into 1,992.  This is a fact of
        exactly that shape, and it must contribute NOTHING: it cites no
        numerics script and no fixture names it.

        The earlier version of this test scanned the source for the string
        `"kind"` and failed on `run_fixture`'s MUTATION kind, an unrelated
        field -- a crude classifier flagging a whole shape, which is not a
        measurement.
        """
        script = mod.NUMERICS_SCRIPTS[0][0]
        inflated = {
            "id": "F:looks-semantic",
            "epistemic_status": "proved",
            "evidence": [
                {
                    "kind": "exhaustive-enumeration",
                    "supports": "axiom_footprint is empty",
                    "checkers": ["nat_axiom_inventory"],
                }
            ],
        }
        # the positive control, in the same command: a fact that really does
        # cite a load-bearing numerics script MUST be counted, so a census
        # returning 0 for everything cannot pass this test.
        genuine = {
            "id": "F:really-controlled",
            "epistemic_status": "proved",
            "evidence": [{"kind": "instance-pin", "checker_command": f"python3 {script}"}],
        }
        numerics = [numeric(script=script, negative_controls=5)]
        with tempfile.TemporaryDirectory() as d:
            facts = pathlib.Path(d)
            (facts / "F-looks-semantic.json").write_text(json.dumps(inflated))
            (facts / "F-really-controlled.json").write_text(json.dumps(genuine))
            old_facts, old_matrix = mod.FACTS, mod.MATRIX
            mod.FACTS = facts
            mod.MATRIX = facts / "absent.tsv"
            try:
                cen = mod.census([], numerics)
            finally:
                mod.FACTS, mod.MATRIX = old_facts, old_matrix
        self.assertIn("F:really-controlled", cen["load_bearing"])
        self.assertNotIn(
            "F:looks-semantic",
            cen["load_bearing"],
            "a fact whose only semantic signal is its `kind` enum was counted",
        )

    def test_a_numerics_script_without_a_negative_control_contributes_nothing(self):
        rows = [numeric(script="a.py", negative_controls=0)]
        old = mod.numerics_covered_facts
        mod.numerics_covered_facts = lambda: {"a.py": ["F:x"]}
        try:
            cen = mod.census([], rows)
        finally:
            mod.numerics_covered_facts = old
        self.assertEqual(
            cen["load_bearing_facts"],
            0,
            "a numerics script with no negative control was counted as load-bearing",
        )

    def test_a_valid_fixture_with_no_killed_mutation_contributes_nothing(self):
        """A control nothing has demonstrated can fail is not load-bearing, so
        it must not enter the census even though it names a fact."""
        old = mod.numerics_covered_facts
        mod.numerics_covered_facts = lambda: {}
        try:
            dead = mod.census([result(expect="valid", killed=0, fact_ids=["F:a"])], [])
            live = mod.census([result(expect="valid", killed=1, fact_ids=["F:a"])], [])
        finally:
            mod.numerics_covered_facts = old
        self.assertEqual(dead["load_bearing_facts"], 0, "a control with no killed mutation counted")
        self.assertEqual(live["load_bearing_facts"], 1, "a control with a killed mutation was not counted")

    def test_a_numerics_script_with_a_negative_control_contributes(self):
        rows = [numeric(script="a.py", negative_controls=2)]
        old = mod.numerics_covered_facts
        mod.numerics_covered_facts = lambda: {"a.py": ["F:x"]}
        try:
            cen = mod.census([], rows)
        finally:
            mod.numerics_covered_facts = old
        self.assertEqual(cen["load_bearing_facts"], 1)


class RealPackTests(unittest.TestCase):
    """The positive control: the committed pack really runs and really passes."""

    def test_the_real_pack_passes(self):
        results = [mod.run_fixture(fx) for fx in mod.FIXTURES]
        self.assertGreater(len(results), 0, "the pack is empty")
        self.assertGreater(
            sum(r["executed"] for r in results), 0, "the pack executed nothing"
        )
        for guard in (
            mod.guard_zero_executed,
            mod.guard_false_rejected,
            mod.guard_valid_accepted,
            mod.guard_valid_discriminates,
            mod.guard_valid_load_bearing,
            mod.guard_vacuous_is_vacuous,
        ):
            self.assertEqual(guard(results), [], f"{guard.__name__} failed on the real pack")


if __name__ == "__main__":
    unittest.main()
