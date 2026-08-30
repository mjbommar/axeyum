#!/usr/bin/env python3
"""Controls for `scripts/check-falsification-screen.py` (roadmap phase D3,
ADR-0890).

Same discipline as `scripts/tests/test_semantic_control_fixtures.py` for S3:
the subject is a gate whose entire purpose is to refuse a screen that cannot
fail, so the way it fails is by being agreeable. Each negative test below
feeds a guard function a result set that MUST be refused, aimed at exactly
one guard, so deleting that guard's BODY (gutting it to `return []`) kills
exactly this test and no other.

`test_every_guard_is_wired_into_the_table` is the check the CLAUDE.md
Gotchas section asks for explicitly: a guard can exist, have its own
negative test, and still never run if nobody added its call to `main()`.
`build_guard_table` in the checker returns `(name, failures)` pairs for
every guard it runs; this test confirms that list's NAMES equal
`GUARD_NAMES` exactly -- so a guard written but not wired shows up as a
missing name, not as a silent gap.

`RealPackTests.test_the_real_pack_passes` is the positive control that stops
this file from being a set of negatives against a subject that refuses
everything.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location(
    "check_falsification_screen",
    ROOT / "scripts" / "check-falsification-screen.py",
)
mod = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(mod)


def false_result(**over) -> dict:
    base = {
        "id": "fx",
        "kind": "false_statement",
        "family": "f",
        "statement": "s",
        "provenance": "p",
        "executed": 10,
        "counterexamples": 2,
        "first_counterexample": "ce",
        "seconds": 0.0,
    }
    base.update(over)
    return base


def def_result(**over) -> dict:
    base = {
        "id": "D",
        "kind": "definition",
        "domain_note": "n",
        "provenance": "p",
        "reference_note": "r",
        "witnesses": [],
        "executed": 10,
        "mismatches": 0,
        "first_mismatch": "",
        "mutations": [{"id": "m1", "description": "d", "executed": 5, "moved": True, "first_divergence": "x"}],
        "mutations_moved": 1,
        "mutations_vacuous": 0,
        "seconds": 0.0,
    }
    base.update(over)
    return base


def review_result(**over) -> dict:
    base = {"id": "R", "kind": "review_obligation", "reason": "a real reason", "status": "open"}
    base.update(over)
    return base


class ZeroExecutedFalseTests(unittest.TestCase):
    def test_zero_executed_cases_are_refused_per_statement_and_for_the_whole_corpus(self):
        # ONE test method covering both sub-cases this guard checks, so
        # gutting the guard's body kills exactly this one test, not two.
        bad_one = mod.guard_zero_executed_false([false_result(executed=0), false_result(id="ok", executed=10)])
        self.assertTrue(bad_one, "a false statement executing 0 cases was accepted")
        bad_total = mod.guard_zero_executed_false([false_result(executed=0)])
        self.assertTrue(any("whole false-statement corpus" in b for b in bad_total))

    def test_nonzero_execution_is_accepted(self):
        self.assertEqual(mod.guard_zero_executed_false([false_result(executed=10)]), [])


class CorpusNonemptyTests(unittest.TestCase):
    def test_an_empty_corpus_is_refused(self):
        self.assertTrue(mod.guard_corpus_nonempty([]))

    def test_a_nonempty_corpus_is_accepted(self):
        self.assertEqual(mod.guard_corpus_nonempty([false_result()]), [])


class FalseStatementRefutedTests(unittest.TestCase):
    def test_a_false_statement_with_no_counterexample_is_refused(self):
        bad = mod.guard_false_statement_refuted([false_result(counterexamples=0)])
        self.assertTrue(bad, "a retained false statement that found no counterexample was accepted")

    def test_a_refuted_false_statement_is_accepted(self):
        self.assertEqual(mod.guard_false_statement_refuted([false_result(counterexamples=3)]), [])


class DefinitionsNonemptyTests(unittest.TestCase):
    def test_an_empty_registry_is_refused(self):
        self.assertTrue(mod.guard_definitions_nonempty([]))

    def test_a_nonempty_registry_is_accepted(self):
        self.assertEqual(mod.guard_definitions_nonempty([def_result()]), [])


class ZeroExecutedDefinitionsTests(unittest.TestCase):
    def test_a_definition_that_executed_nothing_is_refused(self):
        bad = mod.guard_zero_executed_definitions([def_result(executed=0), def_result(id="ok", executed=10)])
        self.assertTrue(bad, "a definition with 0 executed reference-check cases was accepted")

    def test_nonzero_execution_is_accepted(self):
        self.assertEqual(mod.guard_zero_executed_definitions([def_result(executed=10)]), [])


class CorrectMatchesReferenceTests(unittest.TestCase):
    def test_a_mismatching_correct_candidate_is_refused(self):
        bad = mod.guard_correct_matches_reference([def_result(mismatches=1, first_mismatch="x")])
        self.assertTrue(bad, "a 'correct' candidate that disagrees with the reference was accepted")

    def test_zero_mismatches_is_accepted(self):
        self.assertEqual(mod.guard_correct_matches_reference([def_result(mismatches=0)]), [])


class DefinitionHasMutationTests(unittest.TestCase):
    def test_a_definition_with_no_mutations_is_refused(self):
        bad = mod.guard_definition_has_mutation([def_result(mutations=[])])
        self.assertTrue(bad, "a definition with zero mutations was accepted")

    def test_a_definition_with_a_mutation_is_accepted(self):
        self.assertEqual(mod.guard_definition_has_mutation([def_result()]), [])


class MutationMovesObservationTests(unittest.TestCase):
    def test_a_vacuous_mutation_is_refused(self):
        bad = mod.guard_mutation_moves_observation(
            [def_result(mutations=[{"id": "m", "description": "d", "executed": 5, "moved": False, "first_divergence": ""}])]
        )
        self.assertTrue(bad, "a mutation that moved no observation was accepted")

    def test_a_moving_mutation_is_accepted(self):
        self.assertEqual(mod.guard_mutation_moves_observation([def_result()]), [])


class ReviewObligationsPresentTests(unittest.TestCase):
    def test_an_empty_reason_or_invalid_status_is_refused(self):
        self.assertTrue(mod.guard_review_obligations_present([review_result(reason="")]))
        self.assertTrue(mod.guard_review_obligations_present([review_result(status="maybe")]))

    def test_a_valid_obligation_is_accepted(self):
        self.assertEqual(mod.guard_review_obligations_present([review_result()]), [])


class ReviewObligationsNonemptyTests(unittest.TestCase):
    def test_zero_review_obligations_is_refused(self):
        self.assertTrue(mod.guard_review_obligations_nonempty([]))

    def test_at_least_one_is_accepted(self):
        self.assertEqual(mod.guard_review_obligations_nonempty([review_result()]), [])


class NoIdInBothRegistriesTests(unittest.TestCase):
    def test_a_shared_id_is_refused(self):
        bad = mod.guard_no_id_in_both_registries([def_result(id="X")], [review_result(id="X")])
        self.assertTrue(bad, "a definition id also registered as a review obligation was accepted")

    def test_disjoint_ids_are_accepted(self):
        self.assertEqual(mod.guard_no_id_in_both_registries([def_result(id="X")], [review_result(id="Y")]), [])


class DispatchHasReceiptTests(unittest.TestCase):
    def test_a_dispatch_with_no_receipt_is_refused(self):
        bad = mod.guard_dispatch_has_receipt([{"target_id": "T", "commit": "c"}], {})
        self.assertTrue(bad, "a dispatch naming a target with no receipt at all was accepted")

    def test_a_dispatch_with_a_receipt_is_accepted(self):
        self.assertEqual(
            mod.guard_dispatch_has_receipt([{"target_id": "T", "commit": "c"}], {"T": {"verdict": "clear-for-dispatch"}}), []
        )


class DispatchReceiptIsClearTests(unittest.TestCase):
    def test_a_reject_or_review_required_verdict_is_refused(self):
        bad_reject = mod.guard_dispatch_receipt_is_clear(
            [{"target_id": "T", "commit": "c"}], {"T": {"verdict": "reject-before-dispatch"}}
        )
        self.assertTrue(bad_reject, "dispatch against a reject-before-dispatch receipt was accepted")
        bad_review = mod.guard_dispatch_receipt_is_clear(
            [{"target_id": "T", "commit": "c"}], {"T": {"verdict": "review-required"}}
        )
        self.assertTrue(bad_review, "dispatch against a review-required receipt was accepted")

    def test_a_clear_verdict_is_accepted(self):
        self.assertEqual(
            mod.guard_dispatch_receipt_is_clear(
                [{"target_id": "T", "commit": "c"}], {"T": {"verdict": "clear-for-dispatch"}}
            ),
            [],
        )


class DispatchOrderingTests(unittest.TestCase):
    """Ordering is checked with an INJECTED ancestor function so the test does
    not depend on real git history -- these are the synthetic positive AND
    negative controls; RealPackTests separately exercises the true git path."""

    def test_receipt_after_dispatch_or_missing_commit_is_refused(self):
        bad = mod.guard_dispatch_ordering(
            [{"target_id": "T", "commit": "new"}],
            {"T": {"verdict": "clear-for-dispatch", "git_commit": "old"}},
            ancestor_check=lambda a, b: False,
        )
        self.assertTrue(bad, "a receipt commit NOT an ancestor of the dispatch commit was accepted")
        bad_missing = mod.guard_dispatch_ordering(
            [{"target_id": "T", "commit": None}],
            {"T": {"verdict": "clear-for-dispatch", "git_commit": "old"}},
            ancestor_check=lambda a, b: True,
        )
        self.assertTrue(bad_missing, "a dispatch entry with no commit recorded was accepted")

    def test_receipt_before_dispatch_is_accepted(self):
        good = mod.guard_dispatch_ordering(
            [{"target_id": "T", "commit": "new"}],
            {"T": {"verdict": "clear-for-dispatch", "git_commit": "old"}},
            ancestor_check=lambda a, b: True,
        )
        self.assertEqual(good, [])

    def test_unresolvable_commits_do_not_fail_the_ordering_guard(self):
        """`None` means git could not resolve one of the SHAs (e.g. a synthetic
        test commit) -- this must NOT be silently treated as pass by turning
        into a False comparison; it must simply not fire this guard, leaving
        the structural guards (has_receipt / receipt_is_clear) to still apply."""
        ok = mod.guard_dispatch_ordering(
            [{"target_id": "T", "commit": "new"}],
            {"T": {"verdict": "clear-for-dispatch", "git_commit": "old"}},
            ancestor_check=lambda a, b: None,
        )
        self.assertEqual(ok, [])


class ReceiptIdsAreRegisteredTests(unittest.TestCase):
    def test_a_receipt_for_an_unknown_target_is_refused(self):
        bad = mod.guard_receipt_ids_are_registered({"not-a-real-target-xyz": {}})
        self.assertTrue(bad, "a receipt naming an unregistered target was accepted")

    def test_a_receipt_for_a_real_target_is_accepted(self):
        real_id = mod.FALSE_STATEMENTS[0].id
        self.assertEqual(mod.guard_receipt_ids_are_registered({real_id: {}}), [])


class PinDriftTests(unittest.TestCase):
    def test_no_pin_or_a_changed_value_is_refused(self):
        bad_missing = mod.guard_pin_drift([false_result()], None, "x.json")
        self.assertTrue(bad_missing, "a missing pin was accepted as if nothing needed comparing")
        pin = {"items": [{"id": "fx", "executed": 999, "counterexamples": 2}]}
        bad_drift = mod.guard_pin_drift([false_result(executed=10)], pin, "x.json")
        self.assertTrue(bad_drift, "a drifted executed count against the pin was accepted")

    def test_a_matching_pin_is_accepted(self):
        pin = {"items": [{"id": "fx", "executed": 10, "counterexamples": 2}]}
        self.assertEqual(mod.guard_pin_drift([false_result(executed=10, counterexamples=2)], pin, "x.json"), [])


class PinCoverageTests(unittest.TestCase):
    def test_a_pin_entry_mismatch_either_direction_is_refused(self):
        pin_gone = {"items": [{"id": "gone"}]}
        bad_gone = mod.guard_pin_coverage([], pin_gone)
        self.assertTrue(bad_gone, "a pinned entry that never ran was accepted")
        pin_empty = {"items": []}
        bad_new = mod.guard_pin_coverage([false_result(id="new")], pin_empty)
        self.assertTrue(bad_new, "an entry that ran but is not pinned was accepted")

    def test_matching_sets_are_accepted(self):
        pin = {"items": [{"id": "fx"}]}
        self.assertEqual(mod.guard_pin_coverage([false_result(id="fx")], pin), [])


class GuardTableWiringTests(unittest.TestCase):
    """The check this file exists to make possible: a guard with its own unit
    tests above still does nothing if `main()` never calls it. This confirms
    every name in `GUARD_NAMES` is exactly what `build_guard_table` returns --
    add a guard function without adding it here, or here without wiring it
    into `build_guard_table`, and this test is the one that catches it."""

    def test_every_guard_is_wired_into_the_table(self):
        table = mod.build_guard_table(
            [false_result()], [def_result()], [review_result()], [], {}, None, None, check_pins=False
        )
        names = [n for n, _ in table]
        # check_pins=False on purpose: the pin guards need real pin dicts to
        # run meaningfully, checked separately below with check_pins=True.
        expected = [n for n in mod.GUARD_NAMES if not n.startswith("pin_")]
        self.assertEqual(names, expected)

    def test_pin_guards_are_wired_when_pins_are_checked(self):
        pin = {"items": [{"id": "fx", "executed": 10, "counterexamples": 2}]}
        defpin = {"items": [{"id": "D", "executed": 10, "mismatches": 0, "mutations_moved": 1, "mutations_vacuous": 0}]}
        table = mod.build_guard_table(
            [false_result()], [def_result()], [review_result()], [], {}, pin, defpin, check_pins=True
        )
        names = [n for n, _ in table]
        self.assertEqual(names, mod.GUARD_NAMES)


class RealPackTests(unittest.TestCase):
    """The positive control: the committed pack really runs and really passes,
    and its own receipts/dispatch-log ordering really checks out against real
    git history in this repository."""

    def test_the_real_pack_passes(self):
        false_results = [mod.run_false_statement(fx) for fx in mod.FALSE_STATEMENTS]
        def_results = [mod.run_definition(d) for d in mod.DEFINITIONS]
        review_results = [mod.run_review_obligation(r) for r in mod.REVIEW_OBLIGATIONS]
        self.assertGreater(len(false_results), 0, "the false-statement corpus is empty")
        self.assertGreater(len(def_results), 0, "the definitions registry is empty")
        self.assertGreater(len(review_results), 0, "no review obligations are registered")
        self.assertGreater(sum(r["executed"] for r in false_results), 0)
        self.assertGreater(sum(r["executed"] for r in def_results), 0)

        receipts = mod.load_receipts()
        dispatch_entries = mod.load_dispatch_log()
        corpus_pin = json.loads(mod.CORPUS_PIN.read_text()) if mod.CORPUS_PIN.exists() else None
        defs_pin = json.loads(mod.DEFS_PIN.read_text()) if mod.DEFS_PIN.exists() else None

        table = mod.build_guard_table(
            false_results, def_results, review_results, dispatch_entries, receipts,
            corpus_pin, defs_pin, check_pins=True,
        )
        for name, bad in table:
            self.assertEqual(bad, [], f"guard {name!r} failed on the real, committed pack: {bad}")

    def test_the_real_dispatch_entry_ordering_is_verifiable_in_git_log(self):
        """This is the literal claim ADR-0890 makes: at least one dispatch
        entry's receipt commit is a real, `git merge-base`-confirmed ancestor
        of its dispatch commit in THIS repository's history, not a mock."""
        receipts = mod.load_receipts()
        dispatch_entries = mod.load_dispatch_log()
        self.assertGreater(len(dispatch_entries), 0, "no demo dispatch entry is committed")
        checked_any = False
        for e in dispatch_entries:
            r = receipts.get(e["target_id"])
            if r is None:
                continue
            verdict = mod.is_ancestor_or_equal(r["git_commit"], e["commit"])
            self.assertIsNotNone(verdict, "receipt or dispatch commit did not resolve in git history")
            self.assertTrue(verdict, f"receipt commit is not an ancestor of the dispatch commit for {e['target_id']!r}")
            checked_any = True
        self.assertTrue(checked_any, "no dispatch entry had a matching receipt to check")


class ReceiptRefusedWithoutClearScreenTests(unittest.TestCase):
    """Exercises `scripts/gen-falsification-screen.py`'s OWN refusal, in a
    scratch directory so it never touches the committed receipts/dispatch log."""

    def test_dispatch_demo_refuses_without_a_receipt(self):
        gen_spec = importlib.util.spec_from_file_location(
            "gen_falsification_screen", ROOT / "scripts" / "gen-falsification-screen.py"
        )
        gen = importlib.util.module_from_spec(gen_spec)
        assert gen_spec.loader is not None
        gen_spec.loader.exec_module(gen)
        with tempfile.TemporaryDirectory() as d:
            scratch = pathlib.Path(d)
            old_fals, old_receipts, old_log = gen.FALS_DIR, gen.RECEIPTS_DIR, gen.DISPATCH_LOG
            gen.FALS_DIR = scratch
            gen.RECEIPTS_DIR = scratch / "receipts"
            gen.DISPATCH_LOG = scratch / "dispatch-log.jsonl"
            try:
                rc = gen.dispatch_demo("Nat.land", "test")
            finally:
                gen.FALS_DIR, gen.RECEIPTS_DIR, gen.DISPATCH_LOG = old_fals, old_receipts, old_log
        self.assertNotEqual(rc, 0, "dispatch-demo succeeded with no receipt on disk at all")

    def test_dispatch_demo_refuses_a_non_clear_receipt(self):
        gen_spec = importlib.util.spec_from_file_location(
            "gen_falsification_screen2", ROOT / "scripts" / "gen-falsification-screen.py"
        )
        gen = importlib.util.module_from_spec(gen_spec)
        assert gen_spec.loader is not None
        gen_spec.loader.exec_module(gen)
        with tempfile.TemporaryDirectory() as d:
            scratch = pathlib.Path(d)
            receipts_dir = scratch / "receipts"
            receipts_dir.mkdir()
            (receipts_dir / "lor-aux-comm-of-fuel-unconditional.json").write_text(
                json.dumps({"target_id": "lor-aux-comm-of-fuel-unconditional", "verdict": "reject-before-dispatch", "git_commit": "abc"})
            )
            old_fals, old_receipts, old_log = gen.FALS_DIR, gen.RECEIPTS_DIR, gen.DISPATCH_LOG
            gen.FALS_DIR = scratch
            gen.RECEIPTS_DIR = receipts_dir
            gen.DISPATCH_LOG = scratch / "dispatch-log.jsonl"
            try:
                rc = gen.dispatch_demo("lor-aux-comm-of-fuel-unconditional", "test")
            finally:
                gen.FALS_DIR, gen.RECEIPTS_DIR, gen.DISPATCH_LOG = old_fals, old_receipts, old_log
        self.assertNotEqual(rc, 0, "dispatch-demo succeeded against a reject-before-dispatch receipt")


if __name__ == "__main__":
    unittest.main()
