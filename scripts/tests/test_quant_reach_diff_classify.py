"""Focused tests for `bench-results/quant-reach-diff-20260916/classify.py`
(QUANT-REACH-DIFF).

Synthetic fixtures only, no subprocess, no corpus/z3 dependency -- the four
classification branches (`classify_core`) and the two normalization helpers
(`canon_render`, `parse_last_ground_block`/`parse_universal_census`) are each
exercised directly, following `test_z3_proof_instances.py`'s style.

Each test names the ONE branch it is a positive/negative control for, per
CLAUDE.md's "Evidence, checkers, and blind populations": a test named "every
X" must derive X from the classifier's own output, and this file's own
positive control (`test_admitted_identical_body_both_sides`) is the one the
README's real-run table cites as its "show the identical body on both sides"
requirement.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "bench-results" / "quant-reach-diff-20260916" / "classify.py"
SPEC = importlib.util.spec_from_file_location("quant_reach_diff_classify", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
classify = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = classify
SPEC.loader.exec_module(classify)


class CanonRenderTests(unittest.TestCase):
    def test_commutative_arg_order_does_not_matter(self):
        self.assertEqual(
            classify.canon_render("(+ b a)"), classify.canon_render("(+ a b)")
        )
        self.assertEqual(
            classify.canon_render("(= (f x) 3)"), classify.canon_render("(= 3 (f x))")
        )

    def test_non_commutative_order_still_matters(self):
        # Negative control for the sort above: `-` is NOT in COMMUTATIVE, so
        # swapping its operands must NOT collapse to the same canon form.
        self.assertNotEqual(
            classify.canon_render("(- a b)"), classify.canon_render("(- b a)")
        )

    def test_skolem_collapse(self):
        self.assertEqual(
            classify.canon_render("(f !qsk_3)"), classify.canon_render("(f !qsk_7)")
        )
        self.assertEqual(
            classify.canon_render("(f !qu_1)"), classify.canon_render("(f !qskf_99)")
        )

    def test_skolem_regex_does_not_over_match(self):
        # Negative control: a plain declared symbol that merely starts with
        # a similar letter must NOT be collapsed.
        self.assertNotEqual(
            classify.canon_render("(f quux)"), classify.canon_render("(f SKOLEM)")
        )


class GroundDumpParsingTests(unittest.TestCase):
    def test_last_block_only(self):
        text = (
            "GROUNDDUMP begin reason=first count=1\n"
            "GROUND 0 gen=0 (= a 1)\n"
            "GROUNDDUMP end reason=first\n"
            "GROUNDDUMP begin reason=final count=2\n"
            "GROUND 0 gen=0 (= a 1)\n"
            "GROUND 1 gen=1 (= (f a) 2)\n"
            "GROUNDDUMP end reason=final\n"
        )
        rows = classify.parse_last_ground_block(text)
        self.assertEqual(rows, [(0, 0, "(= a 1)"), (1, 1, "(= (f a) 2)")])

    def test_no_block_is_empty_not_an_exception(self):
        self.assertEqual(classify.parse_last_ground_block(""), [])


class UniversalCensusParsingTests(unittest.TestCase):
    def test_last_occurrence_wins_and_rej_fields_parsed(self):
        text = (
            "QPROBE   universal[0] vars=1 patterns=1 joined=2 starved_joins=0 admitted=0 "
            "rej_handoff=0 rej_poscap=0 rej_nocontext=2 rej_expired=0 rej_subst=0 "
            "rej_true=0 rej_unreleased=0 rej_flood=0 rej_ceiling=0 rej_check=0 "
            "rej_seen=0 rej_dupother=0 rej_true_newterm=0 census_admitted=0\n"
            "QPROBE   universal[0] vars=1 patterns=1 joined=5 starved_joins=0 admitted=1 "
            "rej_handoff=0 rej_poscap=0 rej_nocontext=4 rej_expired=0 rej_subst=0 "
            "rej_true=0 rej_unreleased=0 rej_flood=0 rej_ceiling=0 rej_check=0 "
            "rej_seen=0 rej_dupother=0 rej_true_newterm=0 census_admitted=1\n"
        )
        census = classify.parse_universal_census(text)
        self.assertEqual(census[0]["joined"], 5)
        self.assertEqual(census[0]["rej"]["rej_nocontext"], 4)


class ClassifyCoreTests(unittest.TestCase):
    """One test per class, each doubling as that class's positive control;
    `test_*_negative_control` pairs give the class an adjacent case that must
    NOT fall into it."""

    def test_admitted_identical_body_both_sides(self):
        apps = [{"params": ["5"], "body": "(= (f 5) 6)", "nested": False}]
        ground_rows = [(0, 1, "(= (f 5) 6)")]
        rows = classify.classify_core(apps, [], ground_rows, {})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["class"], classify.CLASS_ADMITTED)
        # The "identical body on both sides" positive control the README
        # cites: z3's body string IS what admitted the term.
        self.assertEqual(rows[0]["body"], "(= (f 5) 6)")

    def test_matched_rejected_needs_args_present_and_census_evidence(self):
        apps = [{"params": ["7"], "body": "(= (f 7) 8)", "nested": False}]
        ground_rows = [(0, 0, "7")]  # the argument, gen 0, but NOT the body
        census = {0: {"vars": 1, "patterns": 1, "joined": 3, "admitted": 0, "rej": {"rej_nocontext": 3}}}
        rows = classify.classify_core(apps, [], ground_rows, census)
        self.assertEqual(rows[0]["class"], classify.CLASS_MATCHED_REJECTED)
        self.assertEqual(rows[0]["reason"], "rej_nocontext")

    def test_never_matched_trigger_did_not_fire_when_args_present_but_no_census_evidence(self):
        apps = [{"params": ["9"], "body": "(= (g 9) 10)", "nested": False}]
        ground_rows = [(0, 0, "9")]
        # No census at all (every rej_* would read 0): args present, nothing
        # rejected -- the trigger simply never fired on this tuple.
        rows = classify.classify_core(apps, [], ground_rows, {})
        self.assertEqual(rows[0]["class"], classify.CLASS_NEVER_MATCHED)
        self.assertEqual(rows[0]["reason"], "trigger-did-not-fire")

    def test_never_matched_missing_term_and_nested_product_flag(self):
        apps = [{"params": ["(h 3)"], "body": "(= (g (h 3)) 11)", "nested": False}]
        ground_rows = []  # "(h 3)" never entered our ground set at all
        not_ground = ["(g (h 3))"]  # z3's own nested-instance list mentions it
        rows = classify.classify_core(apps, not_ground, ground_rows, {})
        # This body is ALSO re-added via the not_ground pass unless already
        # covered; here the application itself is not marked nested, so it is
        # classified on its own merits first.
        matched = [r for r in rows if r["body"] == "(= (g (h 3)) 11)"]
        never_matched = [r for r in matched if r["class"] == classify.CLASS_NEVER_MATCHED]
        self.assertEqual(len(never_matched), 1)
        self.assertEqual(never_matched[0]["reason"], "missing-term")
        self.assertIn("nested_product=True", never_matched[0]["detail"])

    def test_nested_class_from_application_flag(self):
        apps = [
            {
                "params": ["?p_!1"],
                "body": "(= (g ?p_!1) 12)",
                "nested": True,
            }
        ]
        rows = classify.classify_core(apps, [], [], {})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["class"], classify.CLASS_NESTED)

    def test_nested_class_from_not_ground_list_alone(self):
        # Negative control for the two nested paths being independent: an
        # application list with NOTHING in it must still surface a
        # not_ground body passed separately (mirrors the real caller, which
        # gets `not_ground` from z3pi's own extract() and `applications`
        # from a lower-level walk that can, in principle, disagree).
        rows = classify.classify_core([], ["(= (g ?p_!2) 13)"], [], {})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["class"], classify.CLASS_NESTED)

    def test_dedup_by_body_keeps_first_occurrence_params(self):
        apps = [
            {"params": ["a"], "body": "(= x 1)", "nested": False},
            {"params": ["b"], "body": "(= x 1)", "nested": False},
        ]
        rows = classify.classify_core(apps, [], [], {})
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["params"], ["a"])


if __name__ == "__main__":
    unittest.main()
