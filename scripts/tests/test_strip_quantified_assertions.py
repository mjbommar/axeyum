"""Focused tests for `scripts/strip-quantified-assertions.py` (DT-GROUND-PROBE,
ADR-2114 follow-on).

Each test targets one guard/behaviour of `strip_file`/`main`, in the style of
`scripts/tests/test_gen_ledger_coverage.py`: synthetic SMT-LIB text, no
subprocess, no corpus dependency, so this suite is fast and self-contained.
`scripts/tests/mutation_controls.py` can be pointed at this module the same
way it is pointed at other lane checkers.
"""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "strip-quantified-assertions.py"
SPEC = importlib.util.spec_from_file_location("strip_quantified_assertions", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class HasQuantBinderTests(unittest.TestCase):
    def test_plain_ground_form_has_no_binder(self) -> None:
        node = ["and", ["=", "x", "1"], ["<", "y", "2"]]
        self.assertFalse(MODULE.has_quant_binder(node))

    def test_forall_at_top_is_detected(self) -> None:
        node = ["forall", [["x", "Int"]], ["=", "x", "x"]]
        self.assertTrue(MODULE.has_quant_binder(node))

    def test_exists_nested_several_levels_deep_is_detected(self) -> None:
        node = ["and", ["=", "x", "1"], ["not", ["exists", [["y", "Int"]], ["=", "y", "x"]]]]
        self.assertTrue(MODULE.has_quant_binder(node))

    def test_quantifier_inside_a_let_bound_value_is_detected(self) -> None:
        # `(let ((b (forall ((x Int)) (= x x)))) b)` -- the quantifier lives in
        # the BINDING's value, not the let body; a walker that only descends
        # into the body would miss it.
        node = [
            "let",
            [["b", ["forall", [["x", "Int"]], ["=", "x", "x"]]]],
            "b",
        ]
        self.assertTrue(MODULE.has_quant_binder(node))

    def test_a_symbol_named_forall_is_not_a_binder(self) -> None:
        # `forall` used as an ordinary function symbol, not as an operator
        # position of a real binder form -- `(f forall exists)` -- must not
        # register: the detector requires the token to be the FIRST element.
        node = ["f", "forall", "exists"]
        self.assertFalse(MODULE.has_quant_binder(node))


SNIPPET = """\
(set-info :smt-lib-version 2.6)
(set-logic AUFDTLIRA)
(set-info :status unsat)
(declare-datatypes ((tuple0 0)) (((Tuple0))))
(declare-fun x () Int)
(declare-fun y () Int)
; a comment between forms, kept verbatim
(assert (= x 1))
(assert (forall ((v Int)) (=> (= v x) (= v 1))))
(assert (not (exists ((w Int)) (= w y))))
(assert (let ((b (forall ((z Int)) (= z z)))) (not b)))
(assert (< x y))
(check-sat)
"""


class StripFileTests(unittest.TestCase):
    def test_counts_before_after(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        # 5 asserts total: 2 ground (`= x 1`, `< x y`), 3 quantified (direct
        # forall, direct exists, forall hidden inside a let-bound value).
        self.assertEqual(result.kept + result.dropped, 5)
        self.assertEqual(result.kept, 2)
        self.assertEqual(result.dropped, 3)

    def test_a_removed_one_and_a_kept_one(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        removed = SNIPPET[slice(*result.dropped_spans[0])]
        kept = SNIPPET[slice(*result.kept_spans[0])]
        self.assertIn("forall", removed)
        self.assertEqual(kept, "(assert (= x 1))")

    def test_set_logic_is_left_untouched(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        self.assertIn("(set-logic AUFDTLIRA)", result.text)

    def test_kept_forms_are_byte_verbatim_including_comments(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        self.assertIn("(declare-fun x () Int)", result.text)
        self.assertIn("; a comment between forms, kept verbatim", result.text)
        self.assertIn("(assert (= x 1))", result.text)
        self.assertIn("(assert (< x y))", result.text)

    def test_all_quantified_asserts_are_gone_from_output(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        self.assertNotIn("forall", result.text)
        self.assertNotIn("exists", result.text)

    def test_check_sat_and_declarations_survive(self) -> None:
        result = MODULE.strip_file(SNIPPET)
        self.assertIn("(check-sat)", result.text)
        self.assertIn("(declare-datatypes ((tuple0 0)) (((Tuple0))))", result.text)

    def test_unbalanced_parens_raise(self) -> None:
        with self.assertRaises(ValueError):
            MODULE.strip_file("(assert (= x 1)")

    def test_no_quantified_assert_is_a_no_op_on_content(self) -> None:
        text = "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n"
        result = MODULE.strip_file(text)
        self.assertEqual(result.dropped, 0)
        self.assertEqual(result.kept, 1)
        self.assertEqual(result.text, text)


class MainCliTests(unittest.TestCase):
    def _run(self, text: str, extra_args=()):
        with tempfile.TemporaryDirectory() as td:
            src = Path(td) / "in.smt2"
            dst = Path(td) / "out.smt2"
            src.write_text(text)
            rc = MODULE.main(
                ["strip-quantified-assertions.py", *extra_args, str(src), str(dst)]
            )
            out = dst.read_text() if dst.exists() else None
            return rc, out

    def test_mixed_file_exits_zero_and_writes_output(self) -> None:
        rc, out = self._run(SNIPPET)
        self.assertEqual(rc, 0)
        assert out is not None
        self.assertNotIn("forall", out)
        self.assertIn("(assert (= x 1))", out)

    def test_all_quantified_file_is_degenerate(self) -> None:
        text = (
            "(declare-fun x () Int)\n"
            "(assert (forall ((v Int)) (= v x)))\n"
            "(check-sat)\n"
        )
        rc, out = self._run(text)
        self.assertEqual(rc, 4)
        # The output is still written -- the caller decides what a
        # degenerate split means for its own population, this tool only
        # refuses to claim success silently.
        assert out is not None
        self.assertNotIn("forall", out)

    def test_no_quantified_file_is_degenerate(self) -> None:
        text = "(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n"
        rc, _out = self._run(text)
        self.assertEqual(rc, 4)

    def test_unparseable_file_exits_three(self) -> None:
        rc, out = self._run("(assert (= x 1)")
        self.assertEqual(rc, 3)
        self.assertIsNone(out)

    def test_wrong_argument_count_exits_two(self) -> None:
        rc = MODULE.main(["strip-quantified-assertions.py", "only-one-arg"])
        self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
