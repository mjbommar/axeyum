"""Focused tests for `scripts/z3-proof-instances.py` (QUANT-INSTANCE-PROBE).

Style follows `scripts/tests/test_strip_quantified_assertions.py`: synthetic
s-expressions plus one checked-in real z3 proof fixture, no subprocess, no
corpus dependency.

The fixture (`fixtures/z3-proof-instances-sample.proof`) is the literal
`z3 -smt2` output on:

    (set-option :produce-proofs true)
    (declare-fun f (Int) Int)
    (declare-fun a () Int)
    (assert (forall ((x Int)) (= (f x) (+ x 1))))
    (assert (= a 5))
    (assert (not (= (f a) 6)))
    (check-sat)
    (get-proof)

It contains exactly one `(_ quant-inst 5)` step (x := 5), which is the
POSITIVE CONTROL this module's own docstring promises: the raw occurrence
count here must equal `proof-instances.py`'s own count on the same file, and
both must equal 1. Separately verified by hand with plain z3 (not repeated
here as a subprocess test, to keep this suite z3-free and fast): asserting
`(= a 5)`, `(not (= (f a) 6))`, and the recovered instance body together is
`unsat` -- confirming the recovered term really is the sound ground
consequence and not merely something that LOOKS like one.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "z3-proof-instances.py"
FIXTURE = ROOT / "scripts" / "tests" / "fixtures" / "z3-proof-instances-sample.proof"
SPEC = importlib.util.spec_from_file_location("z3_proof_instances", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class TokenizeParseTests(unittest.TestCase):
    def test_simple_roundtrip(self) -> None:
        tree = MODULE.parse(MODULE.tokenize("(a (b c) d)"))
        self.assertEqual(tree, ["a", ["b", "c"], "d"])

    def test_stops_at_first_complete_form_ignoring_trailing_paren(self) -> None:
        # z3's `(get-proof)` output is `((set-logic ..) (proof ..))`; every
        # caller here starts scanning at `(proof`, which leaves the OUTER
        # wrapper's closing paren dangling after the parsed form. A parser
        # that rejected that trailing paren would reject every real input.
        tree = MODULE.parse(MODULE.tokenize("(proof (a b)) )"))
        self.assertEqual(tree, ["proof", ["a", "b"]])

    def test_unbalanced_open_raises(self) -> None:
        with self.assertRaises(ValueError):
            MODULE.parse(MODULE.tokenize("(a (b)"))

    def test_stray_close_before_any_open_raises(self) -> None:
        with self.assertRaises(ValueError):
            MODULE.parse(MODULE.tokenize(")"))

    def test_render_is_inverse_of_parse_for_atoms(self) -> None:
        tree = ["=", ["+", "x", "1"], "y"]
        self.assertEqual(MODULE.render(tree), "(= (+ x 1) y)")


class LetExpansionTests(unittest.TestCase):
    def test_collect_and_expand_fixpoint(self) -> None:
        tree = MODULE.parse(
            MODULE.tokenize("(let (($a (f 1)) ($b (g $a))) $b)")
        )
        env: dict = {}
        MODULE.collect_lets(tree, env)
        self.assertEqual(MODULE.expand("$b", env), ["g", ["f", "1"]])

    def test_depth_limit_bounds_a_truncated_or_cyclic_expansion(self) -> None:
        # Not something z3 ever emits (its output is acyclic), but the guard
        # exists because an unbounded expander on a TRUNCATED proof is a
        # measured incident (CLAUDE.md): "a `let`-expander reached 63.4 GB".
        env = {"$a": "$a"}
        # Must return, not recurse forever.
        result = MODULE.expand("$a", env, limit=5)
        self.assertEqual(result, "$a")


class InstanceBodyTests(unittest.TestCase):
    def test_extracts_the_non_negated_disjunct(self) -> None:
        node = ["or", ["not", ["forall", [["x", "Int"]], ["p", "x"]]], ["p", "5"]]
        self.assertEqual(MODULE.instance_body(node), ["p", "5"])

    def test_order_of_disjuncts_does_not_matter(self) -> None:
        node = ["or", ["p", "5"], ["not", ["q"]]]
        self.assertEqual(MODULE.instance_body(node), ["p", "5"])

    def test_returns_none_when_not_an_or(self) -> None:
        # Negative control #1: the shape simply is not `(or ..)` at all.
        self.assertIsNone(MODULE.instance_body(["p", "5"]))

    def test_returns_none_when_no_disjunct_is_negated(self) -> None:
        # Negative control #2: an `or` that IS present but carries no negated
        # disjunct is not the quant-inst tautology shape either -- a checker
        # that accepted any `or` here would silently manufacture wrong ground
        # assertions from unrelated proof steps.
        node = ["or", ["p", "5"], ["q", "6"]]
        self.assertIsNone(MODULE.instance_body(node))

    def test_returns_none_when_two_disjuncts_are_negated(self) -> None:
        node = ["or", ["not", ["p"]], ["not", ["q"]]]
        self.assertIsNone(MODULE.instance_body(node))


class FindQuantInstTests(unittest.TestCase):
    def test_finds_raw_node_and_its_application(self) -> None:
        tree = MODULE.parse(
            MODULE.tokenize(
                "(mp ((_ quant-inst 5) (or (not F) (p 5))) X Y)"
            )
        )
        raw = MODULE.find_quant_inst_raw(tree)
        self.assertEqual(len(raw), 1)
        self.assertEqual(raw[0][2:], ["5"])
        apps = MODULE.find_quant_inst_applications(tree)
        self.assertEqual(len(apps), 1)
        params, formula = apps[0]
        self.assertEqual(params, ["5"])
        self.assertEqual(formula, ["or", ["not", "F"], ["p", "5"]])

    def test_multiple_occurrences_of_the_same_instance_are_not_merged_by_the_finder(
        self,
    ) -> None:
        # Deduplication happens in `extract`, not in the finder -- the finder
        # reports every occurrence, which is what makes `--count` comparable
        # to `proof-instances.py`'s raw count.
        tree = MODULE.parse(
            MODULE.tokenize(
                "(and ((_ quant-inst 5) (or (not F) (p 5)))"
                " ((_ quant-inst 5) (or (not F) (p 5))))"
            )
        )
        self.assertEqual(len(MODULE.find_quant_inst_raw(tree)), 2)


class ExtractOnFixtureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.text = FIXTURE.read_text(encoding="utf-8", errors="replace")

    def test_raw_count_is_one(self) -> None:
        result = MODULE.extract(self.text)
        self.assertEqual(result["raw_count"], 1)

    def test_recovers_the_expected_ground_body(self) -> None:
        result = MODULE.extract(self.text)
        self.assertEqual(result["unmatched"], 0)
        self.assertEqual(len(result["bodies"]), 1)
        self.assertEqual(
            result["bodies"][0], "(= (+ 5 (* (- 1) (f 5))) (- 1))"
        )

    def test_no_bound_variable_survives_in_the_recovered_body(self) -> None:
        # The recovered term must be GROUND: no `?x!N`-shaped z3-internal
        # bound-variable name, or it is not something a ground checker can
        # consume as an `assert`.
        result = MODULE.extract(self.text)
        for b in result["bodies"]:
            self.assertNotIn("?", b)


class ExtractDedupeTests(unittest.TestCase):
    def test_two_identical_instances_collapse_to_one_body(self) -> None:
        text = (
            "(proof (and "
            "((_ quant-inst 5) (or (not F) (p 5))) "
            "((_ quant-inst 5) (or (not F) (p 5)))"
            "))"
        )
        result = MODULE.extract(text)
        self.assertEqual(result["raw_count"], 2)
        self.assertEqual(result["bodies"], ["(p 5)"])

    def test_no_proof_form_is_reported_not_silently_empty(self) -> None:
        result = MODULE.extract("(check-sat)\nsat\n")
        self.assertEqual(result.get("error"), "NO-PROOF")


class NotGroundTests(unittest.TestCase):
    """A nested instantiation (max-generation >= 2, measured on 11 of
    ADR-2113's 53 cores) can recover a body that still names an OUTER
    quantifier's own bound variable, e.g. `?p_!4`, resolved only by a
    SEPARATE `quant-inst` step elsewhere in the proof. Such a body is not
    ground and must never be emitted as an `(assert ...)` line -- it would be
    an unbound identifier to any SMT-LIB parser."""

    def test_bound_var_body_is_reported_separately_not_as_ground(self) -> None:
        text = (
            "(proof ((_ quant-inst 4) "
            "(or (not F) (= (select2 Heap_ ?p_!4 ownerRef_) this)))"
            ")"
        )
        result = MODULE.extract(text)
        self.assertEqual(result["bodies"], [])
        self.assertEqual(len(result["not_ground"]), 1)
        self.assertIn("?p_!4", result["not_ground"][0])

    def test_a_mix_of_ground_and_not_ground_is_split_correctly(self) -> None:
        text = (
            "(proof (and "
            "((_ quant-inst 5) (or (not F) (p 5))) "
            "((_ quant-inst 6) (or (not G) (q ?x!9)))"
            "))"
        )
        result = MODULE.extract(text)
        self.assertEqual(result["bodies"], ["(p 5)"])
        self.assertEqual(result["not_ground"], ["(q ?x!9)"])

    def test_cli_default_mode_omits_not_ground_bodies(self) -> None:
        # Built directly rather than via the fixture: the fixture's own
        # instantiation is single-level and has no not-ground case to show.
        import contextlib
        import io
        import tempfile

        text = (
            "(proof ((_ quant-inst 4) "
            "(or (not F) (= (select2 Heap_ ?p_!4 ownerRef_) this))))"
        )
        with tempfile.NamedTemporaryFile("w", suffix=".proof", delete=False) as fh:
            fh.write(text)
            path = fh.name
        try:
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = MODULE.main(["z3-proof-instances.py", path])
            self.assertEqual(rc, 0)
            self.assertEqual(out.getvalue(), "")
            self.assertIn("NOT-GROUND 1 of 1", err.getvalue())
        finally:
            Path(path).unlink()


class MainCliTests(unittest.TestCase):
    def _run(self, argv):
        import contextlib
        import io

        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = MODULE.main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_default_mode_prints_one_assert_line(self) -> None:
        rc, out, _err = self._run(["z3-proof-instances.py", str(FIXTURE)])
        self.assertEqual(rc, 0)
        self.assertEqual(out.strip(), "(assert (= (+ 5 (* (- 1) (f 5))) (- 1)))")

    def test_count_flag_matches_extract_raw_count(self) -> None:
        # This IS the positive control the module's docstring promises: the
        # CLI's reported count must equal the library function's own count on
        # the same input, at the same file, in the same process.
        rc, out, _err = self._run(
            ["z3-proof-instances.py", str(FIXTURE), "--count"]
        )
        self.assertEqual(rc, 0)
        cli_count = int(out.strip())
        lib_count = MODULE.extract(
            FIXTURE.read_text(encoding="utf-8", errors="replace")
        )["raw_count"]
        self.assertEqual(cli_count, lib_count)
        self.assertEqual(cli_count, 1)

    def test_no_args_exits_two(self) -> None:
        rc, _out, _err = self._run(["z3-proof-instances.py"])
        self.assertEqual(rc, 2)

    def test_missing_file_exits_two(self) -> None:
        rc, _out, _err = self._run(
            ["z3-proof-instances.py", "/nonexistent/path.proof"]
        )
        self.assertEqual(rc, 2)

    def test_no_proof_file_exits_one(self) -> None:
        import tempfile

        with tempfile.NamedTemporaryFile("w", suffix=".proof", delete=False) as fh:
            fh.write("sat\n")
            path = fh.name
        try:
            rc, _out, _err = self._run(["z3-proof-instances.py", path])
            self.assertEqual(rc, 1)
        finally:
            Path(path).unlink()


if __name__ == "__main__":
    unittest.main()
