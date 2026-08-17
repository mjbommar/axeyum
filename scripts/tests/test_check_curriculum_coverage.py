"""Controls for `check-curriculum-coverage.py`.

The checker currently passes with every node satisfying every condition, which
is exactly the situation in which a gate is indistinguishable from a no-op. So
each condition is driven to FAIL here on a synthetic tree, and the parser is
pinned against the two shapes the real suites use.
"""

from __future__ import annotations

import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_curriculum_coverage", ROOT / "scripts" / "check-curriculum-coverage.py"
)
assert SPEC and SPEC.loader
CC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CC)


def node(node_id: str, status: str, packs: list[str]) -> dict:
    return {
        "id": node_id,
        "kind": "curriculum-node",
        "curriculum_status": status,
        "example_packs": [{"id": p} for p in packs],
    }


def suite(text: str) -> list[pathlib.Path]:
    directory = pathlib.Path(tempfile.mkdtemp())
    path = directory / "math_resource_synthetic_routes.rs"
    path.write_text(text, encoding="utf-8")
    return [path]


NAMED_HELPER = '''
const ALPHA_CASE: &str = include_str!(
    "../../../artifacts/examples/math/alpha-v0/cnf/alpha-refutation.cnf"
);

fn assert_unsat_resource_cnf_checks(label: &str, dimacs: &str) {
    let _ = (label, dimacs);
}

#[test]
fn alpha_emits_checked_drat() {
    assert_unsat_resource_cnf_checks("alpha-v0", ALPHA_CASE);
}
'''

RESULT_TYPE_HELPER = '''
const BETA_CASE: &str = include_str!(
    "../../../artifacts/examples/math/beta-v0/smt2/beta-conflict.smt2"
);

fn check_farkas(label: &str, source: &str) {
    let report = solve(source);
    assert!(matches!(&report.evidence, Evidence::UnsatFarkas(_)), "{label}");
}

#[test]
fn beta_is_farkas_certified() {
    check_farkas("beta-v0", parse_script(BETA_CASE).unwrap());
}
'''

SAT_ONLY = '''
const GAMMA_CASE: &str = include_str!(
    "../../../artifacts/examples/math/gamma-v0/smt2/gamma-model.smt2"
);

fn expect_model(label: &str, source: &str) {
    let report = solve(source);
    assert!(matches!(report.result, CheckResult::Sat(_)), "{label}");
}

#[test]
fn gamma_has_a_model() {
    expect_model("gamma-v0", GAMMA_CASE);
}
'''


class ParserRecognisesBothSuiteShapes(unittest.TestCase):
    def test_helper_named_for_refusal_is_a_negative_control(self) -> None:
        evidence = CC.instance_evidence(suite(NAMED_HELPER))
        self.assertEqual(evidence["alpha-v0"]["instances"], {"cnf/alpha-refutation.cnf"})
        self.assertEqual(evidence["alpha-v0"]["negative"], {"cnf/alpha-refutation.cnf"})

    def test_refusal_asserted_on_the_result_type_is_a_negative_control(self) -> None:
        """The LRA/LIA/BV/UF shape: the helper's NAME says nothing, and the
        instance reaches it through a nested `parse_script(...)` call."""
        evidence = CC.instance_evidence(suite(RESULT_TYPE_HELPER))
        self.assertEqual(evidence["beta-v0"]["negative"], {"smt2/beta-conflict.smt2"})

    def test_a_sat_only_route_is_not_a_negative_control(self) -> None:
        """The discriminating case. If this ever passes, the checker has stopped
        distinguishing anything and every condition below is vacuous."""
        evidence = CC.instance_evidence(suite(SAT_ONLY))
        self.assertEqual(evidence["gamma-v0"]["instances"], {"smt2/gamma-model.smt2"})
        self.assertEqual(evidence["gamma-v0"]["negative"], set())


class EachConditionCanFail(unittest.TestCase):
    def test_covered_with_no_executing_pack_fails(self) -> None:
        evidence = CC.instance_evidence(suite(NAMED_HELPER))
        failures, counts, _ = CC.evaluate(
            [node("curriculum_ghost", "covered", ["never-referenced-v0"])], evidence
        )
        self.assertEqual(counts["running"], 0)
        self.assertTrue(any("does not run" in f for f in failures), failures)

    def test_covered_and_running_but_sat_only_fails(self) -> None:
        evidence = CC.instance_evidence(suite(SAT_ONLY))
        failures, counts, _ = CC.evaluate(
            [node("curriculum_gamma", "covered", ["gamma-v0"])], evidence
        )
        self.assertEqual(counts["running"], 1)
        self.assertEqual(counts["with_negative_control"], 0)
        self.assertTrue(any("to answer, not to refuse" in f for f in failures), failures)

    def test_a_node_meeting_both_conditions_passes(self) -> None:
        evidence = CC.instance_evidence(suite(NAMED_HELPER))
        failures, counts, _ = CC.evaluate(
            [node("curriculum_alpha", "covered", ["alpha-v0"])], evidence
        )
        self.assertEqual(failures, [])
        self.assertEqual(
            {key: counts[key] for key in ("covered", "running", "with_negative_control")},
            {"covered": 1, "running": 1, "with_negative_control": 1},
        )

    def test_a_non_covered_node_is_not_policed(self) -> None:
        """`lean-horizon` nodes name no family on purpose; the gate must not
        demand evidence they are explicitly not claiming."""
        evidence = CC.instance_evidence(suite(NAMED_HELPER))
        failures, counts, _ = CC.evaluate(
            [node("curriculum_horizon", "lean-horizon", [])], evidence
        )
        self.assertEqual(failures, [])
        self.assertEqual(counts["covered"], 0)


class BoundedSaysWhatItIsBoundedBy(unittest.TestCase):
    """R2. `bounded` collapsed four different ceilings into one word."""

    @staticmethod
    def bounded_node(node_id: str, fragments: list[str]) -> dict:
        return {
            "id": node_id,
            "kind": "curriculum-node",
            "curriculum_status": "lean-horizon",
            "decidability": "bounded",
            "axeyum_fragments": fragments,
            "example_packs": [],
        }

    def test_a_node_can_be_bounded_two_ways_at_once(self) -> None:
        """`BV / enumeration (finite groups)` is bounded by a bit width AND by
        an enumeration domain; picking one would be a fiction."""
        kinds = CC.bound_kinds(
            self.bounded_node("g", ["BV / enumeration (finite groups)"])
        )
        self.assertEqual(kinds, ["bit-width", "enumeration-domain"])

    def test_each_kind_is_reachable_from_a_real_fragment(self) -> None:
        for fragment, expected in [
            ("LIA / BV", "bit-width"),
            ("Counting / enumeration", "enumeration-domain"),
            ("NRA", "real-algebraic-admission-cap"),
            ("LRA / NRA", "arithmetic-resource-budget"),
        ]:
            self.assertIn(
                expected, CC.bound_kinds(self.bounded_node("n", [fragment])), fragment
            )

    def test_an_unclassifiable_bounded_node_trips_the_ratchet(self) -> None:
        nodes = [
            self.bounded_node(f"curriculum_mystery_{i}", ["bounded somehow"])
            for i in range(CC.UNCLASSIFIED_BOUND_BASELINE + 1)
        ]
        failures, counts, _ = CC.evaluate(nodes, {})
        self.assertEqual(counts["unclassified_bound"], len(nodes))
        self.assertTrue(any("collapsing again" in f for f in failures), failures)

    def test_the_baseline_itself_does_not_trip(self) -> None:
        nodes = [self.bounded_node("curriculum_mystery", ["bounded somehow"])]
        failures, counts, _ = CC.evaluate(nodes, {})
        self.assertEqual(counts["unclassified_bound"], CC.UNCLASSIFIED_BOUND_BASELINE)
        self.assertEqual(failures, [])


class TheRealTreeIsMeasuredNotAsserted(unittest.TestCase):
    def test_committed_curriculum_map_satisfies_both_conditions(self) -> None:
        evidence = CC.instance_evidence()
        failures, counts, _ = CC.evaluate(CC.curriculum_nodes(), evidence)
        self.assertEqual(failures, [])
        self.assertEqual(counts["covered"], counts["running"])
        self.assertEqual(counts["covered"], counts["with_negative_control"])
        # A floor, so a parser that stops matching cannot report a green zero.
        self.assertGreaterEqual(counts["covered"], 19)


if __name__ == "__main__":
    unittest.main()
