"""Controls for `check-capability-routes.py`.

It passes on the committed table with 0 missing routes, which by itself is
indistinguishable from a checker that finds nothing because it looks for
nothing. Each guard is driven to failure here, and the prose/route distinction —
the one that made the naive version report two false positives — is pinned in
both directions.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_capability_routes", ROOT / "scripts" / "check-capability-routes.py"
)
assert SPEC and SPEC.loader
CR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CR)


class AParenthesisIsNotAlwaysARoute(unittest.TestCase):
    """Written after the naive version reported `(vocabulary)` as a missing
    route. It is prose — "Condition 3 (vocabulary) carries no refutation" — and
    treating English as a symbol name would make the gate cry wolf until someone
    deleted it."""

    def test_a_snake_case_identifier_is_a_route(self) -> None:
        self.assertEqual(
            CR.routes_in("CERTIFIED interpolation (lra_interpolant_certified): ..."),
            ["lra_interpolant_certified"],
        )

    def test_a_qualified_path_is_a_route(self) -> None:
        self.assertEqual(
            CR.routes_in("Craig interpolation (axeyum_cnf::propositional_interpolant)"),
            ["axeyum_cnf::propositional_interpolant"],
        )

    def test_a_plain_english_word_in_parentheses_is_not(self) -> None:
        self.assertEqual(CR.routes_in("Condition 3 (vocabulary) carries no refutation"), [])

    def test_prose_and_a_route_in_one_field_yields_only_the_route(self) -> None:
        self.assertEqual(
            CR.routes_in("bounded blast (bounded_int_blast) over a box (finite)"),
            ["bounded_int_blast"],
        )


class ARouteThatDoesNotExistFailsTheGate(unittest.TestCase):
    @staticmethod
    def _rec(feature: str) -> list[dict[str, str]]:
        return [{"area": "QF_X", "feature": feature, "evidence": "e"}]

    def test_a_missing_route_is_reported(self) -> None:
        failures, checked = CR.evaluate(
            self._rec("thing (route_that_was_deleted): ..."), {"other_fn"}
        )
        self.assertEqual(checked, 1)
        self.assertTrue(failures)
        self.assertIn("route_that_was_deleted", failures[0])

    def test_a_present_route_is_accepted(self) -> None:
        failures, checked = CR.evaluate(
            self._rec("thing (route_present): ..."), {"route_present"}
        )
        self.assertEqual((failures, checked), ([], 1))

    def test_a_qualified_route_resolves_on_its_last_segment(self) -> None:
        """The table writes `axeyum_cnf::foo`; the definition scan sees `fn foo`."""
        failures, _ = CR.evaluate(self._rec("thing (axeyum_cnf::foo): ..."), {"foo"})
        self.assertEqual(failures, [])

    def test_a_module_counts_as_a_definition(self) -> None:
        """`(nia_square)` is a `mod`, not a `fn` — the naive version called it
        missing."""
        self.assertIn("nia_square", CR.definitions())


class TheCommittedTableIsMeasuredNotAssumed(unittest.TestCase):
    def test_every_route_the_real_table_names_exists(self) -> None:
        recs = CR.entries(CR.TABLE.read_text(encoding="utf-8"))
        failures, checked = CR.evaluate(recs, CR.definitions())
        self.assertEqual(failures, [], "the capability table names a route that does not exist")
        self.assertGreaterEqual(
            checked,
            CR.MIN_ROUTES,
            "fewer routes extracted than the floor; the `(route)` convention may have changed",
        )
