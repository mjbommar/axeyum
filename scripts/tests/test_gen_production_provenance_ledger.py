#!/usr/bin/env python3
"""Mutation controls for the production provenance ledger.

The discriminating tests matter more than the failing ones. A ledger that called
everything autonomous would report a rising metric forever; a ledger that called
nothing autonomous could never record the result the programme exists to
produce. So the pair that carries the weight is
`test_a_multi_target_operation_is_counted_as_general` against
`test_a_single_target_operation_is_counted_as_a_capsule` — same shape of input,
one field different, opposite classification.
"""

from __future__ import annotations

import collections
import copy
import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-production-provenance-ledger.py"
SPEC = importlib.util.spec_from_file_location("gen_production_provenance_ledger", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
prov = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(prov)


def fact(fact_id: str, route: str = "kernel-lean", operation: str | None = None):
    document = {
        "id": fact_id,
        "epistemic_status": "proved",
        "proof_route": route,
        "axiom_footprint": [],
    }
    if operation is not None:
        document["evidence"] = [{"checker_operation": {"id": operation}}]
    return document


class ProvenanceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.facts = {
            "F:a": fact("F:a", operation="op-one"),
            "F:b": fact("F:b", operation="op-many"),
            "F:c": fact("F:c"),
        }
        self.widths = {"op-one": 1, "op-many": 2}

    def report(self, facts=None, widths=None):
        return prov.classify(facts or self.facts, widths or self.widths)

    # --- the discriminating pair --------------------------------------------
    def test_a_multi_target_operation_is_counted_as_general(self) -> None:
        report = self.report()
        self.assertEqual(report["generality"][prov.GENERAL], 1)
        self.assertEqual(report["facts_via_multi_target"], ["F:b"])

    def test_a_single_target_operation_is_counted_as_a_capsule(self) -> None:
        report = self.report()
        self.assertEqual(report["generality"][prov.CAPSULE], 1)
        self.assertNotIn("F:a", report["facts_via_multi_target"])

    def test_widening_one_operation_moves_exactly_one_fact(self) -> None:
        """The classification tracks the registry, not a label on the fact."""
        widened = dict(self.widths, **{"op-one": 3})
        before = self.report()["generality"][prov.GENERAL]
        after = self.report(widths=widened)["generality"][prov.GENERAL]
        self.assertEqual((before, after), (1, 2))

    def test_a_fact_with_no_operation_is_neither(self) -> None:
        report = self.report()
        self.assertEqual(report["generality"][prov.NO_OP], 1)

    def test_a_fixture_scope_operation_cannot_move_the_headline(self) -> None:
        """The metric's author could otherwise move it with a JSON edit: register a
        `counterfactual-fixture-only` operation naming three facts, no producer, no
        receipt, no kernel. Found while holding a genuine three-fact producer with
        no authoritative path to register it through."""
        facts = {f"F:{c}": fact(f"F:{c}", operation="op-wide") for c in "abc"}
        auth = self.report(facts=facts, widths={"op-wide": 3})
        self.assertEqual(auth["multi_target_operations"], 1)
        self.assertEqual(len(auth["facts_via_multi_target"]), 3)
        fixture = prov.classify(facts, {"op-wide": 3},
                                {"op-wide": "counterfactual-fixture-only"})
        self.assertEqual(fixture["multi_target_operations"], 0)
        self.assertEqual(fixture["facts_via_multi_target"], [])
        self.assertEqual(fixture["multi_target_fixture_operations"], 1)

    # --- fail closed ---------------------------------------------------------
    def test_an_unknown_route_is_an_error_not_an_other_bucket(self) -> None:
        facts = copy.deepcopy(self.facts)
        facts["F:c"]["proof_route"] = "vibes"
        with self.assertRaisesRegex(prov.ProvenanceError, "unknown proof_route"):
            self.report(facts=facts)

    def test_an_operation_absent_from_the_registry_is_an_error(self) -> None:
        with self.assertRaisesRegex(prov.ProvenanceError, "not in the registry"):
            self.report(widths={"op-one": 1})

    def test_no_settled_facts_is_an_error_not_a_vacuous_pass(self) -> None:
        facts = copy.deepcopy(self.facts)
        for document in facts.values():
            document["epistemic_status"] = "open"
        with self.assertRaisesRegex(prov.ProvenanceError, "vacuously"):
            self.report(facts=facts)

    # --- the committed ledger ------------------------------------------------
    def test_the_committed_ledger_reports_the_live_registry(self) -> None:
        widths, scopes = prov.operation_widths()
        report = prov.classify(prov.load_facts(), widths, scopes)
        text = prov.LEDGER.read_text()
        self.assertIn(f"| {report['settled']} |", text)
        # The claim the whole ledger exists to make. If this ever fails because
        # the number ROSE, that is the result -- regenerate and say so.
        # 0 -> 8 / 0 -> 2: the modeq-family and bounded-induction-factorial-
        # family multi-target operations each produced real settled facts.
        self.assertEqual(report["generality"][prov.GENERAL], 8)
        self.assertEqual(report["multi_target_operations"], 2)

    def test_an_empty_facts_directory_is_an_error_not_a_vacuous_pass(self) -> None:
        """`classify` guards the settled set; `load_facts` guards the corpus. Two
        guards, because an empty directory and a directory of open facts are
        different failures and only one of them is a missing checkout."""
        with tempfile.TemporaryDirectory() as tmp:
            saved, prov.FACTS = prov.FACTS, pathlib.Path(tmp)
            try:
                with self.assertRaisesRegex(prov.ProvenanceError, "vacuously"):
                    prov.load_facts()
            finally:
                prov.FACTS = saved

    def test_the_prose_branch_is_chosen_by_the_number_alone(self) -> None:
        """Pins the rendering independently of the classifier, so deleting the
        branch cannot be masked by the discriminator's own tests."""
        def report(general: int) -> dict:
            # Hand-built, NOT from `classify`. Deriving it from the classifier
            # made this test die when the classifier was mutated, so it pinned
            # nothing the classifier's own tests did not already pin.
            return {
                "settled": 3,
                "generality": collections.Counter(
                    {prov.GENERAL: general, prov.CAPSULE: 2 - general, prov.NO_OP: 1}
                ),
                "by_route": {},
                "multi_target_operations": general,
                "multi_target_fixture_operations": 0,
                "operations": 2,
                "facts_via_multi_target": ["F:b"] if general else [],
                "axiom_free": 3,
            }

        self.assertIn("Both are zero", prov.render(report(0)))
        self.assertNotIn("Both are zero", prov.render(report(1)))
        self.assertIn("first evidence of generality", prov.render(report(1)))

    def test_the_rendered_text_changes_when_generality_appears(self) -> None:
        """A ledger whose prose is fixed would keep saying 'both are zero'."""
        zero = prov.render(self.report(widths={"op-one": 1, "op-many": 1}))
        some = prov.render(self.report())
        self.assertIn("Both are zero", zero)
        self.assertNotIn("Both are zero", some)
        self.assertIn("first evidence of generality", some)


if __name__ == "__main__":
    unittest.main()
