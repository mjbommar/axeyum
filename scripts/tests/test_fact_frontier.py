#!/usr/bin/env python3
"""Fail-closed controls for the machine-readable fact frontier."""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/fact-frontier.py"
SPEC = importlib.util.spec_from_file_location("fact_frontier", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
frontier = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(frontier)


def fact(
    fact_id: str,
    *,
    status: str,
    external: str,
    fragment: str,
    route: str | None = None,
    depends_on: list[str] | None = None,
) -> dict:
    return {
        "id": fact_id,
        "epistemic_status": status,
        "external_status": external,
        "formal": {"language": "lean4", "fragment": fragment, "statement": fact_id},
        "proof_route": route,
        "depends_on": depends_on or [],
    }


class MachineFrontierTests(unittest.TestCase):
    def setUp(self) -> None:
        self.facts = {
            "F:foundation": fact(
                "F:foundation",
                status="proved",
                external="proved",
                fragment="QF_FP",
                route="smt-clausal",
            ),
            "F:research": fact(
                "F:research",
                status="conjectured",
                external="open",
                fragment="Nat",
                depends_on=["F:foundation"],
            ),
            "F:backlog": fact(
                "F:backlog",
                status="open",
                external="proved",
                fragment="QF_FP",
                depends_on=["F:foundation"],
            ),
        }

    def test_snapshot_is_deterministic_and_refuses_unregistered_dispatch(self) -> None:
        first = frontier.build_machine_frontier(self.facts)
        second = frontier.build_machine_frontier(dict(reversed(list(self.facts.items()))))
        self.assertEqual(first, second)
        self.assertEqual(first["selection"]["selected_fact_id"], None)
        self.assertEqual(first["selection"]["admissible_fact_ids"], [])
        self.assertEqual(
            first["selection"]["ready_fact_ids"], ["F:research", "F:backlog"]
        )
        backlog = next(row for row in first["entries"] if row["fact_id"] == "F:backlog")
        self.assertEqual(backlog["route_class"], "decidable")
        rationale = {row["fact_id"]: row["rejected_by"] for row in first["selection"]["rationale"]}
        self.assertIn("no-registered-operation", rationale["F:backlog"])

    def test_rehashed_extra_selection_is_rejected(self) -> None:
        actual = frontier.build_machine_frontier(self.facts)
        actual["selection"]["admissible_fact_ids"] = ["F:backlog"]
        actual["selection"]["selected_fact_id"] = "F:backlog"
        actual["selection"]["outcome"] = "selected"
        actual["frontier_sha256"] = frontier.digest(
            {key: value for key, value in actual.items() if key != "frontier_sha256"}
        )
        with self.assertRaisesRegex(frontier.FrontierError, "stale"):
            frontier.verify_machine_frontier(actual, self.facts)

    def test_only_exact_authoritative_operation_can_license_selection(self) -> None:
        facts = frontier.load()
        target = copy.deepcopy(facts["F:no-integer-square-is-minus-one"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        registry = frontier.load_operation_registry()
        operation = copy.deepcopy(registry["operations"][1])
        registry["operations"] = [operation]
        selected = frontier.build_machine_frontier(facts, registry)
        self.assertEqual(
            selected["selection"]["selected_fact_id"],
            "F:no-integer-square-is-minus-one",
        )
        operation["scope"] = "counterfactual-fixture-only"
        del operation["executor"]
        operation.pop("reviewed_gate_mentions", None)
        refused = frontier.build_machine_frontier(facts, registry)
        self.assertIsNone(refused["selection"]["selected_fact_id"])

    def test_ledger_change_invalidates_saved_frontier(self) -> None:
        actual = frontier.build_machine_frontier(self.facts)
        changed = copy.deepcopy(self.facts)
        changed["F:backlog"]["depends_on"] = ["F:missing"]
        with self.assertRaisesRegex(frontier.FrontierError, "stale"):
            frontier.verify_machine_frontier(actual, changed)

    def test_exact_gate_review_allows_kernel_b_and_new_mention_rejects(self) -> None:
        facts = frontier.load()
        target = copy.deepcopy(facts["F:nat-zero-add"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        registry = frontier.load_operation_registry()
        kernel = copy.deepcopy(registry["operations"][2])
        registry["operations"] = [kernel]
        selected = frontier.build_machine_frontier(facts, registry)
        self.assertEqual(selected["selection"]["selected_fact_id"], "F:nat-zero-add")
        entry = next(row for row in selected["entries"] if row["fact_id"] == target["id"])
        self.assertEqual(entry["unreviewed_gate_mentions"], [])

        kernel["reviewed_gate_mentions"] = kernel["reviewed_gate_mentions"][:-1]
        refused = frontier.build_machine_frontier(facts, registry)
        self.assertIsNone(refused["selection"]["selected_fact_id"])

        kernel["reviewed_gate_mentions"] = [
            *registry["operations"][0]["reviewed_gate_mentions"],
            "validate-facts.py",
        ]
        refused = frontier.build_machine_frontier(facts, registry)
        entry = next(row for row in refused["entries"] if row["fact_id"] == target["id"])
        self.assertEqual(entry["stale_reviewed_gate_mentions"], ["validate-facts.py"])
        self.assertIsNone(refused["selection"]["selected_fact_id"])

    def test_multiple_authoritative_operations_are_not_admissible(self) -> None:
        facts = frontier.load()
        target = copy.deepcopy(facts["F:nat-zero-add"])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[target["id"]] = target
        registry = frontier.load_operation_registry()
        kernel = copy.deepcopy(registry["operations"][2])
        duplicate = copy.deepcopy(kernel)
        duplicate["id"] = "authoritative-kernel-nat-zero-add-induction-v1-alternate"
        registry["operations"] = [kernel, duplicate]
        refused = frontier.build_machine_frontier(facts, registry)
        rationale = next(
            row for row in refused["selection"]["rationale"]
            if row["fact_id"] == target["id"]
        )
        self.assertIn("ambiguous-registered-operation", rationale["rejected_by"])
        self.assertIsNone(refused["selection"]["selected_fact_id"])

    def test_live_loader_rejects_duplicate_fact_identity(self) -> None:
        original = frontier.FACTS
        with self.subTest("duplicate ids cannot be silently overwritten"):
            import json
            import tempfile

            with tempfile.TemporaryDirectory() as temporary:
                root = pathlib.Path(temporary)
                (root / "one.json").write_text(json.dumps(self.facts["F:backlog"]))
                (root / "two.json").write_text(json.dumps(self.facts["F:backlog"]))
                frontier.FACTS = root
                try:
                    with self.assertRaisesRegex(frontier.FrontierError, "duplicate"):
                        frontier.load()
                finally:
                    frontier.FACTS = original


if __name__ == "__main__":
    unittest.main()
