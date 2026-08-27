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

    def test_stale_reviewed_gate_mentions_are_scoped_to_the_operation_not_one_fact(
        self,
    ) -> None:
        """`reviewed_gate_mentions` is authored per OPERATION, over every fact
        in its `applicability.fact_ids` -- not per fact. A gate genuinely
        reviewed for a SIBLING fact in the same multi-fact operation must not
        read as a stale claim on a fact that never needed it; a gate that
        names NO fact in the operation's whole scope must still be caught.
        """
        facts = frontier.load()
        registry = frontier.load_operation_registry()
        operation = next(
            op for op in registry["operations"]
            if op["id"] == "authoritative-mathlib-modeq-family-v1"
        )
        nat_fact_id = "F:ml430-nat-modeq-symm-0a3d4d18"
        self.assertIn(nat_fact_id, operation["applicability"]["fact_ids"])
        self.assertIn(
            "check-autogenesis-modeq-family.py", operation["reviewed_gate_mentions"]
        )
        # Sanity: that reviewed gate really is Int-only text-scan-wise, i.e.
        # it does not itself name the Nat fact -- otherwise this fixture
        # would not exercise the cross-fact scope at all.
        held = frontier.gate_holds(facts)
        self.assertNotIn(
            "check-autogenesis-modeq-family.py", held.get(nat_fact_id, [])
        )

        # The production ledger may already have settled this target. Reopen
        # the in-memory copy because this test exercises review scoping, not
        # the historical moment at which Nat.ModEq.symm was dispatched.
        target = copy.deepcopy(facts[nat_fact_id])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        facts[nat_fact_id] = target

        registry_copy = copy.deepcopy(registry)
        clean = frontier.build_machine_frontier(facts, registry_copy)
        entry = next(row for row in clean["entries"] if row["fact_id"] == nat_fact_id)
        self.assertNotIn(
            "check-autogenesis-modeq-family.py", entry["stale_reviewed_gate_mentions"]
        )

        mutated_op = next(
            op for op in registry_copy["operations"]
            if op["id"] == "authoritative-mathlib-modeq-family-v1"
        )
        # `validate-facts.py` is a real script that mentions none of this
        # operation's facts -- a reviewed mention with nothing left to back
        # it, anywhere in the operation's scope.
        mutated_op["reviewed_gate_mentions"] = mutated_op["reviewed_gate_mentions"] + [
            "validate-facts.py"
        ]
        stale = frontier.build_machine_frontier(facts, registry_copy)
        entry = next(row for row in stale["entries"] if row["fact_id"] == nat_fact_id)
        self.assertIn("validate-facts.py", entry["stale_reviewed_gate_mentions"])
        rationale = next(
            row for row in stale["selection"]["rationale"]
            if row["fact_id"] == nat_fact_id
        )
        self.assertIn("stale-gate-coupling-review", rationale["rejected_by"])

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


def contract(**overrides) -> dict:
    """A minimal, valid producer contract (ADR-0602) for test fixtures.

    Its non_example MUST resolve against the REAL committed ledger --
    `build_machine_frontier`'s `contracts=` argument is always validated
    against `artifacts/facts/`, never against a caller's synthetic `facts`
    dict (see `load_producer_contracts`'s docstring for why) -- so every
    contract fixture here names a real fact id as its non-example.
    """
    built = {
        "schema_version": 1,
        "id": "producer-contract-test-fixture-v1",
        "title": "Test fixture contract",
        "route": "kernel-lane",
        "recipe": {"description": "A test-only recipe."},
        "shape": {
            "formal_language": ["lean4"],
            "fragments": ["Int"],
            "id_prefix": "F:contract-target",
        },
        "non_examples": [
            {"fact_id": "F:nat-zero-add", "reason": "different fragment (Nat, not Int)"}
        ],
    }
    built.update(overrides)
    return built


class ProducerContractAdmissibilityTests(unittest.TestCase):
    """ADR-0602: a producer contract is a NEW, independent admissibility path
    alongside (never instead of) a registered operation. These exercise it in
    isolation, with an empty operation registry, so a contract-driven
    admission can never be confused with the receipt path doc 288 covers.
    """

    def setUp(self) -> None:
        self.empty_registry = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-operation-registry",
            "operations": [],
        }
        self.facts = {
            "F:contract-target": fact(
                "F:contract-target",
                status="open",
                external="proved",
                fragment="Int",
                depends_on=[],
            ),
        }
        self.facts["F:contract-target"]["formal"]["language"] = "lean4"

    def test_matched_contract_with_capable_route_is_admissible(self) -> None:
        built = frontier.build_machine_frontier(
            self.facts, self.empty_registry, contracts=[contract()]
        )
        self.assertEqual(built["selection"]["selected_fact_id"], "F:contract-target")
        entry = next(
            row for row in built["entries"] if row["fact_id"] == "F:contract-target"
        )
        self.assertEqual(
            entry["matched_producer_contract_ids"], ["producer-contract-test-fixture-v1"]
        )
        self.assertEqual(entry["producer_contract_route"], "kernel-lane")
        self.assertTrue(entry["producer_contract_route_capable"])
        rationale = next(
            row for row in built["selection"]["rationale"]
            if row["fact_id"] == "F:contract-target"
        )
        self.assertEqual(rationale["rejected_by"], [])
        self.assertEqual(built["diagnostics"]["admissible_via_contract_count"], 1)
        self.assertEqual(built["diagnostics"]["admissible_via_operation_count"], 0)

    def test_matched_contract_with_incapable_route_is_not_admissible(self) -> None:
        # `cas-bridge` has no capability artifact in this tree (the sibling
        # lane building it has not landed one) -- a shape match alone must
        # not be enough.
        built = frontier.build_machine_frontier(
            self.facts,
            self.empty_registry,
            contracts=[contract(route="cas-bridge")],
        )
        self.assertIsNone(built["selection"]["selected_fact_id"])
        entry = next(
            row for row in built["entries"] if row["fact_id"] == "F:contract-target"
        )
        self.assertEqual(entry["producer_contract_route"], "cas-bridge")
        self.assertFalse(entry["producer_contract_route_capable"])
        rationale = next(
            row for row in built["selection"]["rationale"]
            if row["fact_id"] == "F:contract-target"
        )
        self.assertIn("producer-contract-route-unavailable", rationale["rejected_by"])

    def test_ambiguous_producer_contract_match_is_not_admissible(self) -> None:
        second = contract(id="producer-contract-test-fixture-two-v1")
        built = frontier.build_machine_frontier(
            self.facts, self.empty_registry, contracts=[contract(), second]
        )
        self.assertIsNone(built["selection"]["selected_fact_id"])
        rationale = next(
            row for row in built["selection"]["rationale"]
            if row["fact_id"] == "F:contract-target"
        )
        self.assertIn("ambiguous-producer-contract", rationale["rejected_by"])

    def test_no_route_fact_is_never_admissible_via_contract(self) -> None:
        # `route_class` is a pure function of the ledger (ADR-0602 SS4: the
        # 6 no-route facts are marked as such, never treated as retry
        # candidates). A contract match and a capable route must not override
        # a genuinely unreachable fragment.
        facts = {
            "F:contract-target": fact(
                "F:contract-target",
                status="open",
                external="open",
                fragment="none",
                depends_on=[],
            )
        }
        facts["F:contract-target"]["formal"]["language"] = "lean4"
        built = frontier.build_machine_frontier(
            facts,
            self.empty_registry,
            contracts=[contract(shape={
                "formal_language": ["lean4"],
                "fragments": ["none"],
                "id_prefix": "F:contract-target",
            })],
        )
        entry = next(
            row for row in built["entries"] if row["fact_id"] == "F:contract-target"
        )
        self.assertEqual(entry["route_class"], "no-route")
        self.assertEqual(
            entry["matched_producer_contract_ids"], ["producer-contract-test-fixture-v1"]
        )
        self.assertIsNone(built["selection"]["selected_fact_id"])
        rationale = next(
            row for row in built["selection"]["rationale"]
            if row["fact_id"] == "F:contract-target"
        )
        self.assertIn("no-supported-route", rationale["rejected_by"])

    def test_contracts_default_to_none_not_auto_loaded(self) -> None:
        # `contracts=None` must mean NO contracts, deliberately asymmetric
        # with `registry=None` (auto-loads the real registry) -- see
        # `build_machine_frontier`'s docstring. Confirms a real seed contract
        # never silently appears just because a caller omitted the argument.
        built = frontier.build_machine_frontier(self.facts, self.empty_registry)
        entry = next(
            row for row in built["entries"] if row["fact_id"] == "F:contract-target"
        )
        self.assertEqual(entry["matched_producer_contract_ids"], [])
        self.assertIsNone(built["selection"]["selected_fact_id"])


class RealSeedProducerContractTests(unittest.TestCase):
    """End-to-end over the real ledger and the real committed seed contracts
    -- this is what `fact-frontier.py --json` actually prints, and is the
    ADR-0602 deliverable: dependency-ready x contract-matched x route-capable
    facts become admissible without fabricating a `proved` receipt for any of
    them.
    """

    def test_real_seed_contracts_move_admissible_off_zero(self) -> None:
        facts = frontier.load()
        contracts = frontier.load_producer_contracts()
        built = frontier.build_machine_frontier(facts, contracts=contracts)
        self.assertGreater(built["diagnostics"]["admissible_count"], 0)
        self.assertGreater(built["diagnostics"]["admissible_via_contract_count"], 0)
        selected = built["selection"]["selected_fact_id"]
        self.assertIsNotNone(selected)
        entry = next(row for row in built["entries"] if row["fact_id"] == selected)
        self.assertEqual(len(entry["matched_producer_contract_ids"]), 1)
        self.assertEqual(entry["producer_contract_route"], "kernel-lane")
        self.assertTrue(entry["producer_contract_route_capable"])
        # Not a receipt: nothing in the real ledger's `epistemic_status`
        # changed to reach this, and the selected fact is still genuinely
        # open.
        self.assertEqual(entry["epistemic_status"], "open")

    def test_no_route_facts_are_named_and_never_selected(self) -> None:
        facts = frontier.load()
        contracts = frontier.load_producer_contracts()
        built = frontier.build_machine_frontier(facts, contracts=contracts)
        no_route_ids = set(built["diagnostics"]["no_route_ready_fact_ids"])
        self.assertTrue(no_route_ids)
        self.assertTrue(no_route_ids.isdisjoint(built["selection"]["admissible_fact_ids"]))


if __name__ == "__main__":
    unittest.main()
