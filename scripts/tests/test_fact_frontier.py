#!/usr/bin/env python3
"""Fail-closed controls for the machine-readable fact frontier."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
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


def real_decline(**overrides) -> dict:
    """A well-formed contract-driven decline (doc 291) against the REAL,
    committed `int-modeq-family-v1` contract. `fact_id` and `contract` must
    both resolve against the real ledger (see `load_decline_artifacts`'s
    docstring for why), so every override here still names something real
    unless the test is deliberately checking staleness.
    """
    decline = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-test-decline-v1",
        "contract": "artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json",
        "contract_sha256": "0" * 64,  # overridden below with the REAL current digest
        "fact_id": "F:ml430-int-add-modeq-right-e58108ee",
        "producer": {
            "tool": "crates/axeyum-lean-import/examples/modeq_family_operation.rs",
            "result": "declined",
            "decline_reason": "TerminalNotClosed",
            "decline_message": "test fixture: terminal goal is not an Eq/Iff shape",
        },
    }
    decline.update(overrides)
    return decline


class ProducerContractDeclineTests(unittest.TestCase):
    """Doc 291: a decline is SELECTOR INPUT, not just a receipt. These
    exercise the feedback loop end to end over the real ledger and the real
    `int-modeq-family-v1` contract, since a decline's `fact_id` and
    `contract` must both resolve against the real committed artifacts (see
    `load_decline_artifacts`'s docstring).
    """

    TARGET = "F:ml430-int-add-modeq-right-e58108ee"
    CONTRACT_ID = "producer-contract-int-modeq-family-v1"

    def setUp(self) -> None:
        self.facts = frontier.load()
        self.contracts = frontier.load_producer_contracts()
        self.real_contract = next(
            c for c in self.contracts if c["id"] == self.CONTRACT_ID
        )
        self.real_digest = frontier.digest(self.real_contract)
        # Sanity: the target really is shape-matched by this contract and has
        # no dependencies blocking it, or the test proves nothing.
        self.assertIn(
            self.CONTRACT_ID,
            frontier.matching_contracts(
                self.facts[self.TARGET],
                self.contracts,
                frontier.contract_validator_module().shape_matches,
            ),
        )

    def test_live_decline_removes_admissibility_and_reports_declined(self) -> None:
        decline = real_decline(contract_sha256=self.real_digest)
        built = frontier.build_machine_frontier(
            self.facts, contracts=self.contracts, declines=[decline]
        )
        self.assertNotIn(self.TARGET, built["selection"]["admissible_fact_ids"])
        self.assertIn(self.TARGET, built["selection"]["declined_fact_ids"])
        entry = next(row for row in built["entries"] if row["fact_id"] == self.TARGET)
        self.assertEqual(entry["declined_producer_contract_ids"], [self.CONTRACT_ID])
        rationale = next(
            row for row in built["selection"]["rationale"] if row["fact_id"] == self.TARGET
        )
        self.assertIn("declined-via-contract", rationale["rejected_by"])
        self.assertEqual(built["diagnostics"]["declined_by_contract"], {self.CONTRACT_ID: 1})
        self.assertGreaterEqual(built["diagnostics"]["declined_count"], 1)

    def test_stale_decline_against_a_changed_contract_does_not_suppress(self) -> None:
        # The re-dispatch policy (doc 291): a decline binds to the EXACT
        # contract content that produced it. A wrong/stale `contract_sha256`
        # must not suppress admission -- this is what makes editing a
        # contract's recipe automatically re-open everything it declined.
        stale = real_decline(contract_sha256="f" * 64)
        built = frontier.build_machine_frontier(
            self.facts, contracts=self.contracts, declines=[stale]
        )
        self.assertIn(self.TARGET, built["selection"]["admissible_fact_ids"])
        self.assertNotIn(self.TARGET, built["selection"]["declined_fact_ids"])
        entry = next(row for row in built["entries"] if row["fact_id"] == self.TARGET)
        self.assertEqual(entry["declined_producer_contract_ids"], [])

    def test_declines_default_to_none_not_auto_loaded(self) -> None:
        # Same asymmetry as `contracts=None` (doc 291's docstring): a test
        # overriding the contract set must not have a real, unrelated
        # decline silently subtract from its own controlled scenario.
        built = frontier.build_machine_frontier(self.facts, contracts=self.contracts)
        self.assertIn(self.TARGET, built["selection"]["admissible_fact_ids"])

    def test_shape_matched_count_is_unaffected_by_a_decline(self) -> None:
        # A decline narrows ADMISSION, never the shape-match population
        # itself -- `shape_matched_count` must be identical with and without
        # the decline present.
        without = frontier.build_machine_frontier(self.facts, contracts=self.contracts)
        decline = real_decline(contract_sha256=self.real_digest)
        with_decline = frontier.build_machine_frontier(
            self.facts, contracts=self.contracts, declines=[decline]
        )
        self.assertEqual(
            without["diagnostics"]["shape_matched_count"],
            with_decline["diagnostics"]["shape_matched_count"],
        )
        # ...but admissible_count strictly drops by exactly one.
        self.assertEqual(
            with_decline["diagnostics"]["admissible_count"],
            without["diagnostics"]["admissible_count"] - 1,
        )

    def test_malformed_decline_is_rejected_by_build_machine_frontier(self) -> None:
        # `build_machine_frontier` must not silently accept a malformed
        # decline any more than it accepts a malformed contract -- doc 291's
        # falsifiability requirement (a free-text reason is exactly the
        # "make the selector shut up" loophole).
        bad = real_decline(contract_sha256=self.real_digest)
        bad["producer"]["decline_reason"] = "we tried and it did not work"
        with self.assertRaises(frontier.FrontierError):
            frontier.build_machine_frontier(
                self.facts, contracts=self.contracts, declines=[bad]
            )


class RealDeclineFeedbackLoopTests(unittest.TestCase):
    """End-to-end over the real ledger, the real contracts, AND the real
    committed decline (doc 290's `F:ml430-int-add-modeq-left-ee732b5b`) --
    this is what `fact-frontier.py --json` actually prints. Confirms the
    concrete symptom the task started from is fixed: the selector no longer
    loops on a fact a producer already declined.
    """

    def test_the_declined_fact_is_no_longer_selected(self) -> None:
        facts = frontier.load()
        contracts = frontier.load_producer_contracts()
        declines = frontier.load_decline_artifacts()
        self.assertTrue(declines, "expected at least the doc-290 seed decline")
        built = frontier.build_machine_frontier(facts, contracts=contracts, declines=declines)
        declined_fact_id = "F:ml430-int-add-modeq-left-ee732b5b"
        self.assertNotEqual(built["selection"]["selected_fact_id"], declined_fact_id)
        self.assertNotIn(declined_fact_id, built["selection"]["admissible_fact_ids"])
        self.assertIn(declined_fact_id, built["selection"]["declined_fact_ids"])
        # Selection must still land on SOME fact -- the loop moves on, it
        # does not just refuse.
        self.assertIsNotNone(built["selection"]["selected_fact_id"])


class HeldOutFactIdsMultiManifestTests(unittest.TestCase):
    """Guard: `held_out_fact_ids()` must read EVERY `nursery*.json` manifest
    under a directory, never one file by name.

    Measured 2026-09-01
    (docs/research/11-design-review/2026-09-01-the-selector-selected-a-held-out-fact.md):
    this function used to read `nursery-v1.json` literally, so every held-out
    row in `nursery-v2-extension.json` (190 of them, preregistered
    2026-08-29) was invisible to it -- and `--json` selected one as
    `outcome: selected`. This test dies the moment the glob read is narrowed
    back to a single manifest name, in either direction: it fails if a real
    manifest goes missing from the union, and it fails if the union stops
    growing when a new manifest lands.
    """

    def test_the_real_union_equals_v1_plus_v2_extension_held_out_rows(self) -> None:
        v1 = json.loads(
            (ROOT / "artifacts/autogenesis/nursery-v1.json").read_text()
        )
        v2 = json.loads(
            (ROOT / "artifacts/autogenesis/nursery-v2-extension.json").read_text()
        )
        v1_held_out = {
            e["fact_id"] for e in v1["entries"] if e.get("partition") == "held-out"
        }
        v2_held_out = {
            e["fact_id"] for e in v2["entries"] if e.get("partition") == "held-out"
        }
        # Non-vacuity: if either manifest stopped carrying held-out rows the
        # union check below would pass trivially.
        self.assertGreater(len(v1_held_out), 0)
        self.assertGreater(len(v2_held_out), 0)
        self.assertEqual(v1_held_out & v2_held_out, set())
        self.assertEqual(
            frontier.held_out_fact_ids(), frozenset(v1_held_out | v2_held_out)
        )


class JsonPathHeldOutScreenTests(unittest.TestCase):
    """Guard: `build_machine_frontier` -- the `--json` selection path -- must
    exclude a held-out fact from `admissible_fact_ids` however capable its
    route/producer/gate signals read.

    Measured 2026-09-01: `held_out_fact_ids()` used to be called from exactly
    ONE site, the human-rendered queue line. `--json`, `--output`, `--verify`
    (`selection`, `admissible_fact_ids`, `diagnostics` -- what every
    downstream reader and every brief consumes) applied no held-out screen
    at all, and reported a held-out fact as `admissible_via_contract` /
    `outcome: selected`.
    """

    TARGET = "F:no-integer-square-is-minus-one"

    def setUp(self) -> None:
        # A REAL fact id, reset to `open`: `validate_registry` resolves
        # `applicability.fact_ids` against the real committed ledger, not a
        # caller's synthetic `facts` dict (see `load_operation_registry`'s
        # callers elsewhere in this file), so a fabricated id like
        # "F:target" cannot be used here. Same technique as
        # `test_only_exact_authoritative_operation_can_license_selection`
        # above.
        self.facts = frontier.load()
        target = copy.deepcopy(self.facts[self.TARGET])
        target["epistemic_status"] = "open"
        target["evidence"] = []
        target.pop("proof_route", None)
        target.pop("axiom_footprint", None)
        self.facts[self.TARGET] = target

        real_registry = frontier.load_operation_registry()
        authoritative = copy.deepcopy(next(
            op for op in real_registry["operations"] if op["scope"] == "authoritative"
        ))
        authoritative["applicability"] = {
            "fact_ids": [self.TARGET],
            "formal_languages": [target["formal"]["language"]],
            "fragments": [target["formal"]["fragment"]],
        }
        authoritative.pop("reviewed_gate_mentions", None)
        self.registry = {**real_registry, "operations": [authoritative]}

    def test_a_held_out_fact_is_never_admissible_even_with_a_registered_operation(
        self,
    ) -> None:
        # Without the screen (an explicit empty held-out set): TARGET is
        # open, dependency-ready, has exactly ONE registered operation, a
        # supported route, and no gate mentions -- it WOULD be selected. This
        # establishes the fixture actually reaches admission on every OTHER
        # axis, so the held-out exclusion below is not vacuous.
        without_screen = frontier.build_machine_frontier(
            self.facts, registry=self.registry, held_out=frozenset()
        )
        self.assertIn(self.TARGET, without_screen["selection"]["admissible_fact_ids"])
        self.assertEqual(
            without_screen["selection"]["selected_fact_id"], self.TARGET
        )

        # With the screen naming TARGET held-out: it must be excluded from
        # admissible_fact_ids/selected_fact_id, named (not silently dropped)
        # in both `rationale` and `selection.held_out_ready_fact_ids`, and
        # counted in `diagnostics.held_out_ready_count`.
        with_screen = frontier.build_machine_frontier(
            self.facts, registry=self.registry, held_out=frozenset({self.TARGET})
        )
        self.assertNotIn(self.TARGET, with_screen["selection"]["admissible_fact_ids"])
        self.assertIsNone(with_screen["selection"]["selected_fact_id"])
        self.assertEqual(
            with_screen["selection"]["outcome"], "refused-no-admissible-candidate"
        )
        rationale = {
            row["fact_id"]: row["rejected_by"]
            for row in with_screen["selection"]["rationale"]
        }
        self.assertIn(
            "held-out-blind-evaluation-population", rationale[self.TARGET]
        )
        self.assertIn(
            self.TARGET, with_screen["selection"]["held_out_ready_fact_ids"]
        )
        self.assertEqual(with_screen["diagnostics"]["held_out_ready_count"], 1)


if __name__ == "__main__":
    unittest.main()
