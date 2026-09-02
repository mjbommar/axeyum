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

    ADR-1510 also requires `sizing` on every contract, and -- since this
    fixture's `id_prefix` (`F:contract-target`) never matches any REAL
    committed fact, so its live population against the real ledger is
    always zero -- a `retirement` block too (rule 1(b): an exhausted
    contract must be retired). Both are validated against the real ledger
    the same way non_examples are, never against a caller's synthetic
    `facts`, so a fixture whose `id_prefix` happens to start matching a
    real fact one day would need updating here, not just in `sizing`'s
    count.
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
        "sizing": {
            "date": "2026-09-01",
            "ledger_sha256": "0" * 64,
            "matched_open_ready_count": 0,
            "matched_open_ready_fact_ids": [],
            "note": (
                "test fixture: id_prefix F:contract-target never matches any "
                "real committed fact, so the real-ledger live population is "
                "always zero."
            ),
        },
        "retirement": {
            "date": "2026-09-01",
            "reason": (
                "test fixture: live population against the real ledger is "
                "always zero, so ADR-1510 rule 1(b) requires retirement."
            ),
        },
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


def contract_file_path(contract_id: str) -> str:
    """The real, committed file (relative to the repo root) whose `id`
    matches `contract_id`, discovered by reading every producer contract
    file rather than guessing a filename from the id -- so this stays
    correct even if a contract is ever renamed or its file relocated.
    """
    directory = ROOT / "artifacts" / "autogenesis" / "producer-contracts"
    for path in sorted(directory.glob("*.json")):
        if json.loads(path.read_text()).get("id") == contract_id:
            return str(path.relative_to(ROOT))
    raise AssertionError(f"no committed producer contract file has id {contract_id!r}")


def synthesize_fact_for_contract(
    facts: dict[str, dict], contract_obj: dict, suffix: str
) -> tuple[dict[str, dict], str]:
    """Add ONE synthetic, open, dependency-ready fact -- never written to
    disk, never a real committed artifact -- shaped to match `contract_obj`'s
    real `shape`, into a COPY of `facts`. Returns `(new_facts, fact_id)`.
    """
    shape = contract_obj["shape"]
    synthetic_id = f"F:contract-drift-synthetic-{suffix}"
    synthetic = fact(
        synthetic_id,
        status="open",
        external="open",
        fragment=shape["fragments"][0],
        depends_on=[],
    )
    synthetic["formal"]["language"] = shape["formal_language"][0]
    if "title_prefix" in shape:
        synthetic["title"] = shape["title_prefix"] + f"synthetic test target {suffix}"
    if "statement_contains" in shape:
        synthetic["formal"]["statement"] = (
            f"synthetic {shape['statement_contains']} test statement {suffix}"
        )
    if "id_prefix" in shape and not synthetic_id.startswith(shape["id_prefix"]):
        synthetic_id = f"{shape['id_prefix']}-synthetic-{suffix}"
        synthetic["id"] = synthetic_id
    module = frontier.contract_validator_module()
    assert module.shape_matches(shape, synthetic), (
        "synthetic fixture must match its own contract's shape predicate, "
        "or it proves nothing about that contract"
    )
    new_facts = dict(facts)
    new_facts[synthetic_id] = synthetic
    return new_facts, synthetic_id


def derive_contract_admissible_target(
    facts: dict[str, dict], contracts: list[dict]
) -> tuple[dict[str, dict], str, str]:
    """Find a fact this lane's real producer contracts can currently admit,
    deriving it from the ledger at test time -- CLAUDE.md: "a test named
    'every X' or relying on 'an X exists' must derive its X from the
    authority, not a literal" -- rather than a hard-coded id that drifts the
    moment the fact is proved (exactly what broke this suite once already).

    Real-ledger-first: if the real ledger currently has a fact genuinely
    admissible via exactly one real contract (open, dependency-ready, not
    held-out, route-capable, gate-review-clean, not already declined), that
    real fact is returned unmodified.

    Synthetic fallback: measured 2026-09-01 (this lane's own investigation,
    reproducible via `python3 scripts/fact-frontier.py --json`), the real
    ledger's contract-admissible population is currently exhausted for BOTH
    committed seed contracts -- `int-modeq-family-v1` closed its whole
    matched family and now carries a `retirement` block, and
    `nat-coprime-family-v1`'s one remaining live candidate
    (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`) is blocked on an unrelated
    `gate-coupling-review-required` finding (`gen-obstruction-producers.py`
    names it). Neither is something a test-drift fix may touch (editing a
    contract or a fact ledger is out of scope here, and forcing the
    assertion to pass by weakening it would be exactly the checker-that-
    cannot-fail defect CLAUDE.md warns against). So the fallback adds ONE
    synthetic fact -- never written to disk -- shaped to match a REAL,
    NOT-retired contract, into a COPY of `facts`. This keeps every test
    honestly exercising the real contract-admission machinery while the
    real population is temporarily empty, and reverts to the real-ledger
    branch automatically the moment that population is nonempty again.
    """
    built = frontier.build_machine_frontier(facts, contracts=contracts)
    for candidate_id in built["selection"]["admissible_fact_ids"]:
        entry = next(row for row in built["entries"] if row["fact_id"] == candidate_id)
        if len(entry["matched_producer_contract_ids"]) == 1:
            return facts, candidate_id, entry["matched_producer_contract_ids"][0]

    live_contracts = sorted(
        (c for c in contracts if "retirement" not in c), key=lambda c: c["id"]
    )
    assert live_contracts, (
        "no non-retired producer contract available to synthesize a target "
        "against -- every real seed contract is retired"
    )
    contract_obj = live_contracts[0]
    new_facts, synthetic_id = synthesize_fact_for_contract(
        facts, contract_obj, "9f3a1b2c"
    )
    return new_facts, synthetic_id, contract_obj["id"]


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
        # See `derive_contract_admissible_target`'s docstring: real-ledger
        # -first, synthetic fallback only while the real population is
        # temporarily exhausted/gate-blocked (measured 2026-09-01).
        target_facts, _fact_id, _contract_id = derive_contract_admissible_target(
            facts, contracts
        )
        built = frontier.build_machine_frontier(target_facts, contracts=contracts)
        self.assertGreater(built["diagnostics"]["admissible_count"], 0)
        self.assertGreater(built["diagnostics"]["admissible_via_contract_count"], 0)
        selected = built["selection"]["selected_fact_id"]
        self.assertIsNotNone(selected)
        entry = next(row for row in built["entries"] if row["fact_id"] == selected)
        self.assertEqual(len(entry["matched_producer_contract_ids"]), 1)
        self.assertTrue(entry["producer_contract_route_capable"])
        # Not a receipt: nothing in the ledger's `epistemic_status` changed
        # to reach this, and the selected fact is still genuinely open.
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


def derive_contract_path_target(
    facts: dict[str, dict], contracts: list[dict]
) -> tuple[str, str]:
    """A REAL fact id + real contract id whose CONTRACT PATH is currently
    open -- uniquely shape-matched, route-capable, not already declined --
    derived at test time rather than a hard-coded id.

    Declines can only ever validly name a REAL committed `fact_id`
    (`validate_decline_artifacts` checks this against `artifacts/facts/`
    regardless of any caller-supplied `facts` dict -- see
    `load_decline_artifacts`'s docstring), so unlike
    `derive_contract_admissible_target`'s synthetic fallback, a
    decline-mechanism test cannot fall back to a fact that only exists
    in-memory. This derives at the narrower CONTRACT-PATH level instead of
    full pipeline admissibility, which the engine's own diagnostics
    (`declined_fact_ids`, `declined_by_contract`, `declined_count`) already
    treat as a population independent of gate review -- see
    `build_machine_frontier`'s "three populations" comment. Raises if no
    such real fact currently exists (nothing for a decline test to exercise
    honestly).
    """
    built = frontier.build_machine_frontier(facts, contracts=contracts)
    for entry in built["entries"]:
        contract_ids = entry["matched_producer_contract_ids"]
        if (
            len(contract_ids) == 1
            and entry["producer_contract_route_capable"]
            and not entry["declined_producer_contract_ids"]
        ):
            return entry["fact_id"], contract_ids[0]
    raise AssertionError(
        "no real fact currently has an open (undeclined, route-capable, "
        "uniquely shape-matched) contract path -- decline-mechanism tests "
        "have nothing real left to exercise"
    )


class ProducerContractDeclineTests(unittest.TestCase):
    """Doc 291: a decline is SELECTOR INPUT, not just a receipt. These
    exercise the feedback loop end to end over the real ledger and a real
    committed producer contract, against a target `TARGET`/`CONTRACT_ID`
    DERIVED at test time (`derive_contract_path_target`) rather than a
    hard-coded id, since a decline's `fact_id` must resolve to a REAL
    committed fact.

    Measured 2026-09-01: the real ledger's only fact with an open contract
    path today, `F:ml430-nat-coprime-of-lt-minfac-0f79bdba`, is separately
    blocked by an unrelated `gate-coupling-review-required` finding, so it
    is never in `admissible_fact_ids` before OR after these declines --
    these tests check what a decline actually narrows (the CONTRACT path:
    `declined_producer_contract_ids` / `declined_fact_ids` /
    `declined_by_contract` / `declined_count`), which is exactly the
    population doc 291 and ADR-0602 document a decline as touching, and is
    unaffected by that orthogonal gate finding.
    """

    def setUp(self) -> None:
        self.facts = frontier.load()
        self.contracts = frontier.load_producer_contracts()
        self.TARGET, self.CONTRACT_ID = derive_contract_path_target(
            self.facts, self.contracts
        )
        self.real_contract = next(
            c for c in self.contracts if c["id"] == self.CONTRACT_ID
        )
        self.real_digest = frontier.digest(self.real_contract)
        self.contract_path = contract_file_path(self.CONTRACT_ID)
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

    def _decline(self, **overrides) -> dict:
        overrides.setdefault("contract", self.contract_path)
        overrides.setdefault("fact_id", self.TARGET)
        return real_decline(**overrides)

    def test_live_decline_removes_admissibility_and_reports_declined(self) -> None:
        decline = self._decline(contract_sha256=self.real_digest)
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
        # must not suppress the CONTRACT path -- this is what makes editing
        # a contract's recipe automatically re-open everything it declined.
        stale = self._decline(contract_sha256="f" * 64)
        built = frontier.build_machine_frontier(
            self.facts, contracts=self.contracts, declines=[stale]
        )
        self.assertNotIn(self.TARGET, built["selection"]["declined_fact_ids"])
        entry = next(row for row in built["entries"] if row["fact_id"] == self.TARGET)
        self.assertEqual(entry["declined_producer_contract_ids"], [])

    def test_declines_default_to_none_not_auto_loaded(self) -> None:
        # Same asymmetry as `contracts=None` (doc 291's docstring): a test
        # overriding the contract set must not have a real, unrelated
        # decline silently subtract from its own controlled scenario.
        built = frontier.build_machine_frontier(self.facts, contracts=self.contracts)
        self.assertNotIn(self.TARGET, built["selection"]["declined_fact_ids"])
        entry = next(row for row in built["entries"] if row["fact_id"] == self.TARGET)
        self.assertEqual(entry["declined_producer_contract_ids"], [])

    def test_shape_matched_count_is_unaffected_by_a_decline(self) -> None:
        # A decline narrows the CONTRACT path, never the shape-match
        # population itself -- `shape_matched_count` must be identical with
        # and without the decline present.
        without = frontier.build_machine_frontier(self.facts, contracts=self.contracts)
        decline = self._decline(contract_sha256=self.real_digest)
        with_decline = frontier.build_machine_frontier(
            self.facts, contracts=self.contracts, declines=[decline]
        )
        self.assertEqual(
            without["diagnostics"]["shape_matched_count"],
            with_decline["diagnostics"]["shape_matched_count"],
        )
        # ...but declined_count strictly increases by exactly one, and this
        # fact is now named among the declined.
        self.assertEqual(
            with_decline["diagnostics"]["declined_count"],
            without["diagnostics"]["declined_count"] + 1,
        )
        self.assertNotIn(self.TARGET, without["selection"]["declined_fact_ids"])
        self.assertIn(self.TARGET, with_decline["selection"]["declined_fact_ids"])

    def test_malformed_decline_is_rejected_by_build_machine_frontier(self) -> None:
        # `build_machine_frontier` must not silently accept a malformed
        # decline any more than it accepts a malformed contract -- doc 291's
        # falsifiability requirement (a free-text reason is exactly the
        # "make the selector shut up" loophole).
        bad = self._decline(contract_sha256=self.real_digest)
        bad["producer"]["decline_reason"] = "we tried and it did not work"
        with self.assertRaises(frontier.FrontierError):
            frontier.build_machine_frontier(
                self.facts, contracts=self.contracts, declines=[bad]
            )


class RealDeclineFeedbackLoopTests(unittest.TestCase):
    """End-to-end over the real ledger, the real contracts, AND the real
    committed decline artifacts (doc 290 seeded the first one) -- this is
    what `fact-frontier.py --json` actually prints. Confirms the concrete
    symptom the task started from is fixed: the selector no longer loops on
    a fact a producer already declined.

    The declined fact checked below is DERIVED, not the doc-290 literal:
    measured 2026-09-01, every real committed decline against either seed
    contract went stale the moment ADR-1510 added a `sizing` block to both
    contract files -- by the re-dispatch policy's own design (editing a
    contract auto-reopens what it declined), not a bug -- so
    `declined_fact_ids` over the real declines alone is currently empty. A
    fresh, live decline is layered on top of the real, loaded declines
    (still exercised below, so a crash or a parse regression in
    `load_decline_artifacts` is still caught) against a REAL target derived
    by `derive_contract_path_target` (a decline can only ever validly name a
    real committed fact id, so this cannot fall back to a synthetic fact the
    way full-admissibility derivation does elsewhere in this file).
    """

    def test_the_declined_fact_is_no_longer_selected(self) -> None:
        facts = frontier.load()
        contracts = frontier.load_producer_contracts()
        declines = frontier.load_decline_artifacts()
        self.assertTrue(declines, "expected at least one real committed decline artifact")

        fact_id, contract_id = derive_contract_path_target(facts, contracts)
        contract_obj = next(c for c in contracts if c["id"] == contract_id)
        # A second, independent, SYNTHETIC admissible target on the SAME
        # contract (never declined), so "selection moves on" below is not
        # vacuous even though the real ledger's own admissible-via-contract
        # population is currently empty (see `derive_contract_path_target`'s
        # docstring) -- this decoy fact needs no decline naming it, so it
        # does not run into the real-fact-only constraint on declines.
        target_facts, _fallback_id = synthesize_fact_for_contract(
            facts, contract_obj, "fallback-4b2e"
        )
        fresh_decline = real_decline(
            contract=contract_file_path(contract_id),
            contract_sha256=frontier.digest(contract_obj),
            fact_id=fact_id,
        )
        built = frontier.build_machine_frontier(
            target_facts, contracts=contracts, declines=[*declines, fresh_decline]
        )
        self.assertNotEqual(built["selection"]["selected_fact_id"], fact_id)
        self.assertNotIn(fact_id, built["selection"]["admissible_fact_ids"])
        self.assertIn(fact_id, built["selection"]["declined_fact_ids"])
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
