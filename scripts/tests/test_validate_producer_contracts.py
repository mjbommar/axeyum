#!/usr/bin/env python3
"""Fail-closed controls for the ADR-0602 producer-contract validator."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-producer-contracts.py"
SPEC = importlib.util.spec_from_file_location("validate_producer_contracts", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
contracts_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(contracts_module)


def make_fact(
    fact_id: str,
    *,
    status: str = "open",
    language: str = "lean4-surface",
    fragment: str = "Int",
    title: str = "Mathlib v4.30 source proposition Int.ModEq.add_left",
    statement: str = "a ≡ b [ZMOD n]",
) -> dict:
    return {
        "id": fact_id,
        "title": title,
        "epistemic_status": status,
        "formal": {"language": language, "fragment": fragment, "statement": statement},
    }


def make_contract(**overrides) -> dict:
    contract = {
        "schema_version": 1,
        "id": "producer-contract-test-family-v1",
        "title": "Test family",
        "route": "kernel-lane",
        "recipe": {"description": "A generic checker discharges the shape."},
        "shape": {
            "formal_language": ["lean4-surface"],
            "fragments": ["Int"],
            "statement_contains": "[ZMOD ",
        },
        "non_examples": [
            {"fact_id": "F:other-family", "reason": "different family, no ZMOD token"}
        ],
    }
    contract.update(overrides)
    return contract


class ShapeMatchTests(unittest.TestCase):
    def test_all_fields_are_anded(self) -> None:
        shape = {
            "formal_language": ["lean4-surface"],
            "fragments": ["Int"],
            "title_prefix": "Mathlib v4.30 source proposition ",
            "statement_contains": "[ZMOD ",
        }
        matching = make_fact("F:match")
        self.assertTrue(contracts_module.shape_matches(shape, matching))

        wrong_fragment = make_fact("F:x", fragment="Nat", statement="a ≡ b [MOD n]")
        self.assertFalse(contracts_module.shape_matches(shape, wrong_fragment))

        wrong_language = make_fact("F:x", language="smtlib2")
        self.assertFalse(contracts_module.shape_matches(shape, wrong_language))

        wrong_title = make_fact("F:x", title="Outcome-blind mutation of Int.ModEq.add_left")
        self.assertFalse(contracts_module.shape_matches(shape, wrong_title))

        wrong_statement = make_fact("F:x", statement="Int.fib (m + n) = ...")
        self.assertFalse(contracts_module.shape_matches(shape, wrong_statement))


class ContractValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.facts = {
            "F:target": make_fact("F:target"),
            "F:other-family": make_fact(
                "F:other-family",
                title="Mathlib v4.30 source proposition Int.fib_add",
                statement="Int.fib (m + n) = Int.fib (m - 1) * Int.fib n + Int.fib m * Int.fib (n + 1)",
            ),
        }

    def test_committed_contracts_are_valid(self) -> None:
        facts = contracts_module.load_facts()
        contracts = contracts_module.validate_contracts_dir(facts=facts)
        # A floor, not an equality -- more contracts are expected to land over
        # time and a bare count regression is not what this pins. At least the
        # two ADR-0602 seed families (Int.ModEq congruence, Nat.Coprime) must
        # be present and each genuinely general (more than one fact_ids-shaped
        # match is asserted in their own `notes`, not re-derived here).
        self.assertGreaterEqual(len(contracts), 2)
        ids = {c["id"] for c in contracts}
        self.assertIn("producer-contract-int-modeq-family-v1", ids)
        self.assertIn("producer-contract-nat-coprime-family-v1", ids)

    def test_well_formed_contract_passes(self) -> None:
        contracts_module.validate_contract(make_contract(), self.facts)

    def test_non_example_must_resolve_to_a_real_fact(self) -> None:
        contract = make_contract(
            non_examples=[{"fact_id": "F:does-not-exist", "reason": "invented"}]
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "does not resolve"):
            contracts_module.validate_contract(contract, self.facts)

    def test_non_example_that_actually_matches_is_rejected(self) -> None:
        # THE central falsifiability check: a non-example is checked by
        # EXECUTING the shape predicate, never by trusting `reason`.
        contract = make_contract(
            non_examples=[{"fact_id": "F:target", "reason": "claimed, falsely, not to match"}]
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "MATCHES its own shape"):
            contracts_module.validate_contract(contract, self.facts)

    def test_vacuous_shape_matching_every_open_fact_is_rejected(self) -> None:
        facts = {
            "F:a": make_fact("F:a", fragment="Int", statement="anything [ZMOD 1]"),
            "F:b": make_fact("F:b", fragment="Int", statement="anything else [ZMOD 2]"),
        }
        contract = make_contract(
            shape={"formal_language": ["lean4-surface"], "fragments": ["Int"], "id_prefix": "F:"},
            non_examples=[{"fact_id": "F:a", "reason": "placeholder"}],
        )
        # The non-example itself matches too (id_prefix "F:" matches everything),
        # so the non-example guard fires first -- confirm the MESSAGE, not just
        # that it raises, so this test cannot be satisfied by the wrong guard.
        with self.assertRaisesRegex(contracts_module.ContractError, "MATCHES its own shape"):
            contracts_module.validate_contract(contract, facts)

    def test_vacuous_shape_rejected_even_when_non_example_is_settled(self) -> None:
        # Isolate the vacuous-matcher guard from the non-example guard: put the
        # non-example fact OUTSIDE epistemic_status open (so it cannot match
        # under the non-example check's own terms) but still have the shape
        # swallow every OPEN fact.
        facts = {
            "F:a": make_fact("F:a", fragment="Int", statement="anything [ZMOD 1]"),
            "F:b": make_fact("F:b", fragment="Int", statement="anything else [ZMOD 2]"),
            "F:proved-non-example": make_fact(
                "F:proved-non-example", status="proved", fragment="Nat", statement="unrelated"
            ),
        }
        contract = make_contract(
            shape={"formal_language": ["lean4-surface"], "fragments": ["Int"], "id_prefix": "F:"},
            non_examples=[{"fact_id": "F:proved-non-example", "reason": "wrong fragment"}],
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "matches every open fact"):
            contracts_module.validate_contract(contract, facts)

    def test_shape_narrowed_only_by_language_and_fragment_is_rejected(self) -> None:
        contract = make_contract(
            shape={"formal_language": ["lean4-surface"], "fragments": ["Int"]}
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "too coarse a shape"):
            contracts_module.validate_contract(contract, self.facts)

    def test_empty_non_examples_is_rejected(self) -> None:
        contract = make_contract(non_examples=[])
        with self.assertRaisesRegex(contracts_module.ContractError, "non-empty list"):
            contracts_module.validate_contract(contract, self.facts)

    def test_no_proved_or_epistemic_status_field_is_representable(self) -> None:
        for bad_key in ("proved", "epistemic_status"):
            contract = make_contract()
            contract[bad_key] = "proved"
            with self.assertRaisesRegex(contracts_module.ContractError, "unexpected key"):
                contracts_module.validate_contract(contract, self.facts)

    def test_bad_route_is_rejected(self) -> None:
        contract = make_contract(route="magic")
        with self.assertRaisesRegex(contracts_module.ContractError, "route must be one of"):
            contracts_module.validate_contract(contract, self.facts)

    def test_duplicate_contract_id_across_files_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            contract = make_contract()
            (directory / "one.json").write_text(json.dumps(contract))
            (directory / "two.json").write_text(json.dumps(contract))
            with self.assertRaisesRegex(contracts_module.ContractError, "duplicate producer contract id"):
                contracts_module.validate_contracts_dir(directory, facts=self.facts)

    def test_duplicate_non_example_fact_id_within_one_contract_is_rejected(self) -> None:
        contract = make_contract(
            non_examples=[
                {"fact_id": "F:other-family", "reason": "one"},
                {"fact_id": "F:other-family", "reason": "two"},
            ]
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "duplicate non_example"):
            contracts_module.validate_contract(contract, self.facts)

    def test_unknown_top_level_key_is_rejected(self) -> None:
        contract = make_contract()
        contract["extra"] = "surprise"
        with self.assertRaisesRegex(contracts_module.ContractError, "unexpected key"):
            contracts_module.validate_contract(contract, self.facts)


class SeedContractHoldoutIsolationTests(unittest.TestCase):
    """Held-out isolation binds contract shapes exactly as it binds manual
    dispatch (ADR-0542): no seed contract's matched-open set may contain a
    `nursery-v1.json` held-out fact. Checks the PARTITION, never the count.
    """

    def test_seed_contracts_match_no_held_out_fact(self) -> None:
        nursery_path = ROOT / "artifacts/autogenesis/nursery-v1.json"
        if not nursery_path.is_file():
            self.skipTest("no nursery manifest in this tree")
        nursery = json.loads(nursery_path.read_text())
        partition_of = {entry["fact_id"]: entry["partition"] for entry in nursery["entries"]}

        facts = contracts_module.load_facts()
        for _path, contract in contracts_module.load_contracts():
            matched_held_out = [
                fact_id
                for fact_id, fact in facts.items()
                if partition_of.get(fact_id) == "held-out"
                and contracts_module.shape_matches(contract["shape"], fact)
            ]
            self.assertEqual(
                matched_held_out,
                [],
                f"{contract['id']} shape matches held-out fact(s) {matched_held_out}",
            )


if __name__ == "__main__":
    unittest.main()
