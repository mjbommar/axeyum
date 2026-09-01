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
        "sizing": {
            "date": "2026-09-01",
            "ledger_sha256": "0" * 64,
            "matched_open_ready_count": 1,
            "matched_open_ready_fact_ids": ["F:target"],
        },
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


class ContractLifecycleTests(unittest.TestCase):
    """ADR-1510 rule 1: a contract is sized by the frontier and retires when
    that population empties.

    One test per guard, and each is expected to be the ONLY test that dies
    when its guard is deleted (`scripts/tests/mutation_controls.py
    producer-contracts`).
    """

    def setUp(self) -> None:
        self.facts = {
            "F:target": make_fact("F:target"),
            "F:other-family": make_fact(
                "F:other-family",
                title="Mathlib v4.30 source proposition Int.fib_add",
                statement="Int.fib (m + n) = ...",
            ),
        }
        # Nothing held out unless a test says so -- these fixtures must not
        # depend on the real nursery manifests.
        self.none_held_out: frozenset[str] = frozenset()

    def test_sizing_population_may_not_name_a_held_out_fact(self) -> None:
        # A contract sized against blind evaluation population is counting a
        # capability claim against facts it is forbidden to discharge, so no
        # dispatch could ever falsify it (ADR-0542, ADR-1510).
        contract = make_contract()
        with self.assertRaisesRegex(contracts_module.ContractError, "HELD-OUT"):
            contracts_module.validate_contract(
                contract, self.facts, None, frozenset({"F:target"})
            )
        # Control: the SAME contract and the SAME facts pass once the
        # partition no longer marks that fact held-out, so this test cannot be
        # satisfied by any other guard.
        contracts_module.validate_contract(
            contract, self.facts, None, self.none_held_out
        )

    def test_exhausted_contract_must_be_retired(self) -> None:
        settled = {"F:target": make_fact("F:target", status="proved")}
        settled["F:other-family"] = make_fact(
            "F:other-family",
            title="Mathlib v4.30 source proposition Int.fib_add",
            statement="Int.fib (m + n) = ...",
        )
        contract = make_contract(
            sizing={
                "date": "2026-09-01",
                "ledger_sha256": "0" * 64,
                "matched_open_ready_count": 0,
                "matched_open_ready_fact_ids": [],
            }
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "ZERO live facts"):
            contracts_module.validate_contract(
                contract, settled, None, self.none_held_out
            )
        # Control: adding the retirement block is the whole fix.
        contract["retirement"] = {
            "date": "2026-09-01",
            "reason": "the family it was sized against was finished by another route",
        }
        contracts_module.validate_contract(contract, settled, None, self.none_held_out)

    def test_retirement_may_not_silence_a_contract_with_live_work(self) -> None:
        contract = make_contract()
        contract["retirement"] = {
            "date": "2026-09-01",
            "reason": "claimed exhausted while a live target remains",
        }
        with self.assertRaisesRegex(
            contracts_module.ContractError, "still matches"
        ):
            contracts_module.validate_contract(
                contract, self.facts, None, self.none_held_out
            )

    def test_live_population_excludes_held_out_and_mutation_fixtures(self) -> None:
        # The three exclusions are what make "zero live facts" mean "nothing
        # this contract may ever be dispatched at", rather than "zero rows the
        # raw predicate returned".
        facts = {
            "F:target": make_fact("F:target"),
            "F:ml430-mutation-deadbeef": make_fact("F:ml430-mutation-deadbeef"),
            "F:blocked": make_fact("F:blocked"),
        }
        facts["F:blocked"]["depends_on"] = ["F:target"]
        live = contracts_module.live_population(
            make_contract()["shape"], facts, frozenset()
        )
        self.assertEqual(live, ["F:target"])
        self.assertEqual(
            contracts_module.live_population(
                make_contract()["shape"], facts, frozenset({"F:target"})
            ),
            [],
        )

    def test_sizing_count_must_agree_with_the_population_it_names(self) -> None:
        contract = make_contract(
            sizing={
                "date": "2026-09-01",
                "ledger_sha256": "0" * 64,
                "matched_open_ready_count": 7,
                "matched_open_ready_fact_ids": ["F:target"],
            }
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "must agree"):
            contracts_module.validate_contract(
                contract, self.facts, None, self.none_held_out
            )

    def test_sizing_ledger_digest_must_be_a_sha256(self) -> None:
        contract = make_contract(
            sizing={
                "date": "2026-09-01",
                "ledger_sha256": "not-a-digest",
                "matched_open_ready_count": 1,
                "matched_open_ready_fact_ids": ["F:target"],
            }
        )
        with self.assertRaisesRegex(contracts_module.ContractError, "sha256 digest"):
            contracts_module.validate_contract(
                contract, self.facts, None, self.none_held_out
            )

    def test_ledger_digest_is_stable_and_status_sensitive(self) -> None:
        # The recorded `sizing.ledger_sha256` is only worth having if it can be
        # re-derived AND it moves when the ledger's statuses move.
        before = contracts_module.ledger_digest(self.facts)
        self.assertEqual(before, contracts_module.ledger_digest(dict(self.facts)))
        moved = copy.deepcopy(self.facts)
        moved["F:target"]["epistemic_status"] = "proved"
        self.assertNotEqual(before, contracts_module.ledger_digest(moved))

    def test_held_out_ids_are_read_from_every_nursery_manifest(self) -> None:
        # The defect this exists to prevent, measured 2026-09-01:
        # `fact-frontier.py` selected a `nursery-v2-extension.json` held-out
        # fact as admissible because its reader named `nursery-v1.json`
        # literally. Reading ONE manifest is the bug; reading the glob is the
        # fix, and this test dies if anyone narrows it back.
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            (directory / "nursery-v1.json").write_text(
                json.dumps({"entries": [{"fact_id": "F:one", "partition": "held-out"}]})
            )
            (directory / "nursery-v2-extension.json").write_text(
                json.dumps({"entries": [{"fact_id": "F:two", "partition": "held-out"}]})
            )
            (directory / "nursery-v3.json").write_text(
                json.dumps({"entries": [{"fact_id": "F:three", "partition": "development"}]})
            )
            self.assertEqual(
                contracts_module.held_out_fact_ids(directory),
                frozenset({"F:one", "F:two"}),
            )

    def test_committed_contracts_carry_the_measured_lifecycle(self) -> None:
        # Not a restatement of the validator: this asserts the two seed
        # contracts are in the state the 2026-09-01 measurement found, so a
        # silent re-sizing or un-retirement is visible.
        facts = contracts_module.load_facts()
        held_out = contracts_module.held_out_fact_ids()
        by_id = {c["id"]: c for _p, c in contracts_module.load_contracts()}
        int_modeq = by_id["producer-contract-int-modeq-family-v1"]
        self.assertIsNotNone(int_modeq.get("retirement"))
        self.assertEqual(
            contracts_module.live_population(int_modeq["shape"], facts, held_out), []
        )
        nat_coprime = by_id["producer-contract-nat-coprime-family-v1"]
        self.assertIsNone(nat_coprime.get("retirement"))
        self.assertNotEqual(
            contracts_module.live_population(nat_coprime["shape"], facts, held_out), []
        )


# Measured 2026-09-01 (lane `flywheel-restart`). `nat-coprime-family-v1`'s shape
# matches ONE held-out fact, and it is not a mistake in the contract: the
# contract was authored 2026-08-27 against a ledger where its matched set was
# clean ("none held-out, checked 2026-08-27", its own `notes`), and
# `nursery-v2-extension.json` preregistered 500 further rows on 2026-08-29 --
# one of which its shape happens to match. A contract cannot be written to
# exclude rows that do not exist yet.
#
# This is a PIN on a known, dated defect, not an allowance. It fails in BOTH
# directions: a second contamination makes the list longer, and a fix makes it
# empty. Do not "fix" it by extending this set -- the standing rule is that a
# stable number can be stably wrong, so every entry names its reason.
#
# The live consequence is deliberately NOT gated here, because it is not the
# contract's to fix: `scripts/fact-frontier.py` selected this exact fact as
# `admissible_via_contract` / `outcome: selected`, and its own held-out screen
# (a) reads `nursery-v1.json` literally and cannot see this row, and (b) is
# applied only to the human-rendered queue line, never to the `--json`
# selection every downstream reader uses. That is a selector change and wants
# its own ADR.
KNOWN_HELD_OUT_SHAPE_MATCHES = {
    "producer-contract-nat-coprime-family-v1": [
        "F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce",
    ],
}


class SeedContractHoldoutIsolationTests(unittest.TestCase):
    """Held-out isolation binds contract shapes exactly as it binds manual
    dispatch (ADR-0542). Checks the PARTITION, never the count -- and reads
    the partition from EVERY `nursery*.json` manifest, because reading one
    file is how this went wrong.
    """

    def test_seed_contracts_match_no_unrecorded_held_out_fact(self) -> None:
        held_out = contracts_module.held_out_fact_ids()
        if not held_out:
            self.skipTest("no nursery manifest in this tree")
        facts = contracts_module.load_facts()
        for _path, contract in contracts_module.load_contracts():
            matched_held_out = sorted(
                fact_id
                for fact_id, fact in facts.items()
                if fact_id in held_out
                and contracts_module.shape_matches(contract["shape"], fact)
            )
            self.assertEqual(
                matched_held_out,
                sorted(KNOWN_HELD_OUT_SHAPE_MATCHES.get(contract["id"], [])),
                f"{contract['id']}: shape/held-out overlap moved. Every overlap must "
                "be recorded in KNOWN_HELD_OUT_SHAPE_MATCHES with its reason; an "
                "unrecorded one means a contract is claiming capability over blind "
                "evaluation population.",
            )

    def test_synthetic_v2_style_manifest_is_detected(self) -> None:
        """The mutation control for THIS class's own detection logic, not
        for `held_out_fact_ids` (that guard has its own direct test above,
        `test_held_out_ids_are_read_from_every_nursery_manifest`).

        Put a freshly-invented held-out id in a SECOND manifest -- named and
        shaped like `nursery-v2-extension.json`, sitting beside an untouched
        `nursery-v1.json` -- and confirm `test_seed_contracts_match_no_
        unrecorded_held_out_fact` above would actually SEE it: a real
        contract's shape, matched against the synthetic held-out set, must
        surface the synthetic id. If this class ever regressed to reading
        only `nursery-v1.json` (the exact 2026-09-01 defect), this id -- only
        ever present in the "v2" file -- would silently vanish from the
        matched set and this test would fail.
        """
        facts = contracts_module.load_facts()
        _path, contract = next(
            (p, c)
            for p, c in contracts_module.load_contracts()
            if c["id"] == "producer-contract-nat-coprime-family-v1"
        )
        already_held_out = contracts_module.held_out_fact_ids()
        candidate = next(
            fact_id
            for fact_id, fact in facts.items()
            if fact_id not in already_held_out
            and contracts_module.shape_matches(contract["shape"], fact)
        )
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            (directory / "nursery-v1.json").write_text(json.dumps({"entries": []}))
            (directory / "nursery-v2-extension.json").write_text(
                json.dumps(
                    {"entries": [{"fact_id": candidate, "partition": "held-out"}]}
                )
            )
            synthetic_held_out = contracts_module.held_out_fact_ids(directory)
        self.assertIn(candidate, synthetic_held_out)
        matched_held_out = sorted(
            fact_id
            for fact_id, fact in facts.items()
            if fact_id in synthetic_held_out
            and contracts_module.shape_matches(contract["shape"], fact)
        )
        self.assertIn(candidate, matched_held_out)

    def test_the_v1_only_reader_is_the_one_that_misses_it(self) -> None:
        # The control for the entry above: confirm the overlap is invisible to
        # a `nursery-v1.json`-only reader and visible to the glob reader. If
        # this ever stops discriminating, the pin above has lost its subject.
        v1_path = ROOT / "artifacts/autogenesis/nursery-v1.json"
        v2_path = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"
        if not (v1_path.is_file() and v2_path.is_file()):
            self.skipTest("both nursery manifests are needed for this control")
        v1_held_out = {
            entry["fact_id"]
            for entry in json.loads(v1_path.read_text())["entries"]
            if entry.get("partition") == "held-out"
        }
        all_held_out = contracts_module.held_out_fact_ids()
        for fact_ids in KNOWN_HELD_OUT_SHAPE_MATCHES.values():
            for fact_id in fact_ids:
                self.assertIn(fact_id, all_held_out)
                self.assertNotIn(fact_id, v1_held_out)


if __name__ == "__main__":
    unittest.main()
