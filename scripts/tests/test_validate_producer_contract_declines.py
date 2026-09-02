#!/usr/bin/env python3
"""Fail-closed controls for the contract-driven decline validator (doc 291)."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-producer-contract-declines.py"
SPEC = importlib.util.spec_from_file_location("validate_producer_contract_declines", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
declines_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(declines_module)


def make_contract(**overrides) -> dict:
    contract = {
        "schema_version": 1,
        "id": "producer-contract-test-decline-fixture-v1",
        "title": "Test fixture contract",
        "route": "kernel-lane",
        "recipe": {"description": "A test-only recipe."},
        "shape": {
            "formal_language": ["lean4-surface"],
            "fragments": ["Int"],
            "statement_contains": "[ZMOD ",
        },
        "non_examples": [
            {"fact_id": "F:other-family", "reason": "different family"}
        ],
    }
    contract.update(overrides)
    return contract


def make_decline(**overrides) -> dict:
    decline = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-test-decline-v1",
        "contract": "artifacts/autogenesis/producer-contracts/int-modeq-family-v1.json",
        "contract_sha256": "a" * 64,
        "fact_id": "F:target",
        "producer": {
            "tool": "crates/axeyum-lean-import/examples/modeq_family_operation.rs",
            "result": "declined",
            "decline_reason": "TerminalNotClosed",
            "decline_message": "terminal goal is not an Eq/Iff shape this schema can close",
        },
    }
    decline.update(overrides)
    return decline


class StructuralIdentificationTests(unittest.TestCase):
    def test_contract_and_fact_id_and_declined_result_is_decline_shaped(self) -> None:
        self.assertTrue(declines_module.is_contract_decline_shaped(make_decline()))

    def test_missing_contract_key_is_not_decline_shaped(self) -> None:
        # This is exactly the shape of the eleven pre-ADR-0602 decline files:
        # no top-level `contract` key. They must be silently skipped, never
        # rejected.
        older_style = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-mathlib-int-fib-eq-zero-exact-decline-v1",
            "driver": {"cargo_check": "passed", "clippy": "failed"},
            "state": "driver-typechecks-but-clippy-declines",
        }
        self.assertFalse(declines_module.is_contract_decline_shaped(older_style))

    def test_result_not_declined_is_not_decline_shaped(self) -> None:
        not_a_decline = make_decline()
        not_a_decline["producer"]["result"] = "accepted"
        self.assertFalse(declines_module.is_contract_decline_shaped(not_a_decline))

    def test_non_dict_is_not_decline_shaped(self) -> None:
        self.assertFalse(declines_module.is_contract_decline_shaped("not a dict"))
        self.assertFalse(declines_module.is_contract_decline_shaped(None))
        self.assertFalse(declines_module.is_contract_decline_shaped([1, 2, 3]))


class DeclineValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.facts = {
            "F:target": {"id": "F:target", "epistemic_status": "open"},
            "F:other-family": {"id": "F:other-family", "epistemic_status": "open"},
        }

    def test_well_formed_decline_against_real_contract_passes(self) -> None:
        declines_module.validate_decline(make_decline(), self.facts)

    def test_fact_id_must_resolve_to_a_real_fact(self) -> None:
        decline = make_decline(fact_id="F:does-not-exist")
        with self.assertRaisesRegex(declines_module.DeclineError, "does not resolve to any fact"):
            declines_module.validate_decline(decline, self.facts)

    def test_contract_path_must_resolve_to_a_real_file(self) -> None:
        decline = make_decline(contract="artifacts/autogenesis/producer-contracts/does-not-exist-v1.json")
        with self.assertRaisesRegex(declines_module.DeclineError, "does not resolve to a real file"):
            declines_module.validate_decline(decline, self.facts)

    def test_contract_path_must_resolve_under_the_contracts_directory(self) -> None:
        # A decline pointing outside producer-contracts/ (e.g. at an operation
        # registry or a fact) is not a contract reference at all.
        decline = make_decline(contract="artifacts/autogenesis/operations.json")
        with self.assertRaisesRegex(declines_module.DeclineError, "does not resolve under"):
            declines_module.validate_decline(decline, self.facts)

    def test_free_text_decline_reason_is_rejected(self) -> None:
        # THE central loophole guard: a decline reason that is prose rather
        # than a typed identifier cannot be checked, and free text is exactly
        # how a decline could be used to "make the selector shut up" about a
        # fact with no real producer attempt behind it.
        decline = make_decline()
        decline["producer"]["decline_reason"] = "we tried and it did not work out"
        with self.assertRaisesRegex(declines_module.DeclineError, "not a typed identifier"):
            declines_module.validate_decline(decline, self.facts)

    def test_lowercase_leading_reason_is_rejected(self) -> None:
        decline = make_decline()
        decline["producer"]["decline_reason"] = "terminalNotClosed"
        with self.assertRaisesRegex(declines_module.DeclineError, "not a typed identifier"):
            declines_module.validate_decline(decline, self.facts)

    def test_empty_decline_reason_is_rejected(self) -> None:
        decline = make_decline()
        decline["producer"]["decline_reason"] = ""
        with self.assertRaisesRegex(declines_module.DeclineError, "not a typed identifier"):
            declines_module.validate_decline(decline, self.facts)

    def test_result_must_be_exactly_declined(self) -> None:
        decline = make_decline()
        decline["producer"]["result"] = "proved"
        with self.assertRaisesRegex(declines_module.DeclineError, 'must be exactly "declined"'):
            declines_module.validate_decline(decline, self.facts)

    def test_empty_tool_is_rejected(self) -> None:
        decline = make_decline()
        decline["producer"]["tool"] = ""
        with self.assertRaisesRegex(declines_module.DeclineError, "producer.tool must be a non-empty string"):
            declines_module.validate_decline(decline, self.facts)

    def test_empty_decline_message_is_rejected(self) -> None:
        decline = make_decline()
        decline["producer"]["decline_message"] = ""
        with self.assertRaisesRegex(declines_module.DeclineError, "decline_message must be a non-empty string"):
            declines_module.validate_decline(decline, self.facts)

    def test_malformed_contract_sha256_is_rejected(self) -> None:
        decline = make_decline(contract_sha256="not-a-sha")
        with self.assertRaisesRegex(declines_module.DeclineError, "64-character lowercase hex"):
            declines_module.validate_decline(decline, self.facts)

    def test_short_contract_sha256_is_rejected(self) -> None:
        decline = make_decline(contract_sha256="a" * 63)
        with self.assertRaisesRegex(declines_module.DeclineError, "64-character lowercase hex"):
            declines_module.validate_decline(decline, self.facts)

    def test_missing_top_level_key_is_rejected(self) -> None:
        for key in declines_module.DECLINE_TOP_LEVEL_REQUIRED:
            decline = make_decline()
            del decline[key]
            with self.assertRaisesRegex(declines_module.DeclineError, "missing required key"):
                declines_module.validate_decline(decline, self.facts)

    def test_missing_producer_key_is_rejected(self) -> None:
        for key in declines_module.PRODUCER_REQUIRED:
            decline = make_decline()
            del decline["producer"][key]
            with self.assertRaisesRegex(declines_module.DeclineError, "producer missing required key"):
                declines_module.validate_decline(decline, self.facts)

    def test_wrong_schema_version_is_rejected(self) -> None:
        decline = make_decline(schema_version=2)
        with self.assertRaisesRegex(declines_module.DeclineError, "schema_version must be 1"):
            declines_module.validate_decline(decline, self.facts)

    def test_malformed_fact_id_is_rejected(self) -> None:
        decline = make_decline(fact_id="not-a-fact-id")
        with self.assertRaisesRegex(declines_module.DeclineError, "is malformed"):
            declines_module.validate_decline(decline, self.facts)


class RealLedgerTests(unittest.TestCase):
    """End-to-end over the real committed ledger and the real seed decline."""

    def test_committed_declines_are_valid(self) -> None:
        facts = declines_module.load_facts()
        declines = declines_module.validate_declines_dir(facts=facts)
        self.assertGreaterEqual(len(declines), 1)
        fact_ids = {d["fact_id"] for d in declines}
        self.assertIn("F:ml430-int-add-modeq-left-ee732b5b", fact_ids)

    def test_older_decline_files_are_not_picked_up(self) -> None:
        # The eleven pre-ADR-0602 decline files must never be treated as
        # contract-driven declines: none carries a top-level `contract` key.
        _, loaded = declines_module.load_declines()[0]
        found_paths = {path.name for path, _ in declines_module.load_declines()}
        self.assertNotIn("mathlib-int-fib-eq-zero-exact-decline-v1.json", found_paths)
        self.assertNotIn("euclidean-bounded-induction-decline-v1.json", found_paths)

    def test_main_reports_ok_on_the_committed_ledger(self) -> None:
        self.assertEqual(declines_module.main(), 0)


class DuplicateAndDirScanTests(unittest.TestCase):
    def test_load_declines_skips_non_decline_json_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            (directory / "not-a-decline.json").write_text(json.dumps({"foo": "bar"}))
            (directory / "a-decline.json").write_text(json.dumps(make_decline()))
            found = declines_module.load_declines(directory)
            self.assertEqual(len(found), 1)
            self.assertEqual(found[0][0].name, "a-decline.json")

    def test_unparseable_json_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            (directory / "broken.json").write_text("{not json")
            with self.assertRaises(declines_module.DeclineError):
                declines_module.load_declines(directory)


def make_resolution(**overrides) -> dict:
    resolution = {
        "date": "2026-09-01",
        "route": "kernel-lane",
        # Any path that really exists in this repository; the guard checks the
        # filesystem, not this particular file.
        "closed_by": "crates/axeyum-lean-kernel/src/nat_prelude/primes.rs",
        "diagnosis_status": "not-re-executed",
    }
    resolution.update(overrides)
    return resolution


class DeclineLifecycleTests(unittest.TestCase):
    """ADR-1510 rule 2: a decline dies with its fact.

    One test per guard, and each is expected to be the ONLY test that dies
    when its guard is deleted (`scripts/tests/mutation_controls.py
    producer-contract-declines`).
    """

    def setUp(self) -> None:
        self.open_facts = {"F:target": {"id": "F:target", "epistemic_status": "open"}}
        self.settled_facts = {
            "F:target": {"id": "F:target", "epistemic_status": "proved"}
        }

    def test_settled_fact_without_a_resolution_is_rejected(self) -> None:
        # The measured failure mode: 26 of 27 live suppressions named facts
        # that were already proved, and nothing could tell them apart from a
        # decline suppressing live work.
        with self.assertRaisesRegex(declines_module.DeclineError, "no `resolution` block"):
            declines_module.validate_decline(make_decline(), self.settled_facts)
        # Control: the SAME decline against the SAME settled fact passes once
        # the resolution is there, so this cannot be satisfied by another guard.
        declines_module.validate_decline(
            make_decline(resolution=make_resolution()), self.settled_facts
        )

    def test_open_fact_with_a_resolution_is_rejected(self) -> None:
        # The inverse direction. Without it, a lane could write a resolution
        # ahead of time and permanently silence the guard above while the work
        # is still outstanding.
        decline = make_decline(resolution=make_resolution())
        with self.assertRaisesRegex(declines_module.DeclineError, "still open"):
            declines_module.validate_decline(decline, self.open_facts)

    def test_resolution_closed_by_must_resolve_to_a_real_path(self) -> None:
        decline = make_decline(
            resolution=make_resolution(closed_by="crates/axeyum-lean-kernel/src/no_such_module.rs")
        )
        with self.assertRaisesRegex(
            declines_module.DeclineError, "does not resolve to a real path"
        ):
            declines_module.validate_decline(decline, self.settled_facts)

    def test_resolution_route_must_be_a_producer_route(self) -> None:
        decline = make_decline(resolution=make_resolution(route="by-hand"))
        with self.assertRaisesRegex(declines_module.DeclineError, "resolution.route"):
            declines_module.validate_decline(decline, self.settled_facts)

    def test_diagnosis_status_is_three_valued_not_a_boolean(self) -> None:
        # A boolean here would let "nobody re-checked" be recorded as "still
        # accurate", which is the checker-that-cannot-fail defect moved into
        # the data. 19 of the 26 backfilled resolutions are exactly that case.
        for bad in (True, "yes", "still-accurate"):
            decline = make_decline(resolution=make_resolution(diagnosis_status=bad))
            with self.assertRaisesRegex(
                declines_module.DeclineError, "diagnosis_status"
            ):
                declines_module.validate_decline(decline, self.settled_facts)
        for good in sorted(declines_module.DIAGNOSIS_STATUSES):
            declines_module.validate_decline(
                make_decline(resolution=make_resolution(diagnosis_status=good)),
                self.settled_facts,
            )

    def test_resolution_rejects_unknown_and_missing_keys(self) -> None:
        missing = make_resolution()
        del missing["closed_by"]
        with self.assertRaisesRegex(declines_module.DeclineError, "missing required key"):
            declines_module.validate_decline(
                make_decline(resolution=missing), self.settled_facts
            )
        extra = make_resolution(proved=True)
        with self.assertRaisesRegex(declines_module.DeclineError, "unexpected key"):
            declines_module.validate_decline(
                make_decline(resolution=extra), self.settled_facts
            )

    def test_committed_ledger_has_a_resolution_for_every_settled_decline(self) -> None:
        # Derived from the AUTHORITY (each decline's own fact), never from a
        # literal count: a test named "every settled decline" that iterated a
        # hand-written list would measure the maintainer's memory instead.
        facts = declines_module.load_facts()
        settled_without_resolution = []
        resolved_but_open = []
        for path, decline in declines_module.load_declines():
            fact = facts[decline["fact_id"]]
            settled = fact.get("epistemic_status") not in declines_module.OPEN_STATUSES
            has_resolution = decline.get("resolution") is not None
            if settled and not has_resolution:
                settled_without_resolution.append(path.name)
            if not settled and has_resolution:
                resolved_but_open.append(path.name)
        self.assertEqual(settled_without_resolution, [])
        self.assertEqual(resolved_but_open, [])

    def test_every_committed_resolution_names_an_artifact_that_exists(self) -> None:
        for path, decline in declines_module.load_declines():
            resolution = decline.get("resolution")
            if resolution is None:
                continue
            self.assertTrue(
                (ROOT / resolution["closed_by"]).exists(),
                f"{path.name}: resolution.closed_by {resolution['closed_by']!r} is gone",
            )


if __name__ == "__main__":
    unittest.main()
