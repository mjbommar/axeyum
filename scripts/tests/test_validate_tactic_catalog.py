#!/usr/bin/env python3
"""Controls for `scripts/validate-tactic-catalog.py`.

One test per rule, each over a corrupt copy of the COMMITTED catalog written to
a temporary directory -- so a rule that stops rejecting is a dead test rather
than a quiet pass.  Registered in `scripts/tests/mutation_controls.py` under
``tactic-catalog``; every guard there is mutation-verified to kill exactly one
of these.

The fixtures deliberately corrupt one field at a time and leave everything else
byte-identical to the committed file, because a fixture that violates several
rules at once cannot tell you which guard caught it.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-tactic-catalog.py"
CATALOG = ROOT / "artifacts/autogenesis/tactic-catalog-v1.json"

_spec = importlib.util.spec_from_file_location("validate_tactic_catalog", SCRIPT)
assert _spec is not None and _spec.loader is not None
validator = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(validator)


def load() -> dict:
    return json.loads(CATALOG.read_text())


def run(doc: dict) -> tuple[list[str], list[str], dict | None]:
    return validator.validate_document(doc, ROOT)


def rules(errors: list[str]) -> set[str]:
    return {error.split("|", 1)[0] for error in errors}


def tactic(doc: dict, tactic_id: str) -> dict:
    for entry in doc["tactics"]:
        if entry["id"] == tactic_id:
            return entry
    raise AssertionError(f"no tactic {tactic_id!r} in the committed catalog")


class CommittedCatalogTests(unittest.TestCase):
    def test_committed_catalog_passes(self) -> None:
        errors, _warnings, counts = run(load())
        self.assertEqual(errors, [])
        assert counts is not None
        self.assertGreaterEqual(counts["tactics"], 9)
        self.assertGreaterEqual(counts["distinct_precondition_shapes"], 2)
        self.assertGreater(counts["accepted_goals"], 0)
        self.assertGreater(counts["declined_goals"], 0)
        self.assertGreaterEqual(counts["realizes_capabilities"], 2)

    def test_every_tactic_has_at_least_one_reach_row(self) -> None:
        """The positive half of the reach-empty rule, stated over the real file."""
        for entry in load()["tactics"]:
            reach = entry["reach"]
            with self.subTest(tactic=entry["id"]):
                self.assertGreater(
                    len(reach["accepted_goals"]) + len(reach["declined_goals"]), 0
                )

    def test_committed_catalog_matches_published_schema(self) -> None:
        """Keeps the stdlib checks and the published schema from drifting apart."""
        try:
            import jsonschema  # noqa: F401
        except ImportError:
            self.skipTest("jsonschema is not installed")
        errors: list[str] = []
        validator.schema_check_published(load(), errors)
        self.assertEqual(errors, [])


class CorruptFixtureTests(unittest.TestCase):
    def test_duplicate_id_is_rejected(self) -> None:
        doc = load()
        doc["tactics"].append(copy.deepcopy(doc["tactics"][0]))
        errors, _warnings, _counts = run(doc)
        self.assertIn("unique-ids", rules(errors))

    def test_missing_implementation_path_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:refl-closure")["implemented_by"]["path"] = (
            "crates/axeyum-lean-import/examples/no_such_producer/mod.rs"
        )
        errors, _warnings, _counts = run(doc)
        self.assertIn("implementation-path", rules(errors))

    def test_symbol_absent_from_the_named_file_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:bounded-structural-induction")["implemented_by"]["symbol"] = (
            "try_no_such_move"
        )
        errors, _warnings, _counts = run(doc)
        self.assertIn("implementation-symbol", rules(errors))

    def test_decline_reason_from_another_producer_is_rejected(self) -> None:
        """`TerminalNotClosed` is real -- in the OTHER producer's enum."""
        doc = load()
        tactic(doc, "T:refl-closure")["decline_reasons"] = ["TerminalNotClosed"]
        errors, _warnings, _counts = run(doc)
        self.assertIn("decline-reason", rules(errors))

    def test_budget_value_that_disagrees_with_the_rust_const_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:bounded-structural-induction")["budget"]["MAX_BINDERS"] = 12
        errors, _warnings, _counts = run(doc)
        self.assertIn("budget", rules(errors))

    def test_capability_absent_from_the_overlay_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:refl-closure")["realizes"] = "K:no-such-capability"
        errors, _warnings, _counts = run(doc)
        self.assertIn("capability", rules(errors))

    def test_technique_pinned_to_a_foreign_revision_is_rejected(self) -> None:
        """ADR-0553. `uses_technique` is required on every tactic, so while its
        `revision` was mandatory no tactic could exist here without pinning a
        sibling repository's commit."""
        doc = load()
        tactic(doc, "T:refl-closure")["uses_technique"]["revision"] = "0" * 40
        errors, _warnings, _counts = run(doc)
        self.assertIn("schema", rules(errors))

    def test_residual_measure_none_without_shape_none_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:bounded-structural-induction")["residual"]["measure"] = "none"
        errors, _warnings, _counts = run(doc)
        self.assertIn("residual-measure", rules(errors))

    def test_tactic_with_no_reach_rows_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:absurd-elimination")["reach"] = {
            "accepted_goals": [],
            "declined_goals": [],
        }
        errors, _warnings, _counts = run(doc)
        self.assertIn("reach-empty", rules(errors))

    def test_catalog_with_one_precondition_shape_is_rejected(self) -> None:
        """A catalog whose entries all match one goal shape is a dispatch table."""
        doc = load()
        shared = copy.deepcopy(doc["tactics"][0]["precondition"])
        for entry in doc["tactics"]:
            entry["precondition"] = copy.deepcopy(shared)
        errors, _warnings, _counts = run(doc)
        self.assertIn("precondition-shapes", rules(errors))

    def test_tactic_kind_outside_the_enum_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:refl-closure")["kind"] = "magic"
        errors, _warnings, _counts = run(doc)
        self.assertIn("schema", rules(errors))

    def test_predicate_kind_outside_the_vocabulary_is_rejected(self) -> None:
        doc = load()
        tactic(doc, "T:refl-closure")["precondition"]["structural"]["all_of"] = [
            {"kind": "declaration-name-matches", "args": {"pattern": "descFactorial"}}
        ]
        errors, _warnings, _counts = run(doc)
        self.assertIn("schema", rules(errors))


class NoExternalResolutionTests(unittest.TestCase):
    """ADR-0553: nothing here resolves a `TQ:` id, and nothing may try.

    This class replaces `TechniqueResolutionTests`, which asserted the OPPOSITE
    contract -- that an absent sibling produced one warning per tactic, and a
    present one on pin resolved every technique to a `graph/techniques/*.md`
    file. Those three tests were the strongest evidence that the coupling was a
    live integration and not merely a label.
    """

    def test_the_committed_catalog_produces_no_warnings(self) -> None:
        """Nine `checkout is absent` warnings used to be the normal output."""
        _errors, warnings, _counts = run(load())
        self.assertEqual(warnings, [])

    def test_an_overlay_declaring_an_external_source_is_rejected(self) -> None:
        """The catalog reads the overlay. If the overlay reacquires an external
        source, every tactic is pinned to it again at one remove."""
        overlay = json.loads(
            (ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text()
        )
        overlay["sources"].append(
            {
                "id": "sibling",
                "kind": "external-repository",
                "revision_policy": "pinned",
                "revision": "0" * 40,
            }
        )
        # Drive the guard directly. Routing through `validate_document` with a
        # scratch root ALSO trips `implemented_by.path must exist`, and the
        # mutation harness then reports two guards killing this one test --
        # which is the shared-rejection-path shape this suite exists to avoid.
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            (root / "artifacts/autogenesis").mkdir(parents=True)
            (root / "artifacts/autogenesis/knowledge-overlay-v1.json").write_text(
                json.dumps(overlay)
            )
            errors: list[str] = []
            validator.overlay_capabilities(root, errors)
        self.assertTrue(
            any("declares an external source" in error for error in errors), errors
        )

    def test_the_validator_holds_no_path_outside_the_checkout(self) -> None:
        source = SCRIPT.read_text()
        self.assertNotIn("ROOT.parent", source)
        self.assertNotIn("math-education", source.split('"""', 2)[-1])


class CommandLineTests(unittest.TestCase):
    """The exit status has to depend on the finding, not on the run completing."""

    def test_committed_catalog_exits_zero_and_prints_the_census(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(SCRIPT)],
            capture_output=True, text=True, cwd=str(ROOT), check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("TACTIC_CATALOG|tactics=", completed.stdout)

    def test_unreadable_catalog_exits_nonzero(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            broken = Path(scratch) / "tactic-catalog-v1.json"
            broken.write_text("{ not json")
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), str(broken)],
                capture_output=True, text=True, cwd=str(ROOT), check=False,
            )
        self.assertEqual(completed.returncode, 1)
        self.assertNotIn("TACTIC_CATALOG|tactics=", completed.stdout)


if __name__ == "__main__":
    unittest.main()
