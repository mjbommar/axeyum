"""Controls for `check-carrier-correspondence.py`.

Passing on the committed ledger proves nothing on its own -- every guard is
driven to fail here with a minimal fixture, plus one clean fixture that must
pass every guard at once. Mutation-verify with `scripts/tests/mutation_controls.py`
(never a hand loop, never in the shared tree): deleting each guard (G0-G8)
must kill EXACTLY the test named for it.
"""

from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_carrier_correspondence", ROOT / "scripts" / "check-carrier-correspondence.py"
)
assert SPEC and SPEC.loader
CC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CC)


def make_row(**overrides) -> dict:
    row = {
        "schema_version": 1,
        "kind": "axeyum-carrier-correspondence",
        "id": "CC:example-row",
        "title": "Example carrier against its Mathlib counterpart, for tests only",
        "axeyum": {
            "carrier": "Example.Carrier",
            "source_location": "crates/axeyum-lean-kernel/src/example.rs:1",
            "verification": "verified-in-kernel-projection",
            "verification_detail": "test fixture",
            "equality_regime": "eq",
            "equality_regime_note": "Literal Eq, for a test fixture only.",
        },
        "mathlib": {
            "counterpart": "ExampleCounterpart",
            "module_path": "Mathlib.Example.Basic",
            "source_location": "Mathlib/Example/Basic.lean:1",
            "verification": "verified-in-pinned-checkout",
            "verification_detail": "test fixture",
            "equality_regime": "eq",
            "equality_regime_note": "Ordinary Eq typeclass, for a test fixture.",
        },
        "grade": "same-statement",
        "reason": "A test fixture reason string that is long enough to clear the schema's floor.",
        "witness": [
            {
                "axeyum_theorem": "Example.Carrier.law",
                "axeyum_location": "crates/axeyum-lean-kernel/src/example.rs:2",
                "axeyum_verification": "verified-in-kernel-projection",
                "mathlib_theorem": "example_law",
                "mathlib_location": "Mathlib/Example/Basic.lean:2",
                "note": "A test fixture witness note, long enough to clear the floor.",
            }
        ],
        "provenance": {
            "date": "2026-09-05",
            "established_by": "test fixture, not a real lane",
            "sources": ["scripts/tests/test_check_carrier_correspondence.py"],
        },
    }
    row.update(overrides)
    return row


def ledger(rows: list[dict]) -> dict:
    return {"schema_version": 1, "kind": "axeyum-carrier-correspondence-ledger", "rows": rows}


# A coverage-satisfying ledger: one row whose carrier text mentions every
# REQUIRED_COVERAGE family, so guard-specific fixtures below don't ALSO trip
# G7 as an unrelated side effect (each test should kill exactly its own guard).
COVERING_CARRIER = " / ".join(CC.REQUIRED_COVERAGE)
KERNEL_IDS = {"Example.Carrier.law", "Example.Carrier"}


def clean_ledger() -> dict:
    return ledger([make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})])


class CleanFixturePasses(unittest.TestCase):
    def test_clean_ledger_has_no_violations(self) -> None:
        problems, stats = CC.check_document(clean_ledger(), KERNEL_IDS)
        self.assertEqual(problems, [], problems)
        self.assertEqual(stats["rows"], 1)


class EachGuardCanFail(unittest.TestCase):
    def test_g0_duplicate_id(self) -> None:
        row_a = make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})
        row_b = copy.deepcopy(row_a)  # same id as row_a
        problems, _ = CC.check_document(ledger([row_a, row_b]), KERNEL_IDS)
        self.assertTrue(any("duplicate `id`" in p for p in problems), problems)

    def test_g1_grade_not_in_closed_enum(self) -> None:
        row = make_row(
            axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER},
            grade="probably-the-same",
        )
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("is not one of" in p and "grade" in p for p in problems), problems)

    def test_g2_witness_required_but_missing(self) -> None:
        row = make_row(
            axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER},
            grade="different-object",
            witness=[],
        )
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("witness` is empty" in p for p in problems), problems)

    def test_g2_witness_forbidden_but_present(self) -> None:
        base = make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})
        row = make_row(
            axeyum=base["axeyum"],
            grade="no-counterpart",
            mathlib={
                "counterpart": None, "module_path": None, "source_location": None,
                "verification": "not-applicable", "equality_regime": "none",
                "equality_regime_note": "no counterpart to compare against",
            },
            witness=base["witness"],  # non-empty, which is the violation
        )
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("witness` is non-empty" in p for p in problems), problems)

    def test_g3_no_counterpart_mathlib_side_not_null(self) -> None:
        row = make_row(
            axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER},
            grade="no-counterpart",
            witness=[],
            # mathlib.counterpart left non-null -- the violation
        )
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("mathlib.counterpart is not null" in p for p in problems), problems)

    def test_g4_kernel_projection_name_does_not_resolve(self) -> None:
        row = make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})
        row["witness"][0]["axeyum_theorem"] = "Example.Carrier.doesNotExist"
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(
            any("is not in artifacts/autogenesis/kernel-dependency-projection-v1.json" in p for p in problems),
            problems,
        )

    def test_g5_empty_ledger_is_a_violation(self) -> None:
        problems, _ = CC.check_document(ledger([]), KERNEL_IDS)
        self.assertTrue(any("ZERO rows" in p for p in problems), problems)

    def test_g6_no_row_cites_the_kernel_projection(self) -> None:
        row = make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})
        row["witness"][0]["axeyum_verification"] = "verified-in-source-only"
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("zero witnesses across the ledger claim" in p for p in problems), problems)

    def test_g7_coverage_floor_missing_a_required_family(self) -> None:
        row = make_row()  # carrier is "Example.Carrier", not the covering string
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("coverage floor" in p for p in problems), problems)

    def test_g8_mathlib_theorem_and_location_must_be_null_together(self) -> None:
        row = make_row(axeyum={**make_row()["axeyum"], "carrier": COVERING_CARRIER})
        row["witness"][0]["mathlib_theorem"] = None  # location stays non-null -- the violation
        problems, _ = CC.check_document(ledger([row]), KERNEL_IDS)
        self.assertTrue(any("must be null together or present together" in p for p in problems), problems)

    def test_kernel_projection_file_missing_is_its_own_violation(self) -> None:
        problems: list[str] = []
        # Exercise the real function against a path that cannot exist, via
        # monkeypatching the module-level constant rather than the filesystem.
        original = CC.KERNEL_PROJECTION
        try:
            CC.KERNEL_PROJECTION = ROOT / "artifacts" / "autogenesis" / "does-not-exist-v1.json"
            ids = CC.load_kernel_declaration_ids(problems)
        finally:
            CC.KERNEL_PROJECTION = original
        self.assertEqual(ids, set())
        self.assertTrue(any("does not exist" in p for p in problems), problems)


if __name__ == "__main__":
    unittest.main()
