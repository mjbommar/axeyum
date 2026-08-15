"""Contract tests for the derived Lean axiom ledger.

Two things are under test and they are different. The first is that the
committed ledger agrees with the kernel *right now* — one Cargo-backed
measurement, taken once. The second, and the reason this file exists at all, is
that the gate **fires**: the previous ledger transcribed `integer: 34` into
seven places and kept publishing it for two days after the Int development was
proved down to 1, because nothing compared the published number to a
measurement. Every negative control below mutates a captured measurement rather
than the kernel, so the drift cases run without a rebuild.
"""

from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_axiom_ledger",
    ROOT / "scripts" / "gen-lean-axiom-ledger.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


def clone(measurement: GEN.Measurement) -> GEN.Measurement:
    return GEN.Measurement(
        copy.deepcopy(measurement.axiom_rows),
        copy.deepcopy(measurement.surface_rows),
        copy.deepcopy(measurement.surface_counts),
    )


class LeanAxiomLedgerContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        # One Cargo-backed measurement for the whole suite; the mutation tests
        # then work on copies of it.
        cls.measurement = GEN.measure()

    def setUp(self) -> None:
        self.data = GEN.load_manifest()

    def failures(self, measurement: GEN.Measurement | None = None) -> list[str]:
        return GEN.validate_manifest(self.data, measurement or self.measurement)

    # ---- the committed state agrees with the kernel ----------------------

    def test_committed_ledger_matches_the_runtime_measurement(self) -> None:
        self.assertEqual(self.failures(), [])
        counts = Counter(row["prelude"] for row in self.measurement.axiom_rows)
        # Asserted against the manifest, not against a number typed here: a
        # literal in this file is exactly the defect being fixed.
        self.assertEqual(
            dict(counts),
            {
                prelude: value
                for prelude, value in self.data["measurement"]["axiom_counts"].items()
                if prelude != "total" and value
            },
        )
        self.assertEqual(
            len(self.measurement.axiom_rows),
            self.data["measurement"]["axiom_counts"]["total"],
        )

    def test_coverage_includes_the_axiom_free_preludes(self) -> None:
        surface = self.measurement.surface_counts
        # The whole point of the second measurement: a prelude with no axioms
        # must still be *named*, or zero is indistinguishable from unmeasured.
        self.assertTrue({"nat", "logic"} <= set(surface))
        for prelude in ("nat", "logic"):
            self.assertEqual(surface[prelude]["total_trusted"], 0)

    def test_render_is_deterministic_and_states_the_measured_numbers(self) -> None:
        first = GEN.render(self.data)
        second = GEN.render(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        total = self.data["measurement"]["axiom_counts"]["total"]
        self.assertIn(f"**{total} total assumptions:**", first)
        self.assertIn(self.data["trust_policy"]["publication_rule"], first)
        self.assertIn(
            f"**{len(self.data['retired_entries'])} assumptions have been retired**",
            first,
        )

    # ---- the derived block cannot be edited by hand -----------------------

    def test_a_hand_edited_count_fails(self) -> None:
        self.data["measurement"]["axiom_counts"]["integer"] += 33
        self.assertTrue(
            any("measurement block is stale" in failure for failure in self.failures())
        )

    def test_a_hand_edited_trusted_surface_fails(self) -> None:
        self.data["measurement"]["trusted_surface"]["nat"]["axiom"] = 7
        self.assertTrue(
            any("measurement block is stale" in failure for failure in self.failures())
        )

    def test_a_stale_publication_rule_fails(self) -> None:
        self.data["trust_policy"]["integer_assumptions"] = 34
        self.assertTrue(
            any("trust_policy is stale" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        self.data["trust_policy"]["publication_rule"] = "axiom-free"
        self.assertTrue(
            any("trust_policy is stale" in failure for failure in self.failures())
        )

    def test_trust_policy_must_name_an_existing_adr(self) -> None:
        self.data["trust_policy"]["adr"] = "docs/research/09-decisions/adr-9999-no.md"
        self.assertTrue(
            any(
                "trust_policy.adr must name an existing file" in failure
                for failure in self.failures()
            )
        )

    # ---- the population cannot move silently ------------------------------

    def test_a_discharged_axiom_fails_until_it_is_filed_as_retired(self) -> None:
        shrunk = clone(self.measurement)
        victim = shrunk.axiom_rows.pop()
        shrunk.surface_rows = [
            row
            for row in shrunk.surface_rows
            if not (
                row["prelude"] == victim["prelude"] and row["name"] == victim["name"]
            )
        ]
        shrunk.surface_counts[victim["prelude"]]["axiom"] -= 1
        shrunk.surface_counts[victim["prelude"]]["total_trusted"] -= 1
        failures = self.failures(shrunk)
        self.assertTrue(
            any("the kernel no longer admits" in failure for failure in failures),
            failures,
        )
        self.assertTrue(
            any("--accept-population-change" in failure for failure in failures)
        )

        # ...and the deliberate acceptance clears it, filing the row rather
        # than deleting it.
        arrived, departed = GEN.accept_population_change(
            self.data,
            shrunk,
            "2026-08-15",
            "proved out",
            ["scripts/gen-lean-axiom-ledger.py"],
        )
        self.assertEqual(arrived, [])
        self.assertEqual(departed, [f"{victim['prelude']}::{victim['name']}"])
        GEN.refresh(self.data, shrunk)
        # Only the population complaint must be gone.  The live-document scan
        # still objects, because a synthetic measurement makes the committed
        # prose stale -- which is the scan doing its job, not a defect here.
        self.assertEqual(
            GEN.validate_rows(self.data["entries"], shrunk)
            + GEN.validate_retired(
                self.data["retired_entries"], self.data["entries"], shrunk
            ),
            [],
        )
        self.assertIn(
            (victim["prelude"], victim["name"]),
            {GEN.entry_key(row) for row in self.data["retired_entries"]},
        )

    def test_a_new_axiom_fails_until_it_is_accepted(self) -> None:
        grown = clone(self.measurement)
        template = grown.axiom_rows[0]
        invented = {**template, "name": "Real.zzz_invented"}
        grown.axiom_rows.append(invented)
        grown.axiom_rows.sort(key=GEN.entry_key)
        grown.surface_rows.append({**invented, "kind": "axiom"})
        grown.surface_counts["real"]["axiom"] += 1
        grown.surface_counts["real"]["total_trusted"] += 1
        self.assertTrue(
            any(
                "ledger is missing admitted axioms" in failure
                for failure in self.failures(grown)
            )
        )

    def test_retired_row_cannot_be_live_or_still_admitted(self) -> None:
        revived = copy.deepcopy(self.data["entries"][0])
        revived.update(
            {
                "retired_on": "2026-08-15",
                "retirement_note": "n/a",
                "retirement_evidence": ["scripts/gen-lean-axiom-ledger.py"],
            }
        )
        self.data["retired_entries"].append(revived)
        self.data["retired_entries"].sort(key=GEN.entry_key)
        failures = self.failures()
        self.assertTrue(any("is both live and retired" in f for f in failures))
        self.assertTrue(
            any("kernel still admits it as an axiom" in f for f in failures)
        )

    def test_retired_rows_need_a_date_note_and_real_evidence(self) -> None:
        self.data["retired_entries"][0]["retired_on"] = "whenever"
        self.data["retired_entries"][0]["retirement_note"] = ""
        self.data["retired_entries"][0]["retirement_evidence"] = ["nope/missing.md"]
        failures = self.failures()
        self.assertTrue(any("retired_on must be an ISO date" in f for f in failures))
        self.assertTrue(any("missing non-empty retirement_note" in f for f in failures))
        self.assertTrue(any("missing retirement evidence" in f for f in failures))

    # ---- the two measurements police each other ---------------------------

    def test_a_prelude_dropping_out_of_coverage_fails(self) -> None:
        blind = clone(self.measurement)
        del blind.surface_counts["integer"]
        blind.surface_rows = [
            row for row in blind.surface_rows if row["prelude"] != "integer"
        ]
        with self.assertRaises(GEN.LedgerError) as caught:
            GEN.cross_check(blind)
        self.assertIn("no coverage line", str(caught.exception))

    def test_the_two_inventories_must_agree_on_counts(self) -> None:
        skewed = clone(self.measurement)
        skewed.surface_counts["real"]["axiom"] += 1
        with self.assertRaises(GEN.LedgerError) as caught:
            GEN.cross_check(skewed)
        self.assertIn("the two inventories disagree on real", str(caught.exception))

    def test_the_two_inventories_must_agree_on_canonical_types(self) -> None:
        skewed = clone(self.measurement)
        for row in skewed.surface_rows:
            if row["kind"] == "axiom":
                row["canonical_type"] += " "
                break
        with self.assertRaises(GEN.LedgerError) as caught:
            GEN.cross_check(skewed)
        self.assertIn("render different canonical types", str(caught.exception))

    def test_a_surface_run_with_no_coverage_lines_is_an_error(self) -> None:
        with self.assertRaises(GEN.LedgerError) as caught:
            GEN.parse_trusted_surface("", "Compiling axeyum-lean-kernel v0.1.0\n")
        self.assertIn("no per-prelude coverage lines", str(caught.exception))

    def test_declared_coverage_must_match_emitted_rows(self) -> None:
        with self.assertRaises(GEN.LedgerError) as caught:
            GEN.parse_trusted_surface(
                "", "nat: axiom=3 opaque=0 quotient=0 total_trusted=3\n"
            )
        self.assertIn("declared axiom=3 but emitted 0 rows", str(caught.exception))

    # ---- rows keep their reviewed shape -----------------------------------

    def test_name_preserving_type_and_digest_drift_fail(self) -> None:
        self.data["entries"][0]["canonical_type"] += " "
        failures = self.failures()
        self.assertTrue(any("canonical type drift" in failure for failure in failures))
        self.assertTrue(
            any("stored type and digest disagree" in failure for failure in failures)
        )

        self.data = GEN.load_manifest()
        self.data["entries"][0]["type_sha256"] = "0" * 64
        failures = self.failures()
        self.assertTrue(any("type digest drift" in failure for failure in failures))

    def test_classification_and_discharge_states_are_closed_enums(self) -> None:
        self.data["entries"][0]["classification"] = "probably-okay"
        self.assertTrue(any("invalid classification" in f for f in self.failures()))

        self.data = GEN.load_manifest()
        self.data["entries"][0]["discharge_status"] = "done-ish"
        self.assertTrue(any("invalid discharge_status" in f for f in self.failures()))

    def test_discharged_requires_retained_repository_evidence(self) -> None:
        self.data["entries"][0]["discharge_status"] = "discharged"
        self.assertTrue(
            any("discharged row requires retained evidence" in f for f in self.failures())
        )

    def test_derivable_theorem_cannot_be_retained_as_an_axiom(self) -> None:
        self.data["entries"][0]["classification"] = "derivable-theorem"
        self.data["entries"][0]["discharge_status"] = "retained"
        self.assertTrue(
            any("derivable theorem cannot be retained" in f for f in self.failures())
        )

    # ---- documents that cite the counts -----------------------------------

    def test_every_declared_live_document_states_a_current_count(self) -> None:
        counts = self.measurement.axiom_counts
        self.assertTrue(self.data["live_documents"])
        for path_text in self.data["live_documents"]:
            text = (ROOT / path_text).read_text(encoding="utf-8")
            self.assertEqual(GEN.scan_live_document(path_text, text, counts), [])

    def test_a_stale_count_in_a_cited_document_fails(self) -> None:
        counts = self.measurement.axiom_counts
        failures = GEN.scan_live_document(
            "fake.md", "real 30, integer 34, string 1 today", counts
        )
        self.assertTrue(any("stale ledger count" in failure for failure in failures))
        self.assertTrue(any("integer=34" in failure for failure in failures))

    def test_a_document_that_stops_citing_the_ledger_fails(self) -> None:
        # The cheapest way to pass a stale-number scan is to delete the
        # sentence.  Liveness makes that a failure instead of a silent pass.
        failures = GEN.scan_live_document("fake.md", "no numbers here at all", {})
        self.assertTrue(
            any("states no recognised count claim" in failure for failure in failures)
        )

    def test_every_anchored_pattern_recognises_a_current_claim(self) -> None:
        # A pattern that matches nothing anywhere is a pattern that gates
        # nothing.  Each must fire on at least one declared document.
        corpus = "\n".join(
            (ROOT / path).read_text(encoding="utf-8")
            for path in self.data["live_documents"]
        )
        for label, pattern, _ in GEN.COUNT_CLAIM_PATTERNS:
            with self.subTest(pattern=label):
                self.assertRegex(corpus, pattern)


if __name__ == "__main__":
    unittest.main()
