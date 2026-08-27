"""Focused tests for `scripts/gen-kernel-facts.py`.

Each test targets one guard; `scripts/tests/mutation_controls.py kernel-facts`
deletes guards one at a time and requires each deletion to kill exactly one
test.

The tests that matter most here are the ones about REFUSAL and about the
provenance marker, because this generator's whole risk is bulk-producing facts
whose checkers cannot fail. Two of them therefore run `/usr/bin/grep` for real
against the emitted pattern -- deliberately the system grep and not the
interactive `grep` shell function, which on this host wraps `ugrep` and
disagrees with GNU grep about `\\t`. Asserting a pattern's TEXT would not have
caught the 54-fact `\\t` incident this ledger has already had; running it does.

No test invokes cargo. `parse_projection` and `build_batch` are driven from
synthetic TSV in the tool's own eight-field shape.
"""

from __future__ import annotations

import importlib.util
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-kernel-facts.py"
SPEC = importlib.util.spec_from_file_location("gen_kernel_facts", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


STR = "axeyum.string._2.Str"


def row(
    name: str,
    *,
    prelude: str = "string",
    kind: str = "theorem",
    footprint: int = 0,
    theorem_deps: str = "",
    rendered: str | None = None,
) -> str:
    """One eight-field projection row, tab separated, in the tool's own order."""
    body = rendered if rendered is not None else f"Eq.{{1}} {STR} {STR} {STR}"
    return "\t".join(
        [prelude, kind, name, str(footprint), "", "", theorem_deps, body]
    )


def projection(*rows: str) -> str:
    return "\n".join(rows) + "\n"


def _extract_pattern(command: str) -> str:
    """The ERE inside the emitted `grep -cE '...'`, for running it for real."""
    match = re.search(r"grep -[cq]E '(.*)'$", command)
    assert match, command
    return match.group(1)


class ParseProjectionTests(unittest.TestCase):
    def test_keeps_theorems_and_drops_other_kinds(self) -> None:
        rows = MODULE.parse_projection(
            projection(
                row("axeyum.string.2.append_assoc"),
                row("axeyum.string.2.append", kind="definition"),
            )
        )
        self.assertEqual([r.name for r in rows], ["axeyum.string.2.append_assoc"])

    def test_zero_rows_is_an_error_not_an_empty_answer(self) -> None:
        """A debug build's SIGABRT prints nothing and exits 134.

        "Measured, and there was nothing to report" is the most dangerous
        available reading of an empty projection, so it must be a hard error.
        """
        with self.assertRaises(SystemExit) as caught:
            MODULE.parse_projection("")
        self.assertIn("zero rows", str(caught.exception))

    def test_disagreeing_type_across_prelude_groups_is_an_error(self) -> None:
        with self.assertRaises(SystemExit) as caught:
            MODULE.parse_projection(
                projection(
                    row("axeyum.string.2.append_assoc", rendered="A"),
                    row("axeyum.string.2.append_assoc", prelude="creal", rendered="B"),
                )
            )
        self.assertIn("disagreeing", str(caught.exception))

    def test_wrong_field_count_is_an_error(self) -> None:
        with self.assertRaises(SystemExit) as caught:
            MODULE.parse_projection("string\ttheorem\tX\n")
        self.assertIn("expected 8", str(caught.exception))


class DeriveRefusalTests(unittest.TestCase):
    def _row(self, **kw):
        return MODULE.parse_projection(projection(row(**kw)))[0]

    def test_nonzero_axiom_footprint_is_declined(self) -> None:
        """The projection prints the footprint SIZE, never the axiom NAMES.

        So `axiom_footprint` could only be filled by guessing, and the entire
        value of that field is that it was measured.
        """
        with self.assertRaises(MODULE.Declined) as caught:
            MODULE.derive(
                self._row(name="axeyum.string.2.thm", footprint=3),
                "string",
                "2026-08-27",
                {},
            )
        self.assertIn("footprint size is 3", str(caught.exception))

    def test_zero_footprint_is_accepted(self) -> None:
        fact = MODULE.derive(
            self._row(name="axeyum.string.2.thm"), "string", "2026-08-27", {}
        )
        self.assertEqual(fact["axiom_footprint"], [])

    def test_prelude_without_a_falsifiable_footprint_checker_is_declined(self) -> None:
        with self.assertRaises(MODULE.Declined) as caught:
            MODULE.derive(
                self._row(name="axeyum.string.2.thm"), "axreal", "2026-08-27", {}
            )
        self.assertIn("PRELUDE_CONTRACT", str(caught.exception))

    def test_unconfirmable_numeric_namespace_spelling_is_declined(self) -> None:
        """`lean_pp` renders `axeyum.string.2.X`'s namespace as `axeyum.string._2.`.

        That is a RULE this script applies, so it is checked against the type
        body rather than trusted: if the `_`-form does not occur there, the
        script cannot confirm how the declaration is spelled inside its own
        statement and must refuse.
        """
        with self.assertRaises(MODULE.Declined) as caught:
            MODULE.derive(
                self._row(name="axeyum.string.2.thm", rendered="Eq.{1} Nat Nat Nat"),
                "string",
                "2026-08-27",
                {},
            )
        self.assertIn("cannot confirm how the declaration is spelled", str(caught.exception))

    def test_empty_rendered_type_is_declined(self) -> None:
        with self.assertRaises(MODULE.Declined) as caught:
            MODULE.derive(
                self._row(name="axeyum.string.2.thm", rendered="   "),
                "string",
                "2026-08-27",
                {},
            )
        self.assertIn("rendered type is empty", str(caught.exception))


class ProseHonestyTests(unittest.TestCase):
    def test_generated_prose_makes_no_mathematical_claim_and_says_so(self) -> None:
        statement = MODULE.generated_statement("axeyum.string.2.append_assoc", "string")
        self.assertIn("MECHANICALLY GENERATED, UNREVIEWED PROSE", statement)
        self.assertIn("NO mathematical characterisation", statement)

    def test_notes_state_that_absent_commentary_means_nobody_looked(self) -> None:
        notes = MODULE.generated_notes(
            "axeyum.string.2.append_assoc", "string", "axeyum.string._2.append_assoc"
        )
        self.assertIn("nobody has looked, NOT that there is nothing to say", notes)

    def test_external_status_is_never_emitted(self) -> None:
        fact = MODULE.derive(
            MODULE.parse_projection(projection(row("axeyum.string.2.thm")))[0],
            "string",
            "2026-08-27",
            {},
        )
        self.assertNotIn("external_status", fact)

    def test_provenance_carries_both_marker_keys(self) -> None:
        fact = MODULE.derive(
            MODULE.parse_projection(projection(row("axeyum.string.2.thm")))[0],
            "string",
            "2026-08-27",
            {},
        )
        self.assertEqual(fact["provenance"]["generated_by"], MODULE.GENERATOR_ID)
        self.assertEqual(fact["provenance"]["curation"], MODULE.CURATION_GENERATED)


class CheckerShapeTests(unittest.TestCase):
    def test_anchor_is_a_posix_class_that_gnu_grep_matches_against_a_real_tab(
        self,
    ) -> None:
        """Run the emitted pattern; do not merely assert its text.

        In a scripted (GNU) grep `\\t` is a literal `t`, so an anchor written
        that way silently matches nothing -- 54 facts / 68 checkers in this
        ledger were once wrong for exactly this reason, while passing when a
        human ran them in an interactive shell backed by ugrep.
        """
        kernel_cmd, _ = MODULE.checker_commands("axeyum.string.2.append_assoc", "string")
        # Extracted with a `-[cq]E` pattern on purpose: this test is about the
        # ANCHOR, and it must not also die when the `-c`/`-q` guard is mutated
        # (`test_uses_grep_c_not_grep_q` owns that one).
        pattern = _extract_pattern(kernel_cmd)

        hit = subprocess.run(
            ["/usr/bin/grep", "-cE", pattern],
            input="axeyum.string.2.append_assoc\t\n",
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(hit.stdout.strip(), "1", "the anchor must match a real tab")
        self.assertEqual(hit.returncode, 0)

        # And the negative control, in the same test: a DIFFERENT theorem's line
        # must not satisfy it, and the command must exit non-zero. Without this
        # half the assertion above would also pass for the pattern `.` .
        miss = subprocess.run(
            ["/usr/bin/grep", "-cE", pattern],
            input="axeyum.string.2.append_nil\t\n",
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(miss.stdout.strip(), "0")
        self.assertNotEqual(miss.returncode, 0, "an absent theorem must FAIL the checker")

    def test_prefix_of_a_longer_theorem_name_does_not_satisfy_the_anchor(self) -> None:
        """`isPrefix_nil` must not be re-derived by `isPrefix_nil_extra`'s line."""
        kernel_cmd, _ = MODULE.checker_commands("axeyum.string.2.isPrefix_nil", "string")
        pattern = _extract_pattern(kernel_cmd)
        got = subprocess.run(
            ["/usr/bin/grep", "-cE", pattern],
            input="axeyum.string.2.isPrefix_nil_extra\t\n",
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(got.stdout.strip(), "0")

    def test_uses_grep_c_not_grep_q(self) -> None:
        """`-q` exits at the first match and SIGPIPEs the producer.

        Under `set -o pipefail` that becomes status 141, which reads as "not
        found" -- the same unchanged tree reported 7 orphans on one run and 3 on
        the next when a repository script did this.
        """
        kernel_cmd, _ = MODULE.checker_commands("axeyum.string.2.thm", "string")
        self.assertIn("grep -cE", kernel_cmd)
        self.assertNotIn("grep -q", kernel_cmd)

    def test_constructed_preludes_get_include_constructed(self) -> None:
        _, creal_cmd = MODULE.checker_commands("CReal.thm", "creal")
        _, string_cmd = MODULE.checker_commands("axeyum.string.2.thm", "string")
        self.assertIn("--include-constructed", creal_cmd)
        self.assertNotIn("--include-constructed", string_cmd)


class BatchTests(unittest.TestCase):
    def _batch(self, text: str, monkey_registered: dict | None = None):
        original = MODULE.registered_map
        MODULE.registered_map = lambda: dict(monkey_registered or {})
        try:
            return MODULE.build_batch(MODULE.parse_projection(text), "string", "2026-08-27")
        finally:
            MODULE.registered_map = original

    def test_already_registered_theorems_are_not_regenerated(self) -> None:
        facts, declined = self._batch(
            projection(row("axeyum.string.2.a"), row("axeyum.string.2.b")),
            {"axeyum.string.2.a": "F:already-there"},
        )
        self.assertEqual([f["formal"]["kernel_theorem"] for f in facts], ["axeyum.string.2.b"])
        self.assertEqual(declined, [])

    def test_within_batch_dependency_edges_resolve_to_batch_ids(self) -> None:
        facts, _ = self._batch(
            projection(
                row("axeyum.string.2.base"),
                row("axeyum.string.2.derived", theorem_deps="axeyum.string.2.base"),
            )
        )
        derived = next(f for f in facts if f["id"] == "F:string-derived")
        self.assertEqual(derived["depends_on"], ["F:string-base"])

    def test_a_declined_theorem_never_becomes_a_dangling_dependency(self) -> None:
        """A dependency edge may only name a fact that was actually written.

        The refused theorem here has an empty rendered type, so it produces no
        file; if it still occupied the batch id map, its dependent would declare
        `depends_on` on a fact that does not exist and the ledger DAG would have
        a dangling edge. (The empty-type refusal is used rather than the
        non-zero-footprint one so that this test and
        `test_nonzero_axiom_footprint_is_declined` do not both die under one
        mutation, which would make either control ambiguous about what it
        measured.)
        """
        facts, declined = self._batch(
            projection(
                row("axeyum.string.2.base", rendered="   "),
                row("axeyum.string.2.derived", theorem_deps="axeyum.string.2.base"),
            )
        )
        self.assertEqual([n for n, _ in declined], ["axeyum.string.2.base"])
        derived = next(f for f in facts if f["id"] == "F:string-derived")
        self.assertEqual(derived["depends_on"], [])
        self.assertEqual([f["id"] for f in facts], ["F:string-derived"])

    def test_omitted_dependency_edges_are_disclosed_in_notes(self) -> None:
        facts, _ = self._batch(
            projection(row("axeyum.string.2.derived", theorem_deps="Nat.unregistered_helper"))
        )
        self.assertIn("DEPENDENCY EDGES OMITTED", facts[0]["notes"])
        self.assertIn("Nat.unregistered_helper", facts[0]["notes"])

    def test_two_theorems_slugging_to_one_id_is_declined_not_merged(self) -> None:
        """`a_b` and `a__b` both slug to `F:string-a-b`.

        Silently merging them would give one fact id two different subjects,
        and the second write would overwrite the first with no diagnostic.
        """
        facts, declined = self._batch(
            projection(row("axeyum.string.2.a_b"), row("axeyum.string.2.a__b"))
        )
        self.assertEqual(len(facts), 1)
        self.assertEqual(len(declined), 1)
        self.assertIn("collides with", declined[0][1])

    def test_a_slug_taken_by_an_existing_curated_fact_is_declined(self) -> None:
        """A generated fact must never overwrite a hand-written one."""
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            (directory / "F-string-a.json").write_text("{}", encoding="utf-8")
            original = MODULE.FACTS_DIR
            MODULE.FACTS_DIR = directory
            try:
                facts, declined = self._batch(
                    projection(row("axeyum.string.2.a"), row("axeyum.string.2.b"))
                )
            finally:
                MODULE.FACTS_DIR = original
        self.assertEqual([f["id"] for f in facts], ["F:string-b"])
        self.assertIn("collides with an existing fact file", declined[0][1])

    def test_output_is_deterministic_and_reads_no_wall_clock(self) -> None:
        text = projection(row("axeyum.string.2.b"), row("axeyum.string.2.a"))
        first, _ = self._batch(text)
        second, _ = self._batch(text)
        self.assertEqual(MODULE.render(first[0]), MODULE.render(second[0]))
        self.assertEqual([f["id"] for f in first], ["F:string-a", "F:string-b"])
        self.assertEqual(first[0]["provenance"]["date"], "2026-08-27")


class AuditTests(unittest.TestCase):
    """`--audit` is what makes the provenance marker load-bearing.

    Each test writes a fact tree into a temp dir and repoints the module at it.
    """

    def _audit_with(self, facts: list[dict]) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for fact in facts:
                (directory / (fact["id"].replace("F:", "F-", 1) + ".json")).write_text(
                    json.dumps(fact, indent=2), encoding="utf-8"
                )
            original = MODULE.FACTS_DIR
            MODULE.FACTS_DIR = directory
            try:
                return MODULE.audit()
            finally:
                MODULE.FACTS_DIR = original

    def _generated(self) -> dict:
        return MODULE.derive(
            MODULE.parse_projection(projection(row("axeyum.string.2.thm")))[0],
            "string",
            "2026-08-27",
            {},
        )

    def test_a_freshly_generated_fact_audits_clean(self) -> None:
        self.assertEqual(self._audit_with([self._generated()]), [])

    def test_hand_edited_prose_under_a_generated_marker_is_a_problem(self) -> None:
        """Enrichment must declare itself by flipping `curation`.

        Otherwise a curated-looking fact sits under a `generated-unreviewed`
        marker and the two become indistinguishable again -- which is the exact
        thing the marker exists to prevent.
        """
        fact = self._generated()
        fact["title"] = "Append is associative on the free monoid"
        problems = self._audit_with([fact])
        self.assertEqual(len(problems), 1)
        self.assertIn("title is not what the generator emits", problems[0])

    def test_flipping_curation_to_curated_permits_enriched_prose(self) -> None:
        fact = self._generated()
        fact["title"] = "Append is associative on the free monoid"
        fact["provenance"]["curation"] = MODULE.CURATION_CURATED
        self.assertEqual(self._audit_with([fact]), [])

    def test_an_added_external_status_is_a_problem(self) -> None:
        fact = self._generated()
        fact["external_status"] = "proved"
        problems = self._audit_with([fact])
        self.assertEqual(len(problems), 1)
        self.assertIn("must not carry external_status", problems[0])

    def test_a_checker_that_cannot_fail_is_a_problem(self) -> None:
        """The whole risk of bulk generation, caught at the marker.

        `cargo run ... theorem_dependency_inventory` with the pipe removed exits
        0 on completion alone -- it lists theorems and says nothing about
        whether THIS one is among them. That is the repository's central audit
        finding (40 of 162 runs), reproduced here as a control.
        """
        fact = self._generated()
        fact["evidence"][0]["checker_command"] = (
            "cargo run -q --release -p axeyum-lean-kernel --example "
            "theorem_dependency_inventory"
        )
        problems = self._audit_with([fact])
        self.assertEqual(len(problems), 1)
        self.assertIn("does not match a shape whose exit status depends", problems[0])

    def test_an_unknown_curation_value_is_a_problem(self) -> None:
        fact = self._generated()
        fact["provenance"]["curation"] = "probably-fine"
        problems = self._audit_with([fact])
        self.assertEqual(len(problems), 1)
        self.assertIn("is not one of", problems[0])

    def test_a_curation_marker_without_a_generator_marker_is_a_problem(self) -> None:
        """`curation` is defined only for generated facts.

        A hand-written fact claiming `curated` would otherwise read as "a lane
        reviewed this generated skeleton", which is a different and stronger
        statement than "a lane wrote this".
        """
        fact = self._generated()
        del fact["provenance"]["generated_by"]
        problems = self._audit_with([fact])
        self.assertEqual(len(problems), 1)
        self.assertIn("curation marker is defined only for generated", problems[0])

    def test_curated_facts_without_either_marker_are_ignored(self) -> None:
        self.assertEqual(
            self._audit_with([{"id": "F:hand-written", "provenance": {"date": "x"}}]), []
        )


if __name__ == "__main__":
    unittest.main()
