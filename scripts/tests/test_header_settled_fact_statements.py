#!/usr/bin/env python3
"""Controls for `scripts/header-settled-fact-statements.py`.

Every test drives the REAL module, loaded from its real path. A suite that
restates its subject is testing the restatement.

Each test names the ONE guard it drives, so
`scripts/tests/mutation_controls.py header-settled-fact-statements` can report
which deletion kills which test.

The refusal cases are the point of the suite. This tool rewrites the
`formal.statement` of settled facts, which is the field
`check-settled-fact-statements.py` exists to keep from moving quietly. What makes
that safe is not the rewrite -- it is the four refusals, each declining a case
the tool cannot prove is a pure prefix. A suite exercising only the happy path
would let every refusal be deleted while staying green.

Each refusal test asserts the REASON, not merely that nothing changed. Deleting
the ABSENT guard alone leaves a fact refused for a different reason (DIVERGENT),
so a test that only checked "unchanged" would not distinguish the guards from
each other.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts" / "header-settled-fact-statements.py"

_spec = importlib.util.spec_from_file_location("header_settled_fact_statements", SUBJECT)
assert _spec is not None and _spec.loader is not None
hsfs = importlib.util.module_from_spec(_spec)
sys.modules["header_settled_fact_statements"] = hsfs
_spec.loader.exec_module(hsfs)

THEOREM_TYPE = "((x0 : AxNat) -> Eq.{1} AxNat (Nat.add x0 x0) (Nat.mul x0 x0))"
DEF_TYPE = "((x0 : Int) -> ((x1 : AxNat) -> Rat))"


def row(prelude: str, kind: str, name: str, canonical: str) -> str:
    return f"{prelude}\t{kind}\t{name}\t0\t\t\t\t{canonical}"


class Harness(unittest.TestCase):
    """A scratch facts tree, projection TSV and pins manifest."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        self.facts = self.root / "facts"
        self.facts.mkdir()
        self.pins = self.root / "pins.json"
        self.pins.write_text(
            json.dumps({"schema_version": 2, "coverage_floor": {}, "amendments": [], "pins": []}),
            encoding="utf-8",
        )
        self.projection = self.root / "projection.tsv"
        self.projection.write_text(
            "\n".join(
                [
                    row("nat", "theorem", "Nat.demo", THEOREM_TYPE),
                    row("rat", "definition", "Rat.normalize", DEF_TYPE),
                ]
            )
            + "\n",
            encoding="utf-8",
        )

    def fact(self, fact_id: str, **formal: object) -> None:
        payload = {
            "id": fact_id,
            "statement": "prose that this suite never changes",
            "epistemic_status": formal.pop("epistemic_status", "proved"),
            "formal": {"language": "lean4", **formal},
        }
        name = fact_id.replace(":", "-") + ".json"
        (self.facts / name).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    def run_tool(self, *extra: str) -> int:
        return hsfs.run(
            [
                "--projection",
                str(self.projection),
                "--facts",
                str(self.facts),
                "--pins",
                str(self.pins),
                *extra,
            ]
        )

    def reason(self, fact_id: str) -> str | None:
        """Why the tool declined `fact_id`, straight out of `classify`."""
        decls = hsfs.read_projection(self.projection)
        _fixable, refused = hsfs.classify(self.facts, decls)
        for got_id, _name, why in refused:
            if got_id == fact_id:
                return why
        return None

    def statement(self, fact_id: str) -> str:
        name = fact_id.replace(":", "-") + ".json"
        return json.loads((self.facts / name).read_text(encoding="utf-8"))["formal"]["statement"]

    def amendments(self) -> list[dict]:
        return json.loads(self.pins.read_text(encoding="utf-8"))["amendments"]


class Fixes(Harness):
    def test_a_theorem_whose_statement_is_its_canonical_type_gets_a_theorem_header(self) -> None:
        """G-check: `--check` exits on the FINDING, and `--apply` heads the fact."""
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--apply"), 0)
        self.assertEqual(self.statement("F:demo"), f"theorem Nat.demo : {THEOREM_TYPE}")
        self.assertEqual(self.run_tool("--check"), 0)

    def test_a_definition_gets_def_and_not_theorem(self) -> None:
        """G-keyword: the header keyword follows the declaration's KIND."""
        self.fact("F:defn", kernel_theorem="Rat.normalize", statement=DEF_TYPE)
        self.assertEqual(self.run_tool("--apply"), 0)
        self.assertEqual(self.statement("F:defn"), f"def Rat.normalize : {DEF_TYPE}")

    def test_the_prefix_preserves_the_proposition_verbatim(self) -> None:
        """G-fix: what follows the header is the old statement, byte for byte."""
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.run_tool("--apply")
        self.assertTrue(self.statement("F:demo").endswith(THEOREM_TYPE))


class Refusals(Harness):
    def test_a_name_absent_from_the_projection_is_refused_as_absent(self) -> None:
        """G-absent: a proof-isolated import has no persistent declaration to render."""
        self.fact("F:ml430", kernel_theorem="Nat.gcd_greatest", statement=THEOREM_TYPE)
        self.assertEqual(self.reason("F:ml430"), "ABSENT")
        self.assertEqual(self.run_tool("--apply"), 0)
        self.assertEqual(self.statement("F:ml430"), THEOREM_TYPE)
        # And a refusal leaves no record claiming an edit was made. Asserted
        # here rather than in its own test so that deleting the ABSENT guard
        # kills exactly one case.
        self.assertEqual(self.amendments(), [])

    def test_a_statement_that_is_not_the_rendering_is_refused_as_divergent(self) -> None:
        """G-divergent: byte-identity is the whole argument that a prefix is safe."""
        self.fact("F:hand", kernel_theorem="Nat.demo", statement="Nat.demo : forall x, x = x")
        self.assertEqual(self.reason("F:hand"), "DIVERGENT")
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:hand"), "Nat.demo : forall x, x = x")

    def test_two_renderings_of_one_name_are_refused_as_ambiguous(self) -> None:
        """G-ambiguous: one name, two canonical types, no defensible choice."""
        self.projection.write_text(
            row("a", "theorem", "Nat.demo", THEOREM_TYPE)
            + "\n"
            + row("b", "theorem", "Nat.demo", DEF_TYPE)
            + "\n",
            encoding="utf-8",
        )
        self.fact("F:amb", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.assertEqual(self.reason("F:amb"), "AMBIGUOUS")
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:amb"), THEOREM_TYPE)

    def test_a_kind_with_no_header_keyword_is_refused(self) -> None:
        """G-kind: `theorem` is not a safe default for a recursor."""
        self.projection.write_text(
            row("nat", "recursor", "Nat.rec", THEOREM_TYPE) + "\n", encoding="utf-8"
        )
        self.fact("F:rec", kernel_theorem="Nat.rec", statement=THEOREM_TYPE)
        self.assertEqual(self.reason("F:rec"), "UNKNOWN-KIND")
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:rec"), THEOREM_TYPE)


class Scope(Harness):
    def test_an_already_headed_statement_is_left_alone(self) -> None:
        """G-header: a fact that already satisfies the bind is not double-headed."""
        headed = f"theorem Nat.demo : {THEOREM_TYPE}"
        self.fact("F:headed", kernel_theorem="Nat.demo", statement=headed)
        self.assertEqual(self.run_tool("--check"), 0)
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:headed"), headed)

    def test_an_unsettled_fact_is_out_of_scope(self) -> None:
        """G-settled: this bind is about SETTLED facts' statements."""
        self.fact(
            "F:open",
            epistemic_status="open",
            kernel_theorem="Nat.demo",
            statement=THEOREM_TYPE,
        )
        self.assertEqual(self.run_tool("--check"), 0)
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:open"), THEOREM_TYPE)

    def test_a_fact_naming_no_declaration_is_out_of_scope(self) -> None:
        """G-named: the bind only applies once a fact names a `kernel_theorem`."""
        self.fact("F:unnamed", statement=THEOREM_TYPE)
        self.assertEqual(self.run_tool("--check"), 0)
        self.run_tool("--apply")
        self.assertEqual(self.statement("F:unnamed"), THEOREM_TYPE)


class Amendment(Harness):
    def test_apply_records_an_amendment_with_both_digests(self) -> None:
        """G-amend-record: the pins gate refuses a re-pin without one."""
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.run_tool("--apply")
        rows = self.amendments()
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["fact_id"], "F:demo")
        self.assertEqual(rows[0]["from_sha256"], hashlib.sha256(THEOREM_TYPE.encode()).hexdigest())
        self.assertEqual(
            rows[0]["to_sha256"],
            hashlib.sha256(f"theorem Nat.demo : {THEOREM_TYPE}".encode()).hexdigest(),
        )
        self.assertTrue(rows[0]["reason"])

    def test_re_heading_a_reverted_fact_does_not_duplicate_the_amendment(self) -> None:
        """G-amend-dedup: one act, one record, even if the header is reverted.

        A plain second `--apply` cannot reach this guard: the fact is headed by
        then, so `classify` returns nothing to do. The guard is reachable only
        when the statement comes BACK -- a bad merge, a revert -- and the
        amendment for the original act is still on file. Asserting the count is
        stable rather than equal to 1 keeps deleting the RECORDING (0 then 0)
        the business of the digests test above, so neither mutation kills both.
        """
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.run_tool("--apply")
        first = len(self.amendments())
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        self.run_tool("--apply")
        self.assertEqual(len(self.amendments()), first)


class Input(Harness):
    def test_an_empty_projection_is_an_error_not_a_quiet_pass(self) -> None:
        """G-subject: a tool whose authority vanished must not report `PASS`."""
        self.projection.write_text("", encoding="utf-8")
        self.fact("F:demo", kernel_theorem="Nat.demo", statement=THEOREM_TYPE)
        with self.assertRaises(hsfs.HeaderError):
            self.run_tool("--check")

    def test_a_missing_projection_is_an_error(self) -> None:
        """G-subject: absence of the authority is not absence of work."""
        self.projection.unlink()
        with self.assertRaises(hsfs.HeaderError):
            self.run_tool("--check")


if __name__ == "__main__":
    unittest.main()
