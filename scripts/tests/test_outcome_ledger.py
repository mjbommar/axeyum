#!/usr/bin/env python3
"""Control suite for `scripts/outcome_ledger.py` (ADR-2102).

The ledger is a table that other lanes will quote without re-deriving, so **a
checker that cannot fail is worse than no checker**: if this file passes on a
library that silently truncates a field, drops a row or waves a branch binary
through as `main`, the whole phase has made the wrong numbers faster to get.

Every assertion here is a bug class that reached a published ADR in this
repository, written as a fixture the library must survive:

  ADR-2020  a census split records on `;` when the field CONTAINS `;`, and
            truncated its own largest bucket.  Here: the hostile round trip.
  ADR-2075  a partial reading summed as a total.  Here: the aggregate guard,
            and the three-valued `partial` column that keeps "the instrument
            said no" apart from "nothing could say".
  ADR-2085  a staleness gate that flagged the wrong rows and missed 16 real
            ones.  Here: the ancestor check, driven against a REAL git repo in
            both directions plus the unresolvable case.
  ADR-2045  `losses=0` by verdict with five new aborts underneath.  Here:
            `exit_status` is its own column and an abort is its own verdict.

Three of these are NEGATIVE controls (the library must REFUSE), one derives its
population from the authority rather than from a literal, and the rest drive a
distinction the producer makes and require it to survive to the consumer.

Run: python3 -m unittest scripts.tests.test_outcome_ledger
Exit status is the finding.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
ROOT = SCRIPTS.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import outcome_ledger as ol  # noqa: E402

# ---------------------------------------------------------------------------
# Fixtures.  Schema 3 (ADR-2105: the `name`/`features` members) is what the
# CLI writes now, and `_trail_line`'s default; `schema_version=2` is kept
# available for the one fixture that drives this library's prose-fallback
# path.  The partial spelling is the one ADR-2075's twelve files printed and
# nobody read.
# ---------------------------------------------------------------------------

#: A detail that carries every character a separator bug has ever eaten here.
#: The suite ASSERTS it actually contains them -- a hostile fixture that is not
#: hostile is a vacuous control (ADR-2101 made the same point about its own).
HOSTILE_DETAIL = (
    'budget exhausted; the reduced solve\'s own reason was "x=1|y=2"\n'
    "\tsecond line\r\\ and a trailing backslash \\"
)


def _trail_line(
    *,
    partial: bool,
    attempts: list[dict],
    schema_version: int = 3,
    features: str | None = None,
) -> str:
    """Builds one `; route-trail …` / `; partial route-trail …` line.

    Schema 3 (ADR-2105) by default -- the current renderer's own schema -- so
    every test that does not care about the schema exercises the shape this
    library reads from a REAL capture today. `schema_version=2` is kept
    available (and used by exactly one test,
    `CaptureToRow.test_the_four_features_answers_stay_apart`) to prove the
    prose-fallback path this library still owes every committed schema-1/2
    sweep.

    `features`, when given, is the `features` JSON member ADR-2105 added --
    absent below schema 3 even if passed, matching what a real schema-2
    binary's `to_json` actually emits (nothing).
    """
    prefix = "; partial route-trail " if partial else "; route-trail "
    body = {"schema_version": schema_version, "partial": partial}
    if schema_version >= 3 and features is not None:
        body["features"] = features
    body["attempts"] = attempts
    if partial:
        body["in_flight_after"] = attempts[-1]["route"] if attempts else None
        body["open_segment_ns"] = 19_000_000_000
    return prefix + json.dumps(body)


COMPLETE_ATTEMPTS = [
    {"route": "fd:parse", "outcome": "probe", "detail": "string_bound=12", "elapsed_ns": 1_000_000},
    {
        "route": "dl-online",
        "outcome": "declined",
        "reason": "not-applicable",
        "detail": "not difference-shaped",
        "elapsed_ns": 2_000_000,
    },
    {"route": "qf-bv", "outcome": "decided", "verdict": "unsat", "elapsed_ns": 48_000_000},
]

PARTIAL_ATTEMPTS = [
    {"route": "fd:parse", "outcome": "probe", "detail": "string_bound=12", "elapsed_ns": 1_000_000},
    {
        "route": "q:bool-skeleton",
        "outcome": "declined",
        "reason": "budget",
        "detail": HOSTILE_DETAIL,
        "elapsed_ns": 4_000_000,
    },
]


def _capture(tmp: Path, name: str, lines: list[str]) -> Path:
    path = tmp / name
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def _row(tmp: Path, capture: Path, **over) -> ol.LedgerRow:
    kwargs = dict(
        sweep_id="fixture",
        arm="A",
        corpus_path="QF_LRA/sub/dir/x.smt2",
        binary_sha="deadbeef",
        exit_status=0,
        elapsed_ms=51,
        host="s5",
        core="1,9",
        load="0.42",
    )
    kwargs.update(over)
    return ol.row_from_capture(capture, **kwargs)


class EscapingRoundTrip(unittest.TestCase):
    """ADR-2020, as a fixture rather than as a caveat."""

    def test_the_hostile_fixture_is_actually_hostile(self):
        # A control on the control.  If HOSTILE_DETAIL ever loses its tab or
        # its pipe, the round-trip test below keeps passing while testing
        # nothing -- which is precisely how a guard stops guarding.
        for char, name in (
            ("\t", "TAB"),
            ("\n", "LF"),
            ("\r", "CR"),
            ("|", "PIPE"),
            (";", "SEMICOLON"),
            ("=", "EQUALS"),
            ('"', "QUOTE"),
            ("\\", "BACKSLASH"),
        ):
            self.assertIn(char, HOSTILE_DETAIL, f"the hostile fixture lost its {name}")

    def test_escape_unescape_is_an_exact_inverse(self):
        self.assertEqual(ol._unescape(ol._escape(HOSTILE_DETAIL)), HOSTILE_DETAIL)

    def test_a_literal_backslash_t_is_not_a_tab(self):
        # Sequential `str.replace` unescaping fails exactly here: the source
        # holds backslash + `t`, which escapes to `\\t` and must come back as
        # two characters, not as a tab.
        source = "a\\tb"
        self.assertEqual(ol._unescape(ol._escape(source)), source)
        self.assertNotIn("\t", ol._unescape(ol._escape(source)))

    def test_an_escaped_field_carries_no_separator(self):
        escaped = ol._escape(HOSTILE_DETAIL)
        self.assertNotIn("\t", escaped)
        self.assertNotIn("\n", escaped)
        self.assertNotIn("\r", escaped)
        self.assertNotIn(ol.LIST_SEP, escaped)

    def test_a_detail_containing_the_separators_survives_the_whole_row(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp,
                "partial.out",
                ["unknown", _trail_line(partial=True, attempts=PARTIAL_ATTEMPTS)],
            )
            row = _row(tmp, capture)
            ol.append_row("fixture", row, ledger_dir=tmp / "ledger")
            back = ol.read_ledger(tmp / "ledger" / "fixture.tsv")
            self.assertEqual(len(back), 1)
            self.assertEqual(back[0].details, [HOSTILE_DETAIL])
            self.assertEqual(back[0].reasons, [("q:bool-skeleton", "budget")])


class TypedDeclineName(unittest.TestCase):
    """ADR-2104's typed detail variant, carried beside the free-text detail.

    `route_trace.rs`'s `to_json` now emits the `name` member (ADR-2105), so
    every real schema-3 capture with a typed decline fills this column --
    it is no longer only a fixture proving the reader path in advance of the
    producer. The fixture below still constructs its own trail line rather
    than dispatching a real query, for the same reason every other test in
    this file does: this suite is about the LIBRARY's column plumbing, not
    about re-running the solver.
    """

    def _row_with_names(self, tmp: Path) -> ol.LedgerRow:
        attempts = [
            {"route": "fd:parse", "outcome": "probe", "elapsed_ns": 1_000_000},
            {
                "route": "nia-square",
                "outcome": "declined",
                "reason": "budget",
                "name": "square-coefficient-guard-exceeded",
                "detail": "coefficient 2^97 exceeds the guard",
                "elapsed_ns": 2_000_000,
            },
            {
                "route": "qf-bv",
                "outcome": "declined",
                "reason": "unsupported",
                "name": "backend",
                "detail": "term #9 has sort (Uninterpreted 4)",
                "elapsed_ns": 3_000_000,
            },
        ]
        capture = _capture(
            tmp, "named.out", ["unknown", _trail_line(partial=False, attempts=attempts)]
        )
        return _row(tmp, capture)

    def test_the_typed_name_survives_to_the_row(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            row = self._row_with_names(Path(tmpdir))
            self.assertEqual(row.names, ["square-coefficient-guard-exceeded", "backend"])
            self.assertTrue(row.has_typed_names)

    def test_a_row_with_no_declines_at_all_has_no_names(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            attempts = [
                {"route": "fd:parse", "outcome": "probe", "elapsed_ns": 1},
                {"route": "qf-bv", "outcome": "decided", "verdict": "unsat", "elapsed_ns": 2},
            ]
            capture = _capture(
                tmp, "d.out", ["unsat", _trail_line(partial=False, attempts=attempts)]
            )
            row = _row(tmp, capture)
            self.assertEqual(row.reasons, [])
            self.assertEqual(row.names, [])

    def test_the_typed_axis_and_the_prose_axis_are_separate_columns(self):
        """Two declines with the SAME reason and detail stay apart by name.

        ADR-2101 drove the equivalent for `reason`/`kind`; this is the same
        requirement one level down, and it is why `name` is its own column
        rather than appended into `decline_reasons`.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            attempts = [
                {
                    "route": "r",
                    "outcome": "declined",
                    "reason": "unsupported",
                    "name": "backend",
                    "detail": "same words",
                    "elapsed_ns": 1,
                },
                {
                    "route": "r",
                    "outcome": "declined",
                    "reason": "unsupported",
                    "name": "ingest-refusal",
                    "detail": "same words",
                    "elapsed_ns": 1,
                },
            ]
            capture = _capture(
                tmp, "t.out", ["unknown", _trail_line(partial=False, attempts=attempts)]
            )
            row = _row(tmp, capture)
            self.assertEqual(row.reasons, [("r", "unsupported"), ("r", "unsupported")])
            self.assertEqual(row.details, ["same words", "same words"])
            self.assertEqual(row.names, ["backend", "ingest-refusal"])

    def test_the_names_line_up_with_the_reasons_one_for_one(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            row = self._row_with_names(Path(tmpdir))
            self.assertEqual(len(row.names), len(row.reasons))
            self.assertEqual(len(row.names), len(row.details))

    def test_a_producer_with_no_name_member_yields_empty_names_not_missing_ones(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp,
                "c.out",
                ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)],
            )
            row = _row(tmp, capture)
            # One decline in COMPLETE_ATTEMPTS, and it carries no `name`. The
            # list is still ALIGNED with the reasons -- a consumer zipping the
            # three axes must not have to know which producer wrote the row.
            self.assertEqual(len(row.reasons), 1)
            self.assertEqual(row.names, [""])
            self.assertFalse(row.has_typed_names)

    def test_the_name_round_trips_through_a_written_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ol.append_row("fixture", self._row_with_names(tmp), ledger_dir=tmp / "ledger")
            back = ol.read_ledger(tmp / "ledger" / "fixture.tsv")
            self.assertEqual(back[0].names, ["square-coefficient-guard-exceeded", "backend"])


class SchemaVersions(unittest.TestCase):
    """An append-only table that cannot read its own history is not one."""

    def test_the_current_schema_is_the_newest_known_header(self):
        self.assertEqual(ol.KNOWN_HEADERS[ol.COLUMNS], ol.SCHEMA_VERSION)
        self.assertEqual(max(ol.KNOWN_HEADERS.values()), ol.SCHEMA_VERSION)

    def test_schema_1_differs_from_the_current_one_by_exactly_the_new_column(self):
        # Derived, not listed: a future column added without a version fails
        # here rather than measuring the maintainer's memory.
        added = [c for c in ol.COLUMNS if c not in ol.COLUMNS_V1]
        removed = [c for c in ol.COLUMNS_V1 if c not in ol.COLUMNS]
        self.assertEqual(added, ["decline_names"])
        self.assertEqual(removed, [])

    def test_a_schema_1_file_is_still_readable(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "old.tsv"
            values = {c: f"v-{c}" for c in ol.COLUMNS_V1}
            path.write_text(
                "\t".join(ol.COLUMNS_V1)
                + "\n"
                + "\t".join(values[c] for c in ol.COLUMNS_V1)
                + "\n",
                encoding="utf-8",
            )
            rows = ol.read_ledger(path)
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0].corpus_path, "v-corpus_path")
            # The column the old schema has no room for comes back EMPTY, and
            # `names` is then an empty LIST -- distinguishable from `[""]`,
            # which is "one decline, producer said nothing".
            self.assertEqual(rows[0].decline_names, "")
            # One `decline_reasons` element in the fixture, so `names` is
            # padded to one empty string rather than coming back short.
            self.assertEqual(rows[0].names, [""])
            self.assertFalse(rows[0].has_typed_names)

    def test_every_committed_sweep_is_a_known_schema(self):
        """Derived from what is on disk, not from a list.

        The 220 rows this ADR committed are schema 1.  If a later change makes
        them unreadable, this fails here rather than in whatever lane next
        quotes them.
        """
        ledger = ROOT / "bench-results" / "ledger"
        if not ledger.is_dir():
            # `scripts/tests/mutation_controls.py` copies the tree to a scratch
            # root with `bench-results/` EXCLUDED (206 MB), so this test's
            # subject is genuinely absent there. Skipping says so; passing on an
            # empty glob would be the "empty result from a tool never pointed at
            # your subject" failure this repository has a rule about.
            self.skipTest(f"{ledger} is not present (mutation scratch copy excludes it)")
        files = [f for f in sorted(ledger.glob("*.tsv")) if f.name != ol.INDEX_NAME]
        self.assertGreaterEqual(len(files), 7, f"{ledger} holds {len(files)} sweeps")
        for path in files:
            header = tuple(path.read_text(encoding="utf-8").splitlines()[0].split("\t"))
            self.assertIn(header, ol.KNOWN_HEADERS, f"{path.name} is an unknown schema")
            self.assertGreater(len(ol.read_ledger(path)), 0, f"{path.name} has no rows")

    def test_appending_a_current_row_to_a_schema_1_file_is_refused(self):
        """A FILE keeps the schema it was opened with.

        The alternative is dropping the new column silently, which is the
        schema-drift failure this library exists to make unreachable.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            ledger.mkdir()
            (ledger / "fixture.tsv").write_text(
                "\t".join(ol.COLUMNS_V1) + "\n", encoding="utf-8"
            )
            capture = _capture(
                tmp,
                "c.out",
                ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)],
            )
            with self.assertRaises(ol.SchemaDrift):
                ol.append_row("fixture", _row(tmp, capture), ledger_dir=ledger)


class SchemaDrift(unittest.TestCase):
    """Exit criterion 1: a writer that emits an unknown column is refused."""

    def test_a_file_with_an_extra_column_is_refused_on_read(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "drift.tsv"
            header = list(ol.COLUMNS) + ["invented_by_a_writer"]
            path.write_text("\t".join(header) + "\n", encoding="utf-8")
            with self.assertRaises(ol.SchemaDrift) as caught:
                ol.read_ledger(path)
            self.assertIn("invented_by_a_writer", str(caught.exception))

    def test_a_file_missing_a_column_is_refused_on_read(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "drift.tsv"
            header = [c for c in ol.COLUMNS if c != "partial"]
            path.write_text("\t".join(header) + "\n", encoding="utf-8")
            with self.assertRaises(ol.SchemaDrift) as caught:
                ol.read_ledger(path)
            self.assertIn("partial", str(caught.exception))

    def test_a_reordered_header_is_refused_rather_than_read_positionally(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "drift.tsv"
            header = list(ol.COLUMNS)
            header[0], header[1] = header[1], header[0]
            path.write_text("\t".join(header) + "\n", encoding="utf-8")
            with self.assertRaises(ol.SchemaDrift):
                ol.read_ledger(path)

    def test_appending_to_a_drifted_file_is_refused_before_it_writes(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            ledger.mkdir()
            path = ledger / "fixture.tsv"
            header = list(ol.COLUMNS) + ["invented_by_a_writer"]
            path.write_text("\t".join(header) + "\n", encoding="utf-8")
            before = path.read_text(encoding="utf-8")
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            with self.assertRaises(ol.SchemaDrift):
                ol.append_row("fixture", _row(tmp, capture), ledger_dir=ledger)
            self.assertEqual(path.read_text(encoding="utf-8"), before)

    def test_a_row_must_name_the_sweep_it_is_appended_to(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            row = _row(tmp, capture, sweep_id="one")
            with self.assertRaises(ol.LedgerError):
                ol.append_row("another", row, ledger_dir=tmp / "ledger")

    def test_every_writer_goes_through_the_library(self):
        """Exit criterion 1, derived from the authority rather than from a list.

        The schema cannot drift at a writer that never formats a row itself.
        The population is every executable under `bench-results/ledger-20260915/`
        plus the shared runner -- discovered, not enumerated, so a fourth writer
        added tomorrow is covered the day it lands.  Each must reach the ledger
        through `scripts/outcome_ledger.py` (directly or through the runner) and
        must not write into a ledger directory by hand.
        """
        sweep_dir = SCRIPTS / "ledger-sweeps"
        runner = SCRIPTS / "ledger-run-one.sh"
        writers = sorted(sweep_dir.glob("*.sh")) if sweep_dir.is_dir() else []
        self.assertGreaterEqual(
            len(writers),
            3,
            f"ADR-2102 wires THREE sweep writers; {sweep_dir} holds {len(writers)}",
        )
        self.assertTrue(runner.exists(), f"{runner} is the shared writer and is missing")

        self.assertIn(
            "outcome_ledger.py",
            runner.read_text(encoding="utf-8"),
            "the shared runner does not call the library at all",
        )
        for writer in writers:
            text = writer.read_text(encoding="utf-8")
            self.assertIn(
                "ledger-run-one.sh",
                text,
                f"{writer.name} does not go through the shared runner",
            )
            for line in text.splitlines():
                stripped = line.strip()
                if stripped.startswith("#"):
                    continue
                # A row is appended with `>>` into a path naming the ledger.
                # Any such line in a sweep script means it is formatting the
                # schema itself, which is where a column the library does not
                # know would come from.
                if ">>" in stripped and "ledger-dir" not in stripped:
                    self.assertNotIn(
                        "bench-results/ledger/",
                        stripped,
                        f"{writer.name} writes the ledger by hand: {stripped!r}",
                    )

    def test_the_writers_pass_trace(self):
        """A sweep that forgets `--trace` records a table of empty route columns.

        This is not hypothetical: PLAN-SIZING measured that the Tier 1 harness
        captured stdout into a shell variable AND never passed `--trace`, so
        even keeping the capture would have carried no routing lines.  The flag
        lives in the shared runner, once, and this pins it there.
        """
        text = (SCRIPTS / "ledger-run-one.sh").read_text(encoding="utf-8")
        self.assertIn("--trace", text)


class CaptureToRow(unittest.TestCase):
    def test_a_complete_trail_fills_every_routing_column(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp,
                "c.out",
                [
                    # `features` comes off the schema-3 JSON member now
                    # (ADR-2105), not this prose line -- kept here only to
                    # prove it is NOT what the row's `feature_classes` reads
                    # (it says the wrong thing on purpose; see
                    # `test_schema_3_features_come_from_the_json_member_not_the_prose_line`).
                    "; features none",
                    _trail_line(
                        partial=False,
                        attempts=COMPLETE_ATTEMPTS,
                        features="Int|Real",
                    ),
                    "unsat",
                ],
            )
            row = _row(tmp, capture)
            self.assertEqual(row.verdict, "unsat")
            self.assertEqual(row.decided_by, "qf-bv")
            self.assertEqual(row.bound_by, "qf-bv")
            self.assertEqual(row.attempt_count, 3)
            self.assertEqual(
                row.trail, ["fd:parse:probe", "dl-online:declined", "qf-bv:decided"]
            )
            self.assertEqual(row.per_attempt_ms, [1, 2, 48])
            self.assertEqual(row.partial, ol.PARTIAL_NO)
            self.assertEqual(row.reasons, [("dl-online", "not-applicable")])
            self.assertEqual(row.feature_classes, ["Int", "Real"])

    def test_a_partial_trail_is_recorded_as_partial(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp, "p.out", ["unknown", _trail_line(partial=True, attempts=PARTIAL_ATTEMPTS)]
            )
            row = _row(tmp, capture)
            self.assertEqual(row.partial, ol.PARTIAL_YES)
            self.assertTrue(row.is_partial)

    def test_a_capture_with_no_trail_still_produces_a_row(self):
        """An aborted file is an outcome, not an absence to drop.

        Dropping it would make every rate in the ledger a rate over the files
        that happened to finish -- the shape ADR-2045 found underneath
        `losses=0`.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(tmp, "a.out", ["(error \"out of memory\")"])
            row = _row(tmp, capture, exit_status=134)
            self.assertEqual(row.verdict, "abort")
            self.assertEqual(row.exit_status, "134")
            self.assertEqual(row.attempts, "0")
            self.assertEqual(row.partial, ol.PARTIAL_UNKNOWN)

    def test_exit_status_is_its_own_column_and_does_not_fold_into_the_verdict(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            row = _row(tmp, capture, exit_status=124)
            self.assertEqual(row.verdict, "unsat")
            self.assertEqual(row.exit_status, "124")

    def test_the_four_features_answers_stay_apart(self):
        """No two of the four collapse, and `scan_ran` names the reason.

        ADR-2100 measured that **482 of 643** undecided Tier 1 rows never reach
        the quantifier-free dispatch ladder, so `not-dispatched` is the common
        case rather than an edge one -- and without its own token it would be
        byte-identical, in this column, to a row from a binary built before the
        instrument existed.

        SCHEMA 2, DELIBERATELY -- the one retained schema-2 fixture in this
        suite. `features` has no JSON member at all below schema 3
        (ADR-2105), so this is the only way left to drive the prose-fallback
        path (`features_from_stdout`, via `features_from_capture`) a
        committed schema-1/2 sweep still needs. A schema-3 trail's `features`
        comes from the JSON member instead -- see
        `test_schema_3_features_come_from_the_json_member_not_the_prose_line`
        below, which proves the prose lines here would be IGNORED on a
        current capture.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            trail = _trail_line(
                partial=False, attempts=COMPLETE_ATTEMPTS, schema_version=2
            )
            rows = {
                "absent": _row(tmp, _capture(tmp, "a.out", ["unsat", trail])),
                "not_dispatched": _row(
                    tmp,
                    _capture(tmp, "n.out", ["; features not-dispatched", "unsat", trail]),
                ),
                "empty": _row(
                    tmp, _capture(tmp, "e.out", ["; features none", "unsat", trail])
                ),
                "classes": _row(
                    tmp, _capture(tmp, "c.out", ["; features Int|Real", "unsat", trail])
                ),
            }
            values = [r.features for r in rows.values()]
            self.assertEqual(len(set(values)), 4, values)

            self.assertEqual(rows["absent"].features, ol.FEATURES_ABSENT)
            self.assertIsNone(rows["absent"].feature_classes)
            self.assertIsNone(rows["absent"].scan_ran)

            self.assertEqual(rows["not_dispatched"].features, ol.FEATURES_NOT_DISPATCHED)
            self.assertIsNone(rows["not_dispatched"].feature_classes)
            self.assertIs(rows["not_dispatched"].scan_ran, False)

            self.assertEqual(rows["empty"].features, ol.FEATURES_EMPTY)
            self.assertEqual(rows["empty"].feature_classes, [])
            self.assertIs(rows["empty"].scan_ran, True)

            self.assertEqual(rows["classes"].feature_classes, ["Int", "Real"])
            self.assertIs(rows["classes"].scan_ran, True)

    def test_schema_3_features_come_from_the_json_member_not_the_prose_line(self):
        """The other half of ADR-2105: on a CURRENT capture the prose is a
        RENDERING and reading it again would be a second authority.

        Each row below carries a `; features` prose line that says the
        OPPOSITE of its trail's JSON member. If `features_from_capture` ever
        regressed to reading the prose first, every assertion here would
        report the prose's answer instead and this test would not notice the
        member was ignored -- so the fixtures are adversarial ON PURPOSE.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)

            not_dispatched_trail = _trail_line(
                partial=False, attempts=COMPLETE_ATTEMPTS, features=None
            )
            row = _row(
                tmp,
                _capture(
                    tmp,
                    "n.out",
                    ["; features Int|Real", "unsat", not_dispatched_trail],
                ),
            )
            self.assertEqual(row.features, ol.FEATURES_NOT_DISPATCHED, row.features)

            empty_trail = _trail_line(
                partial=False, attempts=COMPLETE_ATTEMPTS, features="none"
            )
            row = _row(
                tmp,
                _capture(
                    tmp, "e.out", ["; features not-dispatched", "unsat", empty_trail]
                ),
            )
            self.assertEqual(row.features, ol.FEATURES_EMPTY, row.features)
            self.assertEqual(row.feature_classes, [])

            classes_trail = _trail_line(
                partial=False, attempts=COMPLETE_ATTEMPTS, features="Function|Array"
            )
            row = _row(
                tmp,
                _capture(
                    tmp, "c.out", ["; features none", "unsat", classes_trail]
                ),
            )
            self.assertEqual(row.features, "Function|Array", row.features)
            self.assertEqual(row.feature_classes, ["Function", "Array"])

    def test_corpus_path_is_stored_whole_and_not_reduced_to_a_basename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            row = _row(tmp, capture)
            self.assertEqual(row.corpus_path, "QF_LRA/sub/dir/x.smt2")


class Aggregates(unittest.TestCase):
    """ADR-2075's error, as a refusal."""

    def _mixed(self, tmp: Path) -> list[ol.LedgerRow]:
        complete = _capture(
            tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
        )
        partial = _capture(
            tmp, "p.out", ["unknown", _trail_line(partial=True, attempts=PARTIAL_ATTEMPTS)]
        )
        return [_row(tmp, complete), _row(tmp, partial, corpus_path="QF_LRA/p.smt2")]

    def test_verdict_counts_refuses_a_population_containing_a_partial_reading(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rows = self._mixed(Path(tmpdir))
            with self.assertRaises(ol.PartialInAggregate):
                ol.verdict_counts(rows)

    def test_verdict_counts_sums_when_told_to(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rows = self._mixed(Path(tmpdir))
            counts = ol.verdict_counts(rows, include_partial=True)
            self.assertEqual(counts, {"unsat": 1, "unknown": 1})

    def test_an_unknown_completeness_row_is_refused_too(self):
        """`unknown` is not a synonym for `no`.

        A capture with no trail cannot say whether the reading was a total.
        Letting it through because it is "not marked partial" is the ADR-2075
        collapse in the other direction.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            rows = [
                _row(
                    tmp,
                    _capture(
                        tmp,
                        "c.out",
                        ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)],
                    ),
                ),
                _row(tmp, _capture(tmp, "a.out", ["(error \"boom\")"]), exit_status=134),
            ]
            with self.assertRaises(ol.PartialInAggregate):
                ol.verdict_counts(rows)

    def test_bound_by_includes_partials_by_default_because_that_is_where_it_matters(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rows = self._mixed(Path(tmpdir))
            counts = ol.bound_by_counts(rows)
            self.assertEqual(counts, {"qf-bv": 1, "q:bool-skeleton": 1})


class Staleness(unittest.TestCase):
    """Exit criterion 3, driven against a real repository in both directions."""

    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.repo = Path(self._dir.name) / "repo"
        self.repo.mkdir()
        env = {
            **os.environ,
            "GIT_AUTHOR_NAME": "t",
            "GIT_AUTHOR_EMAIL": "t@example.com",
            "GIT_COMMITTER_NAME": "t",
            "GIT_COMMITTER_EMAIL": "t@example.com",
        }
        self.env = env
        self._git("init", "-b", "main")
        (self.repo / "f").write_text("a\n", encoding="utf-8")
        self._git("add", "f")
        self._git("commit", "-m", "a")
        self.on_main = self._git("rev-parse", "HEAD").strip()
        self._git("checkout", "-b", "lane")
        (self.repo / "f").write_text("b\n", encoding="utf-8")
        self._git("commit", "-am", "b")
        self.on_branch = self._git("rev-parse", "HEAD").strip()
        self._git("checkout", "main")

    def tearDown(self):
        self._dir.cleanup()

    def _git(self, *args: str) -> str:
        proc = subprocess.run(
            ["git", *args],
            cwd=self.repo,
            env=self.env,
            capture_output=True,
            text=True,
            check=True,
        )
        return proc.stdout

    def _rows(self, *shas: str) -> list[ol.LedgerRow]:
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            return [_row(tmp, capture, binary_sha=sha) for sha in shas]

    def test_a_main_ancestor_binary_is_not_flagged(self):
        flagged = ol.flag_stale(self._rows(self.on_main), repo=self.repo)
        self.assertEqual(flagged, [])

    def test_a_branch_binary_is_flagged(self):
        flagged = ol.flag_stale(self._rows(self.on_branch), repo=self.repo)
        self.assertEqual(len(flagged), 1)
        self.assertEqual(flagged[0].binary_sha, self.on_branch)

    def test_a_sha_that_does_not_resolve_is_flagged_rather_than_waved_through(self):
        """"I cannot check this" is reported as stale, not as fine.

        A row from a deleted branch, or from a binary whose commit was never
        pushed anywhere, must not read as a `main` measurement just because the
        ancestor query errored.
        """
        flagged = ol.flag_stale(self._rows("0" * 40), repo=self.repo)
        self.assertEqual(len(flagged), 1)

    def test_an_unknown_commit_is_not_reported_as_a_branch(self):
        """The three-valued classification, and the reason it has three values.

        `git merge-base --is-ancestor <garbage> main` exits non-zero all by
        itself, so a two-valued rule flags this row correctly and says
        "branch" -- sending a reader to look for a branch that does not exist.
        Measured: with the existence check deleted every OTHER test in this
        file stays green, which is why this one has to exist separately.
        """
        self.assertEqual(
            ol.sha_status("0" * 40, repo=self.repo), ol.SHA_UNKNOWN
        )
        self.assertEqual(ol.sha_status(self.on_branch, repo=self.repo), ol.SHA_ON_BRANCH)
        self.assertEqual(ol.sha_status(self.on_main, repo=self.repo), ol.SHA_ON_MAIN)

    def test_load_raises_unless_allow_branch(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            ol.append_row(
                "fixture", _row(tmp, capture, binary_sha=self.on_branch), ledger_dir=ledger
            )
            with self.assertRaises(ol.StaleRows):
                ol.load(["fixture"], ledger_dir=ledger, repo=self.repo)
            rows, flagged = ol.load(
                ["fixture"], ledger_dir=ledger, allow_branch=True, repo=self.repo
            )
            self.assertEqual(len(rows), 1)
            self.assertEqual(len(flagged), 1)

    def test_a_flagged_row_is_still_returned(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            ol.append_row(
                "fixture", _row(tmp, capture, binary_sha=self.on_branch), ledger_dir=ledger
            )
            ol.append_row(
                "fixture",
                _row(tmp, capture, binary_sha=self.on_main, corpus_path="QF_LRA/y.smt2"),
                ledger_dir=ledger,
            )
            rows, flagged = ol.load(
                ["fixture"], ledger_dir=ledger, allow_branch=True, repo=self.repo
            )
            self.assertEqual(len(rows), 2)
            self.assertEqual(len(flagged), 1)


class AppendOnly(unittest.TestCase):
    def test_the_header_is_written_once_and_rows_accumulate(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            for i in range(3):
                ol.append_row(
                    "fixture",
                    _row(tmp, capture, corpus_path=f"QF_LRA/{i}.smt2"),
                    ledger_dir=ledger,
                )
            text = (ledger / "fixture.tsv").read_text(encoding="utf-8")
            self.assertEqual(text.count("\t".join(ol.COLUMNS)), 1)
            self.assertEqual(len(ol.read_ledger(ledger / "fixture.tsv")), 3)

    def test_the_index_registers_each_sweep_exactly_once(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            for i in range(3):
                ol.append_row(
                    "fixture",
                    _row(tmp, capture, corpus_path=f"QF_LRA/{i}.smt2"),
                    ledger_dir=ledger,
                )
            ol.append_row(
                "second",
                _row(tmp, capture, sweep_id="second"),
                ledger_dir=ledger,
            )
            lines = (ledger / ol.INDEX_NAME).read_text(encoding="utf-8").splitlines()
            self.assertEqual(lines[0], "\t".join(ol.INDEX_COLUMNS))
            self.assertEqual([line.split("\t")[0] for line in lines[1:]], ["fixture", "second"])

    def test_register_is_idempotent_so_a_consolidation_can_be_re_run(self):
        """A sharded sweep registers its files after the fact, sequentially.

        Concurrent appends to one index over NFS are a read-then-append race,
        and a ledger row can exceed the 4 KiB that makes an `O_APPEND` write
        atomic -- the dry-run row in ADR-2102 is 3.8 KiB of decline details on
        ONE file. So shards write per-shard directories and the consolidation
        registers each one; running that twice must not double the index.
        """
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            ledger = tmp / "ledger"
            capture = _capture(
                tmp, "c.out", ["unsat", _trail_line(partial=False, attempts=COMPLETE_ATTEMPTS)]
            )
            ol.append_row("fixture", _row(tmp, capture), ledger_dir=ledger)
            ol.register("fixture", ledger_dir=ledger, note="again")
            ol.register("fixture", ledger_dir=ledger, note="and again")
            lines = (ledger / ol.INDEX_NAME).read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(lines), 2, lines)

    def test_a_sweep_id_cannot_escape_the_ledger_directory(self):
        with self.assertRaises(ol.LedgerError):
            ol.ledger_path("../../etc/passwd")


if __name__ == "__main__":
    unittest.main()
