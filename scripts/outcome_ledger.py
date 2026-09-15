#!/usr/bin/env python3
"""The outcome ledger (ADR-2102) — Phase 3 of the dispatch-and-instrumentation plan.

Every sweep this repository ran in the week before this file existed produced
``(file -> route that decided -> elapsed -> routes declined and why)`` and threw
it away after grepping ONE token out of it.  Three measured consequences:

  * ``bench-results/dispatch-plan-sizing-20260915/README.md`` had to RE-RUN 645
    undecided Tier 1 rows with ``--trace`` because the harness that produced
    them captured stdout into a shell variable, grepped the verdict, and
    discarded the rest -- and would have carried no routing lines anyway,
    because it never passed ``--trace``.
  * ADR-2035 re-derived 22 "declining" rows to find 8 of them decided anyway.
  * ADR-2050 re-derived 13 rows per-row to check a list it had inherited.

This module is the table that makes each of those a query.

----------------------------------------------------------------------------
What it is NOT
----------------------------------------------------------------------------

**It does not replace the interleaved A/B.**  The ledger RECORDS; the A/B is
still how a claim is made.  The same binary scored 77, 79 and 85 on one
division in a single day purely on ambient load, so a delta computed between
two single-arm ledger runs at different loads is that error with a database in
front of it.  Every aggregate here carries ``binary_sha``, ``host``, ``load``
and ``partial`` for exactly that reason, and :func:`verdict_counts` refuses a
population containing partial readings unless told.

----------------------------------------------------------------------------
Why TSV and not JSONL
----------------------------------------------------------------------------

JSONL needs no escaping invented and would make the separator bug (ADR-2020)
structurally unreachable, which is a real argument for it.  TSV wins anyway,
for reasons that are about how measurements are CHECKED here:

  * every board, census and sizing artifact in this repository is a TSV
    (``phase1-ceiling.tsv`` is already 645 rows in nearly this shape), and
    exit criterion 2 of ADR-2102 literally ``join``s ledger rows against those
    files by ``corpus_path``;
  * ``cut -f``, ``sort``, ``join`` and ``awk`` are how every number here gets
    spot-checked, and a ledger nobody can spot-check by hand is a worse ledger
    than one with an escape function;
  * the separator hazard is answered by making THIS MODULE the only writer and
    the only reader, with one :func:`_escape` / :func:`_unescape` pair and a
    hostile round-trip fixture (tab, newline, CR, ``|``, ``;``, ``=``, quote,
    backslash) in the control suite.

----------------------------------------------------------------------------
Layout
----------------------------------------------------------------------------

    bench-results/ledger/INDEX.tsv        one row per sweep, append-only
    bench-results/ledger/<sweep-id>.tsv   the rows, append-only

Both are append-only.  Nothing in this module rewrites a row: a re-measurement
is a NEW row with a new ``sweep_id``, so the table keeps the history that makes
"did that change at commit Y" answerable at all.

----------------------------------------------------------------------------
Usage
----------------------------------------------------------------------------

As a library::

    from outcome_ledger import append_row, load, row_from_capture

    row = row_from_capture("out/000123.out", corpus_path="QF_LRA/x.smt2", ...)
    append_row("ab-smoke", row)

    rows, stale = load(["ab-smoke"])          # stale rows are FLAGGED, not dropped
    rows, stale = load(["ab-smoke"], allow_branch=True)

As a command::

    scripts/outcome_ledger.py append --sweep-id S --arm A ...   # one row
    scripts/outcome_ledger.py show   --sweep-id S [--allow-branch]
    scripts/outcome_ledger.py agg    --sweep-id S [--include-partial]

Exit status depends on the finding: ``show`` exits non-zero when a row is
flagged stale and ``--allow-branch`` was not given, and ``agg`` exits non-zero
when it refuses a population.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import route_trace_reader as rtr  # noqa: E402

#: Where sweeps write.  Relative to the repository root.
LEDGER_DIR = Path("bench-results/ledger")

#: The index every sweep registers itself in, so `load` can enumerate without
#: globbing and a reader can see at a glance which sweeps exist.
INDEX_NAME = "INDEX.tsv"

#: Bumped on ANY column rename, removal, reordering or addition.  A reader that
#: guesses at an unknown schema is how ADR-2075's watchdog rows were swept into
#: an aggregate that thought it had totals; this refuses instead.
#:
#: **2** adds `decline_names` (ADR-2104's typed detail variant).  The table is
#: append-only, so a file keeps the schema it was opened with: `read_ledger`
#: understands every version in :data:`KNOWN_HEADERS` and `append_row` refuses
#: to append a newer row to an older file rather than silently dropping the
#: column.  A new sweep gets a new file and the current schema.
SCHEMA_VERSION = 2

#: The intra-field separator, fixed at `|` and never `;`.  ADR-2020: a census
#: split records on `;` when the `why=` field CONTAINS `;`, and truncated its
#: own largest bucket.  `|` is escaped inside a field (see `_escape`), so this
#: is a real separator rather than a hopeful one.
LIST_SEP = "|"

#: Schema 1: the plan's §4 list, and the shape of every row written before
#: ADR-2104 typed the decline detail.  Kept so the committed sweeps stay
#: readable -- an append-only table that cannot read its own history is not one.
COLUMNS_V1: tuple[str, ...] = (
    "sweep_id",
    "arm",
    "corpus_path",
    "binary_sha",
    "features",
    "verdict",
    "exit_status",
    "decided_by",
    "bound_by",
    "attempts",
    "attempt_trail",
    "elapsed_ms",
    "elapsed_ms_per_attempt",
    "partial",
    "decline_reasons",
    "decline_details",
    "host",
    "core",
    "load",
)

#: Every column of the CURRENT schema, in order.  This tuple is what
#: `append_row` writes and validates against.
COLUMNS: tuple[str, ...] = (
    # -- which run this row belongs to -----------------------------------
    "sweep_id",
    "arm",
    # -- what was measured -----------------------------------------------
    "corpus_path",
    "binary_sha",
    "features",
    # -- the outcome ------------------------------------------------------
    "verdict",
    "exit_status",
    # -- the routing ------------------------------------------------------
    "decided_by",
    "bound_by",
    "attempts",
    "attempt_trail",
    "elapsed_ms",
    "elapsed_ms_per_attempt",
    "partial",
    "decline_reasons",
    "decline_details",
    # ADR-2104 typed the three previously-free-string `DeclineReason` details
    # into closed enums with an exhaustive `name()`. This column carries that
    # NAME per decline, beside the still-free `decline_details` -- the typed
    # axis and the prose axis in two columns rather than one string a consumer
    # has to split, which is ADR-2020's bug pre-empted rather than repeated.
    #
    # It is EMPTY on every row written by a binary whose `to_json` does not yet
    # emit a `name` member -- which today is all of them, including this ADR's
    # own 220. That producer change is `route_trace.rs`'s wire format and
    # belongs to the trace lane, not to this one; the column exists now so the
    # schema does not have to be reopened after the ledger has writers, and the
    # reader path is driven by a fixture so it is not an unfalsifiable column.
    "decline_names",
    # -- the conditions the level has to be read against ------------------
    "host",
    "core",
    "load",
)

#: Every header this reader understands, and which schema version it is.
#: A header that is not in here is REFUSED, not read positionally.
KNOWN_HEADERS: dict[tuple[str, ...], int] = {COLUMNS_V1: 1, COLUMNS: 2}

INDEX_COLUMNS: tuple[str, ...] = ("sweep_id", "file", "schema_version", "created_utc", "note")

#: The three-valued `partial` column.  `unknown` is NOT a synonym for `no`:
#: a capture with no trail line at all cannot say whether the reading was a
#: total, and recording that as `no` is exactly the ADR-2075 collapse.
PARTIAL_YES = "yes"
PARTIAL_NO = "no"
PARTIAL_UNKNOWN = "unknown"

#: **What `features` names, precisely.**  The construct classes of the FIRST
#: query the quantifier-free dispatch ladder scanned in the run, which is not
#: the same as "the file's features" and does not claim to be.  On a
#: quantifier-free file the two coincide.  On a QUANTIFIED file the ladder is
#: only ever reached by a sub-solve, so the column names the fragment that
#: sub-solve was handed -- measured on this lane's own `AUFLIRA` A/B, six of
#: twenty rows record `none` on files full of arrays and reals.  A top-level
#: scan does not exist to record instead.
#:
#: The four values it can take, and the four different things they mean.  Three
#: of them are not a construct list:
#:
#:   ``""``                the binary that produced this capture predates the
#:                         `; features ` line (ADR-2102) and cannot be asked;
#:   ``"not-dispatched"``  the binary printed the line and said the query never
#:                         reached the quantifier-free dispatch ladder, so the
#:                         construct scan never ran.  ADR-2100 measured this at
#:                         **482 of 643** undecided Tier 1 rows -- 75 % -- so it
#:                         is the common case, not an edge one;
#:   ``"none"``            the scan RAN and the construct set was empty (a query
#:                         carrying nothing but Boolean structure).
#:
#: Collapsing any two of these is the absence-read-as-a-zero shape that cost
#: ADR-2075 twelve files.
FEATURES_ABSENT = ""
FEATURES_NOT_DISPATCHED = "not-dispatched"
FEATURES_EMPTY = "none"

#: The CLI line this module reads the construct classes off.  One producer
#: (`crates/axeyum-bench/examples/smtcomp_cli.rs`), one consumer (here).
FEATURES_PREFIX = "; features "


class LedgerError(Exception):
    """Base class for every refusal this module makes."""


class SchemaDrift(LedgerError):
    """A ledger file's header is not :data:`COLUMNS`.

    Raised rather than read positionally.  A writer that emits a column this
    library does not know about, or drops one it does, makes every downstream
    number a measurement of a different table -- and a positional reader would
    not notice, it would just shift.
    """

    def __init__(self, path: str, header: Sequence[str]) -> None:
        self.path = path
        self.header = list(header)
        extra = [c for c in header if c not in COLUMNS]
        missing = [c for c in COLUMNS if c not in header]
        detail = []
        if extra:
            detail.append(f"columns this library does not know: {extra}")
        if missing:
            detail.append(f"columns missing: {missing}")
        if not detail:
            detail.append("same columns, different ORDER")
        super().__init__(f"{path}: schema drift -- " + "; ".join(detail))


class StaleRows(LedgerError):
    """Rows were measured on a binary that is not an ancestor of local `main`.

    A branch measurement read as a main one is the single easiest way to
    publish a number for a tree nobody can check out.  Pass
    ``allow_branch=True`` when a branch measurement is what you mean -- an
    in-flight lane's own A/B, for instance.
    """

    def __init__(self, flagged: Sequence["LedgerRow"]) -> None:
        self.flagged = list(flagged)
        shas = sorted({r.binary_sha for r in self.flagged})
        super().__init__(
            f"{len(self.flagged)} row(s) were measured on binaries that are NOT "
            f"ancestors of local `main`: {shas}. "
            f"Pass allow_branch=True (or --allow-branch) if that is what you mean."
        )


class PartialInAggregate(LedgerError):
    """An aggregate was asked to sum over readings that are not totals.

    ADR-2075: a partial reading's `decided_by` is a statement about the moment
    the reading was taken, not about the run's answer.  Summing those into a
    decision rate is that error with a database in front of it.
    """

    def __init__(self, what: str, paths: Sequence[str]) -> None:
        self.paths = list(paths)
        shown = ", ".join(self.paths[:5])
        more = "" if len(self.paths) <= 5 else f" (+{len(self.paths) - 5} more)"
        super().__init__(
            f"{len(self.paths)} of the rows are PARTIAL or UNKNOWN readings and cannot be "
            f"summed as {what}: {shown}{more}. Pass include_partial=True if that is what "
            f"you mean."
        )


# ---------------------------------------------------------------------------
# Escaping.  One pair of functions, and the control suite's hostile fixture is
# the only thing standing between this table and ADR-2020.
# ---------------------------------------------------------------------------

_ESCAPES = {
    "\\": "\\\\",
    "\t": "\\t",
    "\n": "\\n",
    "\r": "\\r",
    LIST_SEP: "\\p",
}
_UNESCAPES = {
    "\\": "\\",
    "t": "\t",
    "n": "\n",
    "r": "\r",
    "p": LIST_SEP,
}


def _escape(value: str) -> str:
    """Make `value` safe to carry in one TSV field and one `|`-joined element.

    Backslash is escaped FIRST by construction: the loop rewrites each
    character independently, so there is no second pass to re-escape what the
    first one produced.
    """
    return "".join(_ESCAPES.get(ch, ch) for ch in str(value))


def _unescape(value: str) -> str:
    """The exact inverse of :func:`_escape`, as one left-to-right scan.

    Sequential `str.replace` calls are NOT an inverse: unescaping `\\\\t` by
    replacing `\\t` first yields a tab where the original held a literal
    backslash followed by a `t`.
    """
    out: list[str] = []
    index = 0
    while index < len(value):
        ch = value[index]
        if ch == "\\" and index + 1 < len(value):
            nxt = value[index + 1]
            if nxt in _UNESCAPES:
                out.append(_UNESCAPES[nxt])
                index += 2
                continue
        out.append(ch)
        index += 1
    return "".join(out)


def _join(values: Iterable[str]) -> str:
    return LIST_SEP.join(_escape(v) for v in values)


def _split(value: str) -> list[str]:
    if value == "":
        return []
    return [_unescape(part) for part in value.split(LIST_SEP)]


# ---------------------------------------------------------------------------
# The row
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class LedgerRow:
    """One file, one run, one arm.

    Every field is a string on the wire.  The typed accessors below are for
    readers; the writer never has to decide how to render anything.
    """

    sweep_id: str
    arm: str
    corpus_path: str
    binary_sha: str
    features: str
    verdict: str
    exit_status: str
    decided_by: str
    bound_by: str
    attempts: str
    attempt_trail: str
    elapsed_ms: str
    elapsed_ms_per_attempt: str
    partial: str
    decline_reasons: str
    decline_details: str
    host: str
    core: str
    load: str
    #: ADR-2104's typed detail variant name per decline, `|`-joined, in the
    #: same order as `decline_reasons`.  LAST in the dataclass and defaulted
    #: (the wire order is `COLUMNS`, which `to_line` reads, so the two are free
    #: to differ) because a schema-1 row has no such field and must still
    #: construct.
    decline_names: str = ""

    # -- typed views -------------------------------------------------------

    @property
    def is_partial(self) -> bool:
        return self.partial == PARTIAL_YES

    @property
    def partial_is_unknown(self) -> bool:
        return self.partial == PARTIAL_UNKNOWN

    @property
    def attempt_count(self) -> int:
        return int(self.attempts) if self.attempts else 0

    @property
    def trail(self) -> list[str]:
        return _split(self.attempt_trail)

    @property
    def per_attempt_ms(self) -> list[int | None]:
        return [None if v == "" else int(v) for v in _split(self.elapsed_ms_per_attempt)]

    @property
    def reasons(self) -> list[tuple[str, str]]:
        """`(route, reason)` per decline, in dispatch order."""
        out: list[tuple[str, str]] = []
        for item in _split(self.decline_reasons):
            route, _, reason = item.partition("=")
            out.append((route, reason))
        return out

    @property
    def details(self) -> list[str]:
        return _split(self.decline_details)

    @property
    def names(self) -> list[str]:
        """ADR-2104's typed detail variant per decline, in dispatch order.

        ALIGNED one-for-one with :attr:`reasons`, always.  A row whose schema
        has no such column, or whose producer emitted no `name` member, is
        padded with empty strings rather than coming back short -- a consumer
        that zips the three axes together must not have to know which schema
        version each row came from, and a list that is silently shorter is how
        an axis gets read off by one.

        `[]` therefore means "no declines", never "no names"; use
        :attr:`has_typed_names` for that question.
        """
        raw = _split(self.decline_names)
        count = len(self.reasons)
        if len(raw) < count:
            raw = raw + [""] * (count - len(raw))
        return raw

    @property
    def has_typed_names(self) -> bool:
        """Whether ANY decline on this row carries a typed variant name.

        `False` on every row written before the producer emits the `name`
        member -- which is a fact about the BINARY, not about the declines, and
        is why it is a separate question from :attr:`names`.
        """
        return any(name for name in _split(self.decline_names))

    @property
    def feature_classes(self) -> list[str] | None:
        """The construct classes, or `None` when there is no set to report.

        `None` and `[]` are DIFFERENT answers and this returns both: `[]` means
        the scan ran and the set was empty; `None` means there is no set, for
        one of the two reasons :attr:`features` distinguishes -- read that
        column, or :attr:`scan_ran`, when the reason matters.
        """
        if self.features in (FEATURES_ABSENT, FEATURES_NOT_DISPATCHED):
            return None
        if self.features == FEATURES_EMPTY:
            return []
        return _split(self.features)

    @property
    def scan_ran(self) -> bool | None:
        """Whether the construct scan ran: `True`/`False`, or `None` if unasked.

        `None` is the row whose binary predates the instrument -- "I cannot
        tell", which is not the same as `False`.
        """
        if self.features == FEATURES_ABSENT:
            return None
        return self.features != FEATURES_NOT_DISPATCHED

    # -- wire form ---------------------------------------------------------

    def to_line(self) -> str:
        values = [getattr(self, column) for column in COLUMNS]
        return "\t".join(_escape(v) for v in values)

    @classmethod
    def from_line(cls, line: str, header: Sequence[str]) -> "LedgerRow":
        fields = line.rstrip("\n").split("\t")
        if len(fields) != len(header):
            raise SchemaDrift("<row>", header)
        values = {name: _unescape(value) for name, value in zip(header, fields)}
        # Columns the row's schema does not have come back EMPTY rather than
        # absent, so a caller reading a mixed population does not have to know
        # which version each row came from to touch a field.
        for column in COLUMNS:
            values.setdefault(column, "")
        return cls(**values)


# ---------------------------------------------------------------------------
# Building a row from a capture
# ---------------------------------------------------------------------------

_VERDICT_TOKENS = ("sat", "unsat", "unknown")


def verdict_from_stdout(text: str, exit_status: int) -> str:
    """The verdict token the CLI printed, or `abort`/`none`.

    Matches the harness convention every sweep here uses -- the FIRST bare
    `sat`/`unsat`/`unknown` line -- and then adds the distinction ADR-2045
    measured and the boards did not: a run that printed no verdict and exited
    non-zero is an **abort**, which is its own outcome and not an `unknown`.
    """
    for line in text.splitlines():
        token = line.strip()
        if token in _VERDICT_TOKENS:
            return token
    return "abort" if exit_status != 0 else "none"


def features_from_stdout(text: str) -> str:
    """The `; features ` line's payload, or :data:`FEATURES_ABSENT`.

    Read off the machine form the CLI prints under `--trace`
    (``; features Int|Real`` / ``; features none`` /
    ``; features not-dispatched``), not off any prose.  A binary built before
    ADR-2102 prints no such line at all, and the empty string that comes back
    is a different answer from each of the other three -- see
    :data:`FEATURES_ABSENT`.
    """
    for line in text.splitlines():
        if line.startswith(FEATURES_PREFIX):
            payload = line[len(FEATURES_PREFIX) :].strip()
            return payload if payload else FEATURES_EMPTY
    return FEATURES_ABSENT


def row_from_capture(
    stdout_path: str | Path,
    *,
    sweep_id: str,
    arm: str,
    corpus_path: str,
    binary_sha: str,
    exit_status: int,
    elapsed_ms: int,
    host: str,
    core: str,
    load: str,
) -> LedgerRow:
    """Build one row from a `--trace` stdout capture.

    The routing columns come from :mod:`route_trace_reader` and from nothing
    else -- this module never anchors on a `; route ` prefix, which is the bug
    that cost ADR-2075 twelve files and this lane's own predecessor 103 rows.

    A capture with **no trail line** still produces a row.  An aborted or
    killed-before-any-output file is an outcome the ledger exists to record,
    and dropping it would make every rate here a rate over the files that
    happened to finish.  Such a row carries `attempts=0`, empty route columns
    and `partial=unknown`.
    """
    text = Path(stdout_path).read_text(encoding="utf-8", errors="replace")
    verdict = verdict_from_stdout(text, exit_status)
    features = features_from_stdout(text)

    try:
        trail = rtr.read_file(stdout_path)
    except rtr.NoTrailLine:
        trail = None

    if trail is None:
        return LedgerRow(
            sweep_id=sweep_id,
            arm=arm,
            corpus_path=corpus_path,
            binary_sha=binary_sha,
            features=features,
            verdict=verdict,
            exit_status=str(exit_status),
            decided_by="none",
            bound_by="none",
            attempts="0",
            attempt_trail="",
            elapsed_ms=str(elapsed_ms),
            elapsed_ms_per_attempt="",
            partial=PARTIAL_UNKNOWN,
            decline_reasons="",
            decline_details="",
            decline_names="",
            host=host,
            core=core,
            load=load,
        )

    declines = trail.decline_reasons()
    return LedgerRow(
        sweep_id=sweep_id,
        arm=arm,
        corpus_path=corpus_path,
        binary_sha=binary_sha,
        features=features,
        verdict=verdict,
        exit_status=str(exit_status),
        decided_by=trail.decided_by or "none",
        bound_by=trail.bound_by or "none",
        attempts=str(trail.attempt_count),
        attempt_trail=_join(f"{a.route}:{a.outcome}" for a in trail.attempts),
        elapsed_ms=str(elapsed_ms),
        elapsed_ms_per_attempt=_join(
            "" if a.elapsed_ns is None else str(a.elapsed_ns // 1_000_000)
            for a in trail.attempts
        ),
        partial=PARTIAL_YES if trail.partial else PARTIAL_NO,
        decline_reasons=_join(f"{route}={reason}" for route, reason, _ in declines),
        decline_details=_join(detail or "" for _, _, detail in declines),
        # ADR-2104's typed variant name, one per decline in the same order.
        # `""` where the producer emitted no `name` member.
        decline_names=_join(a.name or "" for a in trail.attempts if a.declined),
        host=host,
        core=core,
        load=load,
    )


# ---------------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------------


def ledger_path(sweep_id: str, *, ledger_dir: str | Path = LEDGER_DIR) -> Path:
    if "/" in sweep_id or sweep_id in ("", ".", ".."):
        raise LedgerError(f"sweep_id {sweep_id!r} is not a single path segment")
    return Path(ledger_dir) / f"{sweep_id}.tsv"


def index_path(*, ledger_dir: str | Path = LEDGER_DIR) -> Path:
    return Path(ledger_dir) / INDEX_NAME


def register(
    sweep_id: str, *, ledger_dir: str | Path = LEDGER_DIR, note: str = ""
) -> None:
    """Append this sweep to the index, once.

    The index is append-only and carries no counts: a count would have to be
    rewritten on every append, and a file that gets rewritten is a file two
    lanes can clobber.  `load` counts rows itself.

    Public because a SHARDED sweep writes its rows on several hosts into
    several per-shard ledger directories (concurrent appends to one index over
    NFS are a read-then-append race, and a row here can exceed the 4 KiB that
    makes an `O_APPEND` write atomic), and the consolidation step then needs to
    register each finished file into the repository's index SEQUENTIALLY.
    Idempotent, so running it twice is not an error.
    """
    path = ledger_path(sweep_id, ledger_dir=ledger_dir)
    idx = index_path(ledger_dir=ledger_dir)
    existing: set[str] = set()
    if idx.exists():
        with idx.open("r", encoding="utf-8") as handle:
            for i, line in enumerate(handle):
                if i == 0:
                    continue
                existing.add(line.split("\t", 1)[0])
    if sweep_id in existing:
        return
    idx.parent.mkdir(parents=True, exist_ok=True)
    new = not idx.exists()
    with idx.open("a", encoding="utf-8") as handle:
        if new:
            handle.write("\t".join(INDEX_COLUMNS) + "\n")
        handle.write(
            "\t".join(
                _escape(v)
                for v in (
                    sweep_id,
                    path.name,
                    str(SCHEMA_VERSION),
                    time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                    note,
                )
            )
            + "\n"
        )


def append_row(
    sweep_id: str,
    row: LedgerRow,
    *,
    ledger_dir: str | Path = LEDGER_DIR,
    note: str = "",
) -> Path:
    """Append one row, creating the file and its header if need be.

    Validates the existing header against :data:`COLUMNS` BEFORE writing, so a
    schema drift is caught at the writer rather than discovered by a reader
    three sweeps later.
    """
    if row.sweep_id != sweep_id:
        raise LedgerError(
            f"row.sweep_id={row.sweep_id!r} does not match the file it is being "
            f"appended to ({sweep_id!r}); a row must name its own sweep"
        )
    path = ledger_path(sweep_id, ledger_dir=ledger_dir)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.stat().st_size > 0:
        with path.open("r", encoding="utf-8") as handle:
            header = handle.readline().rstrip("\n").split("\t")
        # A FILE keeps the schema it was opened with. Appending a current row
        # to an older file would either shift every field or silently drop the
        # newer column; both are worse than refusing, and a sweep is one file,
        # so the fix is always "start the next sweep".
        if tuple(header) != COLUMNS:
            raise SchemaDrift(str(path), header)
        prelude = ""
    else:
        prelude = "\t".join(COLUMNS) + "\n"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(prelude + row.to_line() + "\n")
    register(sweep_id, ledger_dir=ledger_dir, note=note)
    return path


# ---------------------------------------------------------------------------
# Staleness
# ---------------------------------------------------------------------------


def _git(args: Sequence[str], *, repo: str | Path | None = None) -> tuple[int, str]:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(repo) if repo else None,
        capture_output=True,
        text=True,
    )
    return proc.returncode, proc.stdout.strip()


#: What a row's `binary_sha` turned out to be, checked against local `main`.
#:
#: THREE values and not two, for the same reason `partial` has three: a commit
#: this repository has never seen is a different finding from one on a live
#: branch, and reporting both as "stale" tells a reader to go and look at a
#: branch that may not exist.  A row from a deleted lane, a truncated sha, or a
#: binary built somewhere else all land in `unknown-commit`.
SHA_ON_MAIN = "main"
SHA_ON_BRANCH = "branch"
SHA_UNKNOWN = "unknown-commit"


def sha_status(sha: str, *, repo: str | Path | None = None, main: str = "main") -> str:
    """Classify one `binary_sha`: on `main`, on a branch, or unknown.

    Local `main`, deliberately: `origin/main` lags during a push window, and a
    row written from a commit that is on local main but not yet pushed is not a
    branch measurement.

    The existence check is separate from the ancestor check ON PURPOSE, and
    this module's own mutation control is why the comment says so.
    `git merge-base --is-ancestor <garbage> main` also exits non-zero, so
    folding the two together still answers "not an ancestor" and every test
    stays green -- while a row whose commit this repository has never seen gets
    reported as though a reader could go and look at it.  Deleting the check
    was measured as SURVIVED before this distinction existed.
    """
    if not sha:
        return SHA_UNKNOWN
    code, _ = _git(["cat-file", "-e", f"{sha}^{{commit}}"], repo=repo)
    if code != 0:
        return SHA_UNKNOWN
    code, _ = _git(["merge-base", "--is-ancestor", sha, main], repo=repo)
    return SHA_ON_MAIN if code == 0 else SHA_ON_BRANCH


def is_main_ancestor(sha: str, *, repo: str | Path | None = None, main: str = "main") -> bool:
    """Whether `sha` is an ancestor of the LOCAL `main`."""
    return sha_status(sha, repo=repo, main=main) == SHA_ON_MAIN


def sha_statuses(
    rows: Sequence[LedgerRow], *, repo: str | Path | None = None, main: str = "main"
) -> dict[str, str]:
    """Each DISTINCT `binary_sha` in `rows`, classified.  One `git` call each."""
    out: dict[str, str] = {}
    for row in rows:
        if row.binary_sha not in out:
            out[row.binary_sha] = sha_status(row.binary_sha, repo=repo, main=main)
    return out


def flag_stale(
    rows: Sequence[LedgerRow], *, repo: str | Path | None = None, main: str = "main"
) -> list[LedgerRow]:
    """Every row whose `binary_sha` is not an ancestor of local `main`.

    One `git` call per DISTINCT sha, not per row.
    """
    statuses = sha_statuses(rows, repo=repo, main=main)
    return [row for row in rows if statuses[row.binary_sha] != SHA_ON_MAIN]


# ---------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------


def schema_of(header: Sequence[str]) -> int:
    """The schema version this header is, or a refusal.

    Looked up in :data:`KNOWN_HEADERS` rather than compared against the current
    `COLUMNS` alone: an append-only table whose reader cannot read its own
    history is not an append-only table.  A header that is in no version is
    REFUSED and never read positionally -- a writer that invented a column, or
    dropped one, would otherwise just shift every field one place.
    """
    version = KNOWN_HEADERS.get(tuple(header))
    if version is None:
        raise SchemaDrift("<header>", header)
    return version


def read_ledger(path: str | Path) -> list[LedgerRow]:
    """Every row in one ledger file, refusing on schema drift."""
    path = Path(path)
    with path.open("r", encoding="utf-8") as handle:
        header_line = handle.readline()
        if not header_line:
            return []
        header = header_line.rstrip("\n").split("\t")
        if tuple(header) not in KNOWN_HEADERS:
            raise SchemaDrift(str(path), header)
        return [LedgerRow.from_line(line, header) for line in handle if line.strip()]


def load(
    sweep_ids: Iterable[str],
    *,
    ledger_dir: str | Path = LEDGER_DIR,
    allow_branch: bool = False,
    repo: str | Path | None = None,
    main: str = "main",
) -> tuple[list[LedgerRow], list[LedgerRow]]:
    """Load sweeps, flagging rows measured on a non-`main` binary.

    Returns `(rows, flagged)`.  Nothing is dropped: the flagged rows are ALSO
    in `rows`, because a lane's own in-flight A/B is a legitimate thing to
    read -- what is not legitimate is reading it as a main measurement without
    noticing.  With `allow_branch=False` (the default) a non-empty `flagged`
    raises :class:`StaleRows`.
    """
    rows: list[LedgerRow] = []
    for sweep_id in sweep_ids:
        rows.extend(read_ledger(ledger_path(sweep_id, ledger_dir=ledger_dir)))
    flagged = flag_stale(rows, repo=repo, main=main)
    if flagged and not allow_branch:
        raise StaleRows(flagged)
    return rows, flagged


# ---------------------------------------------------------------------------
# Aggregates
# ---------------------------------------------------------------------------


def _guard_partials(rows: Sequence[LedgerRow], what: str, include_partial: bool) -> None:
    if include_partial:
        return
    suspect = [
        r.corpus_path for r in rows if r.is_partial or r.partial_is_unknown
    ]
    if suspect:
        raise PartialInAggregate(what, suspect)


def _counts(keys: Iterable[str]) -> dict[str, int]:
    out: dict[str, int] = {}
    for key in keys:
        out[key] = out.get(key, 0) + 1
    return out


def verdict_counts(
    rows: Sequence[LedgerRow], *, include_partial: bool = False
) -> dict[str, int]:
    """How many rows carry each verdict.  REFUSES over partial/unknown rows."""
    _guard_partials(rows, "verdicts", include_partial)
    return _counts(r.verdict for r in rows)


def decided_by_counts(
    rows: Sequence[LedgerRow], *, include_partial: bool = False
) -> dict[str, int]:
    """How many rows each route decided.  REFUSES over partial/unknown rows."""
    _guard_partials(rows, "decisions", include_partial)
    return _counts(r.decided_by for r in rows)


def bound_by_counts(
    rows: Sequence[LedgerRow], *, include_partial: bool = True
) -> dict[str, int]:
    """How many rows each route BOUND.

    Partials are included by default here and that is deliberate: an undecided
    file is exactly where "which route ate the budget" matters.  Read it beside
    the fact that an attempt is recorded when it FINISHES, so on a killed run
    the route actually consuming the budget contributed nothing.
    """
    _guard_partials(rows, "bindings", include_partial)
    return _counts(r.bound_by for r in rows)


def decline_reason_counts(
    rows: Sequence[LedgerRow], *, include_partial: bool = True
) -> dict[str, int]:
    """How often each `(route, reason)` pair declined.  Not a rate."""
    _guard_partials(rows, "declines", include_partial)
    return _counts(f"{route}\t{reason}" for row in rows for route, reason in row.reasons)


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------


def _cmd_append(args: argparse.Namespace) -> int:
    row = row_from_capture(
        args.capture,
        sweep_id=args.sweep_id,
        arm=args.arm,
        corpus_path=args.corpus_path,
        binary_sha=args.binary_sha,
        exit_status=args.exit_status,
        elapsed_ms=args.elapsed_ms,
        host=args.host,
        core=args.core,
        load=args.load,
    )
    path = append_row(args.sweep_id, row, ledger_dir=args.ledger_dir, note=args.note)
    if args.quiet:
        return 0
    print(f"{path}\t{row.corpus_path}\t{row.verdict}\t{row.decided_by}\t{row.partial}")
    return 0


def _cmd_register(args: argparse.Namespace) -> int:
    path = ledger_path(args.sweep_id, ledger_dir=args.ledger_dir)
    if not path.exists():
        print(f"REFUSED: {path} does not exist", file=sys.stderr)
        return 2
    # Reading it validates the header before the index claims it is a ledger.
    rows = read_ledger(path)
    register(args.sweep_id, ledger_dir=args.ledger_dir, note=args.note)
    print(f"registered\t{args.sweep_id}\t{len(rows)} rows")
    return 0


def _cmd_show(args: argparse.Namespace) -> int:
    try:
        rows, flagged = load(
            args.sweep_id,
            ledger_dir=args.ledger_dir,
            allow_branch=True,
        )
    except (SchemaDrift, LedgerError) as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 2
    print("\t".join(COLUMNS))
    for row in rows:
        print(row.to_line())
    if flagged:
        print(
            f"STALE: {len(flagged)} of {len(rows)} rows were measured on a binary that is "
            f"NOT an ancestor of local `main`",
            file=sys.stderr,
        )
        statuses = sha_statuses(flagged)
        for sha in sorted(statuses):
            print(f"  binary_sha {sha}: {statuses[sha]}", file=sys.stderr)
        if not args.allow_branch:
            return 1
    return 0


def _cmd_agg(args: argparse.Namespace) -> int:
    try:
        rows, flagged = load(args.sweep_id, ledger_dir=args.ledger_dir, allow_branch=True)
    except LedgerError as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 2
    print(f"rows                 : {len(rows)}")
    print(f"partial readings     : {sum(1 for r in rows if r.is_partial)}")
    print(f"unknown completeness : {sum(1 for r in rows if r.partial_is_unknown)}")
    print(f"stale rows (branch)  : {len(flagged)}")
    status = 0
    try:
        counts = verdict_counts(rows, include_partial=args.include_partial)
    except PartialInAggregate as exc:
        print(f"verdicts             : REFUSED -- {exc}", file=sys.stderr)
        status = 1
    else:
        print("-- verdict --")
        for key, count in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {count:6d}  {key}")
    print("-- bound_by (partials included) --")
    for key, count in sorted(
        bound_by_counts(rows, include_partial=True).items(), key=lambda kv: (-kv[1], kv[0])
    ):
        print(f"  {count:6d}  {key}")
    if flagged and not args.allow_branch:
        print(f"STALE: {len(flagged)} rows are branch measurements", file=sys.stderr)
        status = 1
    return status


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--ledger-dir", default=str(LEDGER_DIR), help=f"default {LEDGER_DIR}"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    ap = sub.add_parser("append", help="append one row built from a --trace capture")
    ap.add_argument("--capture", required=True)
    ap.add_argument("--sweep-id", required=True)
    ap.add_argument("--arm", required=True)
    ap.add_argument("--corpus-path", required=True)
    ap.add_argument("--binary-sha", required=True)
    ap.add_argument("--exit-status", type=int, required=True)
    ap.add_argument("--elapsed-ms", type=int, required=True)
    ap.add_argument("--host", default=os.uname().nodename)
    ap.add_argument("--core", default="")
    ap.add_argument("--load", default="")
    ap.add_argument("--note", default="")
    ap.add_argument("--quiet", action="store_true")
    ap.set_defaults(func=_cmd_append)

    rp = sub.add_parser(
        "register", help="add an already-written ledger file to the index (idempotent)"
    )
    rp.add_argument("--sweep-id", required=True)
    rp.add_argument("--note", default="")
    rp.set_defaults(func=_cmd_register)

    sp = sub.add_parser("show", help="print rows, flagging branch measurements")
    sp.add_argument("--sweep-id", action="append", required=True)
    sp.add_argument("--allow-branch", action="store_true")
    sp.set_defaults(func=_cmd_show)

    gp = sub.add_parser("agg", help="verdict / bound_by aggregates")
    gp.add_argument("--sweep-id", action="append", required=True)
    gp.add_argument("--include-partial", action="store_true")
    gp.add_argument("--allow-branch", action="store_true")
    gp.set_defaults(func=_cmd_agg)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
