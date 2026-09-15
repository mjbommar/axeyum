#!/usr/bin/env python3
"""The ONE reader for `smtcomp_cli --trace` route telemetry (ADR-2101).

Every census in this repository used to re-parse the CLI's PROSE rendering of
`RouteTrace`.  Three measured consequences, each its own ADR:

  ADR-2075  a census grepped `^; route `.  The watchdog path prints
            `; partial route `.  Twelve files printing fourteen diagnostic
            lines each matched nothing and were recorded as `bound_by=NONE` --
            "the second-largest unexplained bucket" in two ADRs.  There was
            never an absence; there was a prefix nobody had written the
            consumer half of.
  ADR-2020  a census split records on `;` when the `why=` field CONTAINS `;`.
            It truncated its own largest bucket: 5 outer buckets where there
            were 10, and a 25-row leader that was four distinct causes.
  ADR-2060  one give-up string stood for 28 program points and 15 causes, so
            an `i128` overflow was reported as a clock expiring.

The shape is one shape: the instrument reports through a STRING, the consumer
reads it with a GREP, and nothing typechecks the contract between them.  This
module is the contract.  It reads the `route-trail` JSON -- which the CLI has
emitted on every traced file since ADR-1906 -- and never the prose.

Direction rule: JSON -> prose, never prose -> parse.  The human-readable
`; route …` lines stay, for `git grep` and for eyes; nothing here derives a
number from them.

----------------------------------------------------------------------------
Schema versions, and the one place the prefix is still read
----------------------------------------------------------------------------

Schema 2 (ADR-2101) carries completeness as a top-level `partial` member.
Schema 1 does not, and an artifact written before the bump cannot be asked.
For those, and ONLY for those, this reader falls back to the `; partial `
prose prefix on the trail line itself -- which is legitimate exactly here and
nowhere else, because this is the compatibility shim and there is one of it.
`RouteTrail.partial_source` says which channel answered, so a caller can tell
a stated `false` from an inferred one.

Schema 3 (ADR-2105) adds two more: a per-attempt `name` member on a typed
decline detail (`Attempt.name`), and a top-level `features` member
(`RouteTrail.features`) -- the construct set of the first genuinely-outermost
dispatch scan, moved off a process-global onto the trace itself. Both are
simply absent below schema 3, same "present exactly when there is something
to say" contract the JSON renderer already follows for `detail`; a caller
reading `features` on an older capture falls back to the CLI's own
`; features` prose line (`scripts/outcome_ledger.py`'s `features_from_stdout`
is that fallback) rather than reading `None` as "not-dispatched".

A schema this reader does not know about is REFUSED, not guessed at.

----------------------------------------------------------------------------
Usage
----------------------------------------------------------------------------

As a library::

    from route_trace_reader import read_file, read_files, decided_by_counts

    trail = read_file("run.log")           # raises NoTrailLine if there is none
    trail.decided_by                       # "qf-bv", or None
    trail.bound_by                         # the route that consumed the budget
    trail.partial                          # bool
    trail.decline_reasons()                # [(route, reason, detail), ...]

    counts = decided_by_counts(trails)     # REFUSES if any trail is partial
    counts = decided_by_counts(trails, include_partial=True)   # told to

As a command::

    scripts/route_trace_reader.py FILE...            # one TSV row per file
    scripts/route_trace_reader.py --summary FILE...  # decided_by / bound_by

Exit status depends on the finding: a file with no trail line is named on
stderr and makes the command exit non-zero.  A checker that cannot fail is
worse than no checker.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

#: Schema versions this reader understands.  A newer one is refused rather
#: than read optimistically: a member this code does not know about may be the
#: one that changes what the numbers mean.
KNOWN_SCHEMA_VERSIONS = frozenset({1, 2, 3})

#: The first schema version that states completeness as a field.  Below this,
#: `partial` is inferred from the line prefix -- see the module docstring.
FIRST_SCHEMA_WITH_PARTIAL_FIELD = 2

#: The first schema version that carries the per-attempt typed-detail `name`
#: member (ADR-2104's variant name, e.g. `"backend"`, `"ingest-refusal"`) and
#: the top-level `features` member (ADR-2102's construct-set column, moved off
#: a process-global onto the trace by ADR-2105).  Below this, `Attempt.name`
#: is always `None` and `RouteTrail.features` is always `None` -- which reads
#: as "the binary predates the member", never as "not-dispatched" (that is a
#: real, different, schema-3 answer -- see `RouteTrail.features`).
FIRST_SCHEMA_WITH_NAME_AND_FEATURES = 3

#: The complete and the partial spelling of the trail line.  These two literals
#: are the ONLY place in this repository that should know the prefix exists.
TRAIL_PREFIX = "; route-trail "
PARTIAL_TRAIL_PREFIX = "; partial route-trail "

#: The line the CLI prints when attribution recorded nothing at all.  Distinct
#: from "no route line whatsoever": one says the instrument ran and had nothing,
#: the other says the instrument never ran.  Collapsing them is how an absence
#: gets read as a zero.
UNAVAILABLE_PREFIXES = ("; route unavailable:", "; partial route unavailable:")


class RouteTraceError(Exception):
    """Base class for every refusal this reader makes."""


class NoTrailLine(RouteTraceError):
    """The named file carries no `route-trail` line.

    Carries the path and, when the file said so itself, the CLI's own
    `route unavailable:` reason -- so "the instrument ran and recorded
    nothing" never renders the same as "this file was never traced".
    """

    def __init__(self, path: str, unavailable_reason: str | None = None) -> None:
        self.path = path
        self.unavailable_reason = unavailable_reason
        if unavailable_reason is None:
            super().__init__(f"{path}: no `route-trail` line (was it run with --trace?)")
        else:
            super().__init__(
                f"{path}: attribution recorded nothing: {unavailable_reason}"
            )


class UnknownSchema(RouteTraceError):
    """The trail declares a schema version this reader does not understand."""

    def __init__(self, path: str, version: object) -> None:
        self.path = path
        self.version = version
        super().__init__(
            f"{path}: route-trail schema_version={version!r}, "
            f"this reader knows {sorted(KNOWN_SCHEMA_VERSIONS)}"
        )


class PartialInAggregate(RouteTraceError):
    """An aggregate was asked to sum over readings that are not totals.

    Raised by :func:`decided_by_counts` and friends rather than silently
    including or silently dropping the partial rows.  Both of those are how a
    mid-search reading becomes a total; see ADR-2075.
    """

    def __init__(self, partial_paths: Sequence[str]) -> None:
        self.partial_paths = list(partial_paths)
        shown = ", ".join(self.partial_paths[:5])
        more = "" if len(self.partial_paths) <= 5 else f" (+{len(self.partial_paths) - 5} more)"
        super().__init__(
            f"{len(self.partial_paths)} of the trails are PARTIAL readings and "
            f"cannot be summed as totals: {shown}{more}. "
            f"Pass include_partial=True if that is what you mean."
        )


@dataclass(frozen=True)
class Attempt:
    """One recorded route attempt, exactly as the trail records it."""

    route: str
    #: `"probe"`, `"decided"` or `"declined"`.
    outcome: str
    #: `"sat"`/`"unsat"` on a decided attempt, else `None`.
    verdict: str | None = None
    #: The decline reason token (`"unsupported"`, `"budget"`, …), else `None`.
    reason: str | None = None
    #: The `UnknownKind` wire name, present only on an `incomplete` decline.
    kind: str | None = None
    #: ADR-2104's typed detail VARIANT name (`"backend"`, `"ingest-refusal"`,
    #: …), present only once the producer emits a `name` member beside
    #: `detail`.  `None` on every artifact written before it does -- which is
    #: a different answer from `""`, and the reason this is read with `.get`
    #: rather than assumed.
    name: str | None = None
    #: The producer's own message, present exactly when the variant carries one.
    detail: str | None = None
    #: This attempt's own wall clock, when the timed serializer was used.
    elapsed_ns: int | None = None

    @property
    def decided(self) -> bool:
        return self.outcome == "decided"

    @property
    def declined(self) -> bool:
        return self.outcome == "declined"


@dataclass(frozen=True)
class RouteTrail:
    """One file's route telemetry, read from the JSON and from nothing else."""

    path: str
    schema_version: int
    attempts: tuple[Attempt, ...]
    partial: bool
    #: `"field"` when the JSON stated it (schema >= 2), `"prefix"` when it was
    #: inferred from the `; partial ` prose marker on a schema-1 artifact.
    #: A caller that must not infer checks this.
    partial_source: str
    #: On a partial reading: the route the trail most recently RECORDED, which
    #: is the BOUNDARY the open segment started at -- not the route that was
    #: running.  `None` on a complete trail or an unmarked schema-1 one.
    in_flight_after: str | None = None
    #: On a schema-2 partial reading: the segment no attempt accounts for.
    open_segment_ns: int | None = None
    #: The construct set of the first genuinely-outermost dispatch scan
    #: (ADR-2102's ledger `features` column, moved onto the trace by
    #: ADR-2105) -- `"Int|Real"`, `"none"` for a scan that ran and found no
    #: construct, or `None`.
    #:
    #: `None` is ambiguous ON ITS OWN and deliberately so -- it means ONE of
    #: two different things, and which one depends on :attr:`schema_version`:
    #: below :data:`FIRST_SCHEMA_WITH_NAME_AND_FEATURES` it means "this
    #: artifact predates the member and cannot be asked" (the caller's own
    #: fallback -- e.g. the CLI's `; features` prose line on an older capture
    #: -- is the only source left); at or above it, it means the JSON member
    #: was genuinely absent, which is schema 3's real, stated answer
    #: "not-dispatched" (no genuinely-outermost scan ever ran). Collapsing
    #: those two is the exact absence-read-as-a-zero shape ADR-2075 cost
    #: twelve files; a caller that must tell them apart checks
    #: `schema_version` beside this field, the same discipline
    #: `partial_source` already uses for `partial`.
    features: str | None = None
    #: The whole line, kept so a caller can quote its evidence verbatim.
    raw_line: str = field(default="", repr=False)

    # -- the four fields every census asked the prose for ------------------

    @property
    def decided_by(self) -> str | None:
        """The route that decided the query, or `None` when nothing did.

        The LAST decided attempt, matching `RouteTrace::decided_by`: the front
        door's second-chance ladder can legitimately re-decide, and the final
        decisive entry is the one whose verdict was actually returned.
        """
        for attempt in reversed(self.attempts):
            if attempt.decided:
                return attempt.route
        return None

    @property
    def verdict(self) -> str | None:
        """The verdict the deciding route returned, or `None`."""
        for attempt in reversed(self.attempts):
            if attempt.decided:
                return attempt.verdict
        return None

    @property
    def bound_by(self) -> str | None:
        """The route that consumed the most wall clock, or `None`.

        Ties go to the LATER attempt, matching `RouteTrace::bound_by`'s
        `max_by_key` (which returns the last maximum): among equally expensive
        segments the later one is the closer cause of the budget running out.

        On a partial reading this is the known-misleading field -- an attempt
        is recorded when it FINISHES, so the route actually eating the budget
        has contributed nothing to the comparison.  :attr:`bound_by_is_the_answer`
        is the guard, and it is a real question rather than a caveat in prose.
        """
        best_index: int | None = None
        best: int = -1
        for index, attempt in enumerate(self.attempts):
            elapsed = attempt.elapsed_ns
            if elapsed is None:
                continue
            if elapsed >= best:
                best, best_index = elapsed, index
        if best_index is None:
            return None
        return self.attempts[best_index].route

    @property
    def last(self) -> str | None:
        """The route that spoke last -- a MESSAGE, not a constraint.

        Kept because the CLI reports it, and reported alongside
        :attr:`bound_by` rather than instead of it.  Classifying by this field
        has been refuted here: a census of 403 files was wrong on 67 of 70 in
        two divisions.
        """
        return self.attempts[-1].route if self.attempts else None

    @property
    def attempt_count(self) -> int:
        return len(self.attempts)

    @property
    def total_elapsed_ns(self) -> int | None:
        """The sum of the per-attempt clocks, or `None` if untimed.

        On a partial reading this is the ATTRIBUTED total and excludes
        :attr:`open_segment_ns`, which is the point of keeping them apart.
        """
        timed = [a.elapsed_ns for a in self.attempts if a.elapsed_ns is not None]
        return sum(timed) if timed else None

    @property
    def total_elapsed_ms(self) -> int | None:
        total = self.total_elapsed_ns
        return None if total is None else total // 1_000_000

    @property
    def bound_by_is_the_answer(self) -> bool:
        """Whether :attr:`bound_by` actually explains where the budget went.

        `False` when the open segment exceeds everything the recorded attempts
        account for -- the shape measured on the one `QF_LRA` blind file that
        took the watchdog path: `bound_by=dl-online bound_ms=20 total_ms=26` on
        a 25,241 ms run.  Every field correct, every conclusion wrong.

        A complete trail has no open segment and always answers `True`.  A
        schema-1 partial cannot tell (the member did not exist), and answers
        `False` -- the conservative direction, since the alternative is
        asserting an explanation the artifact does not support.
        """
        if not self.partial:
            return True
        if self.open_segment_ns is None:
            return False
        attributed = self.total_elapsed_ns or 0
        return self.open_segment_ns <= attributed

    def decline_reasons(self) -> list[tuple[str, str, str | None]]:
        """Every decline as `(route, reason, detail)`, in dispatch order.

        The detail is whatever the producer said, carried whole.  It may
        contain `;`, `=`, quotes and newlines -- which is exactly why this
        comes out of a JSON member and not out of a split (ADR-2020).
        """
        return [
            (a.route, a.reason or "unknown", a.detail)
            for a in self.attempts
            if a.declined
        ]


def _attempt_from_json(obj: dict) -> Attempt:
    return Attempt(
        route=obj["route"],
        outcome=obj["outcome"],
        verdict=obj.get("verdict"),
        reason=obj.get("reason"),
        kind=obj.get("kind"),
        name=obj.get("name"),
        detail=obj.get("detail"),
        elapsed_ns=obj.get("elapsed_ns"),
    )


def parse_trail_line(line: str, path: str = "<line>") -> RouteTrail:
    """Parse one `; route-trail …` / `; partial route-trail …` line.

    Raises :class:`NoTrailLine` if the line is neither.
    """
    stripped = line.rstrip("\n")
    if stripped.startswith(PARTIAL_TRAIL_PREFIX):
        prefix_says_partial = True
        blob = stripped[len(PARTIAL_TRAIL_PREFIX) :]
    elif stripped.startswith(TRAIL_PREFIX):
        prefix_says_partial = False
        blob = stripped[len(TRAIL_PREFIX) :]
    else:
        raise NoTrailLine(path)

    obj = json.loads(blob)
    version = obj.get("schema_version")
    if version not in KNOWN_SCHEMA_VERSIONS:
        raise UnknownSchema(path, version)

    if version >= FIRST_SCHEMA_WITH_PARTIAL_FIELD:
        partial = bool(obj["partial"])
        partial_source = "field"
    else:
        # The compatibility shim, and the only prefix read in the repository.
        partial = prefix_says_partial
        partial_source = "prefix"

    return RouteTrail(
        path=path,
        schema_version=version,
        attempts=tuple(_attempt_from_json(a) for a in obj["attempts"]),
        partial=partial,
        partial_source=partial_source,
        in_flight_after=obj.get("in_flight_after"),
        open_segment_ns=obj.get("open_segment_ns"),
        features=obj.get("features"),
        raw_line=stripped,
    )


def read_file(path: str | Path) -> RouteTrail:
    """The trail in `path`, or a refusal naming the file.

    The LAST trail line wins when a log holds several (a rerun appended to the
    same file): the last one is the run the rest of the log describes.
    """
    path = str(path)
    found: str | None = None
    unavailable: str | None = None
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if line.startswith(TRAIL_PREFIX) or line.startswith(PARTIAL_TRAIL_PREFIX):
                found = line
            else:
                for marker in UNAVAILABLE_PREFIXES:
                    if line.startswith(marker):
                        unavailable = line[len(marker) :].strip()
    if found is None:
        raise NoTrailLine(path, unavailable)
    return parse_trail_line(found, path)


def read_files(
    paths: Iterable[str | Path], *, skip_missing: bool = False
) -> tuple[list[RouteTrail], list[NoTrailLine]]:
    """Read many files.

    Returns `(trails, refusals)`.  Nothing is dropped silently: a file with no
    trail comes back in `refusals`, named, and a caller that ignores that list
    is making a choice it can be held to.  `skip_missing` additionally tolerates
    a path that does not exist, which is a different failure from a file that
    exists and was never traced.
    """
    trails: list[RouteTrail] = []
    refusals: list[NoTrailLine] = []
    for path in paths:
        try:
            trails.append(read_file(path))
        except FileNotFoundError:
            if not skip_missing:
                raise
            refusals.append(NoTrailLine(str(path), "file does not exist"))
        except NoTrailLine as exc:
            refusals.append(exc)
    return trails, refusals


def _guard_partials(trails: Sequence[RouteTrail], include_partial: bool) -> None:
    if include_partial:
        return
    partials = [t.path for t in trails if t.partial]
    if partials:
        raise PartialInAggregate(partials)


def decided_by_counts(
    trails: Sequence[RouteTrail], *, include_partial: bool = False
) -> dict[str, int]:
    """How many files each route decided, `"none"` for the undecided.

    REFUSES a mix containing partial readings unless told to include them.  A
    partial trail's `decided_by` is a prefix of the run's answer, not the
    answer: the query had not finished, so "nothing decided it" is a statement
    about the moment the reading was taken.  Summing those into a decision rate
    is the ADR-2075 error with a dictionary in front of it.
    """
    _guard_partials(trails, include_partial)
    counts: dict[str, int] = {}
    for trail in trails:
        key = trail.decided_by or "none"
        counts[key] = counts.get(key, 0) + 1
    return counts


def bound_by_counts(
    trails: Sequence[RouteTrail], *, include_partial: bool = False
) -> dict[str, int]:
    """How many files each route BOUND -- the route a portfolio must beat.

    Unlike :func:`decided_by_counts` this is meaningful on a partial reading
    (an undecided file is exactly where the question matters), so
    `include_partial=True` is a reasonable thing to pass -- but only alongside
    :attr:`RouteTrail.bound_by_is_the_answer`, which says whether the recorded
    attempts account for the budget at all.  The default still refuses, so the
    caller makes the choice explicitly.
    """
    _guard_partials(trails, include_partial)
    counts: dict[str, int] = {}
    for trail in trails:
        key = trail.bound_by or "none"
        counts[key] = counts.get(key, 0) + 1
    return counts


def decline_reason_counts(
    trails: Sequence[RouteTrail], *, include_partial: bool = True
) -> dict[str, int]:
    """How often each `(route, reason)` pair declined, across the trails.

    Partials are INCLUDED by default here, and that is deliberate: a decline
    that was recorded really happened, whether or not the query went on to
    finish.  The field this cannot be read as is a rate.
    """
    _guard_partials(trails, include_partial)
    counts: dict[str, int] = {}
    for trail in trails:
        for route, reason, _detail in trail.decline_reasons():
            key = f"{route}\t{reason}"
            counts[key] = counts.get(key, 0) + 1
    return counts


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------

_COLUMNS = (
    "file",
    "partial",
    "partial_source",
    "schema",
    "decided_by",
    "verdict",
    "bound_by",
    "bound_is_answer",
    "last",
    "attempts",
    "total_ms",
    "in_flight_after",
    "open_segment_ms",
    "features",
)


def _row(trail: RouteTrail) -> list[str]:
    open_ms = (
        "" if trail.open_segment_ns is None else str(trail.open_segment_ns // 1_000_000)
    )
    return [
        trail.path,
        "yes" if trail.partial else "no",
        trail.partial_source,
        str(trail.schema_version),
        trail.decided_by or "none",
        trail.verdict or "none",
        trail.bound_by or "none",
        "yes" if trail.bound_by_is_the_answer else "no",
        trail.last or "none",
        str(trail.attempt_count),
        "" if trail.total_elapsed_ms is None else str(trail.total_elapsed_ms),
        trail.in_flight_after or "",
        open_ms,
        # Raw, not normalised: `""` (below schema 3, ambiguous -- see
        # `RouteTrail.features`) is a DIFFERENT answer from a schema-3
        # `"none"`, and collapsing them here would be the exact bug this
        # column exists to keep this reader from reproducing.
        trail.features or "",
    ]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("files", nargs="+", help="`--trace` output files")
    parser.add_argument(
        "--summary",
        action="store_true",
        help="print decided_by / bound_by histograms instead of one row per file",
    )
    parser.add_argument(
        "--include-partial",
        action="store_true",
        help="let the summary sum decided_by over partial readings",
    )
    parser.add_argument(
        "--allow-missing",
        action="store_true",
        help="report files with no trail line but still exit 0",
    )
    args = parser.parse_args(argv)

    trails, refusals = read_files(args.files, skip_missing=True)

    if args.summary:
        print(f"trails read           : {len(trails)}")
        print(f"partial readings      : {sum(1 for t in trails if t.partial)}")
        try:
            counts = decided_by_counts(trails, include_partial=args.include_partial)
        except PartialInAggregate as exc:
            print(f"decided_by            : REFUSED -- {exc}", file=sys.stderr)
        else:
            print("-- decided_by --")
            for route, count in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
                print(f"  {count:5d}  {route}")
        print("-- bound_by (partials included, read with bound_is_answer) --")
        for route, count in sorted(
            bound_by_counts(trails, include_partial=True).items(),
            key=lambda kv: (-kv[1], kv[0]),
        ):
            print(f"  {count:5d}  {route}")
    else:
        print("\t".join(_COLUMNS))
        for trail in trails:
            print("\t".join(_row(trail)))

    for refusal in refusals:
        print(f"REFUSED: {refusal}", file=sys.stderr)
    if refusals and not args.allow_missing:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
