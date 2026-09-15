#!/usr/bin/env python3
"""Control suite for `scripts/route_trace_reader.py` (ADR-2101).

Every assertion here is a bug class that reached a published ADR, written as a
fixture the reader must survive. The suite exists because the reader is now
the single consumer of route telemetry, and **a checker that cannot fail is
worse than no checker**: if this file passes on a reader that silently returns
empty results, the whole lane has made the censuses faster at being wrong.

So: three of the tests are NEGATIVE CONTROLS that assert the reader REFUSES,
one is a freshness control binding the Python fixtures to the Rust renderer's
own pinned bytes, and the rest drive a distinction the producer makes and
require it to survive to the consumer.

Run: python3 scripts/tests/test-route-trace-reader.py
Exit status is the finding.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
import traceback

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import route_trace_reader as rtr  # noqa: E402

RUST_SOURCE = os.path.join(
    os.path.dirname(ROOT), "crates", "axeyum-solver", "src", "route_trace.rs"
)

# ---------------------------------------------------------------------------
# Fixtures.  Schema 1 is the shape of every artifact committed before ADR-2101;
# schema 2 is what the CLI writes now.  Both are exercised, because the
# repository contains both and a reader that only understands the new one
# cannot re-derive a single published number.
# ---------------------------------------------------------------------------

V1_COMPLETE = (
    '; route-trail {"schema_version":1,"attempts":['
    '{"route":"fd:parse","outcome":"probe","detail":"string_bound=12",'
    '"elapsed_ns":180477315},'
    '{"route":"qf-bv","outcome":"decided","verdict":"unsat","elapsed_ns":48200000}]}'
)

V1_PARTIAL = (
    '; partial route-trail {"schema_version":1,"attempts":['
    '{"route":"fd:parse","outcome":"probe","detail":"string_bound=12",'
    '"elapsed_ns":180477315},'
    '{"route":"q:ground-subset","outcome":"declined","reason":"budget",'
    '"detail":"deadline","elapsed_ns":4519000000}]}'
)

V2_COMPLETE = (
    '; route-trail {"schema_version":2,"partial":false,"attempts":['
    '{"route":"qf-bv","outcome":"decided","verdict":"unsat","elapsed_ns":48200000}]}'
)

V2_PARTIAL = (
    '; partial route-trail {"schema_version":2,"partial":true,'
    '"in_flight_after":"q:mbqi","open_segment_ns":25215000000,"attempts":['
    '{"route":"q:mbqi","outcome":"declined","reason":"not-applicable",'
    '"elapsed_ns":20000000}]}'
)

#: ADR-2020's defect, as a fixture. Every character here appeared in a real
#: `why=` detail: the `;` that a split truncated on, the `;QPROBE ` record
#: separator that had to be invented because of it, an `=` that a
#: `key=value` scan would cut at, and a quote/newline pair an ad-hoc escaper
#: would corrupt.
HOSTILE_DETAIL = (
    'lazy function-consistency CEGAR inconclusive '
    '(rounds=3; atoms=64); the reduced solve\'s own reason was '
    '[ResourceLimit] ;QPROBE budget="8192" \nwidened'
)


def _hostile_trail() -> str:
    import json

    obj = {
        "schema_version": 2,
        "partial": False,
        "attempts": [
            {
                "route": "lia-dpll",
                "outcome": "declined",
                "reason": "budget",
                "detail": HOSTILE_DETAIL,
            },
            {
                "route": "lia-dpll",
                "outcome": "declined",
                "reason": "incomplete",
                "kind": "node-budget",
                "detail": HOSTILE_DETAIL,
            },
            {"route": "qf-bv", "outcome": "decided", "verdict": "sat"},
        ],
    }
    return "; route-trail " + json.dumps(obj, separators=(",", ":"))


def _write(tmp: str, name: str, *lines: str) -> str:
    path = os.path.join(tmp, name)
    with open(path, "w", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")
    return path


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_schema_2_reads_completeness_from_the_field():
    trail = rtr.parse_trail_line(V2_PARTIAL)
    assert trail.partial is True
    assert trail.partial_source == "field", trail.partial_source
    assert trail.in_flight_after == "q:mbqi"
    assert trail.open_segment_ns == 25_215_000_000

    complete = rtr.parse_trail_line(V2_COMPLETE)
    assert complete.partial is False
    assert complete.partial_source == "field"


def test_schema_1_falls_back_to_the_prefix_and_says_so():
    """The compatibility shim, and the ONE place the prefix is read.

    ADR-2075: twelve files printing fourteen diagnostic lines each were
    recorded as having no route line, because the consumer half of the
    `; partial ` convention was never written. Every artifact committed before
    this lane is schema 1, so re-deriving any published number requires this
    path to work -- and requires it to ADMIT that it inferred.
    """
    partial = rtr.parse_trail_line(V1_PARTIAL)
    assert partial.partial is True
    assert partial.partial_source == "prefix", partial.partial_source

    complete = rtr.parse_trail_line(V1_COMPLETE)
    assert complete.partial is False
    assert complete.partial_source == "prefix"
    # …and the complete one still yields its real attribution, so the assertion
    # above is not passing because the reader returns nothing on schema 1.
    assert complete.decided_by == "qf-bv"
    assert complete.verdict == "unsat"


def test_the_fields_every_census_asked_the_prose_for():
    trail = rtr.parse_trail_line(V1_PARTIAL)
    assert trail.decided_by is None
    assert trail.bound_by == "q:ground-subset"
    assert trail.last == "q:ground-subset"
    assert trail.attempt_count == 2
    assert trail.total_elapsed_ms == (180477315 + 4519000000) // 1_000_000


def test_bound_by_admits_when_it_is_not_the_answer():
    """The number ADR-1760 exists to stop being misread.

    `bound_by` maximises over RECORDED attempts and an attempt is recorded when
    it FINISHES, so on a killed run the route eating the budget contributed
    nothing. Measured: `bound_by=dl-online bound_ms=20 total_ms=26` on a
    25,241 ms run.
    """
    trail = rtr.parse_trail_line(V2_PARTIAL)
    assert trail.bound_by == "q:mbqi"
    assert trail.bound_by_is_the_answer is False, (
        "an open segment of 25.2 s against 20 ms of attributed time must not "
        "be reported as explained"
    )
    assert rtr.parse_trail_line(V2_COMPLETE).bound_by_is_the_answer is True


def test_a_detail_containing_the_old_separators_survives_whole():
    """ADR-2020, as a property rather than as a warning in a docstring.

    The census that truncated its own largest bucket split records on `;` when
    the `why=` detail contained `;`. Here the detail contains `;`, the
    `;QPROBE ` separator invented to work around it, an `=`, a quote and a
    newline -- and must come back byte-identical.
    """
    trail = rtr.parse_trail_line(_hostile_trail())
    declines = trail.decline_reasons()
    assert len(declines) == 2, declines
    for _route, _reason, detail in declines:
        assert detail == HOSTILE_DETAIL, f"detail was mangled: {detail!r}"
    assert ";" in HOSTILE_DETAIL and ";QPROBE " in HOSTILE_DETAIL, (
        "the fixture must actually contain the characters it tests for -- "
        "a hostile fixture that is not hostile is a vacuous control"
    )


def test_two_declines_sharing_a_reason_token_stay_distinguishable():
    """ADR-2060: a certificate must carry every distinction its producer makes.

    One give-up string stood for 28 program points and 15 causes, so an `i128`
    overflow was reported as a clock expiring. The two declines in this fixture
    share a route and a detail and differ only in `reason`/`kind`; if the
    reader collapses them, that defect is reachable again through this reader.
    """
    trail = rtr.parse_trail_line(_hostile_trail())
    attempts = [a for a in trail.attempts if a.declined]
    assert attempts[0].reason == "budget" and attempts[0].kind is None
    assert attempts[1].reason == "incomplete" and attempts[1].kind == "node-budget"
    counts = rtr.decline_reason_counts([trail])
    assert counts == {"lia-dpll\tbudget": 1, "lia-dpll\tincomplete": 1}, counts


def test_the_aggregate_refuses_partials_unless_told():
    """NEGATIVE CONTROL, both directions.

    Summing `decided_by` over a mid-search reading is ADR-2075's error with a
    dictionary in front of it. Refusing is only meaningful if the same call
    SUCCEEDS on the complete half, so both are asserted.
    """
    complete = rtr.parse_trail_line(V2_COMPLETE)
    partial = rtr.parse_trail_line(V2_PARTIAL)

    assert rtr.decided_by_counts([complete]) == {"qf-bv": 1}
    try:
        rtr.decided_by_counts([complete, partial])
    except rtr.PartialInAggregate as exc:
        assert len(exc.partial_paths) == 1, exc.partial_paths
    else:
        raise AssertionError("the aggregate summed a partial reading as a total")

    told = rtr.decided_by_counts([complete, partial], include_partial=True)
    assert told == {"qf-bv": 1, "none": 1}, told


def test_a_file_with_no_trail_is_refused_by_name():
    """NEGATIVE CONTROL. An absence must not read as a zero."""
    with tempfile.TemporaryDirectory() as tmp:
        bare = _write(tmp, "bare.log", "unknown")
        try:
            rtr.read_file(bare)
        except rtr.NoTrailLine as exc:
            assert exc.path == bare
            assert exc.unavailable_reason is None
        else:
            raise AssertionError("a file with no trail line was read as empty")

        # …and the DIFFERENT absence: the instrument ran and recorded nothing.
        # Collapsing these two is how "never traced" becomes "decided nothing".
        said = _write(
            tmp, "said.log", "; route unavailable: watchdog fired", "unknown"
        )
        try:
            rtr.read_file(said)
        except rtr.NoTrailLine as exc:
            assert exc.unavailable_reason == "watchdog fired", exc.unavailable_reason
        else:
            raise AssertionError("an explicit `route unavailable` was read as a trail")


def test_an_unknown_schema_is_refused_not_guessed():
    """NEGATIVE CONTROL.

    A future schema may rename the member that says what the numbers mean.
    Reading it optimistically is how a reader keeps returning plausible
    numbers after the producer changed underneath it.
    """
    future = '; route-trail {"schema_version":99,"partial":false,"attempts":[]}'
    try:
        rtr.parse_trail_line(future)
    except rtr.UnknownSchema as exc:
        assert exc.version == 99
    else:
        raise AssertionError("an unknown schema was read as if understood")


def test_the_last_trail_in_a_log_wins():
    with tempfile.TemporaryDirectory() as tmp:
        log = _write(tmp, "rerun.log", V1_COMPLETE, "unsat", V2_PARTIAL, "unknown")
        trail = rtr.read_file(log)
        assert trail.schema_version == 2 and trail.partial is True


def test_the_command_exit_status_depends_on_the_finding():
    """The ledger rule: a checker whose exit status is constant checks nothing."""
    with tempfile.TemporaryDirectory() as tmp:
        good = _write(tmp, "good.log", V2_COMPLETE, "unsat")
        bad = _write(tmp, "bad.log", "unknown")
        cmd = [sys.executable, os.path.join(ROOT, "route_trace_reader.py")]

        ok = subprocess.run(cmd + [good], capture_output=True, text=True)
        assert ok.returncode == 0, ok.stderr
        assert "qf-bv" in ok.stdout, ok.stdout

        refused = subprocess.run(cmd + [good, bad], capture_output=True, text=True)
        assert refused.returncode != 0, "a file with no trail exited 0"
        assert "REFUSED" in refused.stderr, refused.stderr


def test_the_fixtures_match_the_rust_renderer_bytes():
    """FRESHNESS CONTROL, and it postdates the question it answers.

    Python fixtures that drift from the Rust renderer make this whole suite a
    test of the fixtures. So the schema-2 prefixes above are checked against
    the literals `route_trace.rs` pins in its OWN tests: if the renderer moves
    a byte, its test fails and so does this one, and nobody has to remember
    that two files exist.
    """
    source = open(RUST_SOURCE, encoding="utf-8").read()

    # The complete-rendering prefix, as `route_trace.rs` pins it.
    pinned_complete = '{\\"schema_version\\":2,\\"partial\\":false,\\"attempts\\":'
    assert source.count(pinned_complete) >= 1, (
        "route_trace.rs no longer pins the complete rendering this suite's "
        "fixtures are built from -- the fixtures are stale, not the reader"
    )
    assert V2_COMPLETE.startswith(
        '; route-trail ' + pinned_complete.replace('\\"', '"')
    ), V2_COMPLETE

    # The partial rendering, likewise.
    pinned_partial = (
        '{\\"schema_version\\":2,\\"partial\\":true,\\"in_flight_after\\":'
    )
    assert source.count(pinned_partial) >= 1, (
        "route_trace.rs no longer pins the partial rendering -- stale fixtures"
    )

    # And the version itself comes off the constant, not off this file.
    match = re.search(
        r"pub const ROUTE_TRACE_JSON_SCHEMA_VERSION: u32 = (\d+);", source
    )
    assert match, "the schema-version constant moved or was renamed"
    assert int(match.group(1)) == max(rtr.KNOWN_SCHEMA_VERSIONS), (
        f"route_trace.rs emits schema {match.group(1)} but the reader's newest "
        f"known version is {max(rtr.KNOWN_SCHEMA_VERSIONS)}"
    )


def main() -> int:
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    failures = 0
    for test in tests:
        try:
            test()
        except BaseException:  # noqa: BLE001 - a control suite reports everything
            failures += 1
            print(f"FAIL {test.__name__}")
            traceback.print_exc()
        else:
            print(f"ok   {test.__name__}")
    print(f"\n{len(tests) - failures} of {len(tests)} control tests passed")
    if not tests:
        print("ABORT: the suite discovered ZERO tests, which is not a pass")
        return 2
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
