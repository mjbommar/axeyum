#!/usr/bin/env python3
"""Control suite for `aggregate.py`'s impossibility guards.

Follows the pattern `bench-results/instrument-coverage-2026-09-07/scripts/
test_aggregate_guard.py` established: a checker whose exit status does not
depend on its finding is worse than no checker, so each guard gets BOTH a
fixture it must pass and a fixture it must fail. A guard that only ever sees
honest input is indistinguishable from a guard that cannot fire.

The three guards under test, each with its own impossible fixture:

  1. trail total > process wall clock       (the 130.7%-coverage class of bug)
  2. declined prefix > trail total          (a share above 100%)
  3. a decided verdict with no deciding route in its trail

Plus a vacuity control: an input with rows but no decided file must exit 1,
because a deciding-route distribution over zero decided files is vacuous and
would otherwise be reported as a clean empty result.

Run: python3 test_aggregate_guard.py
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
AGGREGATE = os.path.join(HERE, "aggregate.py")

HEADER = ("division\tfile\twall_ms\tverdict\tdecided_by\tbound_by\tlast\t"
          "bound_ms\ttrace_total_ms\tattempts\tlog_path")


def trail(attempts):
    return json.dumps({"schema_version": 1, "attempts": attempts})


def attempt(route, outcome, elapsed_ns, **kw):
    a = {"route": route, "outcome": outcome, "elapsed_ns": elapsed_ns}
    a.update(kw)
    return a


def write_case(tmp, name, wall_ms, verdict, attempts):
    """Writes one log + one TSV row; returns the row text."""
    log = os.path.join(tmp, f"{name}.log")
    with open(log, "w", encoding="utf-8") as f:
        f.write(f"; route-trail {trail(attempts)}\n")
        if verdict in ("sat", "unsat"):
            f.write(f"{verdict}\n")
        else:
            f.write("unknown\n")
    return (f"D\t/f/{name}.smt2\t{wall_ms}\t{verdict}\tNA\tNA\tNA\t0\t0\t"
            f"{len(attempts)}\t{log}")


def run(tmp, rows):
    tsv = os.path.join(tmp, "in.tsv")
    with open(tsv, "w", encoding="utf-8") as f:
        f.write(HEADER + "\n")
        for r in rows:
            f.write(r + "\n")
    p = subprocess.run([sys.executable, AGGREGATE, tsv],
                       capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr


def honest_decided(tmp, name="honest", wall_ms=1000):
    # 100ms of declined prefix, then a 50ms winner: 150ms total, well under
    # the 1000ms wall clock.
    return write_case(tmp, name, wall_ms, "unsat", [
        attempt("fd:parse", "probe", 5_000_000, detail="string_bound=12"),
        attempt("probe", "probe", 1_000_000, detail="fragment {int}"),
        attempt("dl-online", "declined", 94_000_000, reason="not-applicable"),
        attempt("lia-simplex", "decided", 50_000_000, verdict="unsat"),
    ])


def main():
    failures = []

    def check(label, want_rc, rows_fn):
        with tempfile.TemporaryDirectory() as tmp:
            rc, out, err = run(tmp, rows_fn(tmp))
        if rc != want_rc:
            failures.append(
                f"{label}: expected exit {want_rc}, got {rc}\nstderr: {err[:400]}")
        else:
            print(f"  ok  {label} (exit {rc})")
        return rc

    print("positive controls (must PASS -- a guard that rejects everything is "
          "also broken):")
    check("honest decided file", 0, lambda t: [honest_decided(t)])

    print("guard 1 -- trail total exceeds process wall clock:")
    check("impossible: 5000ms of trail in a 100ms process", 1, lambda t: [
        honest_decided(t),
        write_case(t, "over_wall", 100, "unsat", [
            attempt("fd:parse", "probe", 1_000_000),
            attempt("qf-bv", "decided", 5_000_000_000, verdict="unsat"),
        ]),
    ])

    print("guard 3 -- a decided verdict whose trail decides nothing:")
    check("impossible: verdict unsat, every attempt declined", 1, lambda t: [
        honest_decided(t),
        write_case(t, "no_decider", 1000, "unsat", [
            attempt("fd:parse", "probe", 1_000_000),
            attempt("qf-bv", "declined", 2_000_000, reason="unsupported"),
        ]),
    ])

    print("vacuity control -- rows present but nothing decided:")
    check("vacuous: only unsolved files", 1, lambda t: [
        write_case(t, "lost", 24000, "unsolved", [
            attempt("fd:parse", "probe", 1_000_000),
            attempt("nra", "declined", 23_000_000_000, reason="budget",
                    detail="deadline"),
        ]),
    ])

    print("empty-population control -- no rows at all:")
    check("vacuous: zero rows", 1, lambda t: [])

    print("\nrecoverable-share arithmetic (the headline number must be "
          "computed, not asserted):")
    with tempfile.TemporaryDirectory() as tmp:
        rc, out, err = run(tmp, [honest_decided(tmp)])
        if rc != 0:
            failures.append(f"arithmetic fixture did not pass: {err[:400]}")
        else:
            rep = json.loads(out)
            vb = rep["virtual_best_over_our_own_routes"]
            # prefix = 5 + 1 + 94 = 100ms of 150ms total.
            got = vb["recoverable_share"]
            want = 100.0 / 150.0
            if abs(got - want) > 1e-9:
                failures.append(
                    f"recoverable_share = {got}, expected {want} "
                    f"(100ms declined prefix of a 150ms trail)")
            else:
                print(f"  ok  recoverable_share = {got:.4f} as computed by hand")
            if vb["winner_was_not_the_first_route_tried"] != 1:
                failures.append(
                    "winner_was_not_the_first_route_tried should be 1: the "
                    "winner sits at index 3, behind a declined dl-online")
            else:
                print("  ok  winner_was_not_the_first_route_tried = 1")

    if failures:
        print(f"\nFAILED ({len(failures)}):")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("\nall guard controls passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
