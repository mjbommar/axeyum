#!/usr/bin/env python3
"""Per-file portfolio oracle: does a route we already own decide a file we lose?

The question this answers
-------------------------

The 2026-09-07 route-attribution sweep measured *recoverable wall time* on files
we already decide (1.33x) and *binder share* on files we lose (median 84%), and
concluded a portfolio was not worth building.  That is the answer to "if we ran
the same routes concurrently, how much waiting disappears?".  It is **not** the
answer to "is there a route that would have decided this file quickly, which we
never reached because a slower one ran first?"  Those are different questions,
and one dominant route is consistent with a large answer to the second one:
`docs/research/12-performance/qf-abv-route-attribution-2026-09-08.md` records four
QF_ABV files where `abv-online-cdclt` spent 24.009 s of a 24 s budget, declined,
and `array-fast-path` then decided the file in 0.191 s.

Method, and why it needs no new solver knob
-------------------------------------------

`SolverConfig` has no route-selection field, so a strict "run each route alone"
virtual best is not directly measurable -- the earlier sweep said so and declined
to claim one.  But the ladder is **sequential** and each route's `config.timeout`
is clamped to what remains of one wall deadline, so raising the wall budget has
exactly the effect of letting the routes *after* the binder have their turn.  So:

* **control** -- run the file at the competition budget.  A file that decides
  here is stale population, not a prize; it is reported and excluded.
* **probe** -- run the same file at a much larger budget with `--trace`.  The
  `; route-trail` line (`RouteTrace::to_json_with_timing`) carries every
  attempt's own `elapsed_ns`, so we read the deciding route's own cost rather
  than the ladder's total.

A file is scored **portfolio-decidable at the competition budget** when the probe
decides it and

    shared_preamble + deciding_route_own_time  <=  competition_budget

because a portfolio arm starts at t=0: it pays the preamble every arm pays, and
its own time, and nothing for the routes queued in front of it.

What this does NOT measure, stated rather than absorbed
-------------------------------------------------------

1. Routes the ladder never *admits* are invisible here.  Raising the budget lets
   later routes run; it does not make an inadmissible route admissible.  So this
   is a **lower bound** on the portfolio prize, never an upper bound.
2. A route is handed a clamped `config.timeout`, and several of the ladder's
   internal shares are *fractions* of it (`cegar_probe_budget` takes 3/4 of what
   remains, `dl_probe_budget` `min(timeout/4, 6 s)`), so the ladder under a
   150 s budget is a different schedule, not the 24 s schedule with more room.
   `--confirm` therefore checks **reproducibility of the probe**, not the
   budget: it re-runs the probe and requires the same route to decide at a
   comparable cost (`PRIZE-UNCONFIRMED` / `PRIZE-UNSTABLE` otherwise).

   It deliberately does NOT re-run at the competition budget.  That was this
   script's first version and it is a control that cannot pass: a `PRIZE` is by
   construction a file the ladder does not decide at the competition budget, so
   a confirmation run there returns `unknown` every time and would have marked
   every prize unconfirmed while looking like diligence.  Confirming the
   route's own cost under the competition budget needs a route-selection knob,
   which `SolverConfig` does not have; that gap is the finding, not a caveat.
3. The harness allows `WATCHDOG_GRACE` (1 s, `smtcomp_cli.rs`) past the
   configured timeout, so the control arm can report a verdict for a file a real
   external limit would kill.  `control_ms` is printed so that case stays
   visible rather than being absorbed into a verdict.

Output is a TSV, one row per file, plus a `#` summary block.  Every field is
measured; nothing is inferred from a message.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import sys
import time

# Attempts whose outcome is `probe` are the shared preamble (parse, feature
# scan): every arm of a portfolio pays them, so they are charged to every arm.
# Counting them as recoverable is the error that inflated QF_SLIA from 63% to
# 84% in the first draft of the 2026-09-07 aggregate.
PREAMBLE_OUTCOME = "probe"

DECIDED_VERDICTS = ("sat", "unsat")


def parse_trace(stdout: str) -> dict:
    """Pull the verdict and the route trail out of one `smtcomp_cli --trace` run.

    Returns `verdict`, `attempts` (the list `RouteTrace::to_json_with_timing`
    emits) and `trail_present`.  A run with no trail is reported as such and is
    never silently given an empty trail: a coverage number that drops the files
    it never saw is how a stable number becomes a wrong one.
    """
    verdict = None
    attempts = None
    for raw in stdout.splitlines():
        line = raw.rstrip()
        if line.startswith("; route-trail "):
            try:
                attempts = json.loads(line[len("; route-trail ") :])["attempts"]
            except (ValueError, KeyError):
                attempts = None
        elif line in ("sat", "unsat", "unknown"):
            verdict = line
    return {
        "verdict": verdict or "none",
        "attempts": attempts,
        "trail_present": attempts is not None,
    }


def deciding(attempts):
    """The LAST `decided` attempt and its own elapsed ns, or `None`.

    Last, not first: the ladder legitimately re-decides (the quantifier loop
    re-dispatches the whole query once per instantiation round), which is why
    the shipped `decided_by=` field reads the last one too.
    """
    found = None
    for a in attempts:
        if a.get("outcome") == "decided":
            found = (a["route"], int(a.get("elapsed_ns", 0)))
    return found


def preamble_ns(attempts) -> int:
    """Time in leading `probe` attempts, before the first real route attempt."""
    total = 0
    for a in attempts:
        if a.get("outcome") != PREAMBLE_OUTCOME:
            break
        total += int(a.get("elapsed_ns", 0))
    return total


def run_one(binary, path, timeout_ms, cores, mem_mb, wall_slack_s):
    """One `smtcomp_cli --trace` run.  Returns (parsed trace, wall ms)."""
    cmd = []
    if cores:
        cmd += ["taskset", "-c", cores]
    cmd += [binary, path, "--trace", "--timeout-ms", str(timeout_ms)]
    # `ulimit -v` matches how the committed parity sweeps bound memory.
    shell = 'ulimit -v %d; exec "$@"' % (mem_mb * 1024)
    start = time.monotonic()
    try:
        proc = subprocess.run(
            ["/bin/sh", "-c", shell, "sh"] + cmd,
            capture_output=True,
            text=True,
            timeout=timeout_ms / 1000.0 + wall_slack_s,
        )
        out = proc.stdout
    except subprocess.TimeoutExpired as exc:
        raw = exc.stdout or ""
        out = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
    wall_ms = int((time.monotonic() - start) * 1000)
    return parse_trace(out), wall_ms


def classify(row, probe, args):
    """Score one probed file.  Mutates and returns `row`.

    `verdict == "none"` means the process printed no verdict at all: it aborted.
    Measured on `QF_ABV/brummayerbiere/wchains140se.smt2`, which fails a
    127 MB allocation under the 8 GiB `ulimit -v` and exits 134.  That is a
    memory bound, not an absence of routes, and filing it as `NO-ROUTE` would be
    exactly the "the message is not the event" error this division's own
    attribution note was written to correct.
    """
    if probe["verdict"] == "none":
        row["status"] = "ABORTED"
        return row
    if probe["verdict"] not in DECIDED_VERDICTS:
        row["status"] = "NO-ROUTE" if probe["trail_present"] else "NO-ROUTE-NO-TRAIL"
        return row
    if not probe["trail_present"]:
        row["status"] = "DECIDED-NO-TRAIL"
        return row
    win = deciding(probe["attempts"])
    if win is None:
        # Decided by a front-door stage that recorded no `decided` attempt.
        row["status"] = "DECIDED-NO-WINNER"
        return row
    route, own_ns = win
    pre_ns = preamble_ns(probe["attempts"])
    arm_ms = (pre_ns + own_ns) / 1e6
    row.update(
        winner=route,
        winner_own_ms=round(own_ns / 1e6, 1),
        preamble_ms=round(pre_ns / 1e6, 1),
        arm_ms=round(arm_ms, 1),
    )
    # `winner_count` is how many times the winning route appears in the trail.
    # More than once means the front door LOOPED (a string-bound ladder, a
    # quantifier-instantiation loop, a CEGAR refinement), and then the winner's
    # own segment is ONE ROUND OF MANY rather than an arm's cost.  Scoring such
    # a file on that segment understates the work enormously: on
    # `QF_SLIA/.../new.8618.corecstrs.readable.smt2` the deciding segment is
    # 1,172 ms and the file needs 110,546 ms of front-door work.
    winner_count = sum(
        1 for a in probe["attempts"] if a.get("outcome") == "decided" and a["route"] == route
    )
    row["attempts"] = len(probe["attempts"])
    row["winner_count"] = winner_count
    if winner_count > 1:
        row["status"] = "LOOPED-NOT-SCORED"
    elif arm_ms <= args.budget_ms:
        # CANDIDATE, not PRIZE: this instrument cannot confirm that the route
        # decides in that time when it runs FIRST.  Confirmation is a separate
        # measurement -- see the module docstring.
        row["status"] = "PRIZE-CANDIDATE"
    else:
        row["status"] = "TOO-SLOW-ARM"
    return row


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--binary", required=True, help="release smtcomp_cli")
    ap.add_argument("--files", required=True, help="one corpus path per line")
    ap.add_argument("--out", required=True, help="output TSV")
    ap.add_argument("--division", default="?")
    ap.add_argument(
        "--budget-ms",
        type=int,
        default=24_000,
        help="the competition budget the oracle is scored against",
    )
    ap.add_argument(
        "--probe-ms",
        type=int,
        default=150_000,
        help="the enlarged budget that lets routes after the binder run",
    )
    ap.add_argument("--memory-limit-mb", type=int, default=8192)
    ap.add_argument("--cores", default=None, help="taskset -c spec, e.g. 0-3")
    ap.add_argument(
        "--confirm",
        action="store_true",
        help="re-run each scored winner at the competition budget and require "
        "the same route to decide",
    )
    ap.add_argument("--wall-slack-s", type=int, default=30)
    ap.add_argument("--limit", type=int, default=0, help="first N files only (pilot)")
    args = ap.parse_args()

    files = [
        line.strip()
        for line in pathlib.Path(args.files).read_text().splitlines()
        if line.strip()
    ]
    if args.limit:
        files = files[: args.limit]

    rows = []
    for i, path in enumerate(files, 1):
        if not os.path.exists(path):
            rows.append({"file": path, "division": args.division, "status": "MISSING"})
            print(f"[{i}/{len(files)}] MISSING              {path}", file=sys.stderr, flush=True)
            continue

        ctl, ctl_ms = run_one(
            args.binary, path, args.budget_ms, args.cores,
            args.memory_limit_mb, args.wall_slack_s,
        )
        row = {
            "file": path,
            "division": args.division,
            "control_verdict": ctl["verdict"],
            "control_ms": ctl_ms,
            "control_trail": int(ctl["trail_present"]),
        }
        if ctl["verdict"] in DECIDED_VERDICTS:
            # The current tree already decides this file: stale population.
            row["status"] = "STALE-DECIDED"
            rows.append(row)
            print(f"[{i}/{len(files)}] STALE-DECIDED        {path}", file=sys.stderr, flush=True)
            continue

        probe, probe_ms = run_one(
            args.binary, path, args.probe_ms, args.cores,
            args.memory_limit_mb, args.wall_slack_s,
        )
        row.update(
            probe_verdict=probe["verdict"],
            probe_ms=probe_ms,
            probe_trail=int(probe["trail_present"]),
        )
        classify(row, probe, args)

        if args.confirm and row["status"] == "PRIZE-CANDIDATE":
            again, _ = run_one(
                args.binary, path, args.probe_ms, args.cores,
                args.memory_limit_mb, args.wall_slack_s,
            )
            repeat = deciding(again["attempts"]) if again["trail_present"] else None
            if repeat is None or repeat[0] != row["winner"]:
                row["status"] = "CANDIDATE-UNREPRODUCED"
            else:
                own2 = repeat[1] / 1e6
                row["confirm_own_ms"] = round(own2, 1)
                first = row["winner_own_ms"]
                # A win whose own cost is not reproducible is not a number to
                # plan a portfolio on.  The gate is deliberately loose (2x)
                # because these hosts carry other lanes' sweeps, and it is a
                # reproducibility check, not a timing claim.
                if own2 > max(2.0 * first, first + 200.0):
                    row["status"] = "CANDIDATE-UNSTABLE"

        rows.append(row)
        print(
            f"[{i}/{len(files)}] {row['status']:20s} "
            f"{row.get('winner', '-')} arm={row.get('arm_ms')}ms  {path}",
            file=sys.stderr,
            flush=True,
        )

    cols = [
        "file", "division", "status", "control_verdict", "control_ms",
        "control_trail", "probe_verdict", "probe_ms", "probe_trail", "winner",
        "winner_own_ms", "preamble_ms", "arm_ms", "confirm_own_ms",
    ]
    counts = {}
    for r in rows:
        key = r.get("status", "?")
        counts[key] = counts.get(key, 0) + 1
    with open(args.out, "w") as fh:
        fh.write("\t".join(cols) + "\n")
        for r in rows:
            fh.write("\t".join(str(r.get(c, "")) for c in cols) + "\n")
        fh.write(
            f"# division={args.division} files={len(files)} "
            f"budget_ms={args.budget_ms} probe_ms={args.probe_ms} "
            f"cores={args.cores} mem_mb={args.memory_limit_mb}\n"
        )
        for k in sorted(counts):
            fh.write(f"# {k}\t{counts[k]}\n")
    print(json.dumps({"division": args.division, "counts": counts}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
