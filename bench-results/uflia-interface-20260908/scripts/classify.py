#!/usr/bin/env python3
"""Classify a QF_UFLIA sweep against the committed reference verdicts.

Lane `uflia-after-reachability`, step 1. The deliverable is the SPLIT, so this
script's job is to put every reference-solved file we do not decide into exactly
one bucket and to say, per bucket, which route was the last one to run and what
it said.

Buckets (the brief's four):
  a. declined-before-trying — every route that touched the query declined on a
     capacity / admission / modelling guard, and the wall clock is far under the
     budget.
  b. tried-and-timed-out    — a route was still running when the budget expired.
  c. size-or-memory-bound   — a route refused on an explicit size / memory cap.
  d. unknown-other          — anything else, listed individually rather than
     summarised, because a residual bucket that is only a number is where a
     wrong classification hides.

Exit status is 1 when a file cannot be classified, so a bucket nobody wrote
fails the run rather than being silently absent.
"""

import collections
import json
import pathlib
import sys

BUDGET_MS = 24_000
# A run that used less than this share of the budget did not time out, whatever
# else it did. Deliberately generous: the point is to separate "gave up early"
# from "ran out of clock", not to grade the margin.
EARLY_SHARE = 0.5


def load_summary(path):
    rows = []
    with open(path) as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            if parts[0] == "file":
                continue
            rows.append((parts[0], int(parts[1]), parts[2]))
    return rows


def raw_for(outdir, path):
    import hashlib

    key = hashlib.sha256(path.encode()).hexdigest()[:12]
    p = pathlib.Path(outdir) / "raw" / f"{key}.txt"
    return p.read_text() if p.exists() else ""


def trail_of(raw):
    for line in raw.splitlines():
        # BOTH forms. A watchdog kill prints `; partial route-trail`, and the
        # first pass of this analysis read only the completed form — which made
        # every timed-out file report "no route ran", the exact opposite of what
        # its trail says.
        for prefix in ("; route-trail ", "; partial route-trail "):
            if line.startswith(prefix):
                try:
                    return json.loads(line[len(prefix) :])
                except json.JSONDecodeError:
                    return None
    return None


def route_line(raw):
    for line in raw.splitlines():
        if line.startswith("; route ") or line.startswith("; partial route "):
            return line
    return ""


def classify(path, wall_ms, verdict, raw):
    trail = trail_of(raw)
    attempts = (trail or {}).get("attempts", [])
    solver_attempts = [a for a in attempts if a["route"] not in ("probe",)]
    last = solver_attempts[-1] if solver_attempts else None
    # The single most expensive attempt, which is what a decline-vs-timeout call
    # has to be made against: a query can decline ten routes in 3 ms each and
    # still spend 24 s inside the eleventh.
    worst_ns = max((a.get("elapsed_ns", 0) for a in solver_attempts), default=0)
    worst = None
    for a in solver_attempts:
        if a.get("elapsed_ns", 0) == worst_ns:
            worst = a
            break

    watchdog = "route unavailable" in raw or "; partial at=watchdog-kill" in raw
    if watchdog or wall_ms >= BUDGET_MS * 0.95:
        return "b.timeout", worst
    if worst_ns >= BUDGET_MS * EARLY_SHARE * 1e6:
        return "b.timeout", worst
    if last is None:
        return "d.other", None
    reason = last.get("reason", "")
    detail = last.get("detail", "")
    if "memory" in detail or "node cap" in detail or "cnf" in detail.lower():
        return "c.size-bound", last
    if reason in ("incomplete", "unsupported", "not-applicable", "budget"):
        return "a.declined-early", last
    return "d.other", last


def main(argv):
    ref_path, outdirs = argv[1], argv[2:]
    ref = {}
    with open(ref_path) as fh:
        for line in fh:
            f, v = line.rstrip("\n").split("\t")
            ref[f] = v

    rows = []
    for outdir in outdirs:
        rows.extend((outdir, *r) for r in load_summary(pathlib.Path(outdir) / "summary.tsv"))

    decided = 0
    losses = []
    disagreements = []
    for outdir, path, wall_ms, verdict in rows:
        r = ref.get(path)
        ours = verdict if verdict in ("sat", "unsat") else None
        if ours and r and ours != r:
            disagreements.append((path, ours, r))
        if ours:
            decided += 1
        elif r:
            losses.append((outdir, path, wall_ms, verdict))

    print(f"files          {len(rows)}")
    print(f"reference solved {len(ref)}")
    print(f"we decided     {decided}")
    print(f"losses         {len(losses)}")
    if disagreements:
        print("DISAGREEMENTS:")
        for d in disagreements:
            print("  ", d)

    buckets = collections.Counter()
    detail_counts = collections.Counter()
    per_file = []
    unclassified = 0
    for outdir, path, wall_ms, verdict in losses:
        raw = raw_for(outdir, path)
        bucket, attempt = classify(path, wall_ms, verdict, raw)
        buckets[bucket] += 1
        if bucket == "d.other":
            unclassified += 1
        route = attempt["route"] if attempt else "none"
        detail = (attempt or {}).get("detail", "") or (attempt or {}).get("reason", "")
        detail_counts[(bucket, route, detail[:110])] += 1
        per_file.append((bucket, route, wall_ms, path, detail[:200]))

    print()
    print("THE SPLIT")
    for b in sorted(buckets):
        print(f"  {b:20s} {buckets[b]:3d}")

    print()
    print("BY ROUTE AND REASON")
    for (b, route, detail), n in detail_counts.most_common():
        print(f"  {n:3d}  {b:18s} {route:34s} {detail}")

    print()
    print("THE LAST ROUTE THE LADDER REACHED, AND WHAT IT SAID")
    # For a timed-out file `bound_by` is the CEGAR that ate the reserve budget,
    # which is a fact about the BUDGET SPLIT, not about capability. The question
    # this lane was sent to answer is what the routes UNDERNEATH it did with the
    # reserve, and that is the LAST recorded attempt — a different field, and on
    # this population a different answer.
    tail = collections.Counter()
    for outdir, path, wall_ms, verdict in losses:
        raw = raw_for(outdir, path)
        attempts = (trail_of(raw) or {}).get("attempts", [])
        solver_attempts = [a for a in attempts if a["route"] != "probe"]
        if not solver_attempts:
            tail[("none", "no attempt recorded")] += 1
            continue
        last = solver_attempts[-1]
        tail[(last["route"], (last.get("detail") or last.get("reason") or "")[:120])] += 1
    for (route, detail), n in tail.most_common():
        print(f"  {n:3d}  {route:34s} {detail}")

    print()
    print("PER FILE")
    for row in sorted(per_file):
        print(f"  {row[0]:18s} {row[1]:34s} {row[2]:6d}ms  {pathlib.Path(row[3]).name}")

    if unclassified:
        print(f"\nUNCLASSIFIED: {unclassified} — a residual bucket is not a classification")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
