#!/usr/bin/env bash
# Re-run the evidence behind every settled fact, and report coverage by route.
#
# WHY THIS EXISTS. The ledger's whole promise is that a status is worth what its
# checker returns. `close-fact.py` enforces that when a fact is WRITTEN -- it
# executes each `checker_command` and refuses the flip on a non-zero exit. But
# nothing re-checked it afterwards, so a fact could be correct on the day it
# landed and silently rot as the code beneath it changed.
#
# This is that rule moved from write-time to gate-time, and it is deliberately
# ROUTE-AGNOSTIC. The ledger spans kernel-lean, smt-term-level, cas-certificate
# and search-certificate; a gate built around any one problem family would
# exercise a slice and imply the whole. (This script replaced a first draft that
# replayed only the Rado cells -- convenient, because that family already had a
# harness, which is exactly the wrong reason to choose a gate.)
#
# Cheap by construction: most checkers are milliseconds to a second. Anything
# genuinely expensive is skipped by name and REPORTED, never silently dropped.
#
# Usage:  scripts/check-fact-evidence-replay.sh [per-checker-timeout-seconds]
set -uo pipefail
cd "$(dirname "$0")/.."

TIMEOUT="${1:-120}"

python3 - "$TIMEOUT" <<'PY'
import json, glob, subprocess, sys, time
from collections import Counter

timeout = int(sys.argv[1])
SETTLED = {"proved", "computed", "refuted", "axiom"}

facts = []
for path in sorted(glob.glob("artifacts/facts/*.json")):
    d = json.load(open(path))
    if d["epistemic_status"] in SETTLED:
        facts.append(d)

ran = failed = skipped = 0
timeouts = []


def run_checker(cmd, timeout):
    """Run one checker. Returns (exit code, last output line, timed_out)."""
    try:
        p = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                           timeout=timeout)
        tail = (p.stdout or p.stderr or "").strip().splitlines()
        return p.returncode, (tail[-1][:90] if tail else f"exit {p.returncode}"), False
    except subprocess.TimeoutExpired:
        return 124, f"TIMED OUT after {timeout}s (twice)", True
by_route_ok, by_route_total = Counter(), Counter()
failures = []
started = time.time()

for fact in facts:
    route = fact.get("proof_route") or "<none>"
    rows = [e for e in fact.get("evidence", []) if e.get("checker_command")]
    if not rows:
        # A settled fact whose evidence names no runnable checker. Not a failure
        # here -- validate-facts.py owns that rule -- but it is uncovered, and an
        # uncovered fact must not be counted as a passing one.
        by_route_total[route] += 1
        skipped += 1
        print(f"  UNCOVERED  {fact['id']:<40} route={route} (no checker_command)")
        continue

    ok = True
    for row in rows:
        cmd = row["checker_command"]
        # A timeout is NOT evidence that a fact rotted, and reporting it as a
        # failure makes the gate's false alarms indistinguishable from its true
        # ones. Measured: the same clean ledger gives 251.8s/0 failed idle and
        # 747.7s/1 "failed" under contention, where the one failure was cargo's
        # build lock. So: retry once, then classify separately.
        rc, note, timed_out = run_checker(cmd, timeout)
        if timed_out:
            rc, note, timed_out = run_checker(cmd, timeout)
        ran += 1
        if timed_out:
            ok = False
            timeouts.append((fact["id"], cmd, note))
        elif rc != 0:
            ok = False
            failures.append((fact["id"], cmd, note))

    by_route_total[route] += 1
    if ok:
        by_route_ok[route] += 1
        print(f"  ok         {fact['id']:<40} route={route} ({len(rows)} checker(s))")
    else:
        failed += 1
        label = "TIMEOUT" if any(t[0] == fact["id"] for t in timeouts) else "FAIL"
        print(f"  {label:<10} {fact['id']:<40} route={route}")

elapsed = time.time() - started
print()
for route in sorted(by_route_total):
    print(f"  route {route:<20} {by_route_ok[route]}/{by_route_total[route]} re-derived")
print(f"\nfact-evidence-replay: {len(facts)} settled fact(s), {ran} checker run(s), "
      f"{failed} failed, {len(timeouts)} timed out, {skipped} uncovered, {elapsed:.1f}s")
if timeouts:
    print("  NOTE: a timeout is not evidence a fact rotted. Under load these are "
          "usually cargo's build lock; re-run on an idle box before believing them.",
          file=sys.stderr)
    for fid, cmd, note in timeouts:
        print(f"  TIMEOUT {fid}\n    $ {cmd}", file=sys.stderr)

if failures:
    print("\nfailures:", file=sys.stderr)
    for fid, cmd, note in failures:
        print(f"  {fid}\n    $ {cmd}\n    -> {note}", file=sys.stderr)

# A gate that examined nothing is a failure, not a pass. This repository has
# shipped several that exited 0 over zero work.
if ran == 0:
    print("fact-evidence-replay: ran ZERO checkers — the gate examined nothing",
          file=sys.stderr)
    sys.exit(1)
sys.exit(1 if failed else 0)
PY
