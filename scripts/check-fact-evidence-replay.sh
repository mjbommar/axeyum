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
# Cheap by construction: most checkers are milliseconds to a second. A few are
# genuinely expensive, and this comment used to claim they were "skipped by name
# and REPORTED". THAT MECHANISM DID NOT EXIST -- the only thing this script ever
# skipped was a fact with no `checker_command` at all. It was a doc comment
# asserting what the code does not do, in a script written to catch exactly that
# class of defect, which is the whole reason the class keeps being worth naming.
#
# What exists now instead: an evidence row may declare `checker_seconds`, the
# MEASURED typical runtime, and such a row gets a proportional budget rather than
# timing out on every run. `F:sorting-network-optimal-size-n6` is the case that
# forced it -- 490 s measured against a 120 s default, so it timed out every
# sweep, and a gate with a permanent expected failure teaches its readers to
# ignore it. Rows that use an extended budget are REPORTED, so the cost stays
# visible rather than becoming invisible by annotation.
#
# Usage:  scripts/check-fact-evidence-replay.sh [per-checker-timeout-seconds]
set -uo pipefail
cd "$(dirname "$0")/.."

TIMEOUT="${1:-120}"

# THE WHOLE-SWEEP DEADLINE. The per-row bound above stops any ONE bad checker;
# it does not stop 4,122 of them each burning a full budget. If every row timed
# out and retried, the per-row budgets sum to 993,952 s -- 11.5 days -- so
# "one bad row cannot take the gate down" is true and not sufficient.
#
# 9,900 s is deliberately just UNDER `scripts/check.sh`'s 10,800 s cap for this
# step, so when a sweep does run long the INFORMATIVE stop wins the race: this
# script reports which facts it never reached, by name, instead of the gate
# killing it mid-fact with nothing to read.
MAX_SECONDS="${AXEYUM_FACT_REPLAY_MAX_SECONDS:-9900}"

# Checkers write scratch to ${TMPDIR:-/tmp} -- the sorting-network ones write a
# cube directory of DRAT proofs, which runs to gigabytes. That default is correct
# and portable; it is this machine that is unusual, because /tmp here is a 62 G
# **tmpfs**, i.e. RAM. So an unattended sweep of the whole ledger quietly moves
# several GB into memory on a box that has been losing sessions to systemd-oomd,
# and it does it while every lane's cargo build is competing for the same RAM.
#
# Point it at disk when a disk-backed scratch root exists, and otherwise leave
# the portable default alone. Explicitly-set TMPDIR always wins: a caller who
# chose one means it.
if [ -z "${TMPDIR:-}" ] && [ -d /data0/axeyum/scratch ]; then
  export TMPDIR=/data0/axeyum/scratch
fi

# A build probe, BEFORE the sweep. This gate shells out to `cargo` against the
# WORKTREE, so in a shared checkout a neighbouring lane's half-finished edit makes
# every checker in the affected crates exit non-zero -- and the report then reads
# as "your facts rotted".
#
# That is not hypothetical: one run showed `kernel-lean 8/23` and 21 failures
# while another lane was mid-refactor in `int_prelude`. Sampled after that lane
# committed, the same checkers passed in 0.9-3.2 s each. The facts were never
# rotten; the tree did not compile.
#
# A gate that cannot produce a trustworthy answer must say so rather than produce
# an untrustworthy one, so this refuses to run rather than reporting numbers a
# reader would misread. `--force` runs anyway, with the caveat printed.
# The build probe's OWN cap, and its own per-lane log.
#
# Until 2026-08-30 this `cargo check` had no timeout of any kind, and cargo's
# wait on the build-directory lock is UNBOUNDED -- it prints "Blocking waiting
# for file lock" and waits forever. So the gate's very first action could hang
# the whole aggregate gate before a single checker ran, with nothing on stdout
# to say so.
#
# `/tmp/fact-replay-build.log` was also a FIXED-NAME file in a directory every
# lane shares, which is on CLAUDE.md's banned list for exactly the reason it
# looks harmless: two concurrent sweeps silently overwrite each other's
# diagnosis, so the error you read may belong to another lane's tree.
BUILD_PROBE_TIMEOUT="${AXEYUM_FACT_REPLAY_BUILD_TIMEOUT:-1800}"
BUILD_LOG="${TMPDIR:-/tmp}/fact-replay-build-${AXEYUM_AGENT:-$$}.log"

if [ "${2:-}" != "--force" ]; then
  timeout --kill-after=30 "$BUILD_PROBE_TIMEOUT" \
    cargo check -q --workspace --all-features > "$BUILD_LOG" 2>&1
  probe_status=$?
  if [ "$probe_status" -eq 124 ] || [ "$probe_status" -eq 137 ]; then
    echo "fact-evidence-replay: REFUSING TO RUN -- the build probe did not finish" >&2
    echo "  within ${BUILD_PROBE_TIMEOUT}s. cargo's wait on the build-directory lock is" >&2
    echo "  unbounded, so this usually means another cargo is holding it (possibly an" >&2
    echo "  orphan from an earlier capped run). Check for one before re-running:" >&2
    echo "    ps -eo pid,ppid,etimes,args --sort=-etimes | awk '\$2==1' | grep cargo" >&2
    exit 3
  fi
  if [ "$probe_status" -ne 0 ]; then
    echo "fact-evidence-replay: REFUSING TO RUN -- the worktree does not compile." >&2
    echo "  This gate runs every checker against the worktree, so a build failure" >&2
    echo "  makes unrelated facts look rotted. In a shared checkout that is usually" >&2
    echo "  another lane's in-flight work, not a defect in any fact." >&2
    echo "" >&2
    grep -m3 -E '^error' "$BUILD_LOG" | sed 's/^/  /' >&2
    echo "" >&2
    echo "  Verify against committed state instead:" >&2
    echo "    W=\$(scripts/lane-snapshot.sh HEAD) && (cd \"\$W\" && ./scripts/check-fact-evidence-replay.sh)" >&2
    echo "    # NOT \`mktemp -d\` + \`git archive | tar -x\`: that lands 640 MB in /tmp (a" >&2
    echo "    # RAM-backed tmpfs here) and omits \`--touch\`, so cargo reports passes over" >&2
    echo "    # code it never compiled." >&2
    echo "  or re-run with --force to sweep anyway and read the result with that in mind." >&2
    exit 2
  fi
fi

python3 - "$TIMEOUT" "$MAX_SECONDS" <<'PY'
import json, glob, os, re, signal, subprocess, sys, time
from collections import Counter

timeout = int(sys.argv[1])
SETTLED = {"proved", "computed", "refuted", "axiom"}

facts = []
for path in sorted(glob.glob("artifacts/facts/*.json")):
    d = json.load(open(path))
    if d["epistemic_status"] in SETTLED:
        facts.append(d)

ran = failed = skipped = 0
max_seconds = int(sys.argv[2])
not_run = []
extended = []
timeouts = []
timed_out_facts = set()


KILL_GRACE = 10


def _bounded(cmd, timeout):
    """Run one shell command under a HARD bound, killing its whole process tree.

    `subprocess.run(cmd, shell=True, timeout=N)` KILLS ONLY THE DIRECT CHILD.
    Measured at three command shapes -- bare, pipeline, and backgrounded --
    `TimeoutExpired` fires on schedule in all three and the grandchild survives
    in all three:

        cmd            TimeoutExpired 2.00s   grandchild survives: yes
        cmd | cat      TimeoutExpired 2.00s   grandchild survives: yes
        cmd & wait     TimeoutExpired 2.00s   grandchild survives: yes

    That orphan is not untidiness, it is the nine-hour hang. 4,064 of this
    ledger's 4,122 `checker_command`s invoke cargo, and cargo's wait on the
    build-directory lock is UNBOUNDED. One orphaned cargo therefore blocks every
    later cargo checker in the sweep, each of which then burns its own full
    budget twice (timeout, retry, timeout) at 0% CPU -- which is exactly what a
    reaped run looked like: hours of no output, no CPU, and a `python3` waiting
    on a `cargo run`.

    `start_new_session=True` puts the shell in its own session and process
    group, so `killpg` reaches everything it spawned. Returns
    (returncode, stdout, stderr, timed_out).
    """
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
        return p.returncode, out, err, False
    except subprocess.TimeoutExpired:
        try:
            pgid = os.getpgid(p.pid)
        except ProcessLookupError:
            pgid = None
        if pgid is not None:
            # TERM first so a checker with an EXIT trap can clean up its scratch
            # (the sorting-network ones write gigabytes of DRAT cubes), then
            # KILL unconditionally, because an ignored TERM disposition is
            # inherited across exec and a wedged tree will not go on its own.
            #
            # THE PROGRESS TEST IS THE GROUP, NOT THE DIRECT CHILD, and getting
            # that wrong is what the first version of this did. It waited on
            # `p` after the TERM and broke out of the loop when `p` was reaped
            # -- so SIGKILL was never sent. Measured:
            #
            #   /bin/sh -c ./bad.sh   did NOT exec; it forked `bash ./bad.sh`
            #   killpg(SIGTERM)       killed the sh, not the TERM-ignoring bash
            #   p.wait() succeeded    -> break -> no SIGKILL
            #   FINAL survivors = 1   (the bash, holding everything it held)
            #
            # The direct child dying says nothing about the rest of the group,
            # which is the entire population this exists to reap.
            try:
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                pgid = None
            if pgid is not None:
                deadline = time.time() + KILL_GRACE
                while time.time() < deadline:
                    try:
                        os.killpg(pgid, 0)   # does the GROUP still have members?
                    except ProcessLookupError:
                        break
                    time.sleep(0.2)
                try:
                    os.killpg(pgid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        try:
            out, err = p.communicate(timeout=KILL_GRACE)
        except subprocess.TimeoutExpired:
            out, err = "", ""
        return 124, out, err, True


def run_checker(cmd, timeout):
    """Run one checker. Returns (exit code, last output line, timed_out)."""
    rc, out, err, timed_out = _bounded(cmd, timeout)
    if timed_out:
        return 124, f"TIMED OUT after {timeout}s", True
    tail = (out or err or "").strip().splitlines()
    return rc, (tail[-1][:90] if tail else f"exit {rc}"), False


def diagnose(cmd, timeout):
    """Re-run a FAILED checker with stderr restored, and report what it said.

    Checker commands legitimately end in `2>/dev/null`: cargo writes progress to
    stderr, and a `| tail -1` verdict test would otherwise read the wrong line.
    The cost is that when one fails, the reason is already discarded.

    That is not hypothetical. A sorting-network checker exited 1 three times and
    passed three times on the same unchanged fact; the cause was `/tmp` at 80%
    under other lanes' load, and it was INDISTINGUISHABLE from a refuted claim
    because the "No space left on device" went to /dev/null. An infrastructure
    failure that reads as a mathematical one is the most expensive kind of false
    alarm this gate can raise.

    So on failure only -- never on the happy path, where the suppression is
    doing its job -- strip the redirection and run it once more for the message.
    """
    restored = re.sub(r"\s*2>\s*/dev/null", "", cmd)
    if restored == cmd:
        return ""
    _, _, stderr_text, timed_out = _bounded(restored, timeout)
    if timed_out:
        return "    (stderr re-run timed out)"
    err = (stderr_text or "").strip().splitlines()
    if not err:
        return ""
    hint = ""
    joined = " ".join(err[-6:]).lower()
    for needle, note in (("no space left", "DISK FULL -- infrastructure, not mathematics"),
                         ("cannot allocate", "OUT OF MEMORY -- infrastructure"),
                         ("resource temporarily unavailable", "resource exhaustion -- infrastructure"),
                         ("permission denied", "permissions -- infrastructure")):
        if needle in joined:
            hint = f"    >>> {note}"
            break
    return "\n".join(f"    {line[:110]}" for line in err[-4:]) + (f"\n{hint}" if hint else "")
by_route_ok, by_route_total = Counter(), Counter()
failures = []
started = time.time()

for fact in facts:
    route = fact.get("proof_route") or "<none>"
    if time.time() - started > max_seconds:
        # OUT OF BUDGET. A fact we never reached is NOT a passing fact and NOT a
        # failing one -- it is a fourth outcome, the same discipline
        # `scripts/check-fast.sh` applies to a deferred step. It is named, it is
        # counted, and it makes the exit status non-zero.
        not_run.append(fact["id"])
        by_route_total[route] += 1
        continue
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
        # A row that declares a MEASURED cost gets a budget scaled from it. The
        # factor is deliberately generous (2x) and floored at the caller's
        # timeout: this box has shown 1.84x swings between core classes alone,
        # so a budget equal to the measurement would still flake constantly.
        declared = row.get("checker_seconds")
        row_timeout = timeout
        if isinstance(declared, int) and declared > 0:
            row_timeout = max(timeout, declared * 2)
            if row_timeout > timeout:
                extended.append((fact["id"], declared, row_timeout))
        # A timeout is NOT evidence that a fact rotted, and reporting it as a
        # failure makes the gate's false alarms indistinguishable from its true
        # ones. Measured: the same clean ledger gives 251.8s/0 failed idle and
        # 747.7s/1 "failed" under contention, where the one failure was cargo's
        # build lock. So: retry once, then classify separately.
        rc, note, timed_out = run_checker(cmd, row_timeout)
        if timed_out:
            rc, note, timed_out = run_checker(cmd, row_timeout)
        ran += 1
        if timed_out:
            ok = False
            timeouts.append((fact["id"], cmd, note))
        elif rc != 0:
            ok = False
            failures.append((fact["id"], cmd, note, diagnose(cmd, row_timeout)))

    by_route_total[route] += 1
    if ok:
        by_route_ok[route] += 1
        print(f"  ok         {fact['id']:<40} route={route} ({len(rows)} checker(s))")
    else:
        # `failed` and `timed out` must be DISJOINT. Counting a timed-out fact in
        # both made "1 failed, 1 timed out" read as two problems when it is one --
        # and the whole point of separating them is that they mean different
        # things. A fact is FAILED only if some checker genuinely exited non-zero.
        genuinely_failed = any(f[0] == fact["id"] for f in failures)
        if genuinely_failed:
            failed += 1
            print(f"  {'FAIL':<10} {fact['id']:<40} route={route}")
        else:
            timed_out_facts.add(fact["id"])
            print(f"  {'TIMEOUT':<10} {fact['id']:<40} route={route}")

elapsed = time.time() - started
print()
for route in sorted(by_route_total):
    print(f"  route {route:<20} {by_route_ok[route]}/{by_route_total[route]} re-derived")
if extended:
    print()
    for fid, declared, budget in extended:
        print(f"  budget    {fid:<40} declared {declared}s -> allowed {budget}s")
ok_facts = sum(by_route_ok.values())
print(f"\nfact-evidence-replay: {len(facts)} settled fact(s), {ran} checker run(s), "
      f"{ok_facts} re-derived, {failed} failed, {len(timed_out_facts)} timed out, "
      f"{skipped} uncovered, {len(not_run)} NOT RUN, {elapsed:.1f}s")
if not_run:
    print(f"  NOT RUN: the {max_seconds}s sweep budget ran out with "
          f"{len(not_run)} fact(s) unreached. These are UNCHECKED -- neither "
          f"re-derived nor failed:", file=sys.stderr)
    for fid in not_run[:20]:
        print(f"    {fid}", file=sys.stderr)
    if len(not_run) > 20:
        print(f"    ... and {len(not_run) - 20} more", file=sys.stderr)
assert ok_facts + failed + len(timed_out_facts) + skipped + len(not_run) == len(facts), (
    "the per-fact outcome counts must partition the facts; if this fires the "
    "summary is double-counting and cannot be read")
if timeouts:
    print("  NOTE: a timeout is not evidence a fact rotted. Under load these are "
          "usually cargo's build lock; re-run on an idle box before believing them.",
          file=sys.stderr)
    for fid, cmd, note in timeouts:
        print(f"  TIMEOUT {fid}\n    $ {cmd}", file=sys.stderr)

if failures:
    print("\nfailures:", file=sys.stderr)
    for fid, cmd, note, why in failures:
        print(f"  {fid}\n    $ {cmd}\n    -> {note}", file=sys.stderr)
        if why:
            print("    stderr (recovered by re-running without 2>/dev/null):", file=sys.stderr)
            print(why, file=sys.stderr)

# A gate that examined nothing is a failure, not a pass. This repository has
# shipped several that exited 0 over zero work.
if ran == 0:
    print("fact-evidence-replay: ran ZERO checkers — the gate examined nothing",
          file=sys.stderr)
    sys.exit(1)
sys.exit(1 if (failed or timed_out_facts or not_run) else 0)
PY
