#!/usr/bin/env bash
# check-local-ci-freshness.sh — is there a FRESH, PASSING, fully-measured
# `scripts/local-ci.sh --record` for (an ancestor of) HEAD?
#
# `scripts/local-ci.sh` is hosted CI's own comment for "the authoritative gate
# for main", and `--record` exists so the question "did that gate pass on this
# SHA" is answerable from a tracked file instead of a gitignored log nobody else
# can see. A record answers nothing on its own: a record can exist, be green,
# and describe a SHA nobody has built on top of in three days, or a branch that
# was rebased away, or a run whose own step array disagrees with its own
# top-level verdict. This is the checker that turns "a record exists" into "the
# record still means something" — CLAUDE.md's own rule: a checker that cannot
# fail is worse than no checker.
#
# WHAT COUNTS AS FRESH (decided here, not obvious, written down so the next
# lane does not have to re-derive it):
#
#   * The record's `sha` must be HEAD or an ancestor of HEAD. A record for a
#     sha that is NOT in HEAD's history says nothing about this checkout — it
#     is not "old", it is INAPPLICABLE: the sha may be on a branch that got
#     rebased away, or from an unrelated line of history entirely. Checked with
#     `git merge-base --is-ancestor`, not string/prefix comparison.
#
#   * Among applicable (ancestor-or-equal) records, "the newest" is the one
#     CLOSEST TO HEAD in the commit graph (fewest commits between it and HEAD),
#     not the one with the latest `finished_utc`. Time and commit-distance
#     usually agree, but not always — someone could re-run the gate today
#     against a week-old sha to "refresh" a stale finished_utc without the code
#     having moved any closer to HEAD, and that must not read as fresh. Commit
#     distance is reported for diagnostics; finished_utc only breaks ties.
#
#   * The newest applicable record must be no older than
#     AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS (default 48h), measured from
#     `finished_utc` to now.
#
#     TIME, not a commit count. A commit-count budget has to be recalibrated
#     against a velocity that actually varies here: measured on this branch,
#     171 commits in the 24h before this script was written and 53 commits in
#     the 5.6h between the one completed local-ci run and this line being
#     written -- call it 7-10 commits/hour, in BURSTS, across several
#     concurrently-committing lanes (CLAUDE.md's multi-agent section exists
#     because of exactly that traffic). A fixed commit-count ceiling picked
#     against today's velocity is either too strict the next time several
#     lanes land docs/plan commits in a burst (reds the gate over changes that
#     touched no code the sweep exercises), or too loose the next time the repo
#     is quiet for a weekend (a stale record would read as fresh because
#     nothing else landed to make it "far" in commit count). What this checker
#     actually protects against -- main silently broken for a long stretch
#     with nobody re-running the expensive gate -- is a WALL-CLOCK exposure
#     question, not a code-churn one, and 48h is chosen against the run's own
#     measured cost: ~107 minutes of compute (a6ee37c6a-s4.json) serialized
#     behind ONE lock across every lane on the box (local-ci.sh's "one heavy
#     cargo job at a time" rule), with a documented lock-wait budget of up to
#     3h. Sub-day thresholds would be red by construction under that
#     contention; a week would let a broken main hide through several days of
#     landed work. 48h buys roughly one refresh per day even with a missed
#     slot.
#
#   * The record's OWN steps decide pass/fail, not its top-level `verdict`
#     field. `local-ci.sh` computes `verdict` correctly today, but a checker
#     that trusts a summary field instead of re-deriving it from the data that
#     field summarizes is exactly the pattern CLAUDE.md flags across this
#     codebase's checkers (a wrong `evidence_checked`, a wrong axiom count
#     quoted instead of re-read, `explain_corpus` printing a verdict a deeper
#     call would contradict). So: every entry in `steps[]` must have
#     `verdict == "pass"`. Any `fail`, `vacuous`, or `unreadable` step reds this
#     gate, by name, regardless of what the record's own `verdict` field claims
#     -- and if the two ever disagree (top-level PASS, a step not `pass`, or
#     the reverse) that disagreement is itself reported as a reason, because a
#     record that cannot even describe itself consistently is not evidence.
#
#   * No record at all (empty `artifacts/local-ci-runs/`) or no APPLICABLE
#     record (every record present is for a non-ancestor sha) is a FAILURE,
#     not a report. The alternative -- treat silence as merely informational --
#     recreates the exact defect the surrounding work is about: a checker
#     whose default, no-evidence state exits 0. CLAUDE.md's own count is 40 of
#     162 checker runs exiting 0 on completion alone; a "no record = pass"
#     rule would be checker #41 of that shape, just with better prose. Absence
#     is the limit case of staleness (infinitely old) and is treated the same
#     way: it reds.
#
# WIRING: **ENFORCING** in both `scripts/check.sh` and `justfile` as of
# 2026-08-19. It landed `--report-only` for one day for a stated, temporary
# reason: the only record that existed (`a6ee37c6a-s4.json`) was `verdict:
# FAIL` (4 golden-pin failures, fixed in 31442bd5d), and a gate that is red
# from the day it lands is a gate people learn to ignore. Report mode ran the
# identical guards meanwhile, so the printed line flipped to PASS the moment
# `57af69142-s4.json` landed -- an all-pass record, 5/5 steps, 7561 nextest
# tests + 179 doctests in 6656 s -- and both call sites dropped the flag.
#
# WHAT TO DO WHEN THIS REDS AND YOUR CHANGE LOOKS UNRELATED. Almost always
# STALE: the newest applicable record has aged past the 48h budget. The fix is
# to produce a new one, not to soften the gate --
#
#     scripts/local-ci.sh --record     # ~110 min, ONE lock across the whole box
#     # then commit artifacts/local-ci-runs/<sha>-<host>.json
#
# It cannot be run in a 10-minute foreground shell and it does not survive an
# ordinary background job; drive it under `setsid`, and read the RECORD
# afterwards rather than the exit code. Do NOT re-add `--report-only`: the
# whole point of this gate is that it can fail, and the only gate that knows
# whether the authoritative sweep still passes is worth nothing if it cannot.
#
# Usage:
#   scripts/check-local-ci-freshness.sh                 # enforcing: exit 1 on any FAIL reason
#   scripts/check-local-ci-freshness.sh --report-only    # same evaluation, always exits 0
#
# Env:
#   AXEYUM_LOCAL_CI_RECORDS                  record dir (default <repo>/artifacts/local-ci-runs)
#   AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS  staleness budget in hours (default 48)
#   AXEYUM_LOCAL_CI_FRESHNESS_REPO           repo root to evaluate (default: this script's repo;
#                                             override lets the control suite point this SAME
#                                             script at a disposable throwaway repo)
set -uo pipefail

SELF_REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="${AXEYUM_LOCAL_CI_FRESHNESS_REPO:-$SELF_REPO}"

REPORT_ONLY=0
for a in "$@"; do case "$a" in
  --report-only) REPORT_ONLY=1 ;;
esac; done

RECORD_DIR="${AXEYUM_LOCAL_CI_RECORDS:-$REPO_ROOT/artifacts/local-ci-runs}"
MAX_AGE_HOURS="${AXEYUM_LOCAL_CI_FRESHNESS_MAX_AGE_HOURS:-48}"

g() { git -C "$REPO_ROOT" "$@"; }

HEAD_SHA="$(g rev-parse HEAD 2>/dev/null)"
if [ -z "$HEAD_SHA" ]; then
  echo "local-ci-freshness: '$REPO_ROOT' is not a git checkout -- cannot evaluate" >&2
  exit 2
fi

# Read one record file. Prints, one per line: sha / host / finished_utc /
# top-level verdict / count of non-pass steps / then that many "verdict:cmd"
# lines. A malformed file (bad JSON, missing required fields) prints exactly
# PARSE_ERROR and nothing else.
read_record() {
  python3 - "$1" <<'PY'
import json, sys
p = sys.argv[1]
try:
    d = json.load(open(p))
    sha = d["sha"]
    host = d["host"]
    finished = d["finished_utc"]
    verdict = d["verdict"]
    steps = d["steps"]
    if not isinstance(steps, list):
        raise ValueError("steps is not a list")
except Exception:
    print("PARSE_ERROR")
    sys.exit(0)
bad = []
for s in steps:
    v = s.get("verdict", "") if isinstance(s, dict) else ""
    if v != "pass":
        bad.append(f'{v or "MISSING"}:{s.get("cmd", "?") if isinstance(s, dict) else "?"}')
print(sha)
print(host)
print(finished)
print(verdict)
print(len(bad))
for b in bad:
    print(b)
PY
}

shopt -s nullglob
files=("$RECORD_DIR"/*.json)
shopt -u nullglob

fail=0
reasons=()

if [ "${#files[@]}" -eq 0 ]; then
  reasons+=("NO_RECORD: $RECORD_DIR has zero record files -- the authoritative gate has no evidence it has EVER run against this history")
  fail=1
fi

# Phase 1: for every record, is it APPLICABLE (sha resolves and is HEAD or an
# ancestor of HEAD)? Collect "<commits_behind>\t<finished_epoch>\t<file>\t<sha>"
# for the ones that are; everything else is reported and excluded.
CANDIDATES="$(mktemp)"
trap 'rm -f "$CANDIDATES"' EXIT

for f in "${files[@]}"; do
  mapfile -t REC < <(read_record "$f")
  if [ "${REC[0]:-}" = "PARSE_ERROR" ]; then
    echo "local-ci-freshness: WARN unreadable record file '$f' (not valid JSON / missing required fields) -- excluded, not applicable" >&2
    continue
  fi
  sha="${REC[0]}"
  finished="${REC[2]:-}"
  full_sha="$(g rev-parse --verify -q "${sha}^{commit}" 2>/dev/null || true)"
  if [ -z "$full_sha" ]; then
    echo "local-ci-freshness: record '$f' names sha '$sha' which does not resolve in this repo -- excluded, not applicable"
    continue
  fi
  if ! g merge-base --is-ancestor "$full_sha" "$HEAD_SHA" 2>/dev/null; then
    echo "local-ci-freshness: record '$f' (sha=$sha) is NOT an ancestor of HEAD ($HEAD_SHA) -- excluded, not applicable (diverged or rebased away)"
    continue
  fi
  finished_epoch="$(date -u -d "$finished" +%s 2>/dev/null || true)"
  if [ -z "$finished_epoch" ]; then
    echo "local-ci-freshness: WARN record '$f' has an unparseable finished_utc '$finished' -- excluded, not applicable" >&2
    continue
  fi
  behind="$(g rev-list --count "${full_sha}..${HEAD_SHA}" 2>/dev/null || echo -1)"
  printf '%s\t%s\t%s\t%s\n' "$behind" "$finished_epoch" "$f" "$sha" >> "$CANDIDATES"
done

if [ ! -s "$CANDIDATES" ]; then
  if [ "${#files[@]}" -gt 0 ]; then
    reasons+=("NO_APPLICABLE_RECORD: ${#files[@]} record file(s) exist but none is HEAD or an ancestor of HEAD ($HEAD_SHA)")
    fail=1
  fi
else
  # Newest = fewest commits behind HEAD; ties broken by latest finished_epoch.
  NEWEST_LINE="$(sort -t "$(printf '\t')" -k1,1n -k2,2nr "$CANDIDATES" | head -1)"
  NEWEST_FILE="$(printf '%s' "$NEWEST_LINE" | cut -f3)"
  NEWEST_SHA="$(printf '%s' "$NEWEST_LINE" | cut -f4)"
  NEWEST_BEHIND="$(printf '%s' "$NEWEST_LINE" | cut -f1)"
  NEWEST_FINISHED_EPOCH="$(printf '%s' "$NEWEST_LINE" | cut -f2)"
  NOW_EPOCH="$(date -u +%s)"
  AGE_HOURS=$(( (NOW_EPOCH - NEWEST_FINISHED_EPOCH) / 3600 ))

  echo "local-ci-freshness: newest applicable record is '$NEWEST_FILE' (sha=$NEWEST_SHA, ${NEWEST_BEHIND} commit(s) behind HEAD, ${AGE_HOURS}h old)"

  # Guard: STALE.
  if [ "$AGE_HOURS" -gt "$MAX_AGE_HOURS" ]; then
    reasons+=("STALE: newest applicable record is ${AGE_HOURS}h old, exceeds the ${MAX_AGE_HOURS}h budget")
    fail=1
  fi

  mapfile -t NEWEST_REC < <(read_record "$NEWEST_FILE")
  N_TOP_VERDICT="${NEWEST_REC[3]:-}"
  N_BAD_COUNT="${NEWEST_REC[4]:-0}"

  # Guard: the record's own steps, not its summary field, decide pass/fail.
  any_fail=0 any_vacuous=0 any_unreadable=0
  if [ "${N_BAD_COUNT:-0}" -gt 0 ] 2>/dev/null; then
    idx=5
    for ((i = 0; i < N_BAD_COUNT; i++)); do
      line="${NEWEST_REC[$((idx + i))]:-}"
      v="${line%%:*}"
      cmd="${line#*:}"
      # Each branch sets `fail=1` INDEPENDENTLY, on purpose -- not once after
      # the loop. CLAUDE.md's own measurement is six of seven guards in one
      # suite being removable with everything still green because they all
      # rejected through one shared check; a single `fail=1` here would make
      # this exact loop that pattern, since deleting it would silently wave
      # through fail/vacuous/unreadable steps together and three controls
      # would die from one mutation instead of one each.
      case "$v" in
        fail) any_fail=1; fail=1; reasons+=("STEP FAILED: \`$cmd\`") ;;
        vacuous) any_vacuous=1; fail=1; reasons+=("STEP VACUOUS: \`$cmd\` exited 0 having run ZERO tests") ;;
        unreadable) any_unreadable=1; fail=1; reasons+=("STEP UNREADABLE: \`$cmd\` exited 0 but its test count could not be parsed") ;;
        *) fail=1; reasons+=("STEP NON-PASS ($v): \`$cmd\`") ;;
      esac
    done
  fi

  # Guard: top-level verdict must independently say PASS too. A mismatch
  # between this and the per-step derivation above is reported as its own
  # reason -- a record that disagrees with itself is not evidence either way.
  if [ "$N_TOP_VERDICT" != "PASS" ]; then
    if [ "${N_BAD_COUNT:-0}" -eq 0 ] 2>/dev/null; then
      reasons+=("INCONSISTENT RECORD: top-level verdict is '$N_TOP_VERDICT' but every step reads pass")
    else
      reasons+=("NON-PASS: record's top-level verdict is '$N_TOP_VERDICT'")
    fi
    fail=1
  fi
fi

if [ "$fail" = 1 ]; then
  echo "local-ci-freshness: FAIL"
  for r in "${reasons[@]}"; do echo "  - $r"; done
else
  echo "local-ci-freshness: PASS -- fresh, ancestor, all-pass local-ci record covers HEAD's recent history"
fi

if [ "$REPORT_ONLY" = 1 ]; then
  exit 0
fi
[ "$fail" = 1 ] && exit 1
exit 0
