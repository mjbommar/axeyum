#!/usr/bin/env bash
# Controls for `scripts/check-parity-freshness.py`: run the REAL script against
# fabricated ledgers, one scenario at a time, and assert both the exit code and
# the machine-readable line it printed.
#
# Per CLAUDE.md: "a checker that cannot fail is worse than no checker", and a
# gate that has never been SHOWN to fire is the defect this repository keeps
# rediscovering. So the cases below are mostly ledgers the gate must REJECT,
# with the accepting cases present to prove the rejections are not vacuous
# (a script that exits 1 unconditionally would pass every rejection case and
# is killed by case `fresh` and case `warn-band`).
#
# MUTATION-VERIFIED, not asserted by comment. Every guard in
# `check-parity-freshness.py` was deleted one at a time and the cases that died
# recorded (2026-08-21, this suite at 12 cases):
#
#   mutation                                       cases killed
#   ENTRY_RE's ` — <LABEL>` group never matches    evidence-mode-counts,
#                                                  real-ledger-coverage,
#                                                  real-ledger-evidence-entry
#   ANNOTATION_RE never matches                    correction-tolerated,
#                                                  real-ledger-coverage,
#                                                  real-ledger-evidence-entry
#   the raise on an unclassified '## ' header      unknown-header
#   the raise on a missing disagreements row       malformed-entry
#   MIN_LOGICS = 0                                 vacuous-population
#   `if r["disagreements"] > 0: continue` removed  voided-does-not-refresh
#   `if age > max_days: state = "STALE"` removed   stale, voided-does-not-refresh
#   `elif age > warn_days` collapsed to ok         warn-band
#   `unmeasured` forced empty                      unmeasured-reported
#   SOLVER_COMMIT_RE never matches                 solver-currency-no-git,
#                                                  real-solver-currency
#   the `no-git` early return removed              solver-currency-no-git
#   the `behind=` rev-list broken                  real-solver-currency
#   solver currency made FATAL                     fresh, warn-band,
#                                                  evidence-mode-counts,
#                                                  correction-tolerated,
#                                                  unmeasured-reported,
#                                                  solver-currency-unresolvable,
#                                                  solver-currency-is-advisory
#
# Six of the nine kill exactly one case. The three that kill more do so for a
# reason worth stating rather than tidying away:
#
#   * The two parser mutations also kill the two real-ledger cases, because the
#     real ledger contains both an `— EVIDENCE MODE` entry and a `## Correction`
#     block. Those two cases are COVERAGE, not guards: they exist because an
#     empty answer from a parser that was never pointed at its subject is
#     indistinguishable from a strong negative result, so a fixture-only suite
#     would stay green if the shipped ledger's own format drifted away from
#     ENTRY_RE. They are supposed to die whenever the parser stops seeing the
#     real file.
#   * Making solver currency FATAL kills seven cases, which is the point: the
#     gate's header argues at length that currency must stay advisory (a
#     commit-count bound is red-by-construction during a commit burst, and
#     non-ancestry is legitimate when another lane measures from its own
#     branch). `solver-currency-is-advisory` exists so that decision has a
#     control of its own rather than being an emergent property of the others.
#   * Deleting the STALE branch deletes the gate's ONLY failure condition, so
#     both cases whose fixture is stale die. That is not the "everything
#     rejects through one shared check" defect CLAUDE.md warns about -- the
#     void rule has its own mutation above and dies alone -- it just means the
#     staleness comparison is load-bearing, which it is.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT="$PWD/scripts/check-parity-freshness.py"
REAL_LEDGER="$PWD/bench-results/PARITY.md"
[ -r "$SCRIPT" ] || { echo "FAIL: cannot read $SCRIPT"; exit 1; }
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
asserted=0

NOW="2026-08-21T12:00:00Z"
# Valid-looking but deliberately NOT a real object, so the currency probe has a
# defined answer ("unresolvable") in fixtures instead of accidentally resolving.
FIXTURE_SHA="deadbee1234"

# entry <file> <logic> <iso-ts> <disagreements> [label] [solver-sha]
entry() {
  local f="$1" logic="$2" ts="$3" dis="$4" label="${5:-}" sha="${6:-$FIXTURE_SHA}"
  {
    if [ -n "$label" ]; then
      echo "## ${logic} — ${ts} — ${label}"
    else
      echo "## ${logic} — ${ts}"
    fi
    echo
    echo "| field | value |"
    echo "|---|---|"
    echo "| axeyum solved | 100/200 |"
    echo "| reference solved | 150/200 |"
    echo "| **ratio (axeyum / reference)** | **66.7%** |"
    echo "| **disagreements** | **${dis}** |"
    echo "| soundness | $([ "$dis" = 0 ] && echo SOUND || echo FAIL) |"
    echo "| protocol | 24s wall, 8GiB, per-file |"
    echo "| solver commit | \`${sha}\` |"
    echo
  } >> "$f"
}

ledger_header() { printf '# Parity ledger\n\nAppend-only.\n\n' > "$1"; }

# A nine-logic board, every entry `$2` (an ISO timestamp) and sound.
board() {
  local f="$1" ts="$2"
  ledger_header "$f"
  local lg
  for lg in QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA QF_NIA; do
    entry "$f" "$lg" "$ts" 0
  done
}

LISTS="$WORK/lists"; mkdir -p "$LISTS"
for lg in QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA QF_NIA; do
  echo "some/benchmark.smt2" > "$LISTS/$lg.txt"
done

# case <name> <ledger> <lists-dir> <want-rc> <want-substring…>
case_() {
  local name="$1" ledger="$2" lists="$3" want_rc="$4"; shift 4
  local out got_rc pat hits
  out="$(python3 "$SCRIPT" --ledger "$ledger" --lists "$lists" --now "$NOW" 2>&1)"
  got_rc=$?
  asserted=$((asserted + 1))
  if [ "$got_rc" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got_rc (want $want_rc) — $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  for pat in "$@"; do
    # `grep -c`, never `grep -q`: under `set -o pipefail` a `-q` consumer exits
    # at the first match, SIGPIPEs the producer, and the pipeline status 141
    # reads as "not found". Same trap documented in
    # scripts/check-control-registration.sh.
    hits=$(printf '%s\n' "$out" | grep -cF "$pat")
    if [ "${hits:-0}" -eq 0 ]; then
      echo "FAIL case:$name rc ok but missing '$pat' — $(printf '%s' "$out" | tr '\n' '|')"
      fail=1; return
    fi
  done
  echo "ok   case:$name -> rc=$got_rc"
}

# case_repo <name> <ledger> <lists> <repo> <want-rc> <want-substring...>
case_repo() {
  local name="$1" ledger="$2" lists="$3" repo="$4" want_rc="$5"; shift 5
  local out got_rc pat hits
  out="$(python3 "$SCRIPT" --ledger "$ledger" --lists "$lists" --repo "$repo" \
         --now "$NOW" 2>&1)"
  got_rc=$?
  asserted=$((asserted + 1))
  if [ "$got_rc" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got_rc (want $want_rc) — $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  for pat in "$@"; do
    hits=$(printf '%s\n' "$out" | grep -cF "$pat")
    if [ "${hits:-0}" -eq 0 ]; then
      echo "FAIL case:$name rc ok but missing '$pat' — $(printf '%s' "$out" | tr '\n' '|')"
      fail=1; return
    fi
  done
  echo "ok   case:$name -> rc=$got_rc"
}

# --- 1. FRESH: every logic measured an hour ago. Must PASS. Without this the
#        whole suite would be satisfied by a gate that exits 1 always. -------
L="$WORK/fresh.md"; board "$L" "2026-08-21T11:00:00Z"
case_ fresh "$L" "$LISTS" 0 "verdict=PASS" "|stale=0" "|logics=9"

# --- 2. STALE: one logic 40 days old on an otherwise fresh board. Must FAIL,
#        name that logic, and report it as the stalest. ---------------------
L="$WORK/stale.md"; ledger_header "$L"
for lg in QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA; do
  entry "$L" "$lg" "2026-08-21T11:00:00Z" 0
done
entry "$L" QF_NIA "2026-07-12T11:00:00Z" 0
case_ stale "$L" "$LISTS" 1 "verdict=FAIL" "stalest=QF_NIA" \
  "PARITY_FRESHNESS_ERROR|QF_NIA was last validly measured 40.0 days ago"

# --- 3. WARN BAND: 12 days old is past the 10-day warning but inside the
#        14-day budget. Must PASS while SAYING so. Kills a mutation that
#        collapses the warning into the failure. ------------------------------
L="$WORK/warn.md"; ledger_header "$L"
for lg in QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA; do
  entry "$L" "$lg" "2026-08-21T11:00:00Z" 0
done
entry "$L" QF_NIA "2026-08-09T11:00:00Z" 0
case_ warn-band "$L" "$LISTS" 0 "verdict=PASS" "|warn=1" "|stale=0"

# --- 4. EVIDENCE MODE: the freshest entry for a logic carries the trailing
#        ` — EVIDENCE MODE` label, and its older plain entry is stale. A regex
#        without the optional label group cannot see the fresh one. This is
#        the miss that actually happened while the gap analysis was written. --
L="$WORK/evidence.md"; ledger_header "$L"
for lg in QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA QF_NIA; do
  entry "$L" "$lg" "2026-08-21T11:00:00Z" 0
done
entry "$L" QF_BV "2026-07-01T11:00:00Z" 0
entry "$L" QF_BV "2026-08-21T10:00:00Z" 0 "EVIDENCE MODE"
case_ evidence-mode-counts "$L" "$LISTS" 0 "verdict=PASS" "|stale=0" "[evidence]"

# --- 5. A `## Correction — …` block is prose the ledger legitimately carries
#        and must not red the gate. ------------------------------------------
L="$WORK/correction.md"; board "$L" "2026-08-21T11:00:00Z"
printf '## Correction — 2026-08-02: a spurious DIRTY stamp on the entries above\n\nProse.\n\n' >> "$L"
case_ correction-tolerated "$L" "$LISTS" 0 "verdict=PASS" "|logics=9"

# --- 6. An unrecognised `## ` header must EXIT 2, not be silently skipped. A
#        skipped entry is indistinguishable from an absent one, which is how a
#        stale logic reads as fresh. ------------------------------------------
L="$WORK/unknown.md"; board "$L" "2026-08-21T11:00:00Z"
printf '## QF_NIA / 2026-08-21T11:00:00Z\n\nnot the entry format\n\n' >> "$L"
case_ unknown-header "$L" "$LISTS" 2 "PARITY_FRESHNESS_ERROR" "unrecognised"

# --- 7. An entry with no `**disagreements**` row cannot be told apart from a
#        voided one, so it must EXIT 2 rather than be counted as valid. -------
L="$WORK/malformed.md"; board "$L" "2026-08-21T11:00:00Z"
printf '## QF_NIA — 2026-08-21T11:30:00Z\n\n| field | value |\n|---|---|\n| axeyum solved | 1/200 |\n\n' >> "$L"
case_ malformed-entry "$L" "$LISTS" 2 "PARITY_FRESHNESS_ERROR" "disagreements"

# --- 8. A near-empty population is a broken parser, not a green board. -------
L="$WORK/vacuous.md"; ledger_header "$L"
entry "$L" QF_BV "2026-08-21T11:00:00Z" 0
entry "$L" UF "2026-08-21T11:00:00Z" 0
case_ vacuous-population "$L" "$LISTS" 2 "PARITY_FRESHNESS_ERROR" "parsed only 2 logic"

# --- 9. A VOIDED entry (disagreements > 0) is fresh in time but is not a
#        measurement -- the ledger's own rule voids it -- so it must not
#        refresh the clock. QF_NIA's only sound entry is 40 days old. --------
L="$WORK/voided.md"; ledger_header "$L"
for lg in QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL QF_RDL QF_UFLIA; do
  entry "$L" "$lg" "2026-08-21T11:00:00Z" 0
done
entry "$L" QF_NIA "2026-07-12T11:00:00Z" 0
entry "$L" QF_NIA "2026-08-21T11:00:00Z" 3
case_ voided-does-not-refresh "$L" "$LISTS" 1 "verdict=FAIL" "|voided=1" "stalest=QF_NIA"

# --- 10. A committed benchmark list that has NEVER been measured is a coverage
#         gap: reported and counted, deliberately NOT enforced (see the gate's
#         header). This case pins that decision in both directions -- the count
#         is nonzero AND the exit status is 0. --------------------------------
L="$WORK/fresh.md"
LISTS2="$WORK/lists2"; cp -r "$LISTS" "$LISTS2"; echo "x.smt2" > "$LISTS2/QF_ABV.txt"
case_ unmeasured-reported "$L" "$LISTS2" 0 "verdict=PASS" "|unmeasured=1" "QF_ABV"

# --- 11a. SOLVER CURRENCY, degradation: pointed at a directory that is not a
#          checkout, the currency probe must say NO-GIT and must not stop the
#          gate. A staleness gate that cannot run because a diagnostic could not
#          reach git would be a worse gate than one with no diagnostic. -------
L="$WORK/fresh.md"
case_repo solver-currency-no-git "$L" "$LISTS" "$WORK" 0 \
  "verdict=PASS" "NO-GIT" "|max_solver_lag=0"

# --- 11b. SOLVER CURRENCY, unresolvable sha: valid hex that names no object in
#          this checkout. Counted and shown, never fatal -- a sha can legitimately
#          vanish (a rewritten or unmerged branch), and two 2026-08-02 entries in
#          the real ledger already have. ---------------------------------------
case_repo solver-currency-unresolvable "$L" "$LISTS" "$PWD" 0 \
  "verdict=PASS" "UNRESOLVABLE" "|unresolvable_solver_commit=9"

# --- 11c. SOLVER CURRENCY IS ADVISORY, asserted as its own case rather than as
#          a side effect of 11a/11b. A board every one of whose entries has an
#          unusable solver commit is still FRESH, so the exit status must be 0
#          and the verdict PASS. If a later change makes currency fatal, this
#          is the control that dies -- deliberately, because the gate's header
#          argues at length that it must not be. ------------------------------
case_repo solver-currency-is-advisory "$L" "$LISTS" "$PWD" 0 \
  "verdict=PASS" "|stale=0"

# --- 11. COVERAGE, not a fixture: point the gate at the REAL committed ledger
#         and assert a specific NONZERO population. A fixture-only suite stays
#         green if the shipped ledger's format drifts away from ENTRY_RE, which
#         is the "empty answer to a question you did not ask" trap. The exit
#         status is deliberately NOT asserted here -- whether the real board is
#         currently stale is the gate's job to say, not this suite's. ---------
asserted=$((asserted + 1))
real_out="$(python3 "$SCRIPT" --now "$NOW" 2>&1)"
real_logics=$(printf '%s\n' "$real_out" | sed -n 's/.*PARITY_FRESHNESS|logics=\([0-9]*\).*/\1/p')
if [ -z "$real_logics" ] || [ "$real_logics" -lt 9 ]; then
  echo "FAIL case:real-ledger-coverage parsed logics='${real_logics:-<none>}' (want >= 9) — $(printf '%s' "$real_out" | tr '\n' '|')"
  fail=1
else
  echo "ok   case:real-ledger-coverage -> logics=$real_logics from bench-results/PARITY.md"
fi

# --- 12. …and that the label group is alive against the REAL file, so the
#         fixture in case 4 cannot be the only thing keeping it so.
#
#         DERIVED, NOT PINNED (rewritten 2026-09-06). This case used to assert
#         the literal string `2026-08-17T20:21Z`, on the reasoning that the
#         shipped ledger's FRESHEST QF_BV entry was an `— EVIDENCE MODE` one and
#         a label-blind parser would report the 2026-08-02 entry instead. That
#         reasoning expired the moment a later QF_BV sweep landed: by
#         2026-09-05 the freshest QF_BV entry was unlabelled, the literal no
#         longer matched, and the case failed in CI for a reason that had
#         nothing to do with the parser. A control that pins a literal measures
#         the maintainer's memory, which is the failure this suite exists to
#         prevent -- so it now derives both halves from the ledger.
#
#         Half one: the reported row for each logic is that logic's freshest
#         entry, computed from the file. Half two: the file still contains at
#         least one labelled entry, and the checker accepts it. Half two is
#         what keeps the label group alive, and it does so through the
#         unclassified-header raise rather than through entry selection --
#         MEASURED 2026-09-06 on a scratch copy: deleting the `(?: — (?P<label>
#         .+))?` group makes this script exit 2 on the real ledger ("a header
#         this parser does not classify would be SKIPPED"), because the two
#         labelled QF_BV headers stop matching. That kill does not depend on a
#         labelled entry being the freshest, so it survives every future sweep.
#         ------------------------------------------------------------------
asserted=$((asserted + 1))
labelled=$(grep -cE '^## [A-Z][A-Z0-9_]* — [0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z — .+$' "$REAL_LEDGER")
ledger_logics=$(grep -oE '^## [A-Z][A-Z0-9_]* — ' "$REAL_LEDGER" | sort -u | wc -l)
reported_rows=$(printf '%s\n' "$real_out" | awk '/^  [A-Z]/{n++} END{print n+0}')
freshest_mismatch=""
for lg in $(printf '%s\n' "$real_out" | awk '/^  [A-Z]/{print $1}'); do
  want=$(grep -oE "^## ${lg} — [0-9T:Z-]+" "$REAL_LEDGER" | sed -E "s/^## ${lg} — //" | sort | tail -1 | cut -c1-16)
  got=$(printf '%s\n' "$real_out" | awk -v L="$lg" '$1==L{print $3; exit}' | cut -c1-16)
  if [ -n "$want" ] && [ "$want" != "$got" ]; then
    freshest_mismatch="$freshest_mismatch $lg(want=$want got=$got)"
  fi
done
if [ "${reported_rows:-0}" -lt "${ledger_logics:-9}" ]; then
  # NON-VACUITY GUARD. Without this the case passes on an ERROR: the loop below
  # iterates over rows parsed out of $real_out, and an error output has none, so
  # an empty loop leaves $freshest_mismatch empty and every assertion "holds".
  # MEASURED 2026-09-06: the first draft of this rewrite reported ok under a
  # surgical label-group mutation for exactly that reason. A control that cannot
  # fail is worse than no control.
  echo "FAIL case:real-ledger-label-group the checker reported ${reported_rows:-0} row(s) for ${ledger_logics} logic(s) in the ledger — it did not parse the real file, so nothing below was actually asserted: $(printf '%s' "$real_out" | tr '\n' '|' | cut -c1-200)"
  fail=1
elif [ "${labelled:-0}" -lt 1 ]; then
  echo "FAIL case:real-ledger-label-group the real ledger carries NO labelled entry, so nothing here exercises ENTRY_RE's label group; add one or move this assertion"
  fail=1
elif [ -n "$freshest_mismatch" ]; then
  echo "FAIL case:real-ledger-label-group reported row is not the freshest entry for:$freshest_mismatch"
  fail=1
else
  echo "ok   case:real-ledger-label-group -> $labelled labelled entry/entries; every reported row is its logic's freshest"
fi

# --- 13. SOLVER CURRENCY against the REAL ledger and the REAL checkout: at
#         least one row must report a resolvable `behind=` count. This is the
#         case that fails if the `solver commit` row stops being parsed, or if
#         the lag computation silently returns nothing -- both of which would
#         otherwise read as "no currency problems anywhere", the empty answer
#         that looks like a clean bill of health. ---------------------------
asserted=$((asserted + 1))
behind_rows=$(printf '%s\n' "$real_out" | grep -cE '\[[0-9a-f]{7,9} behind=[0-9]+\]')
if [ "${behind_rows:-0}" -lt 1 ]; then
  echo "FAIL case:real-solver-currency no row reported a resolvable behind= count"
  fail=1
else
  echo "ok   case:real-solver-currency -> $behind_rows row(s) with a behind= count"
fi

if [ "$asserted" -lt 15 ]; then
  echo "PARITY_FRESHNESS_CONTROLS|ERROR only $asserted case(s) ran; a suite that" \
       "runs (almost) nothing exits 0 for the wrong reason" >&2
  exit 1
fi
if [ "$fail" = 0 ]; then
  echo "PARITY_FRESHNESS_CONTROLS|ok|cases=$asserted"
else
  echo "PARITY_FRESHNESS_CONTROLS|FAILED|cases=$asserted" >&2
fi
exit "$fail"
