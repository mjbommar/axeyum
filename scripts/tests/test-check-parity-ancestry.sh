#!/usr/bin/env bash
# Controls for `scripts/check-parity-ancestry.py`: run the REAL script against
# fabricated ledgers over a REAL throwaway git repository whose commit graph
# this suite builds, and assert both the exit code and the machine-readable
# line it printed.
#
# WHY A REAL REPOSITORY AND NOT A STUB.  The whole gate is one primitive --
# `git merge-base --is-ancestor` -- so a suite that mocks git tests the parser
# and nothing else. The graph below is built with real commits precisely so the
# ancestry answers are git's, not this file's opinion of them:
#
#     A ── B ── C          (main line)
#      └── D               (side branch, divergent with B and C)
#
# Per CLAUDE.md: "a checker that cannot fail is worse than no checker", and the
# rule for touching one is to delete a guard and require that EXACTLY ONE test
# dies. Every guard in `check-parity-ancestry.py` was deleted one at a time and
# the cases that died RECORDED FROM THE RUN, not predicted (2026-09-09, this
# suite at 15 cases; driver output in the lane's commit message):
#
#   mutation                                        killed  cases
#   `classify` returns "ok" unconditionally           6     superseded,
#                                                           divergent,
#                                                           motivating-incident,
#                                                           evidence-in-default-series,
#                                                           unresolvable-is-advisory,
#                                                           no-git-is-advisory
#   the `git.is_ancestor(b, a)` branch removed        3     superseded,
#     (SUPERSEDED collapses into DIVERGENT)                 motivating-incident,
#                                                           evidence-in-default-series
#   the DIVERGENT fallthrough returns "ok"            1     divergent
#   `if r["disagreements"] > 0: continue` removed     1     voided-row-excluded
#   the series key drops `r["reference"]`             2     second-reference-own-series,
#                                                           real-ledger-coverage
#   ENTRY_RE's ` — <LABEL>` group never matches       3     second-reference-own-series,
#                                                           evidence-in-default-series,
#                                                           real-ledger-coverage
#   ANNOTATION_RE never matches                       1     real-ledger-coverage
#   the raise on an unclassified '## ' header         1     unknown-header
#   the raise on a missing disagreements row          1     malformed-entry
#   MIN_LOGICS = 0                                    1     vacuous-population
#   the "unresolvable" early return in `classify`     1     unresolvable-is-advisory
#   the `git.available` early return in `classify`    1     no-git-is-advisory
#   the OUT-OF-ORDER-TIMESTAMP note deleted           1     out-of-order-timestamp
#   `unresolvable`/`no-git` made FATAL                2     unresolvable-is-advisory,
#                                                           no-git-is-advisory
#   rows[-1] changed to rows[0] (wrong "newest")      5     superseded, divergent,
#                                                           motivating-incident,
#                                                           ordered-passes,
#                                                           out-of-order-timestamp
#
# NINE of the fifteen kill exactly one case, and every one kills at least one --
# there is no dead-weight guard here. The multi-kill ones are stated rather than
# tidied away:
#
#   * `classify` returning "ok" and `rows[-1] -> rows[0]` are the two ways to
#     delete the gate's ONLY failure condition, so every rejecting case dies.
#     That is not the "everything rejects through one shared check" defect --
#     each of the two sub-classifications (SUPERSEDED, DIVERGENT) has its own
#     mutation above and dies alone, as does each exclusion rule. Note that
#     `rows[0]` also kills `ordered-passes` and `out-of-order-timestamp`, which
#     is how a suite distinguishes "the gate stopped firing" from "the gate
#     started firing on the wrong row".
#   * The two parser mutations also kill `real-ledger-coverage`, because the
#     shipped ledger contains both `— SECOND REFERENCE (…)` entries and
#     `## Correction` prose. That case is COVERAGE, not a guard: an empty
#     answer from a parser never pointed at its subject is indistinguishable
#     from a strong negative, so a fixture-only suite would stay green if the
#     real ledger's format drifted. It is supposed to die when the parser stops
#     seeing the real file.
#   * Making unresolvable/no-git FATAL kills exactly the two advisory cases,
#     which is the point: the script's header argues those must stay advisory
#     because no re-measurement fixes a row whose tree no longer exists, and a
#     gate with no remedy is one people learn to override.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT="$PWD/scripts/check-parity-ancestry.py"
REAL_LEDGER="$PWD/bench-results/PARITY.md"
REAL_REPO="$PWD"
[ -r "$SCRIPT" ] || { echo "FAIL: cannot read $SCRIPT"; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
asserted=0

# ---------------------------------------------------------------------------
# The throwaway commit graph.  A ── B ── C, plus D branching off A.
#
# Built in $WORK, never in this checkout: a git guard tested against the shared
# tree is how an empty commit reached main once already.
# ---------------------------------------------------------------------------
REPO="$WORK/repo"
mkdir -p "$REPO"
git -C "$REPO" init --quiet -b trunk
git -C "$REPO" config user.email "controls@example.invalid"
git -C "$REPO" config user.name "ancestry controls"
mk() {
  echo "$1" > "$REPO/f.txt"
  git -C "$REPO" add f.txt
  git -C "$REPO" commit --quiet -m "$1"
  git -C "$REPO" rev-parse HEAD
}
A=$(mk A)
B=$(mk B)
C=$(mk C)
git -C "$REPO" checkout --quiet -b side "$A"
D=$(mk D)
git -C "$REPO" checkout --quiet trunk

# Assert the graph is what the cases assume, rather than trusting the recipe.
git -C "$REPO" merge-base --is-ancestor "$A" "$C" \
  || { echo "FAIL: control setup — A is not an ancestor of C"; exit 1; }
git -C "$REPO" merge-base --is-ancestor "$B" "$D" \
  && { echo "FAIL: control setup — B must NOT be an ancestor of D"; exit 1; }
git -C "$REPO" merge-base --is-ancestor "$D" "$B" \
  && { echo "FAIL: control setup — D must NOT be an ancestor of B"; exit 1; }

# A syntactically valid sha that is deliberately not an object anywhere.
FIXTURE_SHA="deadbee1234"

# entry <file> <logic> <iso-ts> <disagreements> <solver-sha> [label]
entry() {
  local f="$1" logic="$2" ts="$3" dis="$4" sha="$5" label="${6:-}"
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

# Six logics so MIN_LOGICS is satisfied; the case under test is added on top.
PAD_LOGICS="QF_BV QF_SLIA UF QF_LIA QF_LRA QF_IDL"
pad() {
  local f="$1" sha="$2" lg
  for lg in $PAD_LOGICS; do
    entry "$f" "$lg" "2026-09-01T10:00:00Z" 0 "$sha"
  done
}

# case_ <name> <ledger> <repo> <want-rc> <want-substring…>
case_() {
  local name="$1" ledger="$2" repo="$3" want_rc="$4"; shift 4
  local out got_rc pat hits
  out="$(python3 "$SCRIPT" --ledger "$ledger" --repo "$repo" 2>&1)"
  got_rc=$?
  asserted=$((asserted + 1))
  if [ "$got_rc" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got_rc (want $want_rc) — $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  for pat in "$@"; do
    # `grep -c`, never `grep -q`: under `set -o pipefail` a `-q` consumer exits
    # at the first match, SIGPIPEs the producer, and status 141 reads as
    # "not found".
    hits=$(printf '%s\n' "$out" | grep -cF "$pat")
    if [ "${hits:-0}" -eq 0 ]; then
      echo "FAIL case:$name rc ok but missing '$pat' — $(printf '%s' "$out" | tr '\n' '|')"
      fail=1; return
    fi
  done
  echo "ok   case:$name -> rc=$got_rc"
}

# --- 1. ORDERED: every series' newest row descends from its earlier rows.
#        Must PASS. Without this the suite would be satisfied by a script that
#        exits 1 unconditionally. -----------------------------------------
L="$WORK/ordered.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_UFLIA "2026-09-02T10:00:00Z" 0 "$A"
entry "$L" QF_UFLIA "2026-09-03T10:00:00Z" 0 "$B"
entry "$L" QF_UFLIA "2026-09-04T10:00:00Z" 0 "$C"
case_ ordered-passes "$L" "$REPO" 0 "verdict=PASS" "|unordered_pairs=0" "|series=7"

# --- 2. SINGLE ROW: a series with one entry has nothing to order against and
#        must not be reported as broken. Kills a mutation that treats an empty
#        comparison list as a finding. --------------------------------------
L="$WORK/single.md"; ledger_header "$L"; pad "$L" "$C"
case_ single-row "$L" "$REPO" 0 "verdict=PASS" "ok (single row)" "|rows=6"

# --- 3. SUPERSEDED BY OLDER CODE: the newest row was measured at B, an
#        ancestor of C, which an EARLIER row already measured. This is the
#        129-after-151 shape the gate exists for. --------------------------
L="$WORK/superseded.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_UFLIA "2026-09-03T10:00:00Z" 0 "$C"
entry "$L" QF_UFLIA "2026-09-04T10:00:00Z" 0 "$B"
case_ superseded "$L" "$REPO" 1 "verdict=FAIL" "|unordered_pairs=1" \
  "SUPERSEDED-BY-OLDER-CODE: QF_UFLIA" "PARITY_ANCESTRY_ERROR|QF_UFLIA"

# --- 4. DIVERGENT: the newest row was measured on a side branch, so neither
#        commit reaches the other and no before/after reading exists. ------
L="$WORK/divergent.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_LIA "2026-09-03T10:00:00Z" 0 "$B"
entry "$L" QF_LIA "2026-09-04T10:00:00Z" 0 "$D"
case_ divergent "$L" "$REPO" 1 "verdict=FAIL" "DIVERGENT: QF_LIA" \
  "|unordered_series=1"

# --- 5. THE MOTIVATING INCIDENT, with the REAL shas from this repository:
#        `f24c61f91` (the 129/200 QF_UFLIA measurement) is an ancestor of
#        `26d9d80e3` (the fix measured at 151/200). Appended in that order the
#        board's newest row is the older tree, and the gate must say so.
#        Skipped, loudly, if either commit is not in this checkout — a control
#        that silently disappears is worse than one that is absent. ---------
INCIDENT_OLD="f24c61f91"   # the tree the 129/200 row was measured on
INCIDENT_NEW="26d9d80e3"   # the QF_UFLIA fix, 151/200 in its own lane
if git -C "$REAL_REPO" cat-file -e "${INCIDENT_OLD}^{commit}" 2>/dev/null \
   && git -C "$REAL_REPO" cat-file -e "${INCIDENT_NEW}^{commit}" 2>/dev/null; then
  git -C "$REAL_REPO" merge-base --is-ancestor "$INCIDENT_OLD" "$INCIDENT_NEW" \
    || { echo "FAIL case:motivating-incident — premise gone: ${INCIDENT_OLD} is no longer an ancestor of ${INCIDENT_NEW}"; fail=1; }
  L="$WORK/incident.md"; ledger_header "$L"; pad "$L" "$INCIDENT_OLD"
  entry "$L" QF_UFLIA "2026-09-08T21:50:00Z" 0 "$INCIDENT_NEW"
  entry "$L" QF_UFLIA "2026-09-08T22:27:12Z" 0 "$INCIDENT_OLD"
  case_ motivating-incident "$L" "$REAL_REPO" 1 "verdict=FAIL" \
    "SUPERSEDED-BY-OLDER-CODE: QF_UFLIA"
else
  echo "FAIL case:motivating-incident — ${INCIDENT_OLD} / ${INCIDENT_NEW} not resolvable in $REAL_REPO"
  fail=1
fi

# --- 6. SECOND REFERENCE IS ITS OWN SERIES: a yices2-referenced row measured
#        at B, appended after a cvc5-referenced row at C. Those are two
#        different measurements of two different things, so ordering them
#        against each other would manufacture a finding. Must PASS. --------
L="$WORK/secondref.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_LRA "2026-09-03T10:00:00Z" 0 "$C"
entry "$L" QF_LRA "2026-09-04T10:00:00Z" 0 "$B" "SECOND REFERENCE (yices2)"
case_ second-reference-own-series "$L" "$REPO" 0 "verdict=PASS" \
  "QF_LRA [yices2]"

# --- 7. EVIDENCE MODE STAYS IN THE DEFAULT SERIES: its scored counts come
#        from the same default-route run at the same budget, so an evidence
#        row at an OLDER commit does supersede a default row. Must FAIL. ----
L="$WORK/evidence.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_BV "2026-09-03T10:00:00Z" 0 "$C"
entry "$L" QF_BV "2026-09-04T10:00:00Z" 0 "$B" "EVIDENCE MODE"
case_ evidence-in-default-series "$L" "$REPO" 1 "verdict=FAIL" \
  "SUPERSEDED-BY-OLDER-CODE: QF_BV"

# --- 8. A VOIDED ROW IS NOT A CODE-ORDERING DATUM: the ledger's own rule is
#        that `disagreements > 0` voids an entry, and the freshness gate
#        already refuses to let one refresh the clock. Divergent commit,
#        voided row: must PASS. ---------------------------------------------
L="$WORK/voided.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_NIA "2026-09-03T10:00:00Z" 3 "$D"
entry "$L" QF_NIA "2026-09-04T10:00:00Z" 0 "$B"
case_ voided-row-excluded "$L" "$REPO" 0 "verdict=PASS" "|unordered_pairs=0"

# --- 9. UNRESOLVABLE IS ADVISORY: a sha that no longer exists has no
#        re-measurement that fixes it, so it is counted and named, never
#        enforced. ------------------------------------------------------------
L="$WORK/unresolvable.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_RDL "2026-09-03T10:00:00Z" 0 "$FIXTURE_SHA"
entry "$L" QF_RDL "2026-09-04T10:00:00Z" 0 "$B"
case_ unresolvable-is-advisory "$L" "$REPO" 0 "verdict=PASS" \
  "|unresolvable_pairs=1" "some rows unresolvable"

# --- 10. NO GIT IS ADVISORY: pointed at a directory that is not a checkout,
#         the gate reports and passes rather than failing on a probe. -------
NOGIT="$WORK/nogit"; mkdir -p "$NOGIT"
L="$WORK/nogit.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_RDL "2026-09-03T10:00:00Z" 0 "$D"
entry "$L" QF_RDL "2026-09-04T10:00:00Z" 0 "$B"
case_ no-git-is-advisory "$L" "$NOGIT" 0 "verdict=PASS" "NO GIT" "|no_git_pairs=1"

# --- 11. OUT-OF-ORDER TIMESTAMP: file order and timestamp order disagree
#         because two sweeps overlapped. Advisory note, still PASS. --------
L="$WORK/tsorder.md"; ledger_header "$L"; pad "$L" "$A"
entry "$L" QF_IDL "2026-09-05T10:00:00Z" 0 "$B"
entry "$L" QF_IDL "2026-09-04T10:00:00Z" 0 "$C"
case_ out-of-order-timestamp "$L" "$REPO" 0 "verdict=PASS" \
  "OUT-OF-ORDER-TIMESTAMP" "|out_of_order_timestamps=1"

# --- 12. UNKNOWN HEADER: a '## ' line this parser cannot classify would be
#         SKIPPED, and a skipped row is indistinguishable from an absent one.
#         Exit 2, never a green pass. ------------------------------------------
L="$WORK/unknown.md"; ledger_header "$L"; pad "$L" "$A"
printf '## Something Nobody Anticipated\n\n' >> "$L"
case_ unknown-header "$L" "$REPO" 2 "PARITY_ANCESTRY_ERROR" "unrecognised"

# --- 13. MALFORMED ENTRY: no disagreements row, so a voided entry cannot be
#         told from a valid one. Exit 2. -------------------------------------
L="$WORK/malformed.md"; ledger_header "$L"; pad "$L" "$A"
{
  echo "## QF_NRA — 2026-09-04T10:00:00Z"
  echo
  echo "| field | value |"
  echo "|---|---|"
  echo "| axeyum solved | 100/200 |"
  echo
} >> "$L"
case_ malformed-entry "$L" "$REPO" 2 "PARITY_ANCESTRY_ERROR" "disagreements"

# --- 14. VACUOUS POPULATION: three logics is a broken parser or the wrong
#         file, and a near-empty read must not pass. Exit 2. ----------------
L="$WORK/tiny.md"; ledger_header "$L"
entry "$L" QF_BV "2026-09-04T10:00:00Z" 0 "$A"
entry "$L" UF "2026-09-04T10:00:00Z" 0 "$A"
entry "$L" QF_LIA "2026-09-04T10:00:00Z" 0 "$A"
case_ vacuous-population "$L" "$REPO" 2 "PARITY_ANCESTRY_ERROR" "vacuously"

# --- 15. THE REAL LEDGER: an empty answer from a parser that was never
#         pointed at its subject is indistinguishable from a strong negative,
#         so one case runs against the shipped file in this checkout. It
#         asserts COVERAGE (the real series count and the real second-
#         reference series), not a verdict. ---------------------------------
if [ -r "$REAL_LEDGER" ]; then
  out="$(python3 "$SCRIPT" --ledger "$REAL_LEDGER" --repo "$REAL_REPO" 2>&1)"
  got_rc=$?
  asserted=$((asserted + 1))
  n_series=$(printf '%s\n' "$out" | sed -n 's/.*|series=\([0-9]*\).*/\1/p')
  n_rows=$(printf '%s\n' "$out" | sed -n 's/.*|rows=\([0-9]*\).*/\1/p')
  hits=$(printf '%s\n' "$out" | grep -cF "[yices2]")
  if [ "${n_series:-0}" -lt 12 ] || [ "${n_rows:-0}" -lt 40 ] || [ "${hits:-0}" -eq 0 ]; then
    echo "FAIL case:real-ledger-coverage — parsed series=${n_series:-?} rows=${n_rows:-?} yices2-series=${hits:-0}; the shipped ledger carries at least twelve series, forty rows and a second-reference series, so this is a parser that stopped seeing its subject"
    fail=1
  elif [ "$got_rc" != 0 ] && [ "$got_rc" != 1 ]; then
    echo "FAIL case:real-ledger-coverage rc=$got_rc — expected a verdict (0 or 1), not a parse error"
    fail=1
  else
    echo "ok   case:real-ledger-coverage -> rc=$got_rc series=${n_series} rows=${n_rows}"
  fi
else
  echo "FAIL case:real-ledger-coverage — no ledger at $REAL_LEDGER"
  fail=1
fi

echo
echo "asserted ${asserted} case(s)"
if [ "$asserted" -lt 15 ]; then
  echo "FAIL: only ${asserted} case(s) ran; this suite has 15 and a suite that"
  echo "      silently runs fewer is a gate measuring the subset it accepted."
  fail=1
fi
if [ "$fail" != 0 ]; then
  echo "FAIL: check-parity-ancestry controls"
  exit 1
fi
echo "PASS: check-parity-ancestry controls"
