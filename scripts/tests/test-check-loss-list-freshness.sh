#!/usr/bin/env bash
# Controls for `scripts/check-loss-list-freshness.py`: run the REAL script
# against fabricated `bench-results/parity-losses-*` trees, one scenario at a
# time, and assert both the exit code and the machine-readable line it printed.
#
# Per CLAUDE.md: "a checker that cannot fail is worse than no checker", and a
# gate that has never been SHOWN to fire is the defect this repository keeps
# rediscovering. Most cases below are trees the gate must REJECT; the accepting
# cases exist to prove the rejections are not vacuous -- a script that exited 1
# unconditionally would pass every rejection case and is killed by `clean`,
# `warn-band`, `partial-supersession-marked` and `real-tree`.
#
# MUTATION-VERIFIED, not asserted by comment. Every guard in the checker was
# broken one at a time by `scripts/tests/loss_list_freshness_mutations.py` and
# the cases that died RECORDED FROM THAT RUN, not predicted (2026-09-08, this
# suite at 15 cases, 12 mutations, 12 killed):
#
#   mutation                                          cases killed
#   per-division authority collapsed to               addition-is-not-supersession,
#     "the newest set wins"                           partial-supersession-marked
#   the `SUPERSEDED-BY:` requirement removed          unsuperseded
#   the SUPERSEDED-BY target check removed            misdirected-supersession
#   the self-naming SUPERSEDED-BY check removed       self-supersession
#   `if age > max_days` removed                       stale-division
#   `if warn_days < age <= max_days` collapsed        warn-band
#   REQUIRED_MANIFEST_FIELDS emptied                  missing-field, bare-unrecorded
#   the `no MANIFEST.json` branch removed             no-manifest
#   UNRECORDED_RE always matches                      bare-unrecorded
#   MIN_SETS = 0                                      vacuous-population
#   solver currency made FATAL                        clean, warn-band,
#                                                     currency-is-advisory,
#                                                     addition-is-not-supersession,
#                                                     partial-supersession-marked,
#                                                     helper-txt-is-not-a-division,
#                                                     real-tree
#   DIVISION_RE relaxed to `.*`                       helper-txt-is-not-a-division
#
# Nine of the twelve kill exactly one case. The three that kill more do so for
# reasons worth stating rather than tidying away:
#
#   * Collapsing per-division authority kills two because that IS the checker's
#     central model. `addition-is-not-supersession` is the guard;
#     `partial-supersession-marked` is the shape it produces.
#   * Emptying REQUIRED_MANIFEST_FIELDS kills two because both manifest-content
#     cases read that list. The `no MANIFEST.json` branch returns before it and
#     therefore dies alone, which is the check that the two are independent.
#   * Making solver currency FATAL kills seven, which is the point: the
#     checker's header argues currency must stay advisory (bursty velocity, and
#     lanes legitimately measuring from their own worktrees), and
#     `currency-is-advisory` exists so that decision has a control of its own
#     rather than being an emergent property of the others.
#
# WHAT CHANGED WHEN THE TREE DID, and it is worth writing down. On the FIRST run
# of this table the tree held two loss-list sets, one of them a QF_NRA-only
# addition with no supersession banner, and `real-tree` died under BOTH the
# authority-collapse and the DIVISION_RE mutations. After the 2026-09-08 re-cut
# landed -- a third set that is the authority for every division, with both
# older sets marked -- neither mutation moves it any more: with one set on top
# of everything, "newest set wins" and "newest set per division" agree.
#
# So `real-tree` is COVERAGE, not a guard, and its sensitivity is a property of
# the tree rather than of the checker. It stays because a fixture-only suite
# would remain green if the shipped directories' shape drifted away from what
# the parser reads; it must not be counted as evidence that either of those two
# guards is tested. Their fixtures are.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

SCRIPT="$PWD/scripts/check-loss-list-freshness.py"
[ -r "$SCRIPT" ] || { echo "FAIL: cannot read $SCRIPT"; exit 1; }
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
fail=0
asserted=0

NOW="2026-09-08T12:00:00Z"
# Valid-looking but deliberately NOT a real object, so the currency probe has a
# defined answer ("unresolvable") in fixtures rather than accidentally
# resolving against this checkout's history.
FIXTURE_SHA="deadbee1234"

# mkset <root> <dirname> <as_of-iso> <div…>
# Builds a well-formed set: a MANIFEST.json with every required field and one
# non-empty list per division.
mkset() {
  local root="$1" name="$2" as_of="$3"; shift 3
  local d="$root/bench-results/$name"
  mkdir -p "$d"
  local divs="" first=1 lg
  for lg in "$@"; do
    echo "/corpus/$lg/a.smt2" > "$d/$lg.txt"
    if [ "$first" = 1 ]; then divs="\"$lg\""; first=0; else divs="$divs, \"$lg\""; fi
  done
  cat > "$d/MANIFEST.json" <<JSON
{
  "as_of": "$as_of",
  "solver_commit": "$FIXTURE_SHA",
  "binary_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
  "budget_s": 24,
  "divisions": [$divs]
}
JSON
  printf '# %s\n\nfixture\n' "$name" > "$d/README.md"
}

supersede() { printf 'SUPERSEDED-BY: %s\n' "$2" >> "$1/README.md"; }

# case <name> <root> <want-rc> <want-substring…>
case_() {
  local name="$1" root="$2" want_rc="$3"; shift 3
  local out got_rc pat hits
  out="$(python3 "$SCRIPT" --root "$root" --now "$NOW" 2>&1)"
  got_rc=$?
  asserted=$((asserted + 1))
  if [ "$got_rc" != "$want_rc" ]; then
    echo "FAIL case:$name rc=$got_rc (want $want_rc) — $(printf '%s' "$out" | tr '\n' '|')"
    fail=1; return
  fi
  for pat in "$@"; do
    # `grep -c`, never `grep -q`: under `set -o pipefail` a `-q` consumer exits
    # at the first match, SIGPIPEs the producer, and the pipeline status 141
    # reads as "not found".
    hits=$(printf '%s\n' "$out" | grep -cF "$pat")
    if [ "${hits:-0}" -eq 0 ]; then
      echo "FAIL case:$name rc ok but missing '$pat' — $(printf '%s' "$out" | tr '\n' '|')"
      fail=1; return
    fi
  done
  echo "ok   case:$name"
}

# ---------------------------------------------------------------- accepting --

R="$WORK/clean"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV QF_BV
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV QF_BV
supersede "$R/bench-results/parity-losses-20260905" parity-losses-20260908
case_ clean "$R" 0 "|problems=0" "|sets=2" "|divisions=2"

# A set that ADDS a division is not a supersession of the sets before it. This
# is the case the first version of this gate got wrong on its very first run:
# `parity-losses-20260906` is a QF_NRA-only census beside an eleven-division
# set, and a per-SET rule demanded the eleven declare themselves replaced by a
# sweep that never measured them.
R="$WORK/addition"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV QF_BV
mkset "$R" parity-losses-20260906 "2026-09-06T00:00:00Z" QF_NRA
case_ addition-is-not-supersession "$R" 0 "|problems=0" "|divisions=3"

# Partly superseded: one division re-cut, one still authoritative. The marker is
# required, and once present the set is clean even though it is still the
# authority for a division.
R="$WORK/partial"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV QF_BV
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
supersede "$R/bench-results/parity-losses-20260905" parity-losses-20260908
case_ partial-supersession-marked "$R" 0 "|problems=0" "authority for: QF_BV"

# Currency is ADVISORY: a solver commit the checker cannot check is REPORTED
# and does not change the exit status. The fixture root is a bare directory, so
# the probe's answer here is "no git checkout"; `real-tree` below exercises the
# resolvable path against this repository. Both must stay non-fatal, which is
# what the "currency made FATAL" mutation kills.
R="$WORK/currency"
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
case_ currency-is-advisory "$R" 0 "|problems=0" "(no git checkout here)"

# A `.txt` beside the lists is not a population. `abv-watchdog-blind.txt` and
# `UF.axeyum-only24.ab.txt` both live in committed sets; counting either as a
# division would invent a population nobody measured.
R="$WORK/helper"
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
echo "/corpus/x.smt2" > "$R/bench-results/parity-losses-20260908/abv-watchdog-blind.txt"
case_ helper-txt-is-not-a-division "$R" 0 "|divisions=1"

# ---------------------------------------------------------------- rejecting --

R="$WORK/unsuperseded"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
case_ unsuperseded "$R" 1 "no \`SUPERSEDED-BY:\` line"

R="$WORK/misdirected"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
supersede "$R/bench-results/parity-losses-20260905" parity-losses-20261231
case_ misdirected-supersession "$R" 1 "is not a loss-list set in this checkout"

R="$WORK/self"
mkset "$R" parity-losses-20260905 "2026-09-05T00:00:00Z" QF_ABV
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
supersede "$R/bench-results/parity-losses-20260905" parity-losses-20260905
case_ self-supersession "$R" 1 "SUPERSEDED-BY names itself"

R="$WORK/stale"
mkset "$R" parity-losses-20260801 "2026-08-01T00:00:00Z" QF_ABV
case_ stale-division "$R" 1 "past the 14-day budget"

R="$WORK/warn"
mkset "$R" parity-losses-20260827 "2026-08-27T00:00:00Z" QF_ABV
case_ warn-band "$R" 0 "WARN-AGE" "|problems=0"

R="$WORK/nomanifest"
mkdir -p "$R/bench-results/parity-losses-20260908"
echo "/corpus/a.smt2" > "$R/bench-results/parity-losses-20260908/QF_ABV.txt"
case_ no-manifest "$R" 1 "no MANIFEST.json"

R="$WORK/missingfield"
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
python3 - "$R/bench-results/parity-losses-20260908/MANIFEST.json" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d.pop("solver_commit")
json.dump(d, open(p, "w"))
PY
case_ missing-field "$R" 1 "MANIFEST.json missing solver_commit"

# `unrecorded` is accepted only WITH a reason. An absent field and an
# unknowable one are different findings; a gate that cannot tell them apart
# teaches lanes to invent a value.
R="$WORK/bareunrecorded"
mkset "$R" parity-losses-20260908 "2026-09-08T00:00:00Z" QF_ABV
python3 - "$R/bench-results/parity-losses-20260908/MANIFEST.json" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d["binary_sha256"] = "unrecorded"
json.dump(d, open(p, "w"))
PY
case_ bare-unrecorded "$R" 1 "with no reason"

# An empty tree is a FAILURE, not a pass: a scan that stopped matching its
# subject returns the same answer as a clean repository.
R="$WORK/empty"
mkdir -p "$R/bench-results"
case_ vacuous-population "$R" 1 "found NO"

# ------------------------------------------------------------- coverage ------
# Fixtures cannot notice the shipped tree drifting away from what the checker
# parses. This case points the real script at the real repository: it is
# COVERAGE, not a guard, and it is supposed to die whenever the parser stops
# seeing its subject.
case_ real-tree "$PWD" 0 "|problems=0" "cite these, per division:"

echo
if [ "$asserted" -lt 13 ]; then
  echo "FAIL: only $asserted cases ran; this suite asserts at least 13"
  exit 1
fi
if [ "$fail" != 0 ]; then
  echo "FAIL: loss-list freshness controls"
  exit 1
fi
echo "PASS: loss-list freshness controls ($asserted cases)"
