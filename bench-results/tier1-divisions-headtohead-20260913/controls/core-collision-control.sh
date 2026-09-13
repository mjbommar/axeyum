#!/usr/bin/env bash
# `check-core-collisions.sh` printed NO-CORE-COLLISIONS on its very first run,
# over the live fleet, which is exactly the shape of a check that cannot fail.
# This is the measurement that says it can.
#
# The awk program is EXTRACTED from the shipped script between its
# `collision-awk` markers, not re-typed, so a mutation of the shipped logic
# changes what this suite runs.
#
# Fixtures are `uniq -c`-shaped: "<count> <pin spec>", which is what the
# `ps | grep | sort | uniq -c` pipeline in the subject produces.
set -u
cd "$(dirname "$0")"
SUB=../check-core-collisions.sh

# The subject must PARSE.  Extracting a program from a script and running it
# says nothing about whether the script itself still works: an apostrophe added
# to a comment inside the single-quoted AWKPROG ended the string and broke the
# whole file, and this suite passed anyway because it never ran the subject.
bash -n "$SUB" || { echo "FAIL: $SUB does not parse"; exit 1; }

PROG=$(sed -n "/>>> collision-awk/,/<<< collision-awk/p" "$SUB" \
       | sed -n "/^AWKPROG='/,/'\$/p" | sed "1s/^AWKPROG='//" | sed "\$s/'\$//")
[ -n "$PROG" ] || { echo "FAIL: could not extract AWKPROG"; exit 1; }
printf '%s' "$PROG" | grep -q 'PHYSICAL CORE' \
  || { echo "FAIL: the extracted program has no report statement"; exit 1; }

fail=0
run() { printf '%s\n' "$1" | awk -v host=h "$PROG"; }
expect() { # label input expected-rc expected-substring-or-empty
  local out rc
  out=$(run "$2"); rc=$?
  if [ "$rc" != "$3" ]; then
    echo "FAIL: $1 -> rc=$rc, expected $3   (out: $out)"; fail=1; return
  fi
  if [ -n "$4" ] && ! grep -q "$4" <<<"$out"; then
    echo "FAIL: $1 -> did not report '$4'   (out: $out)"; fail=1
  fi
  if [ -z "$4" ] && [ -n "$out" ]; then
    echo "FAIL: $1 -> reported something on a clean fixture: $out"; fail=1
  fi
}

# MUST FIRE ------------------------------------------------------------------
# The exact mistake this lane made: a foreign lane on logical 0 and 2 while the
# board holds 0,8 and 2,10.  Physical cores 0 and 2 are each held twice.
expect "board 0,8 + 2,10 against a lane on 0 and 2" \
"      2 0,8
      1 0
      2 2,10
      1 2" 1 "PHYSICAL CORE 0"
# SMT siblings are ONE core: 5 and 13 collide.
expect "SMT siblings 5 and 13" \
"      1 5
      1 13" 1 "PHYSICAL CORE 5"
# The self-collision: a census shard on 1,9 and a board shard on 1,9 are two
# DIFFERENT jobs on one core, and they share a spec -- so this fixture is the
# one case a naive "distinct specs" rule misses.  It is listed here as a KNOWN
# LIMITATION rather than a passing case: see the CANNOT DETECT block below.
expect "board on 3,11 and a census on 11,3" \
"      1 3,11
      1 11,3" 1 "PHYSICAL CORE 3"

# MUST STAY SILENT -----------------------------------------------------------
# Distinct physical cores.  A checker that flagged these would be worthless.
expect "5,13 and 6,14 -- adjacent but distinct cores" \
"      2 5,13
      2 6,14" 0 ""
# The protocol itself: THREE processes on one spec are one shard's three
# solvers running in sequence.  Flagging this would flag every healthy run.
expect "three solvers on one shard's pin" \
"      3 5,13" 0 ""
expect "a whole box, one spec per core" \
"      1 0
      1 1
      1 2
      1 3
      1 4
      1 5
      1 6
      1 7" 0 ""

# CANNOT DETECT, stated rather than hidden -----------------------------------
# Two jobs pinned to the IDENTICAL spec are indistinguishable from one job's
# sequential solvers in `uniq -c` output, so this check cannot see that case.
# That is the FP-on-the-census collision, and it is why `launch-shard.sh` and
# `census-launch.sh` refuse to write a non-empty output file instead of relying
# on this script.  Asserted here so the gap is a recorded fact, not an
# assumption a later reader has to re-derive.
out=$(run "      2 1,9")
[ -z "$out" ] || { echo "FAIL: the stated blind spot is not actually blind"; fail=1; }

# The SUBJECT, end to end, against a fleet with nothing pinned.  A host with no
# pinned job contributes no evidence, and naming it in the clean line would let
# an idle -- or unreachable -- fleet report the same green as one that was
# checked and found clean.  `_nohost_` cannot resolve, so every host is silent.
out=$(bash "$SUB" _nohost_ 2>&1); rc=$?
if [ "$rc" != 2 ]; then
  echo "FAIL: a fleet with NOTHING pinned did not exit 2 (got $rc)"; fail=1
fi
grep -q "not a clean result, it is no result" <<<"$out" \
  || { echo "FAIL: an unexaminable fleet did not say so"; fail=1; }

[ "$fail" = 0 ] && echo "CORE-COLLISION-OK: fires on 3 collisions, silent on 3 clean layouts, blind spot confirmed, empty fleet refused"
exit "$fail"
