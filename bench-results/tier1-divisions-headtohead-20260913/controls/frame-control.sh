#!/usr/bin/env bash
# `frame-summary.py` prints FRAME OK over the real run, and its FRAME VIOLATED
# branch is unreachable on any run that gets published -- which makes the OK
# unfalsifiable in practice unless something forces the other branch.  This does.
#
# Four fixtures with known answers, in both directions, plus the two cases that
# are neither: an absent loadframe and an empty one.  An absent instrument and a
# clean frame are different findings and must not print the same thing.
set -u
cd "$(dirname "$0")"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
H='ts\thost\tload1\tforeign_pins\tforeign_cores\toverlap\n'

mk() { printf "$H%b" "$2" > "$T/$1"; }
run() { python3 ../frame-summary.py "$T/$1" 2>&1; }
check() { # file expected-rc must-contain
  local out rc
  out=$(run "$1"); rc=$?
  [ "$rc" = "$2" ] || { echo "FAIL: $1 -> rc=$rc expected $2"; fail=1; }
  grep -q "$3" <<<"$out" || { echo "FAIL: $1 -> missing '$3'"; fail=1; }
}

# CLEAN: foreign pins on cores 0, 2, 4; this board uses 1, 3, 5, 6, 7.
mk clean.tsv '07:00:00\ts5\t4.0\t3\t0;2;4\tok\n07:00:30\ts6\t4.0\t3\t0;2;4\tok\n'
check clean.tsv 0 "FRAME OK"

# VIOLATED: a foreign pin on logical 5 -- a core this board uses.
mk v5.tsv '07:00:00\ts5\t4.0\t4\t0;2;4;5\tok\n'
check v5.tsv 1 "FRAME VIOLATED"

# VIOLATED through an SMT SIBLING: logical 11 is physical core 3, which this
# board uses as 3,11.  A check that compared logical numbers would miss this.
mk v11.tsv '07:00:00\ts5\t4.0\t4\t0;2;4;11\tok\n'
check v11.tsv 1 "core 3"

# VIOLATED through a RANGE: `0-7` covers this board's cores and cannot be tested
# by membership, so it must be flagged rather than read as clear.
mk vr.tsv '07:00:00\ts5\t4.0\t2\t0-7;2\tok\n'
check vr.tsv 1 "RANGE"

# THIS LANE'S OWN specs must NOT count as foreign.  After the re-balance they
# appear in `foreign_cores`, and a check that did not subtract them would report
# the board colliding with itself on every single sample.
mk mine.tsv '07:00:00\ts5\t4.0\t5\t0;1,9;2;4;7,15\tok\n'
check mine.tsv 0 "FRAME OK"

# NEITHER: an instrument that did not run, and one that ran and saw nothing.
# Both must be distinguishable from a clean frame.
check absent.tsv 1 "DID NOT RUN"
mk empty.tsv ''
check empty.tsv 1 "RECORDED NOTHING"

[ "$fail" = 0 ] && echo "FRAME-CONTROL-OK: 2 clean, 3 violations (incl. SMT sibling and range), 2 absent/empty"
exit "$fail"
