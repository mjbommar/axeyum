#!/usr/bin/env bash
# Controls for `ab-summarize.py`: show each failing exit status FIRING.
#
# A checker that cannot fail is worse than no checker, and "the sweep was
# clean" and "the checker never looked" print the same thing. Each case below
# is a hand-built TSV that should trip exactly one guard.
#
# Usage: ab-summarize-controls.sh
set -u
LANE="$(cd "$(dirname "$0")" && pwd)"
SUM="$LANE/ab-summarize.py"
W="$(mktemp -d)"
trap 'rm -rf "$W"' EXIT
fail=0

hdr='file\taxeyum\taxeyum_s\taxeyum_k\taxeyumb\taxeyumb_s\taxeyumb_k\tstatus'

expect() { # $1 name  $2 want-exit  $3 file
  python3 "$SUM" "$3" > "$W/out" 2>&1
  got=$?
  if [ "$got" = "$2" ]; then
    echo "PASS $1 (exit $got)"
  else
    echo "FAIL $1: wanted exit $2, got $got"
    sed 's/^/    /' "$W/out"
    fail=1
  fi
}

# clean
printf "$hdr\n" > "$W/clean.tsv"
printf 'a.smt2\tunsat\t0.10\tok\tunsat\t0.10\tok\tunsat\n' >> "$W/clean.tsv"
expect clean 0 "$W/clean.tsv"

# a verdict contradicting the declared :status, in arm B
printf "$hdr\n" > "$W/wrong.tsv"
printf 'a.smt2\tunknown\t0.10\tok\tsat\t0.10\tok\tunsat\n' >> "$W/wrong.tsv"
expect wrong-status 3 "$W/wrong.tsv"

# the two arms decide in opposite directions on one file
printf "$hdr\n" > "$W/opp.tsv"
printf 'a.smt2\tsat\t0.10\tok\tunsat\t0.10\tok\tnone\n' >> "$W/opp.tsv"
expect arms-disagree 4 "$W/opp.tsv"

# an empty run is not a clean run
printf "$hdr\n" > "$W/empty.tsv"
expect empty-run 2 "$W/empty.tsv"

# a TSV with no `status` column cannot support the wrong-verdict check
printf 'file\taxeyum\taxeyumb\n' > "$W/nostatus.tsv"
printf 'a.smt2\tunsat\tunsat\n' >> "$W/nostatus.tsv"
expect missing-column 2 "$W/nostatus.tsv"

[ "$fail" = 0 ] && echo "ALL CONTROLS FIRED" || echo "CONTROLS FAILED"
exit "$fail"
