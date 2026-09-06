#!/usr/bin/env bash
# Interleaved before/after measurement for the S9 lane.
#
#   run-before-after.sh <before-binary> <after-binary> <listing.txt> <timeout-ms> <out.tsv>
#
# The two arms alternate PER FILE rather than running one arm to completion, so
# a load change part-way through the session hits both arms equally instead of
# landing entirely on whichever ran second. Pinned to `taskset -c 0-7` (the
# P-cores on this hybrid box) for the same reason the frontier ratchet is.
#
# One TSV row per (file, arm): verdict, wall-clock ms, and the exit status. The
# script exits non-zero if any run produced no verdict line, so a broken arm
# cannot read as "all unknown".
set -u

before=$1
after=$2
listing=$3
timeout_ms=$4
out=$5

timeout_s=$(( (timeout_ms + 5000) / 1000 ))
printf 'file\tarm\tverdict\tms\tstatus\n' > "$out"

bad=0
run_one() {
  # $1 = binary, $2 = arm label, $3 = file
  local start end ms verdict rc status
  start=$(date +%s%N)
  verdict=$(timeout "${timeout_s}" taskset -c 0-7 "$1" "$3" --timeout-ms "$timeout_ms" 2>/dev/null | tail -1)
  rc=$?
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  case "$verdict" in
    sat|unsat|unknown) status=ok ;;
    "") verdict=no-output; status=no-output; bad=1 ;;
    *) verdict=unexpected; status=unexpected; bad=1 ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s(rc=%s)\n' "$3" "$2" "$verdict" "$ms" "$status" "$rc" >> "$out"
}

while IFS= read -r path; do
  [ -n "$path" ] || continue
  run_one "$before" before "$path"
  run_one "$after" after "$path"
done < "$listing"

exit "$bad"
