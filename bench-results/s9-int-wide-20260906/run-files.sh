#!/usr/bin/env bash
# Run one arm of the S9 measurement over a listing of benchmark files.
#
#   run-files.sh <binary> <listing.txt> <arm-label> <timeout-ms> <out.tsv>
#
# Emits one TSV row per file: arm, file, verdict, wall-clock ms, exit status.
# Pinned to the P-cores (`taskset -c 0-7`) because this box is hybrid and an
# unpinned run is ~1.8x slower on the E-cores; the timing ratchet's reference
# frame note (docs/research/08-planning/frontier-ratchet-reference-frame.md)
# applies here too.
#
# The exit status of the whole script is 0 only when every file produced a
# verdict line; a file whose worker printed nothing is reported as `no-output`
# and makes the script exit 1, so a broken arm cannot be read as "all unknown".
set -u

binary=$1
listing=$2
arm=$3
timeout_ms=$4
out=$5

timeout_s=$(( (timeout_ms + 5000) / 1000 ))
printf 'arm\tfile\tverdict\tms\tstatus\n' > "$out"

bad=0
while IFS= read -r path; do
  [ -n "$path" ] || continue
  start=$(date +%s%N)
  verdict=$(timeout "${timeout_s}" taskset -c 0-7 "$binary" "$path" --timeout-ms "$timeout_ms" 2>/dev/null | tail -1)
  rc=$?
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  case "$verdict" in
    sat|unsat|unknown) status=ok ;;
    "") verdict=no-output; status=no-output; bad=1 ;;
    *) status=unexpected; bad=1 ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s(rc=%s)\n' "$arm" "$path" "$verdict" "$ms" "$status" "$rc" >> "$out"
done < "$listing"

exit "$bad"
