#!/usr/bin/env bash
# Live probe: BOTH ARMS on one file that the lane's own change is supposed to
# move, plus one control file, with the exact flags and envelope the A/B uses.
#
# A missing binary and a hard division produce the identical empty TSV, and a
# lever whose polarity was copied wrong produces an A/B in which both arms are
# the shipped one. This refuses to pass unless the two arms actually DIFFER on
# at least one probe file -- which is the only observation that distinguishes
# "the lever works" from "the lever is being ignored".
#
# Usage: probe.sh [bin] [cores]
set -u
BIN="${1:-/nas3/data/axeyum/harness/dt-exactness/bin/smtcomp_cli-ab}"
PIN="${2:-1,9}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
HERE="$(cd "$(dirname "$0")" && pwd)"
[ -x "$BIN" ] || { echo "PROBE-FAILED: $BIN missing"; exit 2; }

run() {  # $1 = base|arm  $2 = file
  local raw
  if [ "$1" = base ]; then
    raw=$(AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate timeout 40 taskset -c "$PIN" \
            bash -c "ulimit -v 8388608; exec \"\$0\" \"\$1\" --timeout-ms 24000" \
            "$BIN" "$2" 2>/dev/null)
  else
    raw=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL timeout 40 taskset -c "$PIN" \
            bash -c "ulimit -v 8388608; exec \"\$0\" \"\$1\" --timeout-ms 24000" \
            "$BIN" "$2" 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'
}

differed=0
seen=0
for div in UFDTLIRA UFDT AUFDTLIRA UF; do
  list="$HERE/../parity-lists/$div.txt"
  [ -f "$list" ] || { echo "PROBE $div: no pinned list"; continue; }
  n=0
  while read -r f; do
    [ -n "$f" ] || continue
    n=$((n + 1))
    [ "$n" -gt 12 ] && break
    b=$(run base "$f"); a=$(run arm "$f")
    seen=$((seen + 1))
    mark=""
    if [ "${b:-none}" != "${a:-none}" ]; then mark="  <-- ARMS DIFFER"; differed=$((differed + 1)); fi
    echo "PROBE $div base=${b:-none} arm=${a:-none} ${f#"$CORPUS"}$mark"
  done < "$list"
done

echo "PROBE seen=$seen arms_differed_on=$differed"
[ "$seen" -ge 4 ] || { echo "PROBE-FAILED: too few files probed"; exit 1; }
[ "$differed" -ge 1 ] || {
  echo "PROBE-FAILED: the two arms agreed on every probe file. Either the lever"
  echo "  is not reaching the binary (check AXEYUM_DATATYPE_NATIVE_REFUSAL spelling)"
  echo "  or this prefix of the list cannot exercise the change. A prefix of a"
  echo "  path-sorted list is not a sample -- widen it before concluding zero."
  exit 1
}
echo "PROBE-OK"
