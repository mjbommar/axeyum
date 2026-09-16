#!/usr/bin/env bash
# QUANT-INSTANCE-PROBE steps 1+2: for every core already extracted by
# qip-extract.sh (proof + inst/*.json present), build the ground-only file
# and confirm with plain z3 whether it is unsat.
#
#   qip-build-ground.sh <cores.list> <extractdir> <grounddir> <pin> <repo> [budget_s]
set -u
LIST="$1"; EXTRACTDIR="$2"; GROUNDDIR="$3"; PIN="$4"; REPO="$5"; BUDGET="${6:-60}"
mkdir -p "$GROUNDDIR"
SUMMARY="$GROUNDDIR/build-summary.tsv"
printf 'core\tbuild_rc\tquant_stripped\tground_kept\tinstances_added\tnot_ground_dropped\tunmatched\tz3_ground_verdict\n' > "$SUMMARY"

py() { bash -c "ulimit -v 16000000; exec python3 \"\$0\" \"\$@\"" "$@"; }

while IFS= read -r p; do
  [ -n "$p" ] || continue
  b="$(basename "$p")"
  json="$EXTRACTDIR/inst/$b.json"
  out="$GROUNDDIR/$b.ground.smt2"
  if [ ! -f "$json" ]; then
    printf '%s\tNO-JSON\t0\t0\t0\t0\t0\tNA\n' "$b" >> "$SUMMARY"
    continue
  fi
  build_out=$(py "$REPO/bench-results/quant-instance-probe-20260916/build-ground-only.py" \
      "$p" "$json" "$out" 2>&1)
  build_rc=$?
  if [ "$build_rc" -ne 0 ]; then
    printf '%s\t%s\t0\t0\t0\t0\t0\tNA\n' "$b" "BUILD-FAIL-$build_rc" >> "$SUMMARY"
    continue
  fi
  qs=$(printf '%s\n' "$build_out" | grep -oE 'quant_stripped=[0-9]+' | grep -oE '[0-9]+')
  gk=$(printf '%s\n' "$build_out" | grep -oE 'ground_kept=[0-9]+' | grep -oE '[0-9]+')
  ia=$(printf '%s\n' "$build_out" | grep -oE 'instances_added=[0-9]+' | grep -oE '[0-9]+')
  ng=$(printf '%s\n' "$build_out" | grep -oE 'not_ground_dropped=[0-9]+' | grep -oE '[0-9]+')
  um=$(printf '%s\n' "$build_out" | grep -oE 'unmatched=[0-9]+' | grep -oE '[0-9]+')

  a=$(taskset -c "$PIN" timeout $((BUDGET + 20)) z3 -T:$BUDGET "$out" 2>&1)
  v=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || true)

  printf '%s\t0\t%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$qs" "$gk" "$ia" "$ng" "$um" "${v:-NOVERDICT}" >> "$SUMMARY"
done < "$LIST"
echo "DONE $SUMMARY"
