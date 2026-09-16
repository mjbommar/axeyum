#!/usr/bin/env bash
# QUANT-INSTANCE-PROBE step 4 continued: build the ground-only file from OUR
# OWN admitted instance dump (qip-dump-admitted.sh's *.lastblock files).
#
#   qip-build-admitground.sh <cores.list> <dumpdir> <outdir> <repo>
set -u
LIST="$1"; DUMPDIR="$2"; OUTDIR="$3"; REPO="$4"
mkdir -p "$OUTDIR"
SUMMARY="$OUTDIR/build-summary.tsv"
printf 'core\tbuild_rc\tquant_stripped\tground_kept\tadmitted_instances_added\n' > "$SUMMARY"

py() { bash -c "ulimit -v 16000000; exec python3 \"\$0\" \"\$@\"" "$@"; }

while IFS= read -r p; do
  [ -n "$p" ] || continue
  b="$(basename "$p")"
  lb="$DUMPDIR/inst/$b.lastblock"
  out="$OUTDIR/$b.ground.smt2"
  if [ ! -s "$lb" ]; then
    printf '%s\tNO-DUMP\t0\t0\t0\n' "$b" >> "$SUMMARY"
    continue
  fi
  build_out=$(py "$REPO/bench-results/quant-instance-probe-20260916/build-ground-from-dump.py" \
      "$p" "$lb" "$out" 2>&1)
  build_rc=$?
  if [ "$build_rc" -ne 0 ]; then
    printf '%s\t%s\t0\t0\t0\n' "$b" "BUILD-FAIL-$build_rc" >> "$SUMMARY"
    continue
  fi
  qs=$(printf '%s\n' "$build_out" | grep -oE 'quant_stripped=[0-9]+' | grep -oE '[0-9]+')
  gk=$(printf '%s\n' "$build_out" | grep -oE 'ground_kept=[0-9]+' | grep -oE '[0-9]+')
  ia=$(printf '%s\n' "$build_out" | grep -oE 'admitted_instances_added=[0-9]+' | grep -oE '[0-9]+')
  printf '%s\t0\t%s\t%s\t%s\n' "$b" "$qs" "$gk" "$ia" >> "$SUMMARY"
done < "$LIST"
echo "DONE $SUMMARY"
