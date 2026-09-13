#!/usr/bin/env bash
# The NOISE FLOOR: one whole division, the BASE arm only, run start to finish.
# Repeat it and the peak-to-trough band of the division total is the band inside
# which an A/B's net is not a result.
#
# Same binary, same envelope, same cores as `ab-run.sh`, and the SAME `env -u`
# base arm -- an environment with no lever in it. The only difference from the
# A/B is that the second arm is not run, so a shard costs about half as much.
#
# It is measured, not assumed, because the previous lane's own artifact shows the
# band is larger than the effect it was sizing: `UFLIA` reads 73 in that lane's
# A/B base arm and 76 in its single-arm census sweep, AT THE SAME COMMIT ON THESE
# BOXES.
#
# Usage: noise-run.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tbase\tbase_ms\tbase_rc\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  t0=$(date +%s%N)
  raw=$(env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "NOISE-DONE $TAG $n files -> $OUT"
