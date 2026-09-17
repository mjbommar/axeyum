#!/usr/bin/env bash
# A13-LRA sizing: re-run the LRA-MODEL-REPLAY census's diagnostic on the 27
# "no tableau" files and the 11 "disequality" files, on ONE binary, ONE env,
# ONE pinned core, so each row says where the file stops NOW.
#
# The census (`bench-results/lra-model-replay-20260916/`) measured its 47-file
# population at `AXEYUM_LRA_ATOM_SCREEN=16`, because at the SHIPPED screen the
# 27 "no tableau" rows never reach the online engine at all (every one of them
# has more than the 1,024 atoms the screen admits). So this runs each file at
# BOTH screens: the shipped one says what the lever can touch today, the census
# one says whether the mechanism is still where the census left it.
#
# Timing is `$EPOCHREALTIME` (uutils `date` prints nanoseconds under `%3N` on
# s5/s7); a 200 ms sleep is self-checked before any solve.
#
# Usage: sizing-run.sh <list> <out.tsv> <cores> <bin> <tag> [env assignments...]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; TAG="$5"; shift 5
BUDGET=24; HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }
now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then echo "ABORT: clock read ${dt} ms for 200 ms"; exit 3; fi
echo "CLOCK-OK $TAG sleep200=${dt}ms env: $*  bin=$(sha256sum "$AX" | cut -d' ' -f1)"
mkdir -p "$(dirname "$OUT")/cap"
printf 'file\tverdict\trc\tms\tonline_probe\tprobe_sites\tequalities\teq_false\tdiseq_violated\tsplits\tsplit_conflicts\tsimplex_rows\tdiseq_splits_trace\tfill_cap_declines\tstatus\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  n=$((n + 1))
  f="$CORPUS$rel"
  slug=$(echo "$rel" | tr '/' '_')
  cap="$(dirname "$OUT")/cap/$TAG.$slug"
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  t0=$(now_ms)
  env "$@" AXEYUM_LRAMODELPROBE=1 taskset -c "$PIN" timeout -k 5 $((BUDGET + HEADROOM)) \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000)) --trace" \
    "$AX" "$f" > "$cap.out" 2> "$cap.err"
  rc=$?
  t1=$(now_ms)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' "$cap.out"); v=${v:-none}
  probe=$(grep -oE 'online_probe=[a-z_-]+' "$cap.err" | tail -1 | cut -d= -f2)
  sites=$(grep -oE 'LRAMODELPROBE site=[a-z0-9:_-]+' "$cap.err" | cut -d= -f2 | sort | uniq -c | awk '{printf "%s=%s;", $2, $1}')
  eqline=$(grep -m1 'LRAMODELPROBE equalities=' "$cap.err")
  eqs=$(echo "$eqline" | grep -oE 'equalities=[0-9]+' | cut -d= -f2)
  eqf=$(echo "$eqline" | grep -oE 'eq_asserted_false=[0-9]+' | cut -d= -f2)
  dv=$(echo "$eqline" | grep -oE 'diseq_violated_at_point=[0-9]+' | cut -d= -f2)
  sp=$(echo "$eqline" | grep -oE ' splits=[0-9]+' | cut -d= -f2)
  spc=$(echo "$eqline" | grep -oE 'split_conflicts=[0-9]+' | cut -d= -f2)
  rows=$(grep -oE 'simplex_rows=[0-9a-z/]+' "$cap.err" | tail -1 | cut -d= -f2)
  dst=$(grep -oE 'diseq_splits=[0-9a-z/]+' "$cap.err" | tail -1 | cut -d= -f2)
  fcd=$(grep -oE 'fill_cap_declines=[0-9a-z/]+' "$cap.err" | tail -1 | cut -d= -f2)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$v" "$rc" "$((t1 - t0))" "${probe:-n/a}" "${sites:-none}" "${eqs:-n/a}" "${eqf:-n/a}" "${dv:-n/a}" "${sp:-n/a}" "${spc:-n/a}" "${rows:-n/a}" "${dst:-n/a}" "${fcd:-n/a}" "${st:-none}" >> "$OUT"
  echo "[$TAG $n] $v rc=$rc probe=${probe:-n/a} sites=${sites:-none} eqf=${eqf:-n/a} $rel"
done < "$LIST"
echo "SIZING-DONE $TAG $n files -> $OUT"
