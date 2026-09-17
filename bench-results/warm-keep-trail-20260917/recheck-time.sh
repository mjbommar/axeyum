#!/usr/bin/env bash
# Re-run every TIME mover three times per arm on ONE pinned core pair at the
# same 24 s / 8 GiB envelope, recording verdict and wall per pass, arms
# alternating within the passes (ADR-2145; the shape of
# route-ownership-20260915/recheck-movers.sh with timings kept).
#
# Usage: recheck-time.sh <list> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -n "${AXEYUM_WARM_KEEP_TRAIL:-}" ] && { echo "ABORT: lever set in the launching shell"; exit 2; }

now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then echo "ABORT: clock self-check ${dt} ms"; exit 3; fi
echo "CLOCK-OK sleep200=${dt}ms"

one() {  # $1 = A|B
  local t0 t1 raw rc v
  t0=$(now_ms)
  if [ "$1" = "B" ]; then
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" env AXEYUM_WARM_KEEP_TRAIL=on \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" "$AX" "$f" 2>/dev/null)
  else
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" env -u AXEYUM_WARM_KEEP_TRAIL \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(now_ms)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s/%s' "${v:-none}" "$((t1 - t0))" "$rc"
}

printf 'file\tA1\tB1\tB2\tA2\tA3\tB3\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  f="$CORPUS$f"
  a1=$(one A); b1=$(one B)
  b2=$(one B); a2=$(one A)
  a3=$(one A); b3=$(one B)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a1" "$b1" "$b2" "$a2" "$a3" "$b3" >> "$OUT"
  echo "ROW ${f#"$CORPUS"} A=$a1,$a2,$a3 B=$b1,$b2,$b3"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
