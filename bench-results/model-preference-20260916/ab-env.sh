#!/usr/bin/env bash
# Interleaved per-file A/B of ONE BINARY under TWO ENVIRONMENT VALUES (ADR-2140).
#
#   A = the variable UNSET  (ModelPreference::Any, the shipped search)
#   B = AXEYUM_MODEL_PREFERENCE=<value>  (default `zero`)
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, arm order
# alternating per file, so ambient load cancels in the difference rather than
# landing on whichever arm ran second (bench-results/route-ownership-20260915/
# ab-run.sh established the shape; this is that script with the two-binary
# check replaced by a one-binary/two-env contract, and `date` replaced).
#
# TIMING IS `$EPOCHREALTIME`, NEVER `date`: s5 and s7 run uutils coreutils,
# whose `date +%s%3N` prints NANOSECONDS, and a 200 ms sleep is timed before the
# first solve and must read 150-400 ms or the run aborts (exit 3).
#
# EXIT STATUS is recorded per arm as its own column: ADR-2045 measured
# `losses=0` by verdict and five new ABORTS underneath it.
#
# Envelope: 24 s wall, 8 GiB `ulimit -v`, one pinned physical core pair.
#
# Usage: ab-env.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s] [value] [extra B env]
#   extra B env: further `VAR=value` words applied to arm B only, e.g.
#   `AXEYUM_MODEL_PREFERENCE_PHASE=off` for ADR-2140's shrink-only arm.
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"; VALUE="${7:-zero}"; B_EXTRA="${8:-}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -n "${AXEYUM_MODEL_PREFERENCE:-}" ] && {
  echo "ABORT $TAG: AXEYUM_MODEL_PREFERENCE is set in the launching shell; arm A would not be the default"
  exit 2
}

now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }

# Clock self-check: a 200 ms sleep must read 150-400 ms.
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then
  echo "ABORT $TAG: clock self-check read ${dt} ms for a 200 ms sleep"; exit 3
fi
echo "CLOCK-OK $TAG sleep200=${dt}ms"

run_arm() {  # $1 = "A" or "B"
  local t0 t1 raw rc v
  t0=$(now_ms)
  if [ "$1" = "B" ]; then
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env AXEYUM_MODEL_PREFERENCE="$VALUE" $B_EXTRA \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env -u AXEYUM_MODEL_PREFERENCE \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(now_ms)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$((t1 - t0))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm A); b=$(run_arm B)
  else
    first=B; b=$(run_arm B); a=$(run_arm A)
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  bin=$(sha256sum "$AX" | cut -d' ' -f1) B=AXEYUM_MODEL_PREFERENCE=$VALUE $B_EXTRA"
