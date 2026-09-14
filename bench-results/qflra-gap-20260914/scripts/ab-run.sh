#!/usr/bin/env bash
# QFLRA-GAP interleaved per-file A/B.
#
# POLARITY, stated here so no reader has to infer it from a column name:
#
#   BASE  = `AXEYUM_MEMORY_LIMIT_MB` UNSET.  This is EXACTLY the board's
#           configuration: the harness bounds memory with `ulimit -v 8G`, which
#           the solver cannot see, so `memory_budget::current_limit_bytes()`
#           returns `None` and every memory admission screen in the solver
#           (`lra::fm_admission`, `lra::simplex_admission`,
#           `MemoryBudget::clause_ceiling`, the resident-set watchdog) is inert.
#
#   ARM   = `AXEYUM_MEMORY_LIMIT_MB=8192`.  The solver is TOLD the limit the
#           harness is already enforcing on it.  Nothing else differs.
#
# A GAIN is therefore "the arm decided a file the base did not", and the arm is
# the one with the limit SET.
#
# ONE BINARY, two env values -- never two builds.  Both arms run back to back on
# the SAME file on the SAME pinned core, order alternating per file, so ambient
# load cancels in the DIFFERENCE.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> <arm_mb> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BIN="$5"; ARM_MB="$6"; BUDGET="${7:-24}"
HEADROOM=16; VLIM=$((8 * 1024 * 1024))

[ -x "$BIN" ] || { echo "ABORT $TAG: $BIN missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT non-empty"; exit 2; }

run() {  # $1 = "" for BASE, the MiB value for ARM
  local t0 t1 raw v rc
  t0=$(date +%s%N)
  if [ -z "$1" ]; then
    raw=$( ( ulimit -v $VLIM
             exec timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               "$BIN" "$f" --timeout-ms $((BUDGET * 1000)) ) 2>/dev/null )
  else
    raw=$( ( ulimit -v $VLIM
             export AXEYUM_MEMORY_LIMIT_MB="$1"
             exec timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
               "$BIN" "$f" --timeout-ms $((BUDGET * 1000)) ) 2>/dev/null )
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$rc" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\tbase\tbase_rc\tbase_ms\tarm\tarm_rc\tarm_ms\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    b=$(run ""); a=$(run "$ARM_MB"); first=base
  else
    a=$(run "$ARM_MB"); b=$(run ""); first=arm
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$b" "$a" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB_COMPLETE $TAG rows=$(( $(wc -l < "$OUT") - 1 ))"
