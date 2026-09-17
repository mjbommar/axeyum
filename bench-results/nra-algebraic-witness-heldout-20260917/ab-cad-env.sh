#!/usr/bin/env bash
# Interleaved per-file A/B of ONE BINARY under TWO `AXEYUM_NRA_CAD` values
# (ADR-2134's lever, re-measured at head for the ship decision).
#
#   A = armA  (default: `single-cell`, the shipped `CAD_DEFAULT` at 43f1e0f90)
#   B = armB  (default: `algebraic-witness`)
#
# ADR-2145's `bench-results/warm-keep-trail-20260917/ab-env.sh` with the
# variable changed and the arm-name guard from ADR-2134's
# `recheck-movers-env.sh`: both arms run BACK TO BACK on the SAME file on the
# SAME pinned core, arm order alternating per file, so ambient load cancels in
# the difference rather than landing on whichever arm ran second.
#
# TIMING IS `$EPOCHREALTIME`, NEVER `date`: s5 and s7 run uutils coreutils,
# whose `date +%s%3N` prints NANOSECONDS, and a 200 ms sleep is timed before the
# first solve and must read 150-400 ms or the run aborts (exit 3). ADR-2134's
# original `ab-run.sh` timed with `date +%s%N`; its `*_ms` columns are from an
# s5 run and are not reused here.
#
# ARM NAMES ARE DERIVED from `CadPolicy` in the source, not spelled out: an
# unrecognised `AXEYUM_NRA_CAD` value resolves to the shipped default WITHOUT a
# diagnostic, so a typo would measure one arm against itself and report a
# flawless null. The script refuses a name it cannot find in the source.
#
# EXIT STATUS is recorded per arm as its own column, and `:status` from the
# file's header as a further column, so a flip or a disagreement is a row, not
# a recollection.
#
# Envelope: 24 s wall, 8 GiB `ulimit -v`, one pinned physical core pair.
#
# Usage: ab-cad-env.sh <tag> <list> <out.tsv> <cores> <bin> [budget_s] [armA] [armB]
#   The list carries CORPUS-RELATIVE paths (`QF_NRA/...`).
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
ARM_A="${7:-single-cell}"; ARM_B="${8:-algebraic-witness}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ -n "${AXEYUM_NRA_CAD:-}" ] && {
  echo "ABORT $TAG: AXEYUM_NRA_CAD is set in the launching shell"; exit 2
}
[ "$ARM_A" = "$ARM_B" ] && { echo "ABORT $TAG: both arms are the SAME env value"; exit 2; }

ARMS_SRC="${AXEYUM_ARMS_SRC:-$(dirname "$0")/nra_real_root.rs}"
[ -r "$ARMS_SRC" ] || { echo "ABORT $TAG: cannot read $ARMS_SRC for the arm names; set AXEYUM_ARMS_SRC"; exit 2; }
KNOWN=" $(grep -oE '^[[:space:]]*arm: "[a-z-]+",' "$ARMS_SRC" | sed 's/.*"\(.*\)",/\1/' | sort -u | tr '\n' ' ')"
case "$KNOWN" in "" | " ") echo "ABORT $TAG: no arm names found in $ARMS_SRC"; exit 2 ;; esac
for arm in "$ARM_A" "$ARM_B"; do
  case "$KNOWN" in
    *" $arm "*) ;;
    *) echo "ABORT $TAG: '$arm' is not a known AXEYUM_NRA_CAD arm. Known:$KNOWN"; exit 2 ;;
  esac
done

now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }

# Clock self-check: a 200 ms sleep must read 150-400 ms.
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then
  echo "ABORT $TAG: clock self-check read ${dt} ms for a 200 ms sleep"; exit 3
fi
echo "CLOCK-OK $TAG sleep200=${dt}ms armA=$ARM_A armB=$ARM_B"

run_arm() {  # $1 = arm value; uses $f
  local t0 t1 raw rc v
  t0=$(now_ms)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          env AXEYUM_NRA_CAD="$1" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  t1=$(now_ms)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$((t1 - t0))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=A; a=$(run_arm "$ARM_A"); b=$(run_arm "$ARM_B")
  else
    first=B; b=$(run_arm "$ARM_B"); a=$(run_arm "$ARM_A")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "$rel" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
  echo "[$TAG $n] A=$(printf '%s' "$a" | cut -f1) B=$(printf '%s' "$b" | cut -f1) $rel"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  bin=$(sha256sum "$AX" | cut -d' ' -f1) A=AXEYUM_NRA_CAD=$ARM_A B=AXEYUM_NRA_CAD=$ARM_B"
