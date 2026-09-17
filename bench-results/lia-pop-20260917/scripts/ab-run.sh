#!/usr/bin/env bash
# ADR-2143 -- interleaved per-file A/B of TWO BINARIES (a repair has no lever).
#
#   A = smtcomp_cli built at the merge point before the repair (595d50102)
#   B = smtcomp_cli built at the repair commit (7526dfb25)
#
# The script REFUSES unless the two binaries hash differently: two identical
# arms produce a perfect zero that looks exactly like agreement
# (../route-ownership-20260915/ab-run.sh established the check).
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, arm
# order alternating per file, so ambient load cancels in the DIFFERENCE. Exit
# status is a column of its own (ADR-2045 measured `losses=0` by verdict with
# five ABORTS underneath). The file's own `:status` is a column, so a
# disagreement with it can be counted per arm.
#
# TIMING IS `$EPOCHREALTIME`, NEVER `date`: s7 runs uutils coreutils, whose
# `date +%s%3N` prints NANOSECONDS. A 200 ms sleep is timed before the first
# solve and must read 150-400 ms or the run aborts (exit 3).
#
# Envelope: 24 s wall, 8 GiB `ulimit -v`, one pinned physical core pair.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <binA> <binB> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX_A="$5"; AX_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX_A" ] || { echo "ABORT $TAG: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT $TAG: $AX_B missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
if [ "$HA" = "$HB" ]; then
  echo "ABORT $TAG: both arms are the SAME binary ($HA)."
  exit 2
fi

export LC_ALL=C
now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }

# Clock self-check: a 200 ms sleep must read 150-400 ms.
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then
  echo "ABORT $TAG: clock self-check read ${dt} ms for a 200 ms sleep"; exit 3
fi
echo "CLOCK-OK $TAG sleep200=${dt}ms A=$HA B=$HB"

run_arm() {  # $1 = path to the binary
  local t0 t1 raw rc v
  t0=$(now_ms)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$1" "$f" 2>/dev/null)
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
    first=A; a=$(run_arm "$AX_A"); b=$(run_arm "$AX_B")
  else
    first=B; b=$(run_arm "$AX_B"); a=$(run_arm "$AX_A")
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT  A=$HA B=$HB"
