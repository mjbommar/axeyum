#!/usr/bin/env bash
# Interleaved per-file A/B: baseline (`main` at f9075838e) against this lane.
#
# The two arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load — which moved 23 verdicts in one division at fixed code on this
# box — cancels in the DIFFERENCE rather than landing entirely on whichever arm
# ran second.  Arm order alternates per file for the same reason.
#
# Columns: file  base  base_s  lane  lane_s  status
set -u
DIV="${1:?division}"
LIST="${2:?pinned list}"
OUT="${3:?output tsv}"
BASE="${4:?baseline binary}"
LANE="${5:?lane binary}"
BUDGET_S="${6:-24}"

printf 'file\tbase\tbase_s\tlane\tlane_s\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  run() {
    local bin="$1" t0 t1 v
    t0=$(date +%s.%N)
    v=$(timeout $((BUDGET_S * 2 + 10)) "$bin" "$f" --timeout-ms $((BUDGET_S * 1000)) 2>/dev/null \
          | grep -m1 -E '^(sat|unsat|unknown)$')
    t1=$(date +%s.%N)
    printf '%s\t%.2f' "${v:-unknown}" "$(echo "$t1 - $t0" | bc)"
  }
  if [ $((n % 2)) -eq 1 ]; then
    b=$(run "$BASE"); l=$(run "$LANE")
  else
    l=$(run "$LANE"); b=$(run "$BASE")
  fi
  printf '%s\t%s\t%s\t%s\n' "$f" "$b" "$l" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "$DIV: $n files -> $OUT"
