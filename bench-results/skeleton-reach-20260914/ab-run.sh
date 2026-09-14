#!/usr/bin/env bash
# SKELETON-REACH -- the interleaved A/B. ONE BINARY, TWO ENV VALUES.
#
#   ab-run.sh <list> <out.tsv> <core> <bin> <budget_s> <phase>
#
# phase = `ab`    base vs arm          (the measurement)
# phase = `noise` base vs base         (the band, at byte-identical config)
#
# POLARITY.  Both levers ship **Off**; the arm ARMS them.
#   AXEYUM_DECLARED_NAME_WINS   ships Off -- `on` arms  (ADR-2040, this lane)
#   AXEYUM_DISTINCT_LINEAR      ships Off -- `on` arms  (ADR-2000)
#   AXEYUM_ZERO_INST_SKELETON   ships ON  -- `0` kills  (ADR-2025) -- LEFT
#                               SHIPPED IN BOTH ARMS; it is not a lever here.
# So `base` is `env -u` on the first two and the arm sets both to `on`.  A
# reader who inverts this measures the shipped arm in both halves and reports
# the zero as a null.
#
# Both arms of a file run BACK TO BACK on the SAME pinned core, and the arm
# ORDER ALTERNATES by row index, so neither contention nor a within-file drift
# can favour one arm.
#
# THE ARM IS VISIBLE BY MECHANISM, not only by verdict: `giveup` records the
# ingest refusal being removed.  A silently ignored variable would leave the
# arm's `giveup` identical to the base's on every row, which the summarizer
# reports rather than hiding.
set -u
LIST="$1"
OUT="$2"
PIN="$3"
AX="$4"
BUDGET="${5:-24}"
PHASE="${6:-ab}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

base_run() {
  env -u AXEYUM_DECLARED_NAME_WINS -u AXEYUM_DISTINCT_LINEAR AXEYUM_TRACE=1 \
    timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$1" --timeout-ms $((BUDGET * 1000)) 2>&1
}
arm_run() {
  if [ "$PHASE" = noise ]; then
    base_run "$1"
    return
  fi
  env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
    timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$1" --timeout-ms $((BUDGET * 1000)) 2>&1
}

digest() { # stdin -> "verdict|rung|ms|giveupkind"
  local raw v r m g
  raw=$(cat)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then r=decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then r=declined
  else r=absent; fi
  m=$(printf '%s\n' "$raw" | grep -m1 '^; \(partial \)\?route ' | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  g=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2)
  printf '%s|%s|%s|%s' "${v:-NONE}" "$r" "${m:-0}" "${g:-none}"
}

printf 'file\tbase_v\tbase_rung\tbase_ms\tbase_giveup\tarm_v\tarm_rung\tarm_ms\tarm_giveup\torder\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ $((i % 2)) -eq 0 ]; then
    B=$(base_run "$f" | digest); A=$(arm_run "$f" | digest); ORD="base-first"
  else
    A=$(arm_run "$f" | digest); B=$(base_run "$f" | digest); ORD="arm-first"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" \
    "$(printf '%s' "$B" | cut -d'|' -f1)" "$(printf '%s' "$B" | cut -d'|' -f2)" \
    "$(printf '%s' "$B" | cut -d'|' -f3)" "$(printf '%s' "$B" | cut -d'|' -f4)" \
    "$(printf '%s' "$A" | cut -d'|' -f1)" "$(printf '%s' "$A" | cut -d'|' -f2)" \
    "$(printf '%s' "$A" | cut -d'|' -f3)" "$(printf '%s' "$A" | cut -d'|' -f4)" \
    "$ORD" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "DONE $OUT ($i rows, phase=$PHASE)"
