#!/usr/bin/env bash
# SKELETON-REACH -- the 2x2. Neither lever is new; the QUESTION is whether they
# COMPOSE, and nothing has measured that because they did not coexist.
#
#   arm A  base                  distinct-linear OFF, skeleton rung ON  (shipped)
#   arm B  distinct-linear only  distinct-linear ON,  skeleton rung OFF
#   arm C  skeleton only         distinct-linear OFF, skeleton rung ON  (== A)
#
# A and C ARE THE SAME CONFIGURATION ON PURPOSE.  They give a per-file,
# same-arm noise reading inside the very run whose difference is being claimed:
# any row where A and C disagree has a band wider than the effect on that row
# and cannot support one. This is the band being ASSUMED NON-ZERO UNTIL
# MEASURED, measured in the run itself rather than borrowed from another lane.
#   arm D  both                  distinct-linear ON,  skeleton rung ON
#
# POLARITY, stated because both levers invert relative to each other:
#   AXEYUM_DISTINCT_LINEAR ships **Off**  -- `on` ARMS it      (ADR-2000 s6)
#   AXEYUM_ZERO_INST_SKELETON ships **On** -- `0` KILLS it     (ADR-2025 s6)
# So the shipped arm is `env -u AXEYUM_DISTINCT_LINEAR -u AXEYUM_ZERO_INST_SKELETON`,
# which is arm A, and arm D is the candidate.
#
# WHY THE COMPOSITION IS UNTESTED.  ADR-2000 measured distinct-linear on
# 2026-09-13 and found +1 of 356, concluding "the front-door refusal was never
# the binding constraint; the quantified ladder is, at any budget". That was
# true then. ADR-2025's skeleton rung landed 2026-09-14 and does not enter the
# quantified ladder at all -- it refutes before the first instantiation. A file
# refused at INGEST never reaches either. So each lever alone is worth ~nothing
# on these rows and the pair may not be; that is the measurement.
#
#   probe-2x2.sh <list> <out.tsv> <pin> [budget_s]
#
# ONE BINARY, FOUR ENV VALUES. Arms run BACK TO BACK on the SAME pinned core,
# per file, so contention hits all four equally. Arm ORDER ROTATES by row index
# so a systematic within-file drift cannot favour one arm.
set -u
LIST="$1"
OUT="$2"
PIN="${3:-1}"
BUDGET="${4:-24}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-base}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

run_arm() { # $1=arm $2=file -> "verdict|rung|ms|giveup"
  local raw
  case "$1" in
    A) raw=$(env -u AXEYUM_DISTINCT_LINEAR -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
              timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
              --timeout-ms $((BUDGET * 1000)) 2>&1) ;;
    B) raw=$(env AXEYUM_DISTINCT_LINEAR=on AXEYUM_ZERO_INST_SKELETON=0 \
              AXEYUM_TRACE=1 timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
              --timeout-ms $((BUDGET * 1000)) 2>&1) ;;
    C) raw=$(env -u AXEYUM_DISTINCT_LINEAR -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
              timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
              --timeout-ms $((BUDGET * 1000)) 2>&1) ;;
    # `-u` MUST precede every NAME=VALUE. `env FOO=1 -u BAR cmd` does not
    # unset BAR: option parsing stops at the first assignment, so `-u` becomes
    # the COMMAND and the run produces no verdict at all. That spelling was
    # here first and every row of this arm came back `NONE` -- which is why
    # the arm records a verdict rather than only a delta.
    D) raw=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
              timeout $((BUDGET + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$2" \
              --timeout-ms $((BUDGET * 1000)) 2>&1) ;;
  esac
  local v r m g
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then r=decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then r=declined
  else r=absent; fi
  m=$(printf '%s\n' "$raw" | grep -m1 '^; route ' | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  g=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2)
  printf '%s|%s|%s|%s' "${v:-NONE}" "$r" "${m:-0}" "${g:-none}"
}

printf 'file\tA_base\tA_rung\tA_ms\tB_dl\tB_rung\tB_ms\tC_sk\tC_rung\tC_ms\tD_both\tD_rung\tD_ms\torder\n' > "$OUT"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  # Rotate the arm order per row (R8): four rotations of A B C D.
  case $((i % 4)) in
    0) ORD="A B C D" ;;
    1) ORD="B C D A" ;;
    2) ORD="C D A B" ;;
    *) ORD="D A B C" ;;
  esac
  declare -A R=()
  for a in $ORD; do R[$a]=$(run_arm "$a" "$f"); done
  fld() { printf '%s' "${R[$1]}" | cut -d'|' -f"$2"; }
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$f" \
    "$(fld A 1)" "$(fld A 2)" "$(fld A 3)" \
    "$(fld B 1)" "$(fld B 2)" "$(fld B 3)" \
    "$(fld C 1)" "$(fld C 2)" "$(fld C 3)" \
    "$(fld D 1)" "$(fld D 2)" "$(fld D 3)" \
    "${ORD// /}" >> "$OUT"
  i=$((i + 1))
done < "$LIST"
echo "DONE $OUT ($i rows)"
