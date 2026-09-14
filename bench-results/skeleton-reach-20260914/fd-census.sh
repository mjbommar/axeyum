#!/usr/bin/env bash
# SKELETON-REACH -- census what actually stops each file, re-deriving the
# verdict in the SAME run (pre-registration R4: no verdict is inherited from a
# committed list).
#
#   fd-census.sh <list> <out.tsv> <pin> [budget_s]
#
# For every file it records, per row:
#   verdict     re-derived here, not inherited
#   bound_by    the route the trail blames
#   last        the trail's terminal entry
#   attempts    how many route attempts the trail holds -- an `attempts=1`
#               trail whose only entry is the unconditional `fd:parse` PROBE
#               is the shape ADR-2025 called RUNG-NEVER-REACHED
#   ms          total_ms from the route line
#   giveup_kind the give-up line's `kind=`, verbatim
#   giveup_raw  the give-up line's `detail=`, VERBATIM and unbucketed
#
# `giveup_raw` is carried verbatim because pre-registration R3 forbids sizing a
# bucket by its label. `fd:parse` is a LABEL; the bucketing is done afterwards,
# over the raw details, by a separate script whose classes are derived from the
# observed strings rather than guessed. ADR-2020's census separator was
# `;QPROBE` rather than a bare `;` and truncated its largest bucket; this
# writes tab-separated with every tab and newline stripped out of the raw
# field, so a detail containing punctuation cannot shift a column.
set -u
LIST="$1"
OUT="$2"
PIN="${3:-1}"
BUDGET="${4:-24}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-base}"
[ -x "$AX" ] || { echo "ABORT: $AX missing at $AX"; exit 2; }

printf 'file\tverdict\tbound_by\tlast\tattempts\tms\tgiveup_kind\tskel_rung\tgiveup_raw\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  raw=$(AXEYUM_TRACE=1 timeout $((BUDGET + 40)) taskset -c "$PIN" \
          "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  rl=$(printf '%s\n' "$raw" | grep -m1 '^; route ' || true)
  bb=$(printf '%s' "$rl" | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
  lb=$(printf '%s' "$rl" | grep -oE ' last=[^ ]+' | cut -d= -f2)
  at=$(printf '%s' "$rl" | grep -oE 'attempts=[0-9]+' | cut -d= -f2)
  ms=$(printf '%s' "$rl" | grep -oE 'total_ms=[0-9]+' | cut -d= -f2)
  gl=$(printf '%s\n' "$raw" | grep -m1 '^; give-up ' || true)
  gk=$(printf '%s' "$gl" | grep -oE 'kind=[A-Za-z]+' | cut -d= -f2)
  gd=$(printf '%s' "$gl" | sed -n 's/.*detail=//p' | tr '\t\n' '  ')
  # The skeleton rung's own liveness, as a column: absent / declined / decided.
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then
    sr=decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then
    sr=declined
  else
    sr=absent
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$f" "${v:-NONE}" "${bb:-NONE}" "${lb:-NONE}" "${at:-0}" "${ms:-0}" \
    "${gk:-NONE}" "$sr" "${gd:-NONE}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
awk -F'\t' 'NR>1{c[$2" "$3]++} END{for (k in c) print c[k], k}' "$OUT" | sort -rn
