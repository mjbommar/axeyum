#!/usr/bin/env bash
# UFLIA-TRACE -- is the set we DISCARD at a deadline exit already unsatisfiable?
#
#   held-run.sh <list> <out.tsv> <pin> <bin> [budget_s] [replay_ms]
#
# `InstantiationTimeoutSite::RoundHead` and `MidRound` return before
# `finish_quantified_ground_check`, so the ground set they hold is thrown away.
# "We hold an unsat set and never looked" and "we hold an insufficient set"
# produce the IDENTICAL `unknown`. `AXEYUM_QPROBE_HELD_SET_REPLAY` re-checks the
# held set on a budget of its own and PRINTS the verdict without acting on it,
# so this arm measures the shipped verdict plus some wall time and never a
# different verdict -- which is exactly what makes it usable as evidence for
# whether a lever is worth building.
#
# The probe verdict column is the finding; the solver verdict column is here
# only to confirm the arm did not change it.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"; REPLAY="${6:-4000}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\tverdict\texits\thead_n\thead_unsat\tmid_n\tmid_unsat\tmax_ground\tdetail\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  raw=$(AXEYUM_QPROBE=1 AXEYUM_QPROBE_HELD_SET_REPLAY="$REPLAY" \
          taskset -c "$PIN" timeout $((BUDGET + 60)) \
          "$AX" "$p" --timeout-ms $((BUDGET * 1000)) 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  rep=$(printf '%s\n' "$raw" | grep 'QPROBE held-set-replay ' || true)
  n=$(printf '%s\n' "$rep" | grep -c 'exit=' || true)
  hn=$(printf '%s\n' "$rep" | grep -c 'exit=timeout-round-head' || true)
  hu=$(printf '%s\n' "$rep" | grep 'exit=timeout-round-head' | grep -c 'verdict=unsat' || true)
  mn=$(printf '%s\n' "$rep" | grep -c 'exit=timeout-mid-round' || true)
  mu=$(printf '%s\n' "$rep" | grep 'exit=timeout-mid-round' | grep -c 'verdict=unsat' || true)
  mg=$(printf '%s\n' "$rep" | grep -oE 'ground=[0-9]+' | cut -d= -f2 | sort -n | tail -1)
  d=$(printf '%s\n' "$rep" | tr '\n' ';' | cut -c1-300)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$(basename "$p")" "${v:-NOVERDICT}" "${n:-0}" "${hn:-0}" "${hu:-0}" \
    "${mn:-0}" "${mu:-0}" "${mg:-0}" "${d:-NONE}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
