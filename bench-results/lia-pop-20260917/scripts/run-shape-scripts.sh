#!/usr/bin/env bash
# ADR-2143 sizing -- run every public incremental script that carries the
# push / assert / assert-negation-in-a-nested-scope / pop shape through BOTH
# `axeyum` binaries (A = before the repair, B = after) and z3, and compare the
# verdict streams. One line per file:
#
#   file  logic  A_n  B_n  z3_n  A_vs_z3  B_vs_z3  A_vs_B  A_rc  B_rc  z3_rc
#
# `*_n` is how many verdicts each produced inside the budget; `X_vs_Y` compares
# the common prefix and prints `agree` / `DISAGREE@<k>` (first differing
# check-sat, 1-based) / `empty` when either side produced nothing. `unknown`
# on either side is NOT a disagreement.
#
# Envelope: BUDGET s wall per solver per file, 8 GiB `ulimit -v`, one pinned
# core pair; the solvers run one after another, never together.
#
# Usage: run-shape-scripts.sh <list> <out.tsv> <cores> <binA> <binB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX_A="$4"; AX_B="$5"; BUDGET="${6:-600}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/incremental/incremental/
[ -x "$AX_A" ] || { echo "ABORT: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT: $AX_B missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty"; exit 2; }
HA=$(sha256sum "$AX_A" | cut -d' ' -f1); HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
[ "$HA" = "$HB" ] && { echo "ABORT: both arms are the SAME binary"; exit 2; }
echo "SHAPE-RUN A=$HA B=$HB z3=$(z3 --version)"

verdicts() {  # $1 = output file, $2.. = command words; prints the solver's exit status
  local out="$1"; shift
  timeout $((BUDGET + 10)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$@\"" _ "$@" 2>/dev/null > "$out.raw"
  local rc=$?
  grep -oE '^(sat|unsat|unknown)$' "$out.raw" > "$out"
  echo "$rc"
}

compare() {  # $1 $2 = files of verdicts
  local n1 n2 n k a b
  n1=$(wc -l < "$1"); n2=$(wc -l < "$2")
  if [ "$n1" -eq 0 ] || [ "$n2" -eq 0 ]; then echo empty; return; fi
  n=$(( n1 < n2 ? n1 : n2 ))
  for ((k = 1; k <= n; k++)); do
    a=$(sed -n "${k}p" "$1"); b=$(sed -n "${k}p" "$2")
    if [ "$a" != "$b" ] && [ "$a" != unknown ] && [ "$b" != unknown ]; then
      echo "DISAGREE@$k($a/$b)"; return
    fi
  done
  echo agree
}

printf 'file\tlogic\tA_n\tB_n\tz3_n\tA_vs_z3\tB_vs_z3\tA_vs_B\tA_rc\tB_rc\tz3_rc\n' > "$OUT"
T=$(mktemp -d)
while IFS=$'\t' read -r f logic _rest; do
  [ -n "$f" ] || continue
  arc=$(verdicts "$T/a" "$AX_A" "$f" --timeout-ms $((BUDGET * 1000)))
  brc=$(verdicts "$T/b" "$AX_B" "$f" --timeout-ms $((BUDGET * 1000)))
  zrc=$(verdicts "$T/z" z3 -T:"$BUDGET" "$f")
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$logic" "$(wc -l < "$T/a")" "$(wc -l < "$T/b")" "$(wc -l < "$T/z")" \
    "$(compare "$T/a" "$T/z")" "$(compare "$T/b" "$T/z")" "$(compare "$T/a" "$T/b")" \
    "$arc" "$brc" "$zrc" >> "$OUT"
done < "$LIST"
rm -rf "$T"
echo "SHAPE-DONE $OUT"
