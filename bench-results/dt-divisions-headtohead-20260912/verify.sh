#!/usr/bin/env bash
# Cross-verify axeyum verdicts against BOTH references and the declared status.
# Input: a TSV of "<basename><TAB><verdict>" plus a division name to resolve
# paths under the corpus.  Output: one row per file with all four.
# Usage: verify.sh <division> <pairs.tsv> <out.tsv> <cores>
set -u
DIV="$1"; PAIRS="$2"; OUT="$3"; PIN="$4"
ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
printf 'file\taxeyum\tz3\tcvc5\tstatus\tagree\n' > "$OUT"
while IFS=$'\t' read -r b v; do
  f=$(find "$ROOT/$DIV" -name "$b" -print -quit)
  if [ -z "$f" ]; then printf '%s\t%s\tNOFILE\tNOFILE\tNOFILE\tNOFILE\n' "$b" "$v" >> "$OUT"; continue; fi
  z=$(timeout 60 taskset -c "$PIN" /usr/bin/z3 -T:24 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$')
  c=$(timeout 60 taskset -c "$PIN" /nas3/data/axeyum/harness/bin/cvc5 --tlimit=24000 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$')
  s=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  bad=""
  [ -n "$z" ] && [ "$z" != "$v" ] && bad="DISAGREE-z3"
  [ -n "$c" ] && [ "$c" != "$v" ] && bad="${bad}${bad:+,}DISAGREE-cvc5"
  { [ "$s" = sat ] || [ "$s" = unsat ]; } && [ "$s" != "$v" ] && bad="${bad}${bad:+,}DISAGREE-status"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$b" "$v" "${z:-unknown}" "${c:-unknown}" "${s:-none}" "${bad:-ok}" >> "$OUT"
done < "$PAIRS"
echo "VERIFY-DONE $DIV $(($(wc -l < "$OUT") - 1)) rows; disagreements: $(awk -F'\t' 'NR>1 && $6!="ok"' "$OUT" | wc -l)"
