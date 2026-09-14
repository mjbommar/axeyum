#!/usr/bin/env bash
# ADR-2020 -- what the reference does INSTEAD of building the skeleton we refuse.
#
# cvc5's own instruments, none of ours:
#   --stats                 `global::totalTime` -- cvc5's clock, not the wall
#   --dump-instantiations   the instantiation tuples it actually used
#
# `--dump-instantiations` is shown LIVE BY MECHANISM, not by verdict counts: a
# silently ignored flag prints the same verdict. The mechanism check is that the
# tuple count is NONZERO on files it refutes and ZERO on files it does not
# answer -- reported on the summary line.
#
# cvc5's --tlimit is MILLISECONDS (z3's -T: is SECONDS). Getting this wrong
# gives a 1000x budget and a meaningless comparison.
set -u
LIST="$1"; OUT="$2"; PIN="${3:-12}"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
[ -x "$CVC5" ] || { echo "ABORT: $CVC5 missing"; exit 2; }

printf 'file\tverdict\ttotal_ms\tinst_tuples\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  raw=$(timeout 60 taskset -c "$PIN" "$CVC5" --stats --dump-instantiations \
          --tlimit 24000 "$CORPUS/$f" 2>&1)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  ms=$(printf '%s\n' "$raw" | grep -m1 -oE 'global::totalTime = [0-9]+' | grep -oE '[0-9]+$')
  # One line per tuple INSIDE an `(instantiations ...)` block. Skolem blocks
  # have the identical tuple shape, so a bare tuple grep counts them too --
  # track the enclosing block instead of matching the tuple alone.
  inst=$(printf '%s\n' "$raw" | awk '
    /^\(instantiations / { inblock = 1; next }
    /^\(skolem /         { inblock = 0; next }
    /^\)/                { inblock = 0; next }
    inblock && /^ *\( /  { n++ }
    END { print n + 0 }')
  printf '%s\t%s\t%s\t%s\n' "$f" "$v" "${ms:-na}" "${inst:-0}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
