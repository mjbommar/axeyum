#!/usr/bin/env bash
# THE REFERENCE MEASUREMENT: what does a solver that SUCCEEDS spend at the point
# where we die?
#
# ADR-2005 established WHICH strategy cvc5 needs (e-matching alone, 111 of 115).
# This asks the quantity the round-head hypothesis turns on: HOW MUCH does it
# spend, and how many instantiation tuples does it use? A lane proposing to
# redistribute a 24 s budget so the final ground check gets a reserve is making
# an implicit claim that the work is of the same ORDER as the budget. If the
# reference decides in tens of milliseconds, no redistribution of 24 s is the
# missing capability and the round head is a symptom.
#
# Two instruments, both cvc5's own, neither ours:
#   --stats                 `global::totalTime` -- cvc5's own clock, not the wall
#   --dump-instantiations   the exact tuples a winning refutation used
#
# LIVENESS BY MECHANISM, not by verdict counts: `--dump-instantiations` is shown
# live by emitting a NONZERO tuple count on files it refutes and none on files
# it does not, and `global::totalTime` by tracking the wrapper's own wall clock.
# A silently-ignored flag would print the same verdict.
#
# cvc5's --tlimit is MILLISECONDS (z3's -T: is SECONDS). The wrapper `timeout`
# is the backstop for an arm that ignores its own limit. NONE (no verdict-shaped
# line at all) is kept DISTINCT from `unknown`: a crash, an OOM and a self-kill
# all land there and none of them is a solver opinion.
#
# Usage: ref-cost-run.sh <tag> <list-of-absolute-paths> <out.tsv> <cores> [budget_s]
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$CVC5" ] || { echo "ABORT $TAG: $CVC5 missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

printf 'file\tstatus\tverdict\twall_ms\tcvc5_ms\tquants\ttuples\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  # Anchored on the `(set-info :status ...)` FORM and NOT on a `$`-anchored
  # pattern -- the copy of this check in dispatch-decline-audit-20260913 piped
  # the whole line into a `$`-anchored grep and matched nothing on every file.
  st=$(grep -m1 -oE '\(set-info :status +(sat|unsat|unknown)' "$f" 2>/dev/null \
        | grep -oE '(sat|unsat|unknown)$')
  t0=$(date +%s%N)
  raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit $((BUDGET * 1000)) --stats \
                     --dump-instantiations \"\$1\"" \
          "$CVC5" "$f" 2>&1)
  t1=$(date +%s%N)
  wall=$(( (t1 - t0) / 1000000 ))
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  ct=$(printf '%s\n' "$raw" | grep -m1 -oE 'global::totalTime = [0-9]+' | grep -oE '[0-9]+$')
  # One `(instantiations <quant>` block per quantifier that was instantiated;
  # each `( ... )` line inside a block is one tuple. Count both.
  q=$(printf '%s\n' "$raw" | grep -cE '^\(instantiations ')
  tp=$(printf '%s\n' "$raw" | grep -cE '^  \( .* \)$')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${st:-none}" "${v:-NONE}" "$wall" "${ct:-na}" "$q" "$tp" >> "$OUT"
done < "$LIST"
echo "REF-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
