#!/usr/bin/env bash
# Does OUR skolemizer actually FIRE on the undecided Tier-1 files? (ADR-2127)
#
# `crates/axeyum-solver/src/quant_skolemize.rs` is a full polarity-aware
# NNF + Skolemize + prenex pass, applied to the WHOLE assertion set, and it is
# already wired into the ladder as `q:skolem-qf`
# (`crates/axeyum-solver/src/auto.rs:13432`). So the first half of this lane's
# brief describes code that already ships.
#
# "Already ships" is not "already fires". This script measures the difference,
# using the instrumentation the pass already carries:
#
#   `QPROBE skolem-bail`            -- the pass ABANDONED an assertion because a
#                                      quantifier sat under `BoolXor` / `Eq` on
#                                      Bool / `Ite`, where no single Skolem
#                                      choice is valid (`quant_skolemize.rs:386`)
#   `QPROBE ematch skolemize-unchanged` -- the pass ran and changed NOTHING
#                                      (`auto.rs:13438`)
#   `QPROBE ematch retried residual=` -- the pass DID change the query and the
#                                      retry reports whether a quantifier survived
#
# The reason this matters for the build decision: if the pass reaches every
# file and the block is downstream, then re-implementing goal skolemization
# adds nothing, and the lane's remaining value is entirely in the macro half.
# If instead it bails or no-ops on a large share, the shape the census counted
# is NOT being exploited and a second pass has a target.
#
# Exit status depends on the finding: zero files run exits non-zero.
#
# Usage: skolem-reach-probe.sh <division> <list> <out.tsv> <cores> [budget_s] [limit]
set -u
DIV="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-12}"; LIMIT="${6:-0}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
AX=target/release/examples/smtcomp_cli

[ -x "$AX" ] || { echo "ABORT $DIV: $AX missing -- build it first"; exit 2; }
[ -s "$LIST" ] || { echo "ABORT $DIV: $LIST empty"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $DIV: $OUT non-empty; refusing to overwrite"; exit 2; }

printf 'division\tfile\tverdict\tskolem_bail\tunchanged\tretried_lines\tresidual_after\tloop_exit\tms\trc\n' > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && break
  f="$CORPUS$rel"
  [ -f "$f" ] || continue
  n=$((n + 1))
  t0=$(date +%s%N)
  raw=$(AXEYUM_QPROBE=1 timeout $((BUDGET + 16)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>&1)
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  bail=$(printf '%s\n' "$raw" | grep -c 'QPROBE skolem-bail' || true)
  unch=$(printf '%s\n' "$raw" | grep -c 'skolemize-unchanged' || true)
  retr=$(printf '%s\n' "$raw" | grep -c 'QPROBE ematch retried' || true)
  resid=$(printf '%s\n' "$raw" | grep -m1 -oE 'retried residual=(true|false)' | sed 's/.*=//')
  lexit=$(printf '%s\n' "$raw" | grep -m1 -oE 'loop-exit kind=[A-Za-z-]+' | sed 's/.*=//')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$DIV" "$rel" "${v:-none}" "$bail" "$unch" "$retr" "${resid:-none}" "${lexit:-none}" \
    "$(( (t1 - t0) / 1000000 ))" "$rc" >> "$OUT"
done < "$LIST"

if [ "$n" -eq 0 ]; then
  echo "ABORT $DIV: 0 files run"
  exit 3
fi
echo "done $DIV: $n files -> $OUT"
