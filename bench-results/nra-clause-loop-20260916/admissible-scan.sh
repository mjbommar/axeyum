#!/usr/bin/env bash
# What does the clause loop actually DO on the files it can admit?
#
# The A/B says the loop gains nothing on the pinned QF_NRA draw. That is a
# number, not a reason, and the difference matters: "the loop ran and could not
# finish" and "the loop never got offered the file" are different findings with
# different next increments.
#
# This is the scan the ADR-2131 decline slot was built for. `CAD_DECLINE` is
# STICKY and is already full of `non-conjunctive` by the time the loop runs, so
# before that slot existed every one of the loop's own causes was recorded into
# a slot that could not take it and the trace reported `non-conjunctive` for all
# of them -- the arm was observable only through its verdicts. The trace detail
# now carries ` clause-loop=<cause>` when the loop ran.
#
# Usage: admissible-scan.sh <list> <out.tsv> [core] [budget_s]
set -u
LIST="${1:?usage: admissible-scan.sh <list> <out.tsv> [core] [budget_s]}"
OUT="${2:?usage: admissible-scan.sh <list> <out.tsv> [core] [budget_s]}"
CORE="${3:-5}"
BUDGET="${4:-24}"

# A parameter, not a constant. The A/B binary and the DIAGNOSTIC binary are
# different builds living side by side: publishing the diagnostic over the A/B
# path would swap the binary underneath a running sweep, which `build.sh`
# now refuses to do (see its header for the near-miss that guard came from).
BIN="${AXEYUM_SCAN_BIN:-/nas3/data/axeyum/lanes/nra-clause-loop/smtcomp_cli}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
VLIM=$((8 * 1024 * 1024))

[ -x "$BIN" ] || { echo "admissible-scan: $BIN missing" >&2; exit 2; }

printf 'file\tverdict\tsingle_cell_cause\tclause_loop_cause\n' > "$OUT"
n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  raw=$(AXEYUM_NRA_CAD=clause-loop timeout $((BUDGET + 16)) taskset -c "$CORE" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000)) --trace" \
          "$BIN" "$CORPUS/$rel" 2>/dev/null) || true
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || printf 'none')
  # Two separate reads. The single-cell cause is what the sticky slot holds; the
  # clause-loop cause is the new slot, and its ABSENCE means the loop never ran
  # on this file at all -- which is itself an answer.
  sc=$(printf '%s\n' "$raw" | grep -oE 'declined: [a-z0-9-]+ \(cad-arm=' | head -1 | sed 's/^declined: //; s/ (cad-arm=$//')
  cl=$(printf '%s\n' "$raw" | grep -oE 'clause-loop=[a-z0-9-]+' | head -1 | sed 's/^clause-loop=//')
  printf '%s\t%s\t%s\t%s\n' "$rel" "$v" "${sc:-none}" "${cl:-DID-NOT-RUN}" >> "$OUT"
  printf '[%2d] %-8s single-cell=%-18s clause-loop=%s\n' \
    "$n" "$v" "${sc:-none}" "${cl:-DID-NOT-RUN}" >&2
done < "$LIST"
echo "admissible-scan: $n files -> $OUT" >&2
