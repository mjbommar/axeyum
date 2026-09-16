#!/usr/bin/env bash
# ADR-2122 sizing: run one shard of the 23 `QF_LRA` rows that REACH the online
# CDCL(T) engine under `AXEYUM_LRA_BOUND_PROPAGATION=probe`, and keep the whole
# `; theory-layer` line.
#
# # Why these 23 and not the 93
#
# ADR-2111 measured that only 23 of the 93 undecided rows print a
# `; theory-layer` line at all -- the other 70 die inside `lra.rs` before any
# online engine runs, and contribute NOTHING to its counters, not a zero. A
# ceiling computed over 93 would therefore have 70 rows of silence in the
# denominator and would be a smaller number than the truth for a reason that
# has nothing to do with propagation. The population here is re-derived from
# the committed `buckets-93.tsv` by the `decisions` column being present, which
# is the same test ADR-2111 used.
#
# # Why `probe` and not `on`
#
# `probe` builds the identical column-bound table and answers the identical
# entailment questions, and offers NOTHING. So the search it measures is the
# search that actually ran on this tree. A sizing run with the propagator ON
# would count decisions taken by a DIFFERENT search -- the one propagation had
# already changed -- which is the shape of a measurement that cannot be
# compared with the thing it is meant to size.
#
# The probe is still a perturbation: it spends time building the table. That
# costs wall clock on a budget-bound row and so can move a verdict. Every row
# here is already undecided at this budget, so there is no verdict to lose; the
# rc and verdict columns are kept anyway so a surprise is visible rather than
# assumed away.
#
# Usage: sizing-run.sh <shard-id> <list> <out.tsv> <cores> <bin> [budget_s]
set -u
SHARD="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
MODE="${MODE:-probe}"

[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

OUTDIR="$(dirname -- "$OUT")/captures-$SHARD"
mkdir -p "$OUTDIR" || exit 2

printf 'file\tmode\trc\tms\tverdict\tdecisions\tdec_tracked\tdec_implied\tpasses\trow_cells\tderived\tprops\ttheory_props\tcapture\n' > "$OUT"

# One field of the `; theory-layer` line by name. Prints the empty string when
# the line is absent, which is a DIFFERENT thing from `0` and is kept as such:
# a row that never reached the engine reports nothing, not zero.
field() {
  sed -n 's/^; theory-layer .*/&/p' -- "$1" 2>/dev/null \
    | tr ' ' '\n' \
    | sed -n "s/^$2=//p" \
    | head -1
}

while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  if [ ! -r "$f" ]; then echo "UNREADABLE $rel" >&2; continue; fi
  slug="$(printf '%s' "$rel" | tr '/' '_')"
  t0=$(date +%s%N)
  AXEYUM_LRA_BOUND_PROPAGATION="$MODE" \
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$OUTDIR/$slug.out" 2> "$OUTDIR/$slug.err"
  rc=$?
  t1=$(date +%s%N)
  v=$(grep -m1 -oE '^(sat|unsat|unknown)$' -- "$OUTDIR/$slug.out" 2>/dev/null || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$MODE" "$rc" "$(( (t1 - t0) / 1000000 ))" "${v:-none}" \
    "$(field "$OUTDIR/$slug.out" decisions)" \
    "$(field "$OUTDIR/$slug.out" decisions_on_tracked_atoms)" \
    "$(field "$OUTDIR/$slug.out" decisions_on_implied_atoms)" \
    "$(field "$OUTDIR/$slug.out" implied_bound_passes)" \
    "$(field "$OUTDIR/$slug.out" implied_bound_rows_scanned)" \
    "$(field "$OUTDIR/$slug.out" implied_bounds_derived)" \
    "$(field "$OUTDIR/$slug.out" implied_bound_propagations)" \
    "$(field "$OUTDIR/$slug.out" theory_propagations)" \
    "$OUTDIR/$slug.out" >> "$OUT"
done < "$LIST"

echo "SHARD-DONE $SHARD $(($(wc -l < "$OUT") - 1)) rows"
