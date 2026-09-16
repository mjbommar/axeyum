#!/usr/bin/env bash
# ADR-2132: how far does FILL-IN carry the warm tableau above the count it was
# ADMITTED on?
#
# # Why this is a probe and not part of the A/B
#
# It is a MECHANISM measurement, not a comparison of arms, so it does not need
# the A/B's binary and must not share its table. The A/B ran on `axeyum.v1`;
# `warm_cube_entry_nnz` did not exist then. Running this on a later binary is
# therefore correct rather than a compromise -- what would be wrong is putting a
# number from one binary into the other's verdict table, which nothing here does.
#
# # The question, and why the peak alone cannot answer it
#
# `Incremental::with_nonzero_admission` admits the warm cube engine on nonzeros
# AT CONSTRUCTION, capped at `MAX_WARM_CUBE_NONZEROS = 400_000`.
# `Incremental::with_policy` -- the door the ONLINE engine uses -- refuses on
# `m x (nvars+m)` DENSE CELLS at `MAX_TABLEAU_CELLS = 4_000_000`. [ADR-2125]
# showed the two disagree by three orders of magnitude at construction and asked
# whether the dense one should simply be restated in nonzeros.
#
# It should not, and the reason is that a PIVOT CREATES NONZEROS:
# `Tableau::select_entering`'s fill-in-minimising rule exists for exactly that.
# So the construction count bounds the entry footprint and nothing after it.
# [ADR-2111] recorded that it did not take the fill-in measurement.
#
# **A peak read alone settles nothing.** 176,776 nonzeros against a 400,000 cap
# is one claim if the tableau entered at 170,000 and the opposite claim if it
# entered at 4,688. The ratio is the finding; the peak is half of it.
#
# Usage: fill-in-probe.sh <list> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT non-empty; refusing to overwrite"; exit 2; }

field() {
  sed -n "s/^; $2 .*/&/p" -- "$1" 2>/dev/null | tr ' ' '\n' | sed -n "s/^$3=//p" | head -1
}

printf 'file\tbuild\tchecks\tentry_nnz\tfill_peak\tatoms\tlra_rounds\n' > "$OUT"
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  [ -r "$f" ] || { echo "UNREADABLE $rel" >&2; continue; }
  o="$(mktemp)"
  AXEYUM_LRA_WARM_CUBE=on \
    timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$AX" "$f" > "$o" 2>/dev/null
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" \
    "$(field "$o" lazy-smt warm_cube_build)" \
    "$(field "$o" lazy-smt warm_cube_checks)" \
    "$(field "$o" lazy-smt warm_cube_entry_nnz)" \
    "$(field "$o" lazy-smt warm_cube_fill_peak)" \
    "$(field "$o" lazy-smt atoms)" \
    "$(field "$o" lazy-smt lra_rounds)" >> "$OUT"
  rm -f "$o"
done < "$LIST"
echo "FILL-PROBE-DONE -> $OUT"
