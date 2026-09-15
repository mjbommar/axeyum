#!/usr/bin/env bash
# QUANT-ACTIVATION -- the SIZING run.  `qshape.py` over EVERY Tier 1 row of the
# six quantified divisions, decided rows included, because "the target shape is
# present on the undecided files" is worth nothing unless the decided files are
# a different population.  A classifier that answers the same on both is
# measuring the corpus, not the blocker.
#
#   size-run.sh <outdir>
#
# `ulimit -v` because CLAUDE.md records a lane's own analysis script reaching
# 63.4 GB and the kernel OOM-killer taking the whole session.  The classifier
# resolves `let` rather than expanding it, so this ceiling should never bind --
# and if it does, the row says MEMORY rather than vanishing.
set -u
OUT="${1:?usage: size-run.sh <outdir>}"
HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT"

for d in AUFDTLIRA AUFLIRA UF UFDTLIRA UFLIA UFNIA; do
  src="$HERE/lists/$d.verdict-path.tsv"
  [ -s "$src" ] || { echo "ABORT: $src missing or empty"; exit 2; }
  cut -f2 "$src" > "$OUT/$d.paths"
  n_in=$(wc -l < "$OUT/$d.paths")
  ( ulimit -v 16000000; python3 "$HERE/qshape.py" --from-list "$OUT/$d.paths" > "$OUT/$d.shape.tsv" )
  rc=$?
  n_out=$(( $(wc -l < "$OUT/$d.shape.tsv") - 1 ))
  # A classifier that OMITS rather than refuses turns the output into a
  # measurement of the accepted subset.  The counts are compared, not assumed.
  echo "$d rc=$rc in=$n_in out=$n_out"
  [ "$n_in" -eq "$n_out" ] || echo "  WARNING $d: $((n_in - n_out)) rows missing from the classifier output"
done
