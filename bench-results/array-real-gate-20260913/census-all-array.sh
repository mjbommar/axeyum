#!/usr/bin/env bash
# The census over EVERY array-carrying SMT-LIB division, not only the ones whose
# logic NAME contains an R.
#
# Why the wider sweep exists: the targeted run (`census.sh`) found zero
# `real_gate_only` files in the divisions ADR-1955 named, and "we looked where we
# expected a hit and found none" is not a denominator. A benchmark might in
# principle declare a stronger logic than it uses, so the population this change
# reaches can only be bounded by asking about every division that can hold an
# array at all. An empty result from an instrument never pointed at the subject
# is indistinguishable from a strong negative.
#
# TWO STAGES, and the first one is why this finishes. Parsing is the expensive
# instrument: measured 2026-09-13, the parse-everything form managed 25 of
# AUFBV's 1,523 files in 20 minutes (a ~20-hour division, and AUFBV is one of
# 28). So each division is first filtered TEXTUALLY for anything that could
# possibly produce a `Real`, and only the survivors are parsed:
#
#     grep -liE 'real|[0-9]\.[0-9]'
#
# That pattern is deliberately GENEROUS and can only over-include: a Real sort is
# spelled `Real` (directly or through a `define-sort` alias, whose body still
# contains the token), `to_real` contains it case-insensitively, and the only
# other way to introduce a Real is a decimal literal. A file matching none of
# those cannot set `Features::has_real`, so it cannot land in `real_gate_only`
# whatever else it contains. The filtered-out count is PRINTED, so the reader can
# see the size of the population the parser never saw and why it was safe.
#
# Usage: census-all-array.sh <census-binary> <out-dir> [taskset-cores]
set -eu
BIN="${1:?usage: census-all-array.sh <census-binary> <out-dir> [cores]}"
OUT="${2:?usage: census-all-array.sh <census-binary> <out-dir> [cores]}"
CORES="${3:-}"
ROOT=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

# Every division whose logic can contain an array (the `A` in the logic name),
# including the ones already covered by census.sh so this run stands alone.
DIVISIONS="ABV ABVFP ABVFPLRA ALIA ANIA AUFBV AUFBVDTLIA AUFBVDTNIA \
AUFBVDTNIRA AUFBVFP AUFDTLIA AUFDTLIRA AUFDTNIRA AUFFPDTNIRA AUFLIA AUFLIRA \
AUFNIA AUFNIRA QF_ABV QF_ABVFP QF_ABVFPLRA QF_ALIA QF_ANIA QF_AUFBV \
QF_AUFBVFP QF_AUFLIA QF_AUFNIA QF_AX"

RUN=""
[ -n "$CORES" ] && RUN="taskset -c $CORES"

mkdir -p "$OUT"
for d in $DIVISIONS; do
  [ -d "$ROOT/$d" ] || { echo "SKIP $d (absent)"; continue; }
  find "$ROOT/$d" -name '*.smt2' | sort > "$OUT/$d.all"
  n=$(wc -l < "$OUT/$d.all")
  [ "$n" -gt 0 ] || { echo "ABORT: $d list is empty"; exit 2; }
  # Stage 1: anything that could produce a Real. `grep -l` exits 1 on no match,
  # which is a legitimate outcome here and not an error.
  # `xargs`, not `$(cat …)`: QF_BV-scale divisions blow the argv limit, and a
  # truncated argument list would silently shrink the denominator.
  xargs -a "$OUT/$d.all" -d '\n' grep -liE 'real|[0-9]\.[0-9]' -- \
    > "$OUT/$d.list" 2>/dev/null || true
  m=$(wc -l < "$OUT/$d.list")
  echo "== $d ($n files, $m could carry a Real, $((n - m)) filtered out textually)"
  if [ "$m" = 0 ]; then
    echo "real_gate_only, quantifier-free (reaches the gate today): 0 (no file can set has_real)"
    continue
  fi
  # shellcheck disable=SC2086
  $RUN "$BIN" "$OUT/$d.list" > "$OUT/$d.files.tsv" 2> "$OUT/$d.summary.txt"
  cat "$OUT/$d.summary.txt"
done
echo "CENSUS-ALL-DONE"
