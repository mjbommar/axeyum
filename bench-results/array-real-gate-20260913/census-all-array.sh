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
# produce a `Real`, and only the survivors are parsed:
#
#     grep -lE 'Real|to_real|\(/ '
#
# THE FIRST VERSION OF THIS PATTERN FILTERED NOTHING and the run would have been
# reported as a sweep. It was `grep -liE 'real|[0-9]\.[0-9]'`, and every SMT-LIB
# file on earth opens with `(set-info :smt-lib-version 2.6)`, so the decimal
# alternative matched 4,975 of ABV's 4,975 files. A prefilter that matches
# everything is not a prefilter; the "N filtered out textually" column exists so
# that a zero there is VISIBLE rather than silently harmless.
#
# What the pattern covers, and its one stated limit. A `Real` sort is spelled
# `Real` (directly, or through a `define-sort` alias whose body still contains
# the token). `to_real` is the coercion. `(/ ` is SMT-LIB real division, which
# yields a Real from integer numerals. The residual gap is a bare decimal
# literal in a file that never writes `Real`, `to_real` or `/` anywhere — which
# cannot occur in a logic-conformant benchmark, because a decimal literal is
# only in the signature of a logic that also admits the `Real` sort name. The
# divisions where that matters are exactly the ones `census.sh` already parses
# in full.
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
  xargs -a "$OUT/$d.all" -d '\n' grep -lE 'Real|to_real|\(/ ' -- \
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
