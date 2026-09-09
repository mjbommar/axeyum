#!/usr/bin/env bash
# Build `complement/<DIV>.txt`: the division's committed parity list MINUS the
# 2026-09-05 loss population.
#
# WHY THIS PASS EXISTS
# --------------------
# Re-running only the old loss list answers "which of the files we lost do we
# now win?" and is structurally incapable of answering "which files we WON do
# we now lose?". That second question is not hypothetical: `bench-results/PARITY.md`
# records QF_UFLIA at 51 reference-only on 2026-09-08 while only 23 of the 58
# files on the 2026-09-05 list are still unsolved -- so 28 of today's losses are
# files that list cannot name.
#
# The reference is not re-run here (only z3 is installed on this host; the
# divisions use cvc5/bitwuzla/yices), so a complement file that is now unsolved
# is a LOSS CANDIDATE, promoted to a loss only when the benchmark itself
# declares `:status sat` or `:status unsat`. That is oracle-free and sound in
# the direction that matters -- a file with a declared status that we do not
# decide is a loss against any complete solver -- but it under-counts, because
# a benchmark with no declared status is invisible to it. The count is
# cross-checked against PARITY.md's `reference-only` cell per division, and the
# residual is reported rather than absorbed.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
out="$here/../complement"
old="$root/bench-results/parity-losses-20260905"
nra="$root/bench-results/parity-losses-20260906"
mkdir -p "$out"
for src in "$root"/bench-results/parity-lists/*.txt; do
  d="$(basename "$src" .txt)"
  loss="$old/$d.txt"
  if [ ! -f "$loss" ]; then loss="$nra/$d.txt"; fi
  if [ -f "$loss" ]; then
    grep -Fxv -f "$loss" "$src" > "$out/$d.txt"
  else
    cp "$src" "$out/$d.txt"
  fi
  echo "$d $(wc -l < "$out/$d.txt") complement of $(wc -l < "$src")"
done
