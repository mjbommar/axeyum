#!/usr/bin/env bash
# SKELETON-REACH -- the extra suites CLAUDE.md names for a PARSER / front-door
# change. `--lib` runs only unit tests compiled into lib targets and SKIPS
# every integration suite in tests/*.rs; two front-door string tests stayed
# broken across several merges because every lane gated on `--lib` alone.
#
# `--features full` IS MANDATORY: these suites are `#![cfg(feature = "full")]`
# and without it they compile to an empty binary, print "running 0 tests ...
# ok", and exit 0. A NONZERO count is the evidence.
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR=/data0/axeyum/skeleton-reach-target-base
for t in online_string_front_door word_first_fallback qf_slia_fixed_splice stoi_len_abstraction; do
  echo "=== --test $t ==="
  scripts/cargo-serialized.sh test -p axeyum-solver --features full --test "$t" 2>&1 \
    | grep -E '^(test result:|running [0-9]+ tests|error)' || true
done
echo "=== check-suite-gating ==="
python3 scripts/check-suite-gating.py 2>&1 | tail -5
echo "PARSER-GATES-DONE"
