#!/usr/bin/env bash
# DT-QUANT-TRACE -- this lane's exit-criterion 7 gates, run in one sequence so
# they queue on the host flock once rather than racing each other.
#
#   gates.sh [<out.txt>]
#
# Every step prints its own NONZERO TEST COUNT. A feature-gated suite compiles
# to nothing and exits 0, and `cargo test --lib 'a b'` runs zero tests and exits
# 0 -- both are green-looking gates that check nothing (CLAUDE.md). So the
# summary at the end reports counts, not just exit statuses, and a step whose
# count is zero is called out by name.
set -u
OUT="${1:-/dev/stdout}"
cd "$(cd "$(dirname "$0")/../.." && pwd)"
: > "$OUT"

step() {
  local name="$1"; shift
  echo "===== $name" >> "$OUT"
  "$@" >> "$OUT" 2>&1
  echo "----- $name rc=$?" >> "$OUT"
}

step "default-features check (the no-C-dependency promise)" \
  scripts/cargo-serialized.sh check -p axeyum-solver

step "lib sweep, full features" \
  scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full

# The route/dispatch suites this lane's diff can reach: the change is inside
# the quantified arm of `check_auto_dispatch` and it touches the give-up
# DETAIL, so the trail suites and the refusal-decline suite are the ones that
# would see it. Named explicitly rather than by a `--test` glob, because a
# glob that matches nothing runs zero tests and exits 0.
step "dispatch + route-trail suites" \
  scripts/cargo-serialized.sh test -p axeyum-solver --features full \
    --test dispatch_rung_refusal_declines --test decline_detail_typed \
    --test quantified_route_trace --test route_trace --test route_attribution

step "config_registry unit tests" \
  scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
    config_registry::

# The frontier ratchet is LOAD SENSITIVE and prints its own reference frame.
# Read `reference frame [family]` before believing a REGRESSION: the same commit
# on the same machine has read 35 / 39 / 40 purely from neighbouring load
# (CLAUDE.md). Pinned to the P-cores here for the same reason.
step "progress_frontier (read its own reference-frame line)" \
  taskset -c 0-7 scripts/cargo-serialized.sh test -p axeyum-solver \
    --test progress_frontier --features full -- --test-threads=1

echo >> "$OUT"
echo "===== SUMMARY: test counts and exit statuses" >> "$OUT"
grep -E '^(=====|-----|test result:|REGRESSION|PROGRESS|reference frame|NOT COMPARABLE|ADVISORY)' \
  "$OUT" >> "$OUT".summary 2>/dev/null || true
echo "wrote $OUT and $OUT.summary"
