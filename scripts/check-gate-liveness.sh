#!/usr/bin/env bash
# Gate-liveness ratchet: prove that our gates still RUN something.
#
# `cargo test` exits 0 on an empty test binary. A suite that a new
# `#![cfg(feature = "...")]` has emptied is therefore INDISTINGUISHABLE from a
# passing one by exit status — which is not hypothetical:
#
#   * `crates/axeyum-solver/tests/corpus_regression.rs` gained
#     `#![cfg(feature = "full")]` in 4464dae2 (2026-07-17). The pre-push hook and
#     the documented pre-merge command both ran it WITHOUT that feature, so the
#     oracle-free `:status` corpus sweep — the gate that exists to stop a wrong
#     verdict leaving the machine — ran ZERO tests for 15 days while printing
#     "running 0 tests ... ok" and exiting 0.
#   * `cargo test --workspace --lib` on DEFAULT features compiles 23 of
#     `axeyum-solver`'s ~975 unit tests; everything behind `full` is never built.
#
# `hooks/pre-push` now fails a push on any step that runs zero tests, but that is
# a floor of ONE. This script is the ratchet: it pins a MINIMUM count per suite,
# so a suite that quietly loses most of its tests (a `cfg` around a module, a
# renamed feature, a deleted `mod tests`) breaks the build instead of shrinking
# in silence.
#
# It uses `cargo test -- --list`, which COMPILES but does not RUN the tests, so
# the whole check is cheap enough to sit in the aggregate gate.
#
# Raising a floor is expected as suites grow — that is the ratchet working.
# LOWERING one requires a reason in the commit message: a legitimately deleted
# test is fine, a suite that silently stopped compiling is not.
set -uo pipefail

cd "$(dirname "$0")/.."

# package | target-kind:target-name | features | minimum test count
#
# Floors are set below the counts measured on 2026-08-01, with headroom, so
# ordinary test churn does not trip them.
manifest=$(
  cat <<'EOF'
axeyum-solver|test:corpus_regression|full|1
axeyum-solver|lib|full|900
axeyum-solver|test:progress_frontier|full|9
axeyum-solver|test:online_string_front_door|full|40
axeyum-solver|test:word_first_fallback|full|10
axeyum-solver|test:qf_slia_fixed_splice|full|75
axeyum-solver|test:stoi_len_abstraction|full|10
axeyum-solver|test:string_bound_ladder|full|10
axeyum-cnf|lib||300
axeyum-rewrite|lib||1
EOF
)

rc=0
printf '%-52s %8s %8s  %s\n' SUITE COUNT FLOOR RESULT
while IFS='|' read -r pkg target features floor; do
  [ -z "$pkg" ] && continue

  args=(test -p "$pkg")
  [ -n "$features" ] && args+=(--features "$features")
  case "$target" in
    lib) args+=(--lib); label="$pkg:lib" ;;
    test:*) args+=(--test "${target#test:}"); label="$pkg:${target#test:}" ;;
    *) echo "check-gate-liveness: bad target '$target'" >&2; rc=1; continue ;;
  esac

  # `--list` prints one `name: test` line per test and does not execute them.
  if ! out="$(cargo "${args[@]}" -- --list 2>&1)"; then
    printf '%-52s %8s %8s  %s\n' "$label" "-" "$floor" "BUILD FAILED"
    printf '%s\n' "$out" | tail -20 >&2
    rc=1
    continue
  fi
  count=$(printf '%s\n' "$out" | grep -cE ': test$')

  if [ "$count" -lt "$floor" ]; then
    printf '%-52s %8s %8s  %s\n' "$label" "$count" "$floor" "BELOW FLOOR"
    rc=1
  else
    printf '%-52s %8s %8s  %s\n' "$label" "$count" "$floor" "ok"
  fi
done <<<"$manifest"

if [ "$rc" -ne 0 ]; then
  echo >&2
  echo "check-gate-liveness: a gate runs fewer tests than its committed floor." >&2
  echo "  The usual cause is a feature gate that emptied the suite — check for a" >&2
  echo "  new #![cfg(feature = ...)] and whether the invocation passes it." >&2
  echo "  If tests were legitimately removed, LOWER the floor in this file and" >&2
  echo "  say why in the commit message." >&2
fi
exit "$rc"
