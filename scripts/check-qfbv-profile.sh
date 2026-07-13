#!/usr/bin/env bash
set -euo pipefail

cargo clippy -p axeyum-solver --no-default-features --features qfbv --lib -- -D warnings
cargo test -p axeyum-solver --no-default-features --features qfbv \
  --test qfbv_profile

tree="$(cargo tree -p axeyum-solver --no-default-features --features qfbv \
  -e normal --prefix none)"
unexpected="$(printf '%s\n' "$tree" | rg '^axeyum-' | \
  rg -v '^axeyum-(solver|aig|bv|cnf|ir|query|rewrite) ' || true)"
if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'QF_BV profile pulled an unexpected Axeyum crate:' >&2
  printf '%s\n' "$unexpected" >&2
  exit 1
fi
