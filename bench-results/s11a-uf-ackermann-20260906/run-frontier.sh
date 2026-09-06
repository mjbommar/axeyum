#!/usr/bin/env bash
exec taskset -c 0-7 scripts/cargo-serialized.sh test -p axeyum-solver \
  --test progress_frontier --features full -- --test-threads=1
