#!/usr/bin/env bash
# Check exact range population, child hashes, theorem shape, and both algebraic checkers.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/check-gf2-lemire-range.py
python3 scripts/check-gf2-hayes-recurrence.py
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-check -- \
  artifacts/gf2/lemire/degree-400.json

for shard in \
  artifacts/gf2/lemire/range-1-400/shards/shard-1-80 \
  artifacts/gf2/lemire/range-1-400/shards/shard-81-160 \
  artifacts/gf2/lemire/range-1-400/shards/shard-161-240 \
  artifacts/gf2/lemire/range-1-400/shards/shard-241-320 \
  artifacts/gf2/lemire/range-1-400/shards/shard-321-400
do
  cargo run --quiet -p axeyum-cas --bin axeyum-gf2-check-shard -- \
    "$shard" --require-all-found
done
