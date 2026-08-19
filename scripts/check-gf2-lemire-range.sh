#!/usr/bin/env bash
# Check exact range population, child hashes, theorem shape, and both algebraic checkers.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/check-gf2-lemire-range.py
python3 scripts/check-gf2-hayes-recurrence.py
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-hayes-bound
python3 scripts/check-gf2-hayes-sufficient-bound.py
python3 scripts/check-gf2-hayes-layer-bound.py
if python3 scripts/check-gf2-hayes-sufficient-bound.py \
  --threshold 10 >/dev/null 2>&1
then
  echo "GF2_HAYES_SUFFICIENT_MUTATION|status=FAIL|error=weak threshold was accepted" >&2
  exit 1
fi
if python3 scripts/check-gf2-hayes-layer-bound.py \
  --threshold 21 >/dev/null 2>&1
then
  echo "GF2_HAYES_LAYER_MUTATION|status=FAIL|error=weak threshold was accepted" >&2
  exit 1
fi
if python3 scripts/check-gf2-hayes-layer-bound.py \
  --sqrt2-numerator 7 --sqrt2-denominator 5 >/dev/null 2>&1
then
  echo "GF2_HAYES_LAYER_MUTATION|status=FAIL|error=invalid sqrt2 witness was accepted" >&2
  exit 1
fi
if python3 scripts/check-gf2-hayes-sufficient-bound.py \
  --threshold 201 >/dev/null 2>&1
then
  echo "GF2_HAYES_SUFFICIENT_MUTATION|status=FAIL|error=unchecked finite remainder was accepted" >&2
  exit 1
fi
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-hayes-endpoints -- 12
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-hayes-endpoints -- \
  8 --conductor-layers
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-hayes-moments -- 8
cargo run --quiet -p axeyum-cas --bin axeyum-gf2-hayes-fourth-filtration -- 8
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
