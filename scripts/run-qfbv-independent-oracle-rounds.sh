#!/usr/bin/env bash
# Preregistered ADR-0237 QF_BV correctness campaign.
set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 <cvc5-bin> <bitwuzla-bin> <output-dir>" >&2
  exit 2
fi

cvc5_bin=$1
bitwuzla_bin=$2
output_dir=$3

for binary in "$cvc5_bin" "$bitwuzla_bin"; do
  if [ ! -x "$binary" ]; then
    echo "oracle is not executable: $binary" >&2
    exit 2
  fi
done

mkdir -p "$output_dir"
if find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
  echo "output directory must be empty: $output_dir" >&2
  exit 2
fi

{
  echo "cvc5_sha256=$(sha256sum "$cvc5_bin" | cut -d' ' -f1)"
  echo "bitwuzla_sha256=$(sha256sum "$bitwuzla_bin" | cut -d' ' -f1)"
  echo "cvc5_version=$($cvc5_bin --version | head -n 1)"
  echo "bitwuzla_version=$($bitwuzla_bin --version | head -n 1)"
  rustc --version
  cargo --version
} >"$output_dir/environment.txt"

rounds=(
  "uniform-a:uniform-v1:1000000"
  "uniform-b:uniform-v1:2000000"
  "edge-c:edge-v1:3000000"
)

for round in "${rounds[@]}"; do
  IFS=: read -r name profile seed_start <<<"$round"
  echo "running $name profile=$profile seeds=$seed_start..$((seed_start + 4000))"
  AXEYUM_CVC5_BIN="$cvc5_bin" \
  AXEYUM_BITWUZLA_BIN="$bitwuzla_bin" \
  AXEYUM_REQUIRE_CVC5=1 \
  AXEYUM_REQUIRE_CVC5_ALL_DECIDED=1 \
  AXEYUM_CVC5_SAMPLE_STRIDE=1 \
  AXEYUM_REQUIRE_BITWUZLA=1 \
  AXEYUM_REQUIRE_BITWUZLA_ALL_DECIDED=1 \
  AXEYUM_BITWUZLA_SAMPLE_STRIDE=1 \
  AXEYUM_QFBV_AXEYUM_TIMEOUT_MS=30000 \
  AXEYUM_REQUIRE_QFBV_ALL_DECIDED=1 \
  AXEYUM_QFBV_SEED_START="$seed_start" \
  AXEYUM_QFBV_INSTANCES=4000 \
  AXEYUM_QFBV_GENERATOR_PROFILE="$profile" \
  AXEYUM_QFBV_REPORT_PATH="$output_dir/$name.json" \
    cargo test -p axeyum-solver --features z3 --test bv_differential_fuzz \
      bv_differential_fuzz_disagree_zero -- --nocapture \
      2>&1 | tee "$output_dir/$name.log"
done

echo "completed preregistered QF_BV rounds in $output_dir"
