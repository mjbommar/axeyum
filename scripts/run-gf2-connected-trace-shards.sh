#!/usr/bin/env bash
set -euo pipefail

# Run one deterministic residue class of connected-trace shards.  Each shard
# is published atomically, so a failed or interrupted worker cannot masquerade
# as mergeable evidence.  Host-level resource limits belong to the caller
# (normally a bounded transient unit); this script controls only process count.

if [[ $# -ne 10 ]]; then
  echo "usage: $0 BINARY OUTPUT_DIR FIELD_MODULUS ELL DEGREE SHARD_COUNT FIRST_INDEX INDEX_STRIDE PARALLELISM MAX_CANDIDATES" >&2
  exit 2
fi

binary=$1
output_dir=$2
field_modulus=$3
ell=$4
degree=$5
shard_count=$6
first_index=$7
index_stride=$8
parallelism=$9
max_candidates=${10}

for value_name in shard_count first_index index_stride parallelism max_candidates; do
  value=${!value_name}
  if [[ ! $value =~ ^[0-9]+$ ]]; then
    echo "$value_name must be a nonnegative integer, got: $value" >&2
    exit 2
  fi
done

if [[ ! -x $binary ]]; then
  echo "binary is not executable: $binary" >&2
  exit 2
fi
if (( shard_count == 0 || index_stride == 0 || parallelism == 0 )); then
  echo "shard_count, index_stride, and parallelism must be positive" >&2
  exit 2
fi
if (( first_index >= shard_count )); then
  echo "first_index must be smaller than shard_count" >&2
  exit 2
fi

mkdir -p "$output_dir"

run_one() {
  local index=$1
  local output_path="$output_dir/shard-${index}.json"
  local temporary_path="${output_path}.tmp.$BASHPID"

  if [[ -e $output_path ]]; then
    echo "refusing to overwrite existing shard: $output_path" >&2
    return 1
  fi

  trap 'if [[ -e $temporary_path ]]; then unlink "$temporary_path"; fi' RETURN
  "$binary" --connected-shard \
    "$field_modulus" "$ell" "$degree" "$index" "$shard_count" "$max_candidates" \
    >"$temporary_path"
  mv "$temporary_path" "$output_path"
  trap - RETURN
}

export -f run_one
export binary output_dir field_modulus ell degree shard_count max_candidates

last_index=$((shard_count - 1))
seq "$first_index" "$index_stride" "$last_index" \
  | xargs -r -P "$parallelism" -n 1 bash -c 'set -euo pipefail; run_one "$1"' _
