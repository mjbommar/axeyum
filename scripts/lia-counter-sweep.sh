#!/usr/bin/env bash
# Runs `smtcomp_cli --trace` over a committed benchmark list and keeps the
# `; lia …` / `; route …` lines, one log per file.
#
# WHY A SCRIPT AND NOT A LOOP IN A SHELL
# --------------------------------------
# The counters this collects are clock-free on purpose: a count is stable under
# host load where a wall time is not. But the run still records `bound_ms` from
# the route trail, and that number IS load-sensitive, so the parallelism is a
# parameter the log records rather than something the reader has to infer.
#
# Usage:
#   scripts/lia-counter-sweep.sh <list-file> <out-dir> [budget_s] [jobs]
#
# Writes <out-dir>/<n>.log per input line plus <out-dir>/index.tsv with
# (index, file, verdict, wall_ms).
set -uo pipefail

list="${1:?usage: lia-counter-sweep.sh <list-file> <out-dir> [budget_s] [jobs]}"
out="${2:?usage: lia-counter-sweep.sh <list-file> <out-dir> [budget_s] [jobs]}"
budget_s="${3:-24}"
jobs="${4:-6}"

bin="target/release/examples/smtcomp_cli"
if [[ ! -x "$bin" ]]; then
  echo "missing $bin -- build it first:" >&2
  echo "  scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli" >&2
  exit 2
fi

mkdir -p "$out"
: >"$out/index.tsv"
printf 'index\tfile\tverdict\twall_ms\n' >>"$out/index.tsv"

run_one() {
  local index="$1" file="$2"
  local log="$out/$index.log"
  local started ended verdict
  started=$(date +%s%3N)
  # `ulimit -v` matches the parity protocol's memory cap so a refusal here is
  # the same refusal the parity run would see.
  ( ulimit -v $((8 * 1024 * 1024)); timeout "$((budget_s + 6))" "$bin" "$file" \
      --timeout-ms "$((budget_s * 1000))" --trace ) >"$log" 2>&1
  ended=$(date +%s%3N)
  verdict=$(grep -E '^(sat|unsat|unknown)$' "$log" | tail -1)
  [[ -z "$verdict" ]] && verdict="aborted"
  printf '%s\t%s\t%s\t%s\n' "$index" "$file" "$verdict" "$((ended - started))" >>"$out/index.tsv"
}
export -f run_one
export out bin budget_s

index=0
pids=()
while IFS= read -r file; do
  [[ -z "$file" ]] && continue
  index=$((index + 1))
  run_one "$index" "$file" &
  pids+=("$!")
  while [[ "$(jobs -rp | wc -l)" -ge "$jobs" ]]; do
    wait -n 2>/dev/null || true
  done
done <"$list"
wait

echo "wrote $out ($index files, budget ${budget_s}s, jobs $jobs)"
