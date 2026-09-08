#!/usr/bin/env bash
# Runs `smtcomp_cli --trace-json` over a committed parity list and appends every
# run's span log to one JSON Lines file.
#
# One file at a time, deliberately. The point of a span log is per-stage timing,
# and a host running sixteen solves at once measures the memory bus. A sweep
# that finishes four times faster and cannot be compared against the next one is
# not a saving.
#
# Usage:
#   scripts/span-log-sweep.sh <division> <out.jsonl> [limit] [timeout-ms]
#
# Environment:
#   AXEYUM_SPAN_BIN   the binary (default target/release/examples/smtcomp_cli)
#   AXEYUM_SPAN_LIST  the file list (default bench-results/parity-lists/<div>.txt)
#
# The host and the solver commit are stamped into every run header, because a
# span log that does not say which machine and which build produced it cannot be
# compared with the next one and will be anyway.
set -euo pipefail

division="${1:?usage: span-log-sweep.sh <division> <out.jsonl> [limit] [timeout-ms]}"
out="${2:?usage: span-log-sweep.sh <division> <out.jsonl> [limit] [timeout-ms]}"
limit="${3:-60}"
timeout_ms="${4:-24000}"

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
bin="${AXEYUM_SPAN_BIN:-$repo/target/release/examples/smtcomp_cli}"
list="${AXEYUM_SPAN_LIST:-$repo/bench-results/parity-lists/$division.txt}"

[ -x "$bin" ] || { echo "no binary at $bin" >&2; exit 2; }
[ -r "$list" ] || { echo "no list at $list" >&2; exit 2; }

AXEYUM_TRACE_HOST="$(hostname -s)"
AXEYUM_TRACE_COMMIT="$(git -C "$repo" rev-parse --short HEAD)"
export AXEYUM_TRACE_HOST AXEYUM_TRACE_COMMIT

# Truncate once, here, rather than in the binary: the binary APPENDS so that a
# whole sweep lands in one file, which means exactly one place may clear it.
: > "$out"

count=0
while IFS= read -r file; do
  [ -n "$file" ] || continue
  [ "$count" -lt "$limit" ] || break
  count=$((count + 1))
  if [ ! -r "$file" ]; then
    echo "missing: $file" >&2
    continue
  fi
  # The outer `timeout` is a backstop for a process the internal watchdog cannot
  # reach (an abort inside ingest, say). It is generous relative to the internal
  # budget on purpose: if it ever fires it means the internal watchdog did not,
  # and that is a finding, not a run to quietly discard.
  outer=$(( (timeout_ms / 1000) + 30 ))
  timeout -k 5 "${outer}s" "$bin" "$file" \
    --timeout-ms "$timeout_ms" \
    --memory-limit-mb 8192 \
    --trace-json "$out" >/dev/null 2>&1 || echo "outer-timeout-or-error: $file" >&2
done < "$list"

echo "$division: $count files -> $out ($(wc -l < "$out") span rows)" >&2
