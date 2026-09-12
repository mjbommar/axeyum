#!/usr/bin/env bash
# Re-run one file's two arms back to back, serially, N times, pinned to one core
# class, with nothing else of this lane's running. A single-pairing result under
# three-way parallelism is not a finding; this is.
set -u
# Pass the pinned binary as $AXEYUM_CLI; default is this checkout's release build.
CLI="${AXEYUM_CLI:-$(git -C "$(dirname "$0")" rev-parse --show-toplevel)/target/release/examples/smtcomp_cli}"
F="$1"
N="${2:-5}"
for i in $(seq 1 "$N"); do
  for arm in A B; do
    if [ "$arm" = A ]; then unset AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW
    else export AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=1; fi
    start=$(date +%s.%N)
    out=$(taskset -c 0-7 timeout -k 5 120 "$CLI" "$F" --timeout-ms 24000 2>&1)
    end=$(date +%s.%N)
    v=$(printf '%s\n' "$out" | grep -E '^(sat|unsat|unknown)$' | tail -1)
    printf '%s arm=%s verdict=%s wall=%.1f\n' "$i" "$arm" "${v:-none}" \
      "$(echo "$end - $start" | bc)"
  done
done
