#!/usr/bin/env bash
# Drive the ADR-2121 A/B over three divisions, four shards each, one shard per
# pinned core. QF_NRA is the target division, QF_NIA shares the nonlinear code
# (so a regression there is the one a QF_NRA-only sweep would miss), and QF_LRA
# is the CONTROL: nothing linear goes anywhere near this route, so a mover there
# is a finding about the harness and not about the lever.
#
# Divisions run in sequence and shards in parallel, so the four cores carry one
# division at a time and the interleaved pairs stay on the same core.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="${1:?usage: ab-sweep.sh /path/to/smtcomp_cli}"
CORES=(1 9 3 11)

for div in qfnra qfnia qflra; do
  echo "=== $div ===" >&2
  pids=()
  for i in 0 1 2 3; do
    "$HERE/ab-run.sh" \
      --list "$HERE/shard$i-$div.txt" \
      --out "$HERE/ab-$div-shard$i.tsv" \
      --shard "$i" --core "${CORES[$i]}" \
      --binary "$BIN" --arm-b single-cell --budget-s 24 \
      > "$HERE/ab-$div-shard$i.log" 2>&1 &
    pids+=($!)
  done
  rc=0
  for p in "${pids[@]}"; do wait "$p" || rc=1; done
  echo "=== $div done (rc=$rc) ===" >&2
done
echo "ab-sweep: complete" >&2
