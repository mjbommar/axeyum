#!/usr/bin/env bash
# Does a CERTIFIED certificate survive re-validation against a fresh parse?
#
# `smtcomp_cli --evidence` already answers this per file: it produces evidence,
# then re-checks against a FRESH PARSE of the original text — deliberately, so
# re-validation owes nothing to what the producing run kept in memory. It prints
# both halves:
#
#     ; evidence kind=unsat-term-level certified=1 recheck=na arena=ok
#
# `certified=1` with `arena=FAIL` is the defect: the producer claims a checkable
# object and the independent checker disagrees. That combination shipped on
# 2026-08-17 (a certificate storing instance `TermId`s) and had to be reverted.
#
# BOUNDED BY CONSTRUCTION, and that is the point. An earlier attempt swept the
# corpus IN-PROCESS, bounding each file with `rx.recv_timeout` on a worker
# thread. That bounds waiting, not work: Rust cannot kill a thread, so timed-out
# workers kept allocating and one test binary reached 125 GB anon-rss on a 123 GB
# box, taking the machine down with a kernel OOM. Here every file is a SUBPROCESS
# under `ulimit -v` and `timeout`, so an overrun is killed by the OS rather than
# abandoned, and files run ONE AT A TIME.
#
# Usage:
#   scripts/check-evidence-portability.sh [--limit N] [--mem-mb M] [--secs S] [ROOT ...]
#
# Exit 1 only on a genuine `certified=1 / arena=FAIL`. Timeouts, memory kills and
# undecided files are COVERAGE GAPS, reported and not failures — this asks
# whether the certificates we produce are portable, never how many we produce.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

limit=40; mem_mb=4096; secs=20; roots=()
while [ $# -gt 0 ]; do
  case "$1" in
    --limit) limit="$2"; shift 2;;
    --mem-mb) mem_mb="$2"; shift 2;;
    --secs) secs="$2"; shift 2;;
    *) roots+=("$1"); shift;;
  esac
done
[ ${#roots[@]} -eq 0 ] && roots=(corpus/regression artifacts/facts/smt2)

cli=target/release/examples/smtcomp_cli
if [ ! -x "$cli" ]; then
  echo "portability: building $cli (one bounded job)"
  cargo build --release -q -p axeyum-bench --example smtcomp_cli || exit 2
fi

files=$(find "${roots[@]}" -name '*.smt2' -type f 2>/dev/null | sort | head -n "$limit")
[ -z "$files" ] && { echo "portability: no .smt2 under ${roots[*]}" >&2; exit 2; }

total=0; certified=0; failed=0; gaps=0
declare -A kinds
violations=()

while IFS= read -r f; do
  [ -n "$f" ] || continue
  total=$((total + 1))
  # Subprocess + address-space cap + wall clock. The cap is what the earlier
  # in-process attempt lacked.
  line=$( ulimit -v $((mem_mb * 1024)) 2>/dev/null
          timeout "${secs}s" "$cli" --evidence "$f" 2>/dev/null | grep -m1 '^; evidence' )
  if [ -z "$line" ]; then gaps=$((gaps + 1)); continue; fi
  kind=$(sed -n 's/.*kind=\([^ ]*\).*/\1/p' <<<"$line")
  cert=$(sed -n 's/.*certified=\([^ ]*\).*/\1/p' <<<"$line")
  arena=$(sed -n 's/.*arena=\([^ ]*\).*/\1/p' <<<"$line")
  [ -n "$kind" ] && kinds["$kind"]=$(( ${kinds["$kind"]:-0} + 1 ))
  if [ "$cert" = "1" ]; then
    certified=$((certified + 1))
    if [ "$arena" = "FAIL" ]; then
      failed=$((failed + 1))
      violations+=("$f  kind=$kind  certified=1 arena=FAIL")
    fi
  fi
done <<<"$files"

echo
echo "PORTABILITY|files=$total|certified=$certified|arena_fail=$failed|no_evidence_line=$gaps|kinds=${#kinds[@]}"
for k in $(printf '%s\n' "${!kinds[@]}" | sort); do printf '  %5d  %s\n' "${kinds[$k]}" "$k"; done

if [ "$failed" -gt 0 ]; then
  echo
  echo "portability: $failed certificate(s) claim certified=1 and FAIL an independent re-parse:" >&2
  printf '    %s\n' "${violations[@]}" >&2
  echo "  That is the producer and the checker disagreeing about an object that IS present." >&2
  exit 1
fi
echo "portability: OK — every certified certificate here survived a fresh-parse re-check"
