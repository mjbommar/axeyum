#!/bin/bash
# S7b before/after on the two ADR-1701 slice-1 scoring populations.
# Arms interleaved per file; taskset -c 0-7; 24 s budget with an external
# hard-kill backstop.
set -u
BEFORE=$HOME/s7b-before/target/release/examples/smtcomp_cli
AFTER=$HOME/s7b-after/target/release/examples/smtcomp_cli
POP=$HOME/s7b-after/bench-results/adr-1701-slice-1-20260905
OUT=$HOME/s7b-populations
mkdir -p "$OUT"

echo "before sha256: $(sha256sum "$BEFORE")"
echo "after  sha256: $(sha256sum "$AFTER")"

run_one() { # $1 = binary, $2 = file -> prints "verdict\tms"
  local start end verdict
  # `date +%s%3N` is NOT honoured on this host -- it yields nine digits, i.e.
  # nanoseconds -- so read nanoseconds explicitly and divide. Measured rather
  # than assumed: the first run recorded 1,213,398,102 "ms" for a 1.2 s solve.
  start=$(date +%s%N)
  verdict=$(timeout -k 2 30s taskset -c 0-7 "$1" "$2" --timeout-ms 24000 2>/dev/null | grep -E '^(sat|unsat|unknown)$' | tail -1)
  end=$(date +%s%N)
  [ -z "$verdict" ] && verdict=unknown
  printf '%s\t%s' "$verdict" "$(( (end - start) / 1000000 ))"
}

for pop in qf_idl qf_lra; do
  src="$POP/${pop}_population.tsv"
  dst="$OUT/${pop}_before_after.tsv"
  printf 'file\tdeclared\tbefore_verdict\tbefore_ms\tafter_verdict\tafter_ms\n' > "$dst"
  tail -n +2 "$src" | while IFS=$'\t' read -r file declared rest; do
    b=$(run_one "$BEFORE" "$file")
    a=$(run_one "$AFTER" "$file")
    printf '%s\t%s\t%s\t%s\n' "$file" "$declared" "$b" "$a" >> "$dst"
    echo "done $(basename "$file") declared=$declared before=$b after=$a"
  done
  echo "=== $pop complete ==="
done
echo POPULATIONS_DONE
