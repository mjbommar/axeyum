#!/usr/bin/env bash
# A/B of two axeyum binaries on the same file, back to back on the same cores,
# alternating which arm goes first so any drift hits both equally.
# Usage: ab.sh <tag> <list> <out.tsv> <cores> <budget_s>
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; BUDGET="${5:-10}"
BASE=/nas3/data/axeyum/harness/dt-divisions/bin/smtcomp_cli.base
NEW=/nas3/data/axeyum/harness/dt-divisions/bin/smtcomp_cli.guard
for b in "$BASE" "$NEW"; do [ -x "$b" ] || { echo "ABORT $TAG: $b missing"; exit 2; }; done
VLIM=$((8 * 1024 * 1024))

run() { # $1 binary  $2 file -> "verdict<TAB>giveup"
  local raw rc v g
  raw=$(timeout $((BUDGET + 16)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000)) --trace" \
          "$1" "$2" 2>&1)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*')
  [ "$rc" = 124 ] && g="WRAPPER-KILLED"
  [ "$rc" = 134 ] && g="RC134-ABORT"
  printf '%s\t%s' "${v:-unknown}" "${g:-none}"
}

printf 'file\tbase\tbase_giveup\tguard\tguard_giveup\tstatus\n' > "$OUT"
i=0
while read -r f; do
  i=$((i + 1))
  if [ $((i % 2)) = 0 ]; then b=$(run "$BASE" "$f"); n=$(run "$NEW" "$f")
  else                        n=$(run "$NEW" "$f");  b=$(run "$BASE" "$f"); fi
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\t%s\t%s\n' "$(basename "$f")" "$b" "$n" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
