#!/usr/bin/env bash
# For each file in LIST, run ONE arm with `--trace` and print the reason the
# `nra-real-root` rung gave. This is the attribution ADR-2110 landed
# (`CadDecline`, 14 causes) read back on a population, so "the route declined"
# becomes "the route declined BECAUSE", which is the difference between a
# finding and a shrug.
#
# Usage: cause-scan.sh --binary PATH --list FILE --arm VALUE --out TSV
#                      [--core N] [--budget-s N] [--corpus-root DIR]
set -u

BIN=""; LIST=""; ARM=""; OUT=""; CORE=""; BUDGET_S=24
CORPUS_ROOT="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
VLIMIT_KB=$((8 * 1024 * 1024))

while [ $# -gt 0 ]; do
  case "$1" in
    --binary) BIN="$2"; shift 2 ;;
    --list) LIST="$2"; shift 2 ;;
    --arm) ARM="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    --core) CORE="$2"; shift 2 ;;
    --budget-s) BUDGET_S="$2"; shift 2 ;;
    --corpus-root) CORPUS_ROOT="$2"; shift 2 ;;
    *) echo "cause-scan: unknown argument $1" >&2; exit 2 ;;
  esac
done
for required in BIN LIST OUT; do
  if [ -z "${!required}" ]; then echo "cause-scan: --${required,,} required" >&2; exit 2; fi
done

printf 'file\tverdict\tnra_real_root_detail\n' > "$OUT"
n=0
while IFS= read -r rel; do
  [ -n "$rel" ] || continue
  n=$((n + 1))
  pinned=()
  [ -n "$CORE" ] && pinned=(taskset -c "$CORE")
  raw="$(AXEYUM_NRA_CAD="$ARM" "${pinned[@]}" timeout $((BUDGET_S + 6)) \
      bash -c "ulimit -v $VLIMIT_KB; exec '$BIN' '$CORPUS_ROOT/$rel' --timeout-ms $((BUDGET_S * 1000)) --trace" \
      2>/dev/null)" || true
  verdict="$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || printf 'none')"
  # The `nra-real-root` attempt. Read the OUTCOME first and the detail second:
  # an attempt that DECIDED carries no `detail` field at all, and the first
  # version of this script reported that missing field as "no nra-real-root
  # attempt in the trail" -- an empty grep read as a negative result, on the
  # three files where the route actually worked. The attempt's presence and its
  # outcome are now separate reads.
  attempt="$(printf '%s\n' "$raw" | grep -oE '\{"route":"nra-real-root"[^}]*\}' | head -1)"
  if [ -z "$attempt" ]; then
    detail="ABSENT: no nra-real-root attempt in the trail"
  else
    outcome="$(printf '%s\n' "$attempt" | grep -oE '"outcome":"[^"]*"' | head -1 | sed 's/^"outcome":"//; s/"$//')"
    d="$(printf '%s\n' "$attempt" | grep -oE '"detail":"[^"]*"' | head -1 | sed 's/^"detail":"//; s/"$//')"
    if [ -n "$d" ]; then detail="$outcome: $d"; else detail="$outcome"; fi
  fi
  printf '%s\t%s\t%s\n' "$rel" "$verdict" "$detail" >> "$OUT"
  echo "[cause $n] $verdict :: $detail" >&2
done < "$LIST"
echo "cause-scan: $n files -> $OUT" >&2
