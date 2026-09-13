#!/usr/bin/env bash
# ADR-1966 per-file A/B: the SAME binary with and without the decline guards,
# run BACK TO BACK on ONE pinned physical core, with the arm order ALTERNATING
# per file so neither arm systematically benefits from a cold or warm page
# cache and ambient drift cancels in the difference.
#
# `load` is sampled per file and recorded, because the same commit on the same
# machine has moved a division's verdict count by 23 under load alone; a row
# whose two arms saw very different load is not a comparison.
#
# Usage: ab-run.sh <base-bin> <fix-bin> <tag> <pinned-list> <out.tsv> <core>
# Env:   BUDGET (s, default 10), HEADROOM (s, default 8)
set -u
BASE="$1"; FIX="$2"; TAG="$3"; LIST="$4"; OUT="$5"; PIN="$6"
BUDGET="${BUDGET:-10}"
HEADROOM="${HEADROOM:-8}"
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

for b in "$BASE" "$FIX"; do
  [ -x "$b" ] || { echo "ABORT $TAG: $b missing"; exit 2; }
done

run_one() {
  timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
    bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
    "$1" "$2" 2>/dev/null
}

verdict() { printf '%s\n' "$1" | grep -m1 -oE '^(sat|unsat|unknown)$'; }
giveup()  { printf '%s\n' "$1" | grep -m1 -oE 'give-up kind=[^ ]+' | cut -d= -f2; }
attempts(){ printf '%s\n' "$1" | grep -m1 -oE 'attempts=[0-9]+' | cut -d= -f2; }
detail()  { printf '%s\n' "$1" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ' | cut -c1-200; }

printf 'file\tbase_v\tbase_kind\tbase_att\tfix_v\tfix_kind\tfix_att\tload\tbase_detail\tfix_detail\n' > "$OUT"
n=0
while read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  load=$(cut -d' ' -f1 /proc/loadavg)
  if [ $((n % 2)) -eq 1 ]; then
    rb=$(run_one "$BASE" "$f"); rf=$(run_one "$FIX" "$f")
  else
    rf=$(run_one "$FIX" "$f");  rb=$(run_one "$BASE" "$f")
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" \
    "$(verdict "$rb")" "$(giveup "$rb")" "$(attempts "$rb")" \
    "$(verdict "$rf")" "$(giveup "$rf")" "$(attempts "$rf")" \
    "$load" "$(detail "$rb")" "$(detail "$rf")" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files budget=${BUDGET}s core=$PIN"
