#!/usr/bin/env bash
# Re-run a handful of named files N times per arm, interleaved, on one pinned
# core of a quiet box.
#
# A single pairing near the budget is not evidence: a 16 s baseline against a
# 24 s budget flips under ambient load, and that produced a false convert in
# this repository the day before. Every loss and every surprising gain gets
# replicated before it is reported, and BOTH the raw and the replicated numbers
# are published.
#
# Usage: replicate.sh <list> <reps> <out.tsv> <pin> <arm>...
set -u
BUDGET=24
HEADROOM=16
LIST="$1"; REPS="$2"; OUT="$3"; PIN="$4"; shift 4
ARMS=("$@")
AX=/nas3/data/axeyum/harness/ufbv-caps/bin/smtcomp_cli
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

printf 'file\trep\tarm\tverdict\trc\twall_ms\tgiveup\tlever_refused\n' > "$OUT"
for rep in $(seq 1 "$REPS"); do
  while read -r f; do
    n=${#ARMS[@]}
    for k in $(seq 0 $((n - 1))); do
      j=$(((k + rep) % n))
      spec="${ARMS[$j]}"; name="${spec%%:*}"; envs="${spec#*:}"
      envargs=()
      if [ -n "$envs" ]; then
        IFS=',' read -ra kv <<< "$envs"
        for e in "${kv[@]}"; do envargs+=("$e"); done
      fi
      t0=$(date +%s%N); err=$(mktemp)
      raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
              env -u AXEYUM_UFBV_MAX_THEORY_ATOMS -u AXEYUM_UFBV_MAX_INPUT_DAG_NODES \
              "${envargs[@]}" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$f" 2>"$err")
      rc=$?; t1=$(date +%s%N)
      refused=no
      grep -q 'is not a valid\|set but empty' "$err" && refused=yes
      rm -f "$err"
      v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
      g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "${f#"$CORPUS"}" "$rep" "$name" "${v:-none}" "$rc" "$(((t1 - t0) / 1000000))" \
        "${g:-none}" "$refused" >> "$OUT"
    done
  done < "$LIST"
done
echo "REPLICATE-DONE $(($(wc -l < "$OUT") - 1)) rows"
