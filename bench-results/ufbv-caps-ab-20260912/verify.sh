#!/usr/bin/env bash
# Re-verify every NEWLY DECIDED file against both references and its declared
# `:status`.  Not inherited from the board TSV -- re-run, because a converted
# file is the claim this lane is making and a claim should not rest on a
# measurement taken of a different binary.
#
# Units differ and are set accordingly: `z3 -T:<SECONDS>`,
# `cvc5 --tlimit <MILLISECONDS>`.
#
# Usage: verify.sh <list-of-absolute-paths> <envspec-or-empty> <out.tsv> <pin>
set -u
BUDGET=24
HEADROOM=16
LIST="$1"; ENVS="$2"; OUT="$3"; PIN="$4"
AX=${AXEYUM_CAPS_BIN:-/nas3/data/axeyum/harness/ufbv-caps/bin/smtcomp_cli}
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

for b in "$AX" "$Z3" "$CVC5"; do
  [ -x "$b" ] || { echo "ABORT: $b missing"; exit 2; }
done

envargs=()
if [ -n "$ENVS" ]; then
  IFS=',' read -ra kv <<< "$ENVS"
  for e in "${kv[@]}"; do envargs+=("$e"); done
fi

printf 'file\taxeyum\tax_s\tax_k\tz3\tz3_s\tz3_k\tcvc5\tcvc5_s\tcvc5_k\tstatus\tlever_refused\n' > "$OUT"
i=0
while read -r f; do
  i=$((i + 1))
  refused=no
  run() {
    local t0 t1 raw rc v k err
    t0=$(date +%s.%N); err=$(mktemp)
    case "$1" in
      axeyum) raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
                env -u AXEYUM_UFBV_MAX_THEORY_ATOMS -u AXEYUM_UFBV_MAX_INPUT_DAG_NODES \
                "${envargs[@]}" \
                bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
                "$AX" "$2" 2>"$err")
              grep -q 'is not a valid\|set but empty' "$err" && refused=yes ;;
      z3)     raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
                bash -c "ulimit -v $VLIM; exec \"\$0\" -T:$BUDGET \"\$1\"" \
                "$Z3" "$2" 2>"$err") ;;
      cvc5)   raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
                bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit=$((BUDGET * 1000)) \"\$1\"" \
                "$CVC5" "$2" 2>"$err") ;;
    esac
    rc=$?
    rm -f "$err"
    t1=$(date +%s.%N)
    v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
    k=ok
    [ "$rc" = 124 ] && k=wrapper-killed
    [ "$rc" = 134 ] && k=rc134
    [ "$rc" = 137 ] && k=sigkill
    printf '%s\t%.2f\t%s' "${v:-unknown}" "$(echo "$t1-$t0" | bc)" "$k"
  }
  case $((i % 3)) in
    0) order=(axeyum z3 cvc5) ;;
    1) order=(z3 cvc5 axeyum) ;;
    2) order=(cvc5 axeyum z3) ;;
  esac
  declare -A R=()
  for s in "${order[@]}"; do R[$s]=$(run "$s" "$f"); done
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${R[axeyum]}" "${R[z3]}" "${R[cvc5]}" "${st:-none}" "$refused" >> "$OUT"
done < "$LIST"
echo "VERIFY-DONE $(($(wc -l < "$OUT") - 1)) rows"
