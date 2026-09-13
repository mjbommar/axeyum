#!/usr/bin/env bash
# The QF_UFBV cap A/B.
#
# Every ARM runs on the SAME FILE back to back on the SAME pinned physical core
# before any arm starts the next file, and the arm ORDER ROTATES with the file
# index.  Ambient load then cancels in the difference between arms on one file,
# which is the only comparison this experiment makes.  Absolute wall numbers
# from a loaded box are not comparable across files and are not quoted as such.
#
# Same envelope as the board and the census it is answering: 24 s wall, 8 GiB
# address space, `--trace`, wrapper timeout 24+16 s.
#
# The lever refuses a malformed value by PANICKING, and the CLI's worker-thread
# panic handling turns that into `unknown` on stdout -- which reads exactly like
# "the raised cap did not help".  So every row records whether the refusal text
# appeared on stderr, and the summarizer aborts if any row has it.
#
# Usage: ab-run.sh <shard-index> <shard-count> <list> <pin> <out.tsv> <arm>...
#   arm is NAME:ENVSPEC  where ENVSPEC is empty for the baseline or
#   VAR=VAL[,VAR=VAL] otherwise.
set -u
BUDGET=24
HEADROOM=16
SHARD="$1"; NSHARD="$2"; LIST="$3"; PIN="$4"; OUT="$5"; shift 5
ARMS=("$@")
AX=${AXEYUM_CAPS_BIN:-/nas3/data/axeyum/harness/ufbv-caps/bin/smtcomp_cli}
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT shard $SHARD: $AX missing"; exit 2; }

# Live probe: the binary must DECIDE something before any row is written.  A
# missing or broken binary otherwise scores a silent all-unknown that reads
# exactly like a result.
probe=$(printf '(set-logic QF_BV)\n(declare-const x (_ BitVec 4))\n(assert (= x (_ bv3 4)))\n(check-sat)\n' > /tmp/ufbvcaps-probe-$$.smt2; \
        timeout 30 "$AX" /tmp/ufbvcaps-probe-$$.smt2 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
rm -f /tmp/ufbvcaps-probe-$$.smt2
[ "$probe" = "sat" ] || { echo "ABORT shard $SHARD: live probe returned '${probe:-nothing}', not sat"; exit 2; }

printf 'file\tarm\tverdict\trc\twall_ms\tattempts\tdecided_by\tbound_by\tbound_ms\ttotal_ms\tgiveup\tlever_refused\n' > "$OUT"

idx=-1
while read -r f; do
  idx=$((idx + 1))
  [ $((idx % NSHARD)) -eq "$SHARD" ] || continue
  n=${#ARMS[@]}
  for k in $(seq 0 $((n - 1))); do
    # rotate the arm order with the file index
    j=$(((k + idx) % n))
    spec="${ARMS[$j]}"
    name="${spec%%:*}"
    envs="${spec#*:}"
    envargs=()
    if [ -n "$envs" ]; then
      IFS=',' read -ra kv <<< "$envs"
      for e in "${kv[@]}"; do envargs+=("$e"); done
    fi
    t0=$(date +%s%N)
    err=$(mktemp)
    raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env -u AXEYUM_UFBV_MAX_THEORY_ATOMS -u AXEYUM_UFBV_MAX_INPUT_DAG_NODES \
            "${envargs[@]}" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>"$err")
    rc=$?
    t1=$(date +%s%N)
    wall=$(((t1 - t0) / 1000000))
    refused=no
    if grep -q 'is not a valid\|set but empty' "$err"; then refused=yes; fi
    rm -f "$err"
    v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
    rl=$(printf '%s\n' "$raw" | grep -m1 -oE '; (partial )?route decided_by=.*')
    fld() { printf '%s\n' "$rl" | grep -oE "$1=[^ ]+" | head -1 | cut -d= -f2-; }
    att=$(fld attempts); dec=$(fld decided_by); bnd=$(fld bound_by)
    bms=$(fld bound_ms); tms=$(fld total_ms)
    g=$(printf '%s\n' "$raw" | grep -m1 -oE 'give-up kind=[^ ]+ detail=.*' | tr '\t' ' ')
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "${f#"$CORPUS"}" "$name" "${v:-none}" "$rc" "$wall" "${att:-NOROUTE}" \
      "${dec:-na}" "${bnd:-na}" "${bms:-na}" "${tms:-na}" "${g:-none}" "$refused" >> "$OUT"
  done
done < "$LIST"
echo "AB-DONE shard $SHARD $(($(wc -l < "$OUT") - 1)) rows"
