#!/usr/bin/env bash
# UFLIA-TRACE -- reference trace on one list of .smt2 paths.
#
#   ref-run.sh <list> <outdir> <pin> [budget_s]
#
# Four arms per file, each answering a question a verdict cannot:
#
#   z3-default   `-st smt.qi.profile=true`   verdict + :quant-instantiations +
#                :max-generation, i.e. HOW MANY instances the refutation cost
#                and how deep the deepest one was nested.
#   z3-noqi      `-st smt.mbqi=false`        is this core E-MATCHING-ONLY, or
#                does z3 need model-based instantiation for it?
#   z3-proof     `:produce-proofs` + `(get-proof)`   the `(_ quant-inst t1..tn)`
#                rules NAME the ground terms z3 substituted. This is the only
#                arm that can say WHICH instance, as opposed to how many.
#   cvc5         `--stats --dump-instantiations`     a second reference, so a
#                single engine's habits are not read as "what a solver needs".
#
# A missing verdict line is recorded as NOVERDICT and never as a timeout: on
# `-T:` expiry z3 prints `timeout`, and conflating the two makes a crash
# indistinguishable from an exhausted clock.
set -u
LIST="$1"; OUTDIR="$2"; PIN="$3"; BUDGET="${4:-60}"
CVC5=${CVC5:-/nas3/data/axeyum/harness/bin/cvc5}
mkdir -p "$OUTDIR/proof"
OUT="$OUTDIR/ref.$PIN.tsv"

printf 'core\tz3\tz3_ms\tz3_qinst\tz3_maxgen\tz3_noqi\tz3_noqi_ms\tz3_proof\tproof_qinst\tcvc5\tcvc5_ms\tcvc5_inst\n' > "$OUT"
while IFS= read -r p; do
  [ -n "$p" ] || continue
  b="$(basename "$p")"

  t0=$(date +%s%N)
  a=$(taskset -c "$PIN" timeout $((BUDGET + 20)) z3 -T:$BUDGET -st smt.qi.profile=true "$p" 2>&1)
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || true)
  qi=$(printf '%s\n' "$a" | grep -oE ':quant-instantiations +[0-9]+' | grep -oE '[0-9]+$' || true)
  mg=$(printf '%s\n' "$a" | grep -oE ':max-generation +[0-9]+' | grep -oE '[0-9]+$' || true)
  ms=$(( (t1 - t0) / 1000000 ))

  t0=$(date +%s%N)
  a2=$(taskset -c "$PIN" timeout $((BUDGET + 20)) z3 -T:$BUDGET -st smt.mbqi=false "$p" 2>&1)
  t1=$(date +%s%N)
  v2=$(printf '%s\n' "$a2" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || true)
  ms2=$(( (t1 - t0) / 1000000 ))

  # The proof arm runs from a REWRITTEN file: `:produce-proofs` must be set
  # before any assertion, and z3 silently ignores it otherwise.
  tmp="$OUTDIR/proof/$b.query"
  { echo '(set-option :produce-proofs true)'; cat "$p"; echo '(get-proof)'; } > "$tmp"
  a3=$(taskset -c "$PIN" timeout $((BUDGET + 20)) z3 -T:$BUDGET -smt2 "$tmp" 2>&1)
  v3=$(printf '%s\n' "$a3" | grep -m1 -oE '^(sat|unsat|unknown|timeout)$' || true)
  if [ "${v3:-}" = unsat ]; then
    printf '%s\n' "$a3" > "$OUTDIR/proof/$b.proof"
    pq=$(printf '%s\n' "$a3" | grep -oE 'quant-inst' | wc -l | tr -d ' ')
  else
    pq=0
  fi
  rm -f "$tmp"

  t0=$(date +%s%N)
  if [ -x "$CVC5" ]; then
    a4=$(taskset -c "$PIN" timeout $((BUDGET + 20)) "$CVC5" --tlimit=$((BUDGET * 1000)) \
           --stats --dump-instantiations "$p" 2>&1)
    v4=$(printf '%s\n' "$a4" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
    ci=$(printf '%s\n' "$a4" | grep -cE '^\(instantiation|^ *\(' || true)
  else
    a4=""; v4=NOBIN; ci=0
  fi
  t1=$(date +%s%N)
  ms4=$(( (t1 - t0) / 1000000 ))

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$b" "${v:-NOVERDICT}" "$ms" "${qi:-0}" "${mg:-0}" \
    "${v2:-NOVERDICT}" "$ms2" "${v3:-NOVERDICT}" "$pq" \
    "${v4:-NOVERDICT}" "$ms4" "${ci:-0}" >> "$OUT"
done < "$LIST"
echo "DONE $OUT"
