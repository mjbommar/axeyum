#!/usr/bin/env bash
# The mutation control for the linear `distinct` encoding (ADR-2000).
#
# ADR-1976 measured that a SAT-side REFERENCE control is VACUOUS: z3 and cvc5
# agreed with a deliberately broken rewrite on 5 of 5 satisfiable files, because
# an underconstrained `sat` stays `sat`. The lesson generalises to a rule about
# DIRECTION, not about avoiding `sat` files: aim each mutant where it has
# somewhere to go.
#
#   * a WEAKENING mutant can only be caught on an `unsat`;
#   * a STRENGTHENING mutant can only be caught on a `sat`.
#
# FOUR arms over the same file list, on one pinned core:
#
#   base      env -u AXEYUM_DISTINCT_LINEAR            the shipped pairwise path
#   arm       AXEYUM_DISTINCT_LINEAR=on:2              the candidate
#   vacuous   AXEYUM_DISTINCT_LINEAR=mutant:vacuous:2  every index 0 -- the
#                                                       encoding constrains
#                                                       nothing (WEAKER)
#   shared    AXEYUM_DISTINCT_LINEAR=mutant:shared:2   one injection for the
#                                                       whole script instead of
#                                                       one per application
#                                                       (STRONGER wherever two
#                                                       applications share an
#                                                       argument)
#
# The threshold is lowered to 2 on purpose. At the shipped threshold (363) the
# rewrite fires only on the 356 over-cap files, and those are mostly `unknown`
# at 24 s -- a population that cannot distinguish ANY encoding. At `2` the
# rewrite fires on ordinary benchmarks this solver decides, which is the only
# way the control can fail.
#
# THE EXIT STATUS DEPENDS ON ALL THREE FINDINGS:
#
#   1. any row where `base` and `arm` are BOTH DECIDED and DIFFER fails the run
#      -- that is a wrong verdict. A row that moved between decided and
#      `unknown` is reported, not failed: `unknown` is a first-class result here
#      and a no-opinion is not a contradiction (ADR-1957).
#   2. a weakening mutant that never CONTRADICTS an `unsat` fails the run;
#   3. a strengthening mutant that never CONTRADICTS a `sat` fails the run.
#
# (2) and (3) are the important ones. A broken arm that agrees with the shipped
# arm everywhere does not mean the encoding is exact; it means the population
# cannot tell any two encodings apart, and the zero in (1) is then not evidence.
#
# Usage: mutant-control.sh <list> <out.tsv> <cores> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

one() {  # $1 = lever value, or "" for the unset (shipped) arm; $2 = file
  local raw
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_DISTINCT_LINEAR timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  else
    raw=$(AXEYUM_DISTINCT_LINEAR="$1" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$2" 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none
}

printf 'file\tstatus\tbase\tarm\tvacuous\tshared\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  b=$(one "" "$f")
  a=$(one "on:2" "$f")
  v=$(one "mutant:vacuous:2" "$f")
  h=$(one "mutant:shared:2" "$f")
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "${st:-none}" "$b" "$a" "$v" "$h" >> "$OUT"
done < "$LIST"

# --- the findings, classified ---------------------------------------------
#
# ADR-1957: a no-opinion is not an agreement. `unknown` is a first-class result
# here, so an arm that answers `unknown` where the other decided has NOT
# contradicted it -- it has lost (or gained) a verdict. The two are counted
# separately and only the first can fail the run.
#
#   hard   both arms decided, and they DIFFER      -- a wrong verdict. Must be 0.
#   lost   base decided, arm `unknown`             -- a capability regression.
#   gained base `unknown`, arm decided             -- a capability gain.
hard=$(awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat") && ($4=="sat"||$4=="unsat") && $3!=$4' "$OUT" | wc -l)
lost=$(awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat") && !($4=="sat"||$4=="unsat")' "$OUT" | wc -l)
gained=$(awk -F'\t' 'NR>1 && !($3=="sat"||$3=="unsat") && ($4=="sat"||$4=="unsat")' "$OUT" | wc -l)
base_unsat=$(awk -F'\t' 'NR>1 && $3 == "unsat"' "$OUT" | wc -l)
base_sat=$(awk -F'\t' 'NR>1 && $3 == "sat"' "$OUT" | wc -l)
# A mutant FLIP that counts is a DECIDED contradiction: the broken encoding
# answers the opposite verdict, not merely `unknown`. An `unknown` would leave
# open whether the mutant is wrong or just slower.
vac_flips=$(awk -F'\t' 'NR>1 && $3 == "unsat" && $5 == "sat"' "$OUT" | wc -l)
shr_flips=$(awk -F'\t' 'NR>1 && $3 == "sat" && $6 == "unsat"' "$OUT" | wc -l)

echo "MUTANT-CONTROL rows=$n base_unsat=$base_unsat base_sat=$base_sat"
echo "MUTANT-CONTROL hard_disagreements=$hard lost=$lost gained=$gained"
echo "MUTANT-CONTROL vacuous_decided_flips=$vac_flips shared_decided_flips=$shr_flips"
rc=0
if [ "$hard" -ne 0 ]; then
  echo "FAIL: the candidate encoding CONTRADICTED the shipped one on $hard row(s):"
  awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat") && ($4=="sat"||$4=="unsat") && $3!=$4' "$OUT"
  rc=1
fi
if [ "$lost" -ne 0 ]; then
  echo "NOTE: $lost row(s) decided by the shipped arm became \`unknown\` under the"
  echo "      candidate. Not a wrong verdict; a capability cost of the encoding at"
  echo "      this threshold, and the reason the SHIPPED threshold is the pairwise"
  echo "      cap rather than 2:"
  awk -F'\t' 'NR>1 && ($3=="sat"||$3=="unsat") && !($4=="sat"||$4=="unsat")' "$OUT"
fi
if [ "$base_unsat" -eq 0 ]; then
  echo "FAIL: no row was decided unsat by the shipped arm -- the weakening mutant is blind"
  rc=1
elif [ "$vac_flips" -eq 0 ]; then
  echo "FAIL: the WEAKENING mutant produced no DECIDED contradiction on $base_unsat unsat row(s)."
  echo "      The zero above is therefore not evidence of exactness."
  rc=1
fi
if [ "$base_sat" -eq 0 ]; then
  echo "FAIL: no row was decided sat by the shipped arm -- the strengthening mutant is blind"
  rc=1
elif [ "$shr_flips" -eq 0 ]; then
  echo "FAIL: the STRENGTHENING mutant produced no DECIDED contradiction on $base_sat sat row(s)."
  echo "      The freshness guard is untested by this population."
  rc=1
fi
exit "$rc"
