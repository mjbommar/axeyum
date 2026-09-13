#!/usr/bin/env bash
# Re-check, at a MUCH larger budget, every verdict WE produced that nothing
# else confirmed.
#
# Why this exists.  The zero-disagreement check compares our verdict against
# three things: the benchmark's declared `:status`, z3, and cvc5.  A verdict
# none of the three can speak to contributes a zero to that check while being
# confirmed by nothing -- and on this board that is not hypothetical: ABV
# declares `:status unknown` on 199 of its 200 sampled files, and the 4 files we
# decide there are 4 that BOTH references return `unknown` on at 24 s.  So ABV's
# "0 disagreements" rests on 0 comparable verdicts.  Reporting that as a zero
# alongside AUFLIRA's 10-of-10 would be the vacuous-checker failure this
# repository keeps paying for.
#
# A file we decide and a reference does not is also the most valuable thing on
# the board IF it is right, and the worst thing on it if it is wrong.  Either
# way it must not stay unexamined.  So: run both references again at 600 s --
# 25x the board budget -- on exactly those rows.  Three outcomes, all useful:
#
#   a reference now AGREES  -> the verdict is confirmed, and the 24 s row was a
#                              budget difference rather than a capability one
#   a reference now DISAGREES -> a wrong answer, the most important possible
#                              finding, reported loudly
#   both still `unknown`    -> the verdict remains unconfirmed, and the board
#                              must SAY SO rather than count it in a zero
#
# This does not change the board rows.  The board is a 24 s measurement and
# stays one; this is a separate soundness artifact with its own budget, written
# to its own file.
#
# Usage: confirm-unchecked.sh <out.tsv> <cores> <DIV.tsv> [<DIV.tsv> ...]
set -u
BUDGET=600
HEADROOM=60
OUT="$1"; PIN="$2"; shift 2
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

for b in "$Z3" "$CVC5"; do
  [ -x "$b" ] || { echo "ABORT: $b missing"; exit 2; }
done

run() { # $1 solver  $2 file -> "verdict<TAB>seconds<TAB>flag"
  local t0 t1 raw rc v k
  t0=$(date +%s.%N)
  case "$1" in
    z3)   raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" -T:$BUDGET \"\$1\"" "$Z3" "$2" 2>/dev/null) ;;
    cvc5) raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit=$((BUDGET * 1000)) \"\$1\"" \
            "$CVC5" "$2" 2>/dev/null) ;;
  esac
  rc=$?
  t1=$(date +%s.%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  k=ok
  [ "$rc" = 124 ] && k=wrapper-killed
  [ "$rc" = 134 ] && k=rc134
  [ "$rc" = 137 ] && k=sigkill
  printf '%s\t%.1f\t%s' "${v:-unknown}" "$(echo "$t1-$t0" | bc)" "$k"
}

printf 'division\tfile\tours\tz3_600\tz3_s\tz3_k\tcvc5_600\tcvc5_s\tcvc5_k\tstatus\tverdict\n' > "$OUT"
n=0
for tsv in "$@"; do
  div=$(basename "$tsv" .tsv)
  # Select rows where WE decided and NOTHING confirmed it: no usable :status,
  # and neither reference decided at the board budget.
  while IFS=$'\t' read -r f ours _axs _axk z3v _z3s _z3k cvv _cvs _cvk st; do
    case "$ours" in sat|unsat) ;; *) continue ;; esac
    case "$st" in sat|unsat) continue ;; esac
    case "$z3v" in sat|unsat) continue ;; esac
    case "$cvv" in sat|unsat) continue ;; esac
    n=$((n + 1))
    z=$(run z3 "$CORPUS$f")
    c=$(run cvc5 "$CORPUS$f")
    zv=$(printf '%s' "$z" | cut -f1); cv=$(printf '%s' "$c" | cut -f1)
    verdict=UNCONFIRMED
    case "$zv" in sat|unsat) [ "$zv" = "$ours" ] && verdict=CONFIRMED || verdict=DISAGREE ;; esac
    if [ "$verdict" = UNCONFIRMED ] || [ "$verdict" = CONFIRMED ]; then
      case "$cv" in
        sat|unsat) [ "$cv" = "$ours" ] && verdict=CONFIRMED || verdict=DISAGREE ;;
      esac
    fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$div" "$f" "$ours" "$z" "$c" "$st" "$verdict" >> "$OUT"
  done < <(tail -n +2 "$tsv")
done
echo "CONFIRM-DONE $n rows -> $OUT"
d=$(awk -F'\t' 'NR>1 && $11=="DISAGREE"' "$OUT" | wc -l)
u=$(awk -F'\t' 'NR>1 && $11=="UNCONFIRMED"' "$OUT" | wc -l)
c=$(awk -F'\t' 'NR>1 && $11=="CONFIRMED"' "$OUT" | wc -l)
echo "CONFIRMED $c   UNCONFIRMED $u   DISAGREE $d"
# The exit status depends on the FINDING: a disagreement is a wrong answer.
[ "$d" = 0 ] || { echo "!! WRONG ANSWER: $d verdict(s) contradicted at ${BUDGET}s"; exit 1; }
exit 0
