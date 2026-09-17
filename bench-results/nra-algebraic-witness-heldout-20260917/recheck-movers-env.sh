#!/usr/bin/env bash
# `recheck-movers.sh` for an ENV-selected arm: ONE binary, TWO `AXEYUM_NRA_CAD`
# values.
#
# The sibling script takes two binaries and ABORTS when their SHAs match, which
# is the right guard there and an impossible one here -- an env A/B is one
# binary by construction. The corresponding guard is on the two ARM VALUES: if
# they are equal, or if either is a name the parser does not recognise (an
# unrecognised value silently resolves to the shipped default, so a typo turns
# the treatment into the control and reports a perfect null), this refuses.
#
# Everything else is the sibling's protocol verbatim, and for its reasons:
# three passes per arm, arms alternating WITHIN the passes so drift across the
# ~2.5 minutes a row takes does not land entirely on one arm, and a row
# classified only when all three agree.
#
#   STABLE-GAIN      A never decided, B decided 3/3
#   STABLE-LOSS      A decided 3/3, B never decided
#   BOTH-DECIDE      both 3/3
#   NEITHER-DECIDES  both 0/3
#   UNSTABLE         anything else -- reported as ambient, not as an effect
#
# Exit status per pass is its own column: `losses=0` by verdict has coexisted
# with new ABORTs underneath it (ADR-2045).
#
# Usage: recheck-movers-env.sh <list> <out.tsv> <cores> <binary> <armA> <armB> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ARM_A="$5"; ARM_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ "$ARM_A" = "$ARM_B" ] && { echo "ABORT: both arms are the SAME env value"; exit 2; }

# An unrecognised `AXEYUM_NRA_CAD` resolves to the shipped default WITHOUT any
# diagnostic, so a mistyped arm reports a flawless null. Refuse names this
# script does not know rather than measure one arm against itself.
# DERIVED from the source, not spelled out here. A literal list in a script is
# the same hazard as a literal list in a test: it measures whoever last edited
# it. `CadPolicy` is the authority and every arm declares its own name as
# `arm: "..."`, so the names are read straight out of it.
ARMS_SRC="${AXEYUM_ARMS_SRC:-crates/axeyum-solver/src/nra_real_root.rs}"
if [ -r "$ARMS_SRC" ]; then
  KNOWN=" $(grep -oE '^[[:space:]]*arm: "[a-z-]+",' "$ARMS_SRC" \
              | sed 's/.*"\(.*\)",/\1/' | sort -u | tr '\n' ' ')"
else
  echo "ABORT: cannot read $ARMS_SRC to learn the arm names; set AXEYUM_ARMS_SRC"
  exit 2
fi
# An empty derivation would accept everything, which is worse than a literal.
case "$KNOWN" in
  "" | " ") echo "ABORT: read $ARMS_SRC but found no arm names in it"; exit 2 ;;
esac

for arm in "$ARM_A" "$ARM_B"; do
  case "$KNOWN" in
    *" $arm "*) ;;
    *) echo "ABORT: '$arm' is not a known AXEYUM_NRA_CAD arm; it would silently"
       echo "       resolve to the shipped default and the A/B would measure"
       echo "       one arm against itself. Known arms:$KNOWN"
       exit 2 ;;
  esac
done

one() {  # $1 = arm value
  local raw rc v
  raw=$(AXEYUM_NRA_CAD="$1" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
          bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
          "$AX" "$f" 2>/dev/null)
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\n' > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  a1=$(one "$ARM_A"); b1=$(one "$ARM_B")
  b2=$(one "$ARM_B"); a2=$(one "$ARM_A")
  a3=$(one "$ARM_A"); b3=$(one "$ARM_B")

  av="${a1%%/*} ${a2%%/*} ${a3%%/*}"
  bv="${b1%%/*} ${b2%%/*} ${b3%%/*}"
  a_dec=$(printf '%s\n' $av | grep -cE '^(sat|unsat)$')
  b_dec=$(printf '%s\n' $bv | grep -cE '^(sat|unsat)$')
  if [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 3 ]; then cls=STABLE-GAIN
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 0 ]; then cls=STABLE-LOSS
  elif [ "$a_dec" -eq 3 ] && [ "$b_dec" -eq 3 ]; then cls=BOTH-DECIDE
  elif [ "$a_dec" -eq 0 ] && [ "$b_dec" -eq 0 ]; then cls=NEITHER-DECIDES
  else cls=UNSTABLE
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" >> "$OUT"
  echo "$cls ${f#"$CORPUS"}"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
