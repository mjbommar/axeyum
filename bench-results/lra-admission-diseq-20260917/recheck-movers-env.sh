#!/usr/bin/env bash
# ADR-2134's `recheck-movers-env.sh` for the ADR-2146 / ADR-2147 levers: ONE
# binary, TWO ENV STRINGS (`-` = nothing set, the shipped route), three passes
# per arm, arms alternating WITHIN the passes so drift across the minutes a row
# takes does not land entirely on one arm, and a row classified only when all
# three agree:
#
#   STABLE-GAIN      A never decided, B decided 3/3
#   STABLE-LOSS      A decided 3/3, B never decided
#   BOTH-DECIDE      both 3/3
#   NEITHER-DECIDES  both 0/3
#   UNSTABLE         anything else -- reported as ambient, not as an effect
#
# The env-string guard is `ab-arms.sh`'s: only the three lever variables, and
# only the spellings `1 | on | off | 16`, because an unrecognised value is
# silently OFF and a typo would measure the shipped route against itself.
# Exit status per pass is its own column: `losses=0` by verdict has coexisted
# with new ABORTs underneath it (ADR-2045).
#
# Usage: recheck-movers-env.sh <list> <out.tsv> <cores> <binary> <envA> <envB> [budget_s]
#   The list carries CORPUS-RELATIVE paths.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ENV_A="$5"; ENV_B="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
[ "$ENV_A" = "$ENV_B" ] && { echo "ABORT: both arms are the SAME env string"; exit 2; }
for v in AXEYUM_LRA_ADMIT_NONZEROS AXEYUM_LRA_DISEQ_SPLIT AXEYUM_LRA_ATOM_SCREEN; do
  [ -n "${!v:-}" ] && { echo "ABORT: $v is set in the launching shell"; exit 2; }
done
for envstr in "$ENV_A" "$ENV_B"; do
  [ "$envstr" = "-" ] && continue
  for kv in $envstr; do
    k=${kv%%=*}; val=${kv#*=}
    case "$k" in AXEYUM_LRA_ADMIT_NONZEROS|AXEYUM_LRA_DISEQ_SPLIT|AXEYUM_LRA_ATOM_SCREEN) ;;
      *) echo "ABORT: unknown variable '$k' in arm '$envstr'"; exit 2 ;; esac
    case "$val" in 1|on|off|16) ;;
      *) echo "ABORT: value '$val' for $k is not a known spelling"; exit 2 ;; esac
  done
done

now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then echo "ABORT: clock read ${dt} ms for 200 ms"; exit 3; fi
echo "CLOCK-OK sleep200=${dt}ms host=$(hostname) cores=$PIN A=[$ENV_A] B=[$ENV_B] bin=$(sha256sum "$AX" | cut -d' ' -f1)"

one() {  # $1 = env string; uses $f
  local raw rc v
  if [ "$1" = "-" ]; then
    raw=$(timeout -k 5 $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    # shellcheck disable=SC2086
    raw=$(timeout -k 5 $((BUDGET + HEADROOM)) taskset -c "$PIN" env $1 \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s/%s' "${v:-none}" "$rc"
}

printf 'file\tA1\tA2\tA3\tB1\tB2\tB3\tverdict\tstatus\n' > "$OUT"
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  a1=$(one "$ENV_A"); b1=$(one "$ENV_B")
  b2=$(one "$ENV_B"); a2=$(one "$ENV_A")
  a3=$(one "$ENV_A"); b3=$(one "$ENV_B")
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
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$a1" "$a2" "$a3" "$b1" "$b2" "$b3" "$cls" "${st:-none}" >> "$OUT"
  echo "$cls $rel"
done < "$LIST"
echo "RECHECK-DONE -> $OUT"
