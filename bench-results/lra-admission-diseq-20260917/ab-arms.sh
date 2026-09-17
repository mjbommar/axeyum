#!/usr/bin/env bash
# Interleaved per-file A/B of ONE binary under N ENVIRONMENT ARMS (ADR-2146 /
# ADR-2147). ADR-2134's `ab-cad-env.sh` generalised from two arms to N: every
# arm runs on the SAME file on the SAME pinned core back to back, and the arm
# ORDER ROTATES per file (file n starts at arm n mod N), so ambient load lands
# on every arm equally over the list rather than on whichever ran last.
#
# An arm is a NAME=ENV-STRING pair; the env string is a space-separated list
# of `VAR=value` assignments, or `-` for "nothing set" (the shipped route). The
# lever spellings are `1` | `on` to arm and ANYTHING ELSE is off, so a typo in
# an arm's env string would silently measure the shipped route against itself;
# the script therefore refuses an env string whose value is neither `1`, `on`,
# `off` nor `16` (the ADR-2111 screen multiplier the composition arm uses).
#
# TIMING IS `$EPOCHREALTIME`: s5/s7 run uutils coreutils whose `date +%3N`
# prints nanoseconds. A 200 ms sleep must read 150-400 ms before any solve.
#
# Per file, per arm: verdict, wall ms, exit status. Plus `:status` from the
# file's header, so a flip or a disagreement is a row and not a recollection.
#
# Envelope: BUDGET s wall, 8 GiB `ulimit -v`, one pinned physical core pair.
#
# Usage: ab-arms.sh <tag> <list> <out.tsv> <cores> <bin> <budget_s> <name=env> [<name=env> ...]
#   e.g. ab-arms.sh lra.0 lists/QF_LRA-pinned.txt out.tsv 1,9 ./smtcomp_cli 24 \
#          base=- nz=AXEYUM_LRA_ADMIT_NONZEROS=1 sp=AXEYUM_LRA_DISEQ_SPLIT=1 \
#          both="AXEYUM_LRA_ADMIT_NONZEROS=1 AXEYUM_LRA_DISEQ_SPLIT=1"
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; BUDGET="$6"; shift 6
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -r "$LIST" ] || { echo "ABORT $TAG: $LIST unreadable"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
for v in AXEYUM_LRA_ADMIT_NONZEROS AXEYUM_LRA_DISEQ_SPLIT AXEYUM_LRA_ATOM_SCREEN; do
  [ -n "${!v:-}" ] && { echo "ABORT $TAG: $v is set in the launching shell"; exit 2; }
done
[ "$#" -ge 2 ] || { echo "ABORT $TAG: need at least two arms"; exit 2; }

NAMES=(); ENVS=()
for arm in "$@"; do
  name=${arm%%=*}; envstr=${arm#*=}
  [ -n "$name" ] && [ "$name" != "$arm" ] || { echo "ABORT $TAG: arm '$arm' is not name=env"; exit 2; }
  if [ "$envstr" != "-" ]; then
    for kv in $envstr; do
      k=${kv%%=*}; val=${kv#*=}
      case "$k" in AXEYUM_LRA_ADMIT_NONZEROS|AXEYUM_LRA_DISEQ_SPLIT|AXEYUM_LRA_ATOM_SCREEN) ;;
        *) echo "ABORT $TAG: arm '$name' sets unknown variable '$k'"; exit 2 ;; esac
      case "$val" in 1|on|off|16) ;;
        *) echo "ABORT $TAG: arm '$name' value '$val' for $k is not a known spelling"; exit 2 ;; esac
    done
  fi
  for seen in "${NAMES[@]:-}"; do [ "$seen" = "$name" ] && { echo "ABORT $TAG: arm name '$name' repeated"; exit 2; }; done
  NAMES+=("$name"); ENVS+=("$envstr")
done
N=${#NAMES[@]}

now_ms() { local t="$EPOCHREALTIME"; echo $(( ${t%.*} * 1000 + 10#${t#*.} / 1000 )); }
t0=$(now_ms); sleep 0.2; t1=$(now_ms); dt=$((t1 - t0))
if [ "$dt" -lt 150 ] || [ "$dt" -gt 400 ]; then
  echo "ABORT $TAG: clock self-check read ${dt} ms for a 200 ms sleep"; exit 3
fi
echo "CLOCK-OK $TAG sleep200=${dt}ms host=$(hostname) cores=$PIN budget=${BUDGET}s bin=$(sha256sum "$AX" | cut -d' ' -f1)"
for i in $(seq 0 $((N - 1))); do echo "ARM $i ${NAMES[$i]} env=[${ENVS[$i]}]"; done

run_arm() {  # $1 = env string; uses $f. Prints verdict<TAB>ms<TAB>rc
  local t0 t1 raw rc v envstr="$1"
  t0=$(now_ms)
  if [ "$envstr" = "-" ]; then
    raw=$(timeout -k 5 $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    # shellcheck disable=SC2086
    raw=$(timeout -k 5 $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            env $envstr \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(now_ms)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$((t1 - t0))" "$rc"
}

{
  printf 'file'
  for name in "${NAMES[@]}"; do printf '\t%s\t%s_ms\t%s_rc' "$name" "$name" "$name"; done
  printf '\tfirst\tstatus\n'
} > "$OUT"
n=0
while read -r rel; do
  [ -z "$rel" ] && continue
  f="$CORPUS$rel"
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  start=$(( (n - 1) % N ))
  declare -a RES=()
  for i in $(seq 0 $((N - 1))); do
    idx=$(( (start + i) % N ))
    RES[$idx]=$(run_arm "${ENVS[$idx]}")
  done
  line="$rel"
  summary=""
  for i in $(seq 0 $((N - 1))); do
    line="$line	${RES[$i]}"
    summary="$summary ${NAMES[$i]}=$(printf '%s' "${RES[$i]}" | cut -f1)"
  done
  printf '%s\t%s\t%s\n' "$line" "${NAMES[$start]}" "${st:-none}" >> "$OUT"
  echo "[$TAG $n]$summary $rel"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT bin=$(sha256sum "$AX" | cut -d' ' -f1)"
