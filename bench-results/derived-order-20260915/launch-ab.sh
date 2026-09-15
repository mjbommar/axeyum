#!/usr/bin/env bash
# Shard ADR-2106's interleaved one-binary A/B across s5/s6/s7, one PHYSICAL core
# pair per shard.
#
# ADR-2103's `launch-ab.sh` with two differences, both stated because a runner
# that silently diverges from the one it copies is how a comparison stops
# comparing:
#
# 1. **One binary, two env values.** ADR-2106 is a lever, so the arms are
#    `AXEYUM_LADDER_ORDER=hand` and `=derived` out of one build. The
#    same-binary refusal the two-build runners carry is replaced by a
#    same-ENV-VALUE refusal in `ab-run-lever.sh`, which is the thing that can
#    actually be degenerate here.
#
# 2. **Divisions run SERIALLY within a shard.** ADR-2103 measured that launching
#    every division at once put 129/129/133 concurrent shards on 4 pinned cores
#    -- 9x oversubscription collapses both columns toward `unknown`, and a wash
#    of `unknown` reads exactly like no movement. This loops divisions inside
#    ONE remote command per shard.
#
# The file lists are ADR-2100's, reused unchanged
# (`/nas3/data/axeyum/harness/route-ownership/ablists`), and were verified
# byte-identical as file SETS to `postmerge-board-dt`'s `T1_<DIV>.txt` -- which
# is the population ADR-2102's ledger rows were measured on, so the derived
# order is being A/B'd on exactly the files it was derived from. Generalisation
# is the HELD-OUT draw's job, not this run's.
#
# Usage: launch-ab.sh <bin> <outdir> <budget_s> <div> [...]
set -eu
AX="$1"; OUTDIR="$2"; BUDGET="$3"; shift 3
RUNNER=/nas3/data/axeyum/harness/derived-order/ab-run-lever.sh
# The pinned Tier 1 lists by default; `AB_LISTS` points at the HELD-OUT draw
# (`draw-heldout.py`, seeded, excluding every pinned path and every path any
# committed ledger row carries) for the generalisation arm.
ABLISTS="${AB_LISTS:-/nas3/data/axeyum/harness/route-ownership/ablists}"
ENV_A="${AB_ENV_A:-hand}"
ENV_B="${AB_ENV_B:-derived}"
read -r -a HOSTS <<< "${AB_HOSTS:-s5 s6 s7}"
read -r -a CORES <<< "${AB_CORES:-1,9 3,11 5,13 6,14}"
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$RUNNER" ] || { echo "ABORT: $RUNNER missing (deploy it first)"; exit 2; }
if [ "$ENV_A" = "$ENV_B" ]; then
  echo "ABORT: both arms are AXEYUM_LADDER_ORDER=$ENV_A; every number would be vacuous"
  exit 2
fi
echo "bin=$(sha256sum "$AX" | cut -d' ' -f1)"
echo "A=AXEYUM_LADDER_ORDER=$ENV_A"
echo "B=AXEYUM_LADDER_ORDER=$ENV_B"

mkdir -p "$OUTDIR" "$OUTDIR/lists"
for DIV in "$@"; do
  LIST="$ABLISTS/$DIV.txt"
  [ -s "$LIST" ] || { echo "ABORT: $LIST missing or empty"; exit 2; }
  rm -f "$OUTDIR"/lists/"$DIV".*.txt
  awk -v n="$SHARDS" -v div="$DIV" -v out="$OUTDIR/lists" \
    '{ print > sprintf("%s/%s.%02d.txt", out, div, NR % n) }' "$LIST"
done

s=0
for h in "${HOSTS[@]}"; do
  for c in "${CORES[@]}"; do
    # One remote command per shard, looping the divisions SERIALLY inside it.
    CMD=""
    for DIV in "$@"; do
      sl=$(printf '%s/lists/%s.%02d.txt' "$OUTDIR" "$DIV" "$s")
      so=$(printf '%s/%s.shard%02d.tsv' "$OUTDIR" "$DIV" "$s")
      if [ -s "$so" ]; then echo "ABORT: $so already non-empty"; exit 2; fi
      [ -f "$sl" ] || continue
      lg=$(printf '%s/%s.shard%02d.log' "$OUTDIR" "$DIV" "$s")
      CMD="$CMD bash $RUNNER $DIV-$s $sl $so '$c' $AX $ENV_A $ENV_B $BUDGET > $lg 2>&1;"
    done
    if [ -n "$CMD" ]; then
      ssh -n -f -- "$h" "cd /tmp && nohup setsid bash -c \"$CMD\" > /dev/null 2>&1 < /dev/null &"
      echo "LAUNCHED shard $s on $h cores $c ($* serially)"
    fi
    s=$((s + 1))
  done
done
echo "LAUNCH-OK $SHARDS shards, divisions serial per shard"
