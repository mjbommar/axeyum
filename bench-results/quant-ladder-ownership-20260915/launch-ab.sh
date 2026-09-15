#!/usr/bin/env bash
# Shard ADR-2103's interleaved A/B across s5/s6/s7, one PHYSICAL core pair per
# shard. ADR-2100's `launch-ab.sh` with two deliberate differences, both stated
# here because a runner that silently diverges from the one it copies is how a
# comparison stops comparing.
#
# 1. **The A arm is `51baff9ef`, not `7d922fe58`.** The brief named the latter,
#    which was `main` when this lane branched. `main` then moved (ADR-2104,
#    typed `DeclineReason` detail) and the coordinator instructed this lane to
#    merge it. Measuring against `7d922fe58` would therefore put ADR-2104's diff
#    in the B arm and attribute its effect to ADR-2103. `51baff9ef` is this
#    branch's merge-base with `main` and isolates this lane's change exactly.
#    The deviation is deliberate and the reason is the whole point of an A/B.
#
# 2. **The scripts and the file lists are ADR-2100's, reused unchanged** --
#    `/nas3/data/axeyum/harness/route-ownership/{scripts,ablists}` -- so the
#    population is byte-identically the same nine divisions x 200 files that
#    ADR-2100 measured its +2/-2 on, and this lane's columns can be read
#    against that ADR's without a population caveat.
#
# Usage: launch-ab.sh <binA> <binB> <outdir> <budget_s> <div> [...]
set -eu
AX_A="$1"; AX_B="$2"; OUTDIR="$3"; BUDGET="$4"; shift 4
REMOTE=/nas3/data/axeyum/harness/route-ownership/scripts
ABLISTS=/nas3/data/axeyum/harness/route-ownership/ablists
read -r -a HOSTS <<< "${AB_HOSTS:-s5 s6 s7}"
read -r -a CORES <<< "${AB_CORES:-1,9 3,11 5,13 6,14}"
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

[ -x "$AX_A" ] || { echo "ABORT: $AX_A missing"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT: $AX_B missing"; exit 2; }
HA=$(sha256sum "$AX_A" | cut -d' ' -f1)
HB=$(sha256sum "$AX_B" | cut -d' ' -f1)
if [ "$HA" = "$HB" ]; then
  echo "ABORT: both arms are the SAME binary ($HA)."
  echo "  Two identical arms make every number vacuous while looking exactly"
  echo "  like agreement. `ab-run.sh` refuses too; this is the earlier refusal."
  exit 2
fi
echo "A=$HA"
echo "B=$HB"

mkdir -p "$OUTDIR" "$OUTDIR/lists"
for DIV in "$@"; do
  LIST="$ABLISTS/$DIV.txt"
  [ -s "$LIST" ] || { echo "ABORT: $LIST missing or empty"; exit 2; }
  rm -f "$OUTDIR"/lists/"$DIV".*.txt
  awk -v n="$SHARDS" -v div="$DIV" -v out="$OUTDIR/lists" \
    '{ print > sprintf("%s/%s.%02d.txt", out, div, NR % n) }' "$LIST"
done

for DIV in "$@"; do
  s=0
  for h in "${HOSTS[@]}"; do
    for c in "${CORES[@]}"; do
      sl=$(printf '%s/lists/%s.%02d.txt' "$OUTDIR" "$DIV" "$s")
      so=$(printf '%s/%s.shard%02d.tsv' "$OUTDIR" "$DIV" "$s")
      if [ -s "$so" ]; then echo "ABORT: $so already non-empty"; exit 2; fi
      if [ ! -f "$sl" ]; then s=$((s + 1)); continue; fi
      ssh -n -f -- "$h" "cd /tmp && nohup setsid bash $REMOTE/ab-run.sh \
            $DIV-$s $sl $so '$c' $AX_A $AX_B $BUDGET \
            > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $SHARDS shards per division"
