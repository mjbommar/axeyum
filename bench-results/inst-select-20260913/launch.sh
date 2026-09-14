#!/usr/bin/env bash
# Shard a pinned list across THIS LANE'S SIX core pairs and no others.
#
# Core budget: the brief caps this lane at 6 of the fleet's 12 pinned pairs.
# Taken: s5 {1,9  3,11  5,13} and s6 {1,9  3,11  5,13}.
# LEFT FREE for the concurrent lane: all of s7, and both `6,14` pairs.
# Do not widen HOSTS/CORES without re-checking that cap.
#
# One PHYSICAL core per shard (`c,c+8` is a core and its SMT sibling), so no two
# shards of this lane ever share a core.
#
# LAUNCH ONE DIVISION AT A TIME: shard numbering restarts at 0 per division, so
# two divisions launched together would put two of this lane's own shards on one
# physical core.
#
# Refuses to start if any target shard output already exists -- a re-launch into
# a non-empty file silently doubles or truncates a denominator.
#
# Usage: launch.sh <arm-tag> <runner> <outdir> <budget_s> <env-assignments> \
#                  <extra-runner-args> <div>:<list> ...
#   <env-assignments>   a single string, e.g. "" or "AXEYUM_QGROUNDDUMP=..."
#   <extra-runner-args> a single string appended after the runner's fixed args
set -eu
ARM="$1"; RUNNER="$2"; OUTDIR="$3"; BUDGET="$4"; ENVS="$5"; EXTRA="$6"; shift 6
REMOTE=/nas3/data/axeyum/harness/inst-select/scripts
HOSTS=(s5 s6)
CORES=("1,9" "3,11" "5,13")
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

mkdir -p "$OUTDIR" "$OUTDIR/lists"
for spec in "$@"; do
  DIV="${spec%%:*}"; LIST="${spec#*:}"
  rm -f "$OUTDIR"/lists/"$DIV".*.txt
  # Round-robin, so a slow family cannot land entirely on one shard and leave a
  # box with a permanent overhang.
  awk -v n="$SHARDS" -v div="$DIV" -v out="$OUTDIR/lists" \
    '{ print > sprintf("%s/%s.%02d.txt", out, div, NR % n) }' "$LIST"
done

for spec in "$@"; do
  DIV="${spec%%:*}"
  s=0
  for h in "${HOSTS[@]}"; do
    for c in "${CORES[@]}"; do
      sl=$(printf '%s/lists/%s.%02d.txt' "$OUTDIR" "$DIV" "$s")
      so=$(printf '%s/%s.shard%02d.tsv' "$OUTDIR" "$DIV" "$s")
      if [ -s "$so" ]; then echo "ABORT: $so already non-empty"; exit 2; fi
      if [ ! -f "$sl" ]; then s=$((s + 1)); continue; fi
      # `-f` backgrounds ssh AFTER authentication, and the remote redirects all
      # three fds; without both, ssh holds the channel open until the detached
      # job exits and the launcher serialises instead of fanning out.
      ssh -n -f -- "$h" "cd /tmp && nohup setsid env $ENVS bash $REMOTE/$RUNNER \
            $DIV-$s $sl $so '$c' $BUDGET $EXTRA > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $ARM $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $ARM $SHARDS shards per division  envs=[$ENVS]  extra=[$EXTRA]"
