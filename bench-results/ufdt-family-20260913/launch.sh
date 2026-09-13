#!/usr/bin/env bash
# Shard the pinned lists across s5/s6/s7, one PHYSICAL core per shard (`c,c+8` —
# a core and its SMT sibling, so no two shards ever share a core).
#
# Usage: launch.sh <arm-tag> <bin> <outdir> <budget_s> <env-assignments> <div>:<list> ...
#   <env-assignments> is a single string, e.g. "" or "AXEYUM_QUANT_EGRAPH_RESERVE=1"
#
# LAUNCH ONE DIVISION AT A TIME.  Shard numbering restarts at 0 per division, so
# two divisions launched together would put two of THIS LANE's shards on the
# same physical core -- the self-collision that cost the Tier-1 board a whole
# run.  The multi-division form is kept for a future run with more cores; with
# the four core pairs below, call it once per division and wait.
#
# The scripts and lists live on /nas3 because the lane worktree is local to the
# dev box and the compute hosts cannot see it.
#
# Refuses to start if any target shard output already exists — a re-launch into
# a non-empty file silently doubles or truncates a denominator, which is the
# failure `merge-division.py` exists to catch and this exists to prevent.
set -eu
ARM="$1"; BIN="$2"; OUTDIR="$3"; BUDGET="$4"; ENVS="$5"; shift 5
REMOTE=/nas3/data/axeyum/harness/ufdt-family/scripts
HOSTS=(s5 s6 s7)
CORES=("1,9" "3,11" "5,13" "6,14")
SHARDS=$(( ${#HOSTS[@]} * ${#CORES[@]} ))

mkdir -p "$OUTDIR" "$OUTDIR/lists"
for spec in "$@"; do
  DIV="${spec%%:*}"; LIST="${spec#*:}"
  rm -f "$OUTDIR"/lists/"$DIV".*.txt
  # Round-robin so a slow family cannot land entirely on one shard and leave a
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
      ssh -n -f -- "$h" "cd /tmp && nohup setsid env $ENVS bash $REMOTE/census-run.sh \
            $DIV-$s $sl $so '$c' $BIN $BUDGET > $OUTDIR/$DIV.shard$(printf %02d $s).log 2>&1 < /dev/null &"
      echo "LAUNCHED $ARM $DIV shard $s on $h cores $c ($(wc -l < "$sl") files)"
      s=$((s + 1))
    done
  done
done
echo "LAUNCH-OK $ARM $SHARDS shards per division  envs=[$ENVS]"
