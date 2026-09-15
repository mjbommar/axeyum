#!/usr/bin/env bash
# REAL-OPAQUE -- launch the four pinned A/B shards, detached.
#
# FOUR live slots, never more (the brief's cap):
#   s5 core 2 : AUFLIRA.a      s5 core 3 : AUFLIRA.b
#   s6 core 2 : QF_LRA.a       s6 core 3 : QF_LRA.b
# `s7` is deliberately LEFT IDLE for the reference passes.
#
# `nohup setsid` because the harness kills background tasks under memory
# pressure and a measurement half-done is worse than one not started. Progress
# is watched by the ARTIFACT (the row count in the TSV), never by grepping for a
# process with a pattern this script's own command line contains.
#
# THE LANE WORKTREE IS NOT VISIBLE FROM s5/s6/s7. The first launch put four
# `No such file or directory` lines in four logs and produced no TSV at all --
# a silent no-op that looked exactly like a launch. The runner and the lists are
# therefore STAGED on the shared path, and `ab-stage.sh` is what copies them
# there; a launch that skips staging runs an older runner.
#
# Usage: ab-launch.sh [tag]
set -eu
RUN=/nas3/data/axeyum/harness/real-opaque/run
OUT=/nas3/data/axeyum/harness/real-opaque/out
AX=/nas3/data/axeyum/harness/real-opaque/bin/smtcomp_cli-realopaque
LOGS=/nas3/data/axeyum/harness/real-opaque/logs
mkdir -p "$LOGS" "$OUT"

launch() {
  local host="$1" core="$2" list="$3" out="$4"
  ssh -o BatchMode=yes "$host" \
    "nohup setsid bash $RUN/ab-run.sh $RUN/lists/$list $OUT/$out $core $AX 24 \
       > $LOGS/$out.log 2>&1 < /dev/null & echo launched $host core=$core $list"
}

launch s5 2 AUFLIRA.a.list auflira-a.tsv
launch s5 3 AUFLIRA.b.list auflira-b.tsv
launch s6 2 QF_LRA.a.list qflra-a.tsv
launch s6 3 QF_LRA.b.list qflra-b.tsv
echo "4 shards launched; watch $OUT/*.tsv row counts"
