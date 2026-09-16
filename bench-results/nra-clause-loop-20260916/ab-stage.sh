#!/usr/bin/env bash
# Stage the ADR-2131 A/B onto the shared lane path and launch it on the sweep
# host.
#
# `/nas3` is mounted on every fleet host and `/home` is NOT, so the sweep host
# reads the same script bytes and the same file lists the build host wrote,
# rather than a copy nobody compared. Results land there too, and are copied
# back into the repository at the end rather than being written twice.
#
# The sweep host is a PARAMETER and the script refuses to guess: a sweep that
# silently ran on the build host would be measuring a box carrying six other
# lanes, and ADR-2110 measured that as worth up to 8 verdicts on one division.
#
# Usage: ab-stage.sh <sweep-host> [tag]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
HOST="${1:?usage: ab-stage.sh <sweep-host> [tag]}"
TAG="${2:-clauseloop}"
LANE=/nas3/data/axeyum/lanes/nra-clause-loop
AB="$LANE/ab"

[ -x "$LANE/smtcomp_cli" ] || { echo "ab-stage: $LANE/smtcomp_cli missing -- run build.sh" >&2; exit 2; }

mkdir -p "$AB" || exit 2
cp "$HERE"/ab-run.sh "$HERE"/ab-launch.sh "$AB/" || exit 2
cp "$HERE"/shard?-qfnra.txt "$HERE"/shard?-qfnia.txt \
   "$HERE"/shard?-qflra.txt "$HERE"/shard?-qfnraheldout.txt "$AB/" || exit 2
chmod +x "$AB"/ab-run.sh "$AB"/ab-launch.sh

# The host must see the same bytes. Comparing the sha rather than assuming the
# mount is the point of staging here at all.
LOCAL=$(sha256sum "$LANE/smtcomp_cli" | cut -d' ' -f1)
REMOTE=$(ssh -o BatchMode=yes "$HOST" "sha256sum $LANE/smtcomp_cli 2>/dev/null | cut -d' ' -f1")
if [ "$LOCAL" != "$REMOTE" ]; then
  echo "ab-stage: $HOST sees a DIFFERENT binary ($REMOTE) than this host ($LOCAL)" >&2
  exit 2
fi
echo "ab-stage: $HOST sees the same binary, sha256 $LOCAL"

ssh -o BatchMode=yes "$HOST" \
  "nohup setsid $AB/ab-launch.sh $TAG > $AB/launch.log 2>&1 < /dev/null & echo launched"
echo "ab-stage: watch $AB/ab-$TAG.done"
