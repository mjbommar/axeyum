#!/usr/bin/env bash
# ADR-2035 -- push ONE binary and the harness to the three compute hosts.
#
# ONE BINARY, TWO ENV VALUES. The sha256 is printed here and re-printed by every
# runner, so a stale-artifact substitution on any host is visible in the logs
# rather than inferred from a build that "finished fast".
set -eu
AX="$1"
DEST=/tmp/round-cap
SHA=$(sha256sum "$AX" | cut -d' ' -f1)
echo "LOCAL  sha256=$SHA  $AX"
for host in s5 s6 s7; do
  ssh -o BatchMode=yes "$host" "mkdir -p $DEST/lists $DEST/ab"
  scp -q "$AX" "$host:$DEST/smtcomp_cli"
  scp -q bench-results/round-cap-20260914/ab-run.sh \
         bench-results/round-cap-20260914/probe-run.sh "$host:$DEST/"
  scp -q bench-results/round-cap-20260914/lists/*.txt "$host:$DEST/lists/"
  ssh -o BatchMode=yes "$host" \
      "chmod +x $DEST/smtcomp_cli $DEST/*.sh; echo -n '$host   sha256='; sha256sum $DEST/smtcomp_cli | cut -d' ' -f1"
done
