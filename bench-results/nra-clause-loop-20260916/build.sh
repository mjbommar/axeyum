#!/usr/bin/env bash
# Build the ADR-2131 A/B binary and publish it where the sweep host can read it.
#
# ONE binary for both arms. The arms are two values of `AXEYUM_NRA_CAD`, and the
# binary's sha256 is recorded beside it, because "one binary, two env values" is
# a claim and not a convention.
#
# It lands on `/nas3`, which is mounted on every fleet host, so the sweep host
# reads the same bytes the build host produced rather than a copy nobody
# compared. The sha is written next to it for exactly that comparison.
#
# # IT REFUSES TO PUBLISH OVER A LIVE SWEEP, and that guard is not theoretical
#
# On 2026-09-16 this script was launched to rebuild a DIAGNOSTIC binary while
# the A/B sweep was three hours into its second division, reading this exact
# path. `cp` writes in place, so the publish would have swapped the binary
# underneath a running measurement: the two halves of the sweep would have been
# different programs and nothing in the output would have said so. The A/B would
# have printed a clean, wrong number -- and the sha256 file beside it would have
# agreed with the NEW binary, so even the provenance check would have passed.
#
# It was caught by hand with seconds to spare. A guard that can fail is the only
# reason it would be caught next time, so: a sweep is live if the staged `ab`
# directory has shard output but no `.done` marker, and then this script exits
# rather than publishing. `--dest NAME` publishes beside it under another name,
# which is what a diagnostic build should have used in the first place.
set -u
cd "$(dirname "$0")/../.." || exit 2

DEST_NAME="smtcomp_cli"
if [ "${1:-}" = "--dest" ]; then
  DEST_NAME="${2:?--dest needs a name}"
fi

LANE=/nas3/data/axeyum/lanes/nra-clause-loop
mkdir -p "$LANE" || exit 2

if [ "$DEST_NAME" = "smtcomp_cli" ] && [ -d "$LANE/ab" ]; then
  # `ls` rather than a glob test: an unmatched glob expands to itself and would
  # read as a match.
  shards=$(ls "$LANE"/ab/ab-*-shard*.tsv 2>/dev/null | wc -l)
  done_markers=$(ls "$LANE"/ab/ab-*.done 2>/dev/null | wc -l)
  if [ "$shards" -gt 0 ] && [ "$done_markers" -eq 0 ]; then
    echo "build.sh: REFUSING -- a sweep is live ($shards shard files, no .done marker)." >&2
    echo "  Publishing would swap the binary underneath a running measurement." >&2
    echo "  Use: $0 --dest smtcomp_cli_diag" >&2
    exit 2
  fi
fi

scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli || exit 2
cp target/release/examples/smtcomp_cli "$LANE/$DEST_NAME" || exit 2
sha256sum "$LANE/$DEST_NAME" | tee "$LANE/$DEST_NAME.sha256.txt"
echo AB_BINARY_READY
