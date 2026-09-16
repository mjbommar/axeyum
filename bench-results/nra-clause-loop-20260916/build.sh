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
set -u
cd "$(dirname "$0")/../.." || exit 2

DEST=/nas3/data/axeyum/lanes/nra-clause-loop
mkdir -p "$DEST" || exit 2

scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli || exit 2
cp target/release/examples/smtcomp_cli "$DEST/smtcomp_cli" || exit 2
sha256sum "$DEST/smtcomp_cli" | tee "$DEST/sha256.txt"
echo AB_BINARY_READY
