#!/usr/bin/env bash
# Lane euf-driver-mbtc: build the working tree (now a ladder RESERVE rather than
# a half-budget split) and pin it under a NEW name, so the sweeps still running
# against `smtcomp_cli.new` keep executing the binary they started with.
set -euo pipefail
cd "$(dirname "$0")/.."

./scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
cp target/release/examples/smtcomp_cli .lane-euf-driver-mbtc/smtcomp_cli.reserve
sha256sum .lane-euf-driver-mbtc/smtcomp_cli.reserve
echo RESERVE_BUILD_COMPLETE
