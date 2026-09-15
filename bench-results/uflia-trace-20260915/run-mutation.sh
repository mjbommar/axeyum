#!/usr/bin/env bash
# UFLIA-TRACE -- run this lane's mutation control suite with its own cargo
# target dir, so it never competes with the shared checkout's `target/`.
set -eu
cd "$(dirname "$0")/../.."
export AXEYUM_MUTATION_CARGO_TARGET=/data0/axeyum-mutation-target-uflia-trace
exec python3 scripts/tests/mutation_controls.py "${1:-qinst-trigger-alternatives}"
