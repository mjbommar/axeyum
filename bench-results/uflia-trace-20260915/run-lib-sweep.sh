#!/usr/bin/env bash
# UFLIA-TRACE -- the full `--features full` solver unit sweep.
#
# NO wall-clock `timeout` around it. `cargo-serialized.sh` takes a HOST-WIDE
# flock, so a timeout here measures the queue rather than the tests: a first
# attempt died at exit 143 after 600 s having never started, which reads exactly
# like the 24 GiB ceiling firing. Run it detached and wait on the artifact.
set -eu
cd "$(dirname "$0")/../.."
exec scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full
