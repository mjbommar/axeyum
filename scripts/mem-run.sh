#!/usr/bin/env bash
# Run a command under a hard memory cap so a runaway allocation aborts *this*
# process instead of OOM-killing the host (the box has 123 GB; a single NRA /
# bit-blast blowup can claim all of it).
#
# Usage:
#   scripts/mem-run.sh cargo test -p axeyum-solver --test nra
#   MEM_LIMIT_GB=32 scripts/mem-run.sh cargo build
#
# Default cap is 64 GiB (override with MEM_LIMIT_GB). The cap is applied as an
# address-space (`ulimit -v`) limit, which every allocation respects: an
# over-limit `malloc`/`mmap` fails and the program aborts with a clean error
# rather than driving the host into swap/OOM. 64 GiB leaves the host responsive
# while giving builds and solves ample headroom.
set -euo pipefail

LIMIT_GB="${MEM_LIMIT_GB:-64}"
# ulimit -v is in KiB.
ulimit -v "$(( LIMIT_GB * 1024 * 1024 ))"

exec "$@"
