#!/usr/bin/env bash
# Wraps `smtcomp_cli` under `/usr/bin/time -v` so peak RSS can be recorded
# per row through `scripts/ledger-run-one.sh`, which does not itself capture
# it. `ledger-run-one.sh` invokes its `--binary` as:
#
#   bash -c 'ulimit -v N; exec "$0" "$1" --timeout-ms M [--trace]' "$BIN" "$FILE"
#
# so this script receives the corpus FILE as $1 and the CLI flags as the
# remaining args -- the real binary path cannot be an argument, so it comes
# from the REAL_BIN env var, and the RSS capture destination from RSS_OUT.
# Both are set by the caller (run-ladder.sh) per (arm, file) before invoking
# ledger-run-one.sh, and are inherited across `exec`/`timeout`/`taskset`
# because none of those clear the environment.
#
# `time -v` still writes its stats file via wait4() even when the child is
# killed by SIGABRT (rc=134, the allocation-failure abort this lane's
# population is full of) -- only an uncatchable SIGKILL from `timeout`'s
# headroom expiring loses the row, and that is recorded as its own outcome
# (rc=124/137) by the caller reading $RSS_OUT's absence.
set -u
: "${REAL_BIN:?REAL_BIN must be set by the caller}"
: "${RSS_OUT:?RSS_OUT must be set by the caller}"
exec /usr/bin/time -v -o "$RSS_OUT" -- "$REAL_BIN" "$@"
