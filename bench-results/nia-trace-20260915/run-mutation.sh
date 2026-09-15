#!/usr/bin/env bash
# Runs ADR-2112's mutation control suite (lane NIA-TRACE).
#
# A wrapper and not a bare invocation because `mutation_controls.py` copies the
# tree to a scratch root and rebuilds four times; it must never be run in the
# shared worktree, and it must be run detached so a harness timeout does not
# report a killed wrapper as a finished run.
set -uo pipefail
cd -- "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)" || exit 2
exec python3 scripts/tests/mutation_controls.py int-blast-width-floor "$@"
