#!/usr/bin/env bash
# A/B arm A wrapper: the shipped CAD policy. The env var is SET and EMPTY rather
# than unset so the two arms differ in a VALUE, not in the shape of the
# environment. A wrapper rather than the binary itself so
# `recheck-movers.sh`'s same-binary guard still means something while ONE
# binary serves both arms (ADR-2110's arrangement).
export AXEYUM_NRA_CAD=
exec "/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a0ebc4ca26a3fd56a/target/release/examples/smtcomp_cli" "$@"
