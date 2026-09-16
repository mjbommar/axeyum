#!/usr/bin/env bash
# A/B arm B wrapper: ADR-2121's single-cell CAD route. Same binary as arm A.
export AXEYUM_NRA_CAD=single-cell
exec "/home/mjbommar/projects/personal/axeyum/.claude/worktrees/agent-a0ebc4ca26a3fd56a/target/release/examples/smtcomp_cli" "$@"
