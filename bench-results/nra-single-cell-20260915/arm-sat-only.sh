#!/usr/bin/env bash
# Recheck arm B: ADR-2121 single-cell-sat -- run the route, withhold its unsat.
export AXEYUM_NRA_CAD=single-cell-sat
exec "/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/b5abceb2-1e55-4606-b944-34c43c75096d/scratchpad/nsc-sat-cli" "$@"
