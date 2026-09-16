#!/usr/bin/env bash
# A/B arm B wrapper: ADR-2121 single-cell CAD route. Same binary as arm A, and
# the same binary the sweep ran.
export AXEYUM_NRA_CAD=single-cell
exec "/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/b5abceb2-1e55-4606-b944-34c43c75096d/scratchpad/nra-single-cell-cli" "$@"
