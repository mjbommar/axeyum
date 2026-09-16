#!/usr/bin/env bash
# Recheck arm A for the ADR-2121 sat-only A/B: the shipped CAD policy, env var
# SET and EMPTY so the arms differ in a VALUE. Same binary as arm B (sha256 in
# ab-sat-binary-sha256.txt), which is also the binary the sat sweep ran.
export AXEYUM_NRA_CAD=
exec "/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/b5abceb2-1e55-4606-b944-34c43c75096d/scratchpad/nsc-sat-cli" "$@"
