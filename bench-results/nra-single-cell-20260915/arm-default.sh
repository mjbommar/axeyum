#!/usr/bin/env bash
# A/B arm A wrapper: the shipped CAD policy. The env var is SET and EMPTY rather
# than unset so the two arms differ in a VALUE, not in the shape of the
# environment. A wrapper rather than the binary itself so
# `recheck-movers.sh` same-binary guard still means something while ONE binary
# serves both arms (ADR-2110 arrangement). The binary is the one the A/B ran --
# its sha256 is in ab-binary-sha256.txt -- so the recheck and the sweep are
# comparable rather than two builds apart.
export AXEYUM_NRA_CAD=
exec "/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/b5abceb2-1e55-4606-b944-34c43c75096d/scratchpad/nra-single-cell-cli" "$@"
