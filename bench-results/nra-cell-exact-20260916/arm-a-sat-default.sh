#!/usr/bin/env bash
# A/B arm A wrapper: the SHIPPED default. `AXEYUM_NRA_CAD` set and EMPTY resolves
# through `parse_cad_arm("")` to `CAD_DEFAULT`, which ADR-2121 moved to
# `CadPolicy::SINGLE_CELL_SAT`. Same binary as arm B -- the two wrappers differ
# so `recheck-movers.sh`s same-binary guard still means something.
export AXEYUM_NRA_CAD=
exec "/nas3/data/axeyum/lanes/nra-cell-exact/smtcomp_cli" "$@"
