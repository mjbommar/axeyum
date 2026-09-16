#!/usr/bin/env bash
# A/B arm A wrapper: the SHIPPED default. `AXEYUM_NRA_CAD` set and EMPTY resolves
# through `parse_cad_arm("")` to `CAD_DEFAULT`, which ADR-2126 moved to
# `CadPolicy::SINGLE_CELL`. Same binary as arm B -- the two wrappers differ only
# in the env value, so `recheck-movers.sh`s same-binary guard still means
# something while "one binary, two env values" stays true.
export AXEYUM_NRA_CAD=
exec "/nas3/data/axeyum/lanes/nra-clause-loop/smtcomp_cli" "$@"
