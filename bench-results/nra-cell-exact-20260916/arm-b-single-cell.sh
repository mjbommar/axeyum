#!/usr/bin/env bash
# A/B arm B wrapper: ADR-2121s full `single-cell` arm, whose `unsat` is now
# gated on ADR-2126s EXACT delineability check. Same binary as arm A.
export AXEYUM_NRA_CAD=single-cell
exec "/nas3/data/axeyum/lanes/nra-cell-exact/smtcomp_cli" "$@"
