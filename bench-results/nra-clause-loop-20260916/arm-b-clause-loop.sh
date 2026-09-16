#!/usr/bin/env bash
# A/B arm B wrapper: ADR-2131s `clause-loop` arm -- the shipped default PLUS the
# Boolean clause loop, whose `unsat` is gated on `check_clause_refutation`.
#
# ADR-2131 REBASED this arm onto `SINGLE_CELL` (it was on `SINGLE_CELL_SAT`), so
# A and B now differ in exactly `clause_loop`. Before that rebase this A/B also
# switched the single-cell routes `unsat` half OFF in the treatment arm, and
# every verdict that half contributes would have read as a loss caused by the
# loop. `the_single_cell_arm_differs_in_exactly_the_route` is what holds it.
export AXEYUM_NRA_CAD=clause-loop
exec "/nas3/data/axeyum/lanes/nra-clause-loop/smtcomp_cli" "$@"
