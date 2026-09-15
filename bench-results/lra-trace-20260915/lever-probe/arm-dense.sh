#!/usr/bin/env bash
# ONE BINARY, TWO ENV VALUES — the `TableauReserve::Dense` arm (the SHIPPED
# default). Kept as a script rather than as an unset variable so that both arms
# of the lever A/B are explicit: an arm defined by "do not set anything" is one
# a later reader cannot tell from a forgotten export.
exec env AXEYUM_LRA_TABLEAU_RESERVE=dense \
  /nas3/data/axeyum/harness/lra-trace/bin/smtcomp_cli.arm "$@"
