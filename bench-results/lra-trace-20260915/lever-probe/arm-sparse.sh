#!/usr/bin/env bash
# ONE BINARY, TWO ENV VALUES — the `TableauReserve::Sparse` arm (ADR-2111's
# lever, which does NOT ship on). The tableau reserve drops from 128 MiB to
# 16 MiB, which raises the derived coefficient ceiling and therefore the set of
# queries the online CDCL(T) engine ADMITS instead of sending to the offline
# lazy-SMT loop.
exec env AXEYUM_LRA_TABLEAU_RESERVE=sparse \
  /nas3/data/axeyum/harness/lra-trace/bin/smtcomp_cli.arm "$@"
