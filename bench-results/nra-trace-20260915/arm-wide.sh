#!/usr/bin/env bash
# A/B arm B: 16x the CAD cell cap.
export AXEYUM_NRA_CAD=wide
exec /nas3/data/axeyum/scratch/nra-trace-20260915/smtcomp_cli_v2 "$@"
