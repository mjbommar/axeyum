#!/usr/bin/env bash
# A/B arm A: the shipped CAD cell cap. The env var is SET and empty rather than
# unset so the two arms differ in a VALUE, not in the shape of the environment.
export AXEYUM_NRA_CAD=
exec /nas3/data/axeyum/scratch/nra-trace-20260915/smtcomp_cli_v2 "$@"
