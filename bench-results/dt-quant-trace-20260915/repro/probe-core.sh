#!/usr/bin/env bash
# DT-QUANT-TRACE -- full QPROBE output for one file.
#
#   probe-core.sh <file.smt2> [<smtcomp_cli>] [budget_ms]
#
# `AXEYUM_QPROBE` is the ONLY channel that says which exit
# `prove_unsat_by_mbqi_inner` took. Its own doc comment (auto.rs:12740) says
# why: the rung's `qtrace` line cannot distinguish "the MBQI refutation loop ran
# and failed" from "a shape guard fired and the call was e-matching all along",
# because the two are the same `Ok(Unknown)` at the call site. This lane's whole
# question is which of those produced the datatype sentence, so it is measured
# here rather than inferred from the message.
set -u
F="$1"
AX="${2:-/nas3/data/axeyum/harness/dt-quant-trace/bin/smtcomp_cli-base}"
MS="${3:-24000}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
AXEYUM_TRACE=1 AXEYUM_QPROBE=1 timeout 120 "$AX" "$F" --timeout-ms "$MS" 2>&1 \
  | cut -c1-300
