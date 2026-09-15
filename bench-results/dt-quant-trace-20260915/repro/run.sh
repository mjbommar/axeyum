#!/usr/bin/env bash
# DT-QUANT-TRACE -- the mechanism experiment, three files, one command.
#
#   run.sh [<smtcomp_cli>]
#
# THE QUESTION. ADR-2090's give-up census reports "17 mbqi datatype declines in
# three wordings", and the message really does read
#
#     mbqi declined an unsupported fragment: congruence over a datatype
#     argument whose expansion is not exact ... (ADR-0022)
#
# which says MBQI refused a datatype construct. Reading the code says otherwise:
# `prove_unsat_by_mbqi_inner` (auto.rs:12777) solves its GROUND seed with
# `check_mbqi_ground_seed` -> `check_auto` (auto.rs:12319) under a `?`, and
# `auto.rs:2473` wraps whatever error comes back in the "mbqi declined" prefix.
# If that reading is right the refusal is in the quantifier-FREE closure and has
# nothing to do with quantifiers.
#
# THE EXPERIMENT. Three files that differ in exactly one thing each:
#
#   ground.smt2           inexact datatype, UF over it, NO quantifier
#   quantified.smt2       the same, PLUS one universal
#   exact-quantified.smt2 the same universal, but the datatype is EXACT
#
# Predictions, written before running it:
#   * `ground` declines with the ADR-0022 congruence sentence and NO "mbqi"
#     prefix -- there is no quantifier for MBQI to have declined.
#   * `quantified` declines with the SAME sentence, now behind the prefix.
#   * `exact-quantified` does NOT decline -- the control, so the experiment is
#     measuring exactness and not merely the presence of a datatype.
#
# A run where all three decline, or where none does, refutes the reading.
set -u
AX="${1:-/nas3/data/axeyum/harness/dt-quant-trace/bin/smtcomp_cli-base}"
HERE="$(cd "$(dirname "$0")" && pwd)"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

for f in ground quantified exact-quantified; do
  echo "===== $f.smt2 ====="
  AXEYUM_TRACE=1 AXEYUM_QPROBE=1 timeout 60 "$AX" "$HERE/$f.smt2" \
    --timeout-ms 10000 2>&1 \
    | grep -E '^(sat|unsat|unknown)$|^; give-up|^; route |\[mbqi-shape\]|\[mbqi-census\]' \
    | cut -c1-260
done
