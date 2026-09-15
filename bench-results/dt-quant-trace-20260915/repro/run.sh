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
# `prove_unsat_by_mbqi_inner` (auto.rs:12862) solves its GROUND seed with
# `check_mbqi_ground_seed` -> `check_auto` under a `?`, and `auto.rs:2488` wraps
# whatever error comes back in the "mbqi declined" prefix. If that reading is
# right the refusal is in the quantifier-FREE closure and has nothing to do with
# quantifiers.
#
# HOW IT TURNED OUT, recorded here because a hypothesis left in a file as though
# it were the finding is how a stale reading gets cited later (ADR-2114 §1).
#
#   * The DIRECTION was right and the ROUTE was wrong. The refusal is indeed
#     raised by the quantifier-free closure -- but not by MBQI's ground seed,
#     because on 132 of 134 measured files MBQI's refutation loop is never
#     entered at all. A quantifier SHAPE guard diverts to
#     `prove_unsat_by_ematching` first, and it is E-MATCHING's ground
#     `check_auto` (`decide_instantiation`, auto.rs:13482) whose `?` carries the
#     error back to the "mbqi declined" prefix.
#   * THESE THREE FILES DO NOT TEST EITHER READING. All three are decided --
#     `ground.smt2` by `qf-bv`, the other two by `q:bool-skeleton` -- before the
#     datatype rung runs at all. They are kept because that is the finding:
#     a reproducer small enough to write by hand is decided by a rung above the
#     one under test. `degroundify.py` beside them is the replacement, and
#     `probe-core.sh` on a real core is what actually settled it.
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
