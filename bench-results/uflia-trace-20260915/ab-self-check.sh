#!/usr/bin/env bash
# UFLIA-TRACE -- does `AXEYUM_QINST_TRIGGER_ALTERNATIVES` actually reach the
# solve in this binary, through this harness, on this host?
#
#   ab-self-check.sh <bin> [valueB]
#
# A one-binary A/B cannot be sabotaged by using the same build twice, but it has
# the same failure in a different shape: if the variable never arrives, BOTH arms
# are the shipped arm and the run prints a perfect zero indistinguishable from
# agreement. Four ways that happens here and each has been real somewhere in this
# repository: the CLI solves on a WATCHDOG WORKER THREAD (a thread-local override
# would be inert, the environment is not); the cap resolves through a `OnceLock`
# (a value set after the first read is ignored); `taskset`/`bash -c` wrappers can
# drop the environment; and the shipped `1` and an unset variable are different
# code paths through `cap_lever!`.
#
# So this asserts a DIFFERENCE, on a fixture built to have one: a universal whose
# body carries two INCOMPARABLE full-cover candidates, `f(x)` and `g(x)`. The
# shipped arm must report `alternatives=1` and arm B `alternatives=<valueB>`.
# Exit status depends on the finding.
set -u
AX="${1:?usage: ab-self-check.sh <bin> [valueB]}"
VB="${2:-4}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

TMP=$(mktemp -d "${TMPDIR:-/tmp}/uflia-trace-selfcheck.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/two-candidates.smt2" <<'SMT'
(set-logic UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-const b U)
(assert (forall ((x U)) (= (f x) (g x))))
(assert (not (= (f b) (g b))))
(check-sat)
SMT

alts() {  # $1 = "" for the shipped arm, else the cap value
  local raw
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_TRIGGER_ALTERNATIVES AXEYUM_QPROBE=1 \
            "$AX" "$TMP/two-candidates.smt2" --timeout-ms 10000 2>&1)
  else
    raw=$(AXEYUM_QINST_TRIGGER_ALTERNATIVES="$1" AXEYUM_QPROBE=1 \
            "$AX" "$TMP/two-candidates.smt2" --timeout-ms 10000 2>&1)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE 'QPROBE auto-triggers vars=[0-9]+ alternatives=[0-9]+' \
    | grep -oE 'alternatives=[0-9]+' | cut -d= -f2
}

A=$(alts "")
B=$(alts "$VB")
echo "shipped arm: alternatives=${A:-MISSING}"
echo "arm B ($VB):  alternatives=${B:-MISSING}"

if [ -z "${A:-}" ] || [ -z "${B:-}" ]; then
  echo "SELF-CHECK FAILED: no QPROBE auto-triggers line. The probe did not run,"
  echo "  so this check cannot tell the arms apart and neither can the A/B."
  exit 3
fi
if [ "$A" != 1 ]; then
  echo "SELF-CHECK FAILED: the shipped arm reported alternatives=$A, not 1."
  echo "  The lever is not OFF by default in this binary."
  exit 4
fi
if [ "$B" -le "$A" ]; then
  echo "SELF-CHECK FAILED: arm B reported alternatives=$B, no more than the"
  echo "  shipped arm's $A. The variable is not reaching the solve, so both arms"
  echo "  are the shipped arm and every number the A/B prints is vacuous."
  exit 5
fi
echo "SELF-CHECK PASSED: the two arms differ ($A vs $B) through this binary and harness."
