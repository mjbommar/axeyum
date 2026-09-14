#!/usr/bin/env bash
# SKELETON-REACH -- prove the noise phase really runs the SAME arm twice.
#
# A noise floor derived by editing the A/B runner is a claim until something
# checks it: ADR-2025's first attempt to derive one by `sed` silently failed to
# substitute one branch, which would have produced a second copy of the real
# A/B still labelled a noise floor. This checks the mechanism and is itself
# MUTATION-VERIFIED: arming the noise branch must make it exit 1.
#
#   ab-verify-noise.sh <ab-run.sh>
set -u
R="${1:-$(cd "$(dirname "$0")" && pwd)/ab-run.sh}"
[ -r "$R" ] || { echo "ABORT: $R missing"; exit 2; }

# The noise branch must call the BASE runner and return before ever reaching
# the armed `env`.
if ! grep -qE '^\s+if \[ "\$PHASE" = noise \]; then$' "$R"; then
  echo "FAIL: no noise branch in arm_run"
  exit 1
fi
BODY=$(sed -n '/if \[ "\$PHASE" = noise \]; then/,/^  fi$/p' "$R")
if ! printf '%s' "$BODY" | grep -qE 'base_run "\$1"'; then
  echo "FAIL: the noise branch does not call base_run -- it is NOT a same-arm phase"
  exit 1
fi
if ! printf '%s' "$BODY" | grep -qE '^\s+return$'; then
  echo "FAIL: the noise branch does not return -- it falls through to the ARMED env"
  exit 1
fi
if printf '%s' "$BODY" | grep -qE 'AXEYUM_DECLARED_NAME_WINS=on|AXEYUM_DISTINCT_LINEAR=on'; then
  echo "FAIL: the noise branch arms a lever"
  exit 1
fi
echo "NOISE-OK: phase=noise runs base_run twice; the armed env is unreachable from it"
