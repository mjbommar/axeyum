#!/usr/bin/env bash
# ZERO-INST -- assert the noise-floor runner really is byte-identical in both
# arms, and that the real runner really is not.
#
#   ab-verify-noise.sh
#
# A noise floor that quietly arms one arm becomes a second copy of the real
# A/B and makes the lever's effect look like variance. Exit status depends on
# the finding; this is run before the noise phase, not after it.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
REAL="$HERE/ab-run.sh"
NOISE="$HERE/ab-run-noise.sh"
rc=0

# Count only the two `run_arm` invocation branches, not the header comments:
# the header NAMES the variable and would otherwise be counted as arming it.
arming() { grep -cE '^ +raw=\$\(AXEYUM_ZERO_INST_SKELETON=1' "$1" || true; }
unsetting() { grep -cE '^ +raw=\$\(env -u AXEYUM_ZERO_INST_SKELETON' "$1" || true; }

echo "real  runner: arming=$(arming "$REAL")  unsetting=$(unsetting "$REAL")"
echo "noise runner: arming=$(arming "$NOISE")  unsetting=$(unsetting "$NOISE")"

if [ "$(arming "$REAL")" != 1 ] || [ "$(unsetting "$REAL")" != 1 ]; then
  echo "FAIL: ab-run.sh must have exactly one armed and one unset branch"
  rc=1
fi
if [ "$(arming "$NOISE")" != 0 ] || [ "$(unsetting "$NOISE")" != 2 ]; then
  echo "FAIL: ab-run-noise.sh must arm NOTHING and unset in BOTH branches"
  rc=1
fi
if [ "$rc" = 0 ]; then
  echo "NOISE-RUNNER-OK: both arms shipped; the real runner differs by one arm"
fi
exit "$rc"
