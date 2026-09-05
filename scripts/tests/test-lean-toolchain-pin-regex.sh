#!/usr/bin/env bash
# Negative and positive controls for the Lean toolchain PIN REGEX in
# scripts/install-pinned-lean.sh.
#
# The defect this exists for, measured 2026-09-05: ADR-1594 (2026-09-03,
# commit 792224e73) moved `lean-toolchain` from
# `leanprover/lean4:v4.30.0` to `leanprover/lean4:v4.34.0-rc1`, and the
# install script's regex (`^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+$`) had
# no `-rcN` alternative, so CI's "real Lean kernel + solver-proof
# cross-check" job died at "install pinned official Lean toolchain" with
# `unexpected lean-toolchain value: leanprover/lean4:v4.34.0-rc1`. The ADR's
# claim that "no workflow edit is needed" was false.
#
# This script runs the install script's `--validate-only PIN` mode, which
# exercises exactly the regex the real install path uses and DOES NOT
# download elan, install anything, or touch the network. Every control below
# pins a specific value through the specific flag and checks the specific
# exit status and message -- not merely "the script exits nonzero", which a
# missing-file or usage error also produces.
#
# Usage: scripts/tests/test-lean-toolchain-pin-regex.sh
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

INSTALL_SCRIPT=./scripts/install-pinned-lean.sh

fail=0
pass() { printf 'toolchain-pin-regex: PASS  %s\n' "$1"; }
bad() {
  printf 'toolchain-pin-regex: FAIL  %s\n' "$1" >&2
  fail=1
}

# check NAME VALUE EXPECT_STATUS
check() {
  local name=$1 value=$2 expect=$3
  local out status
  out=$("$INSTALL_SCRIPT" --validate-only "$value" 2>&1)
  status=$?
  if [ "$status" -ne "$expect" ]; then
    bad "$name: expected exit $expect, got $status for value '$value' (output: $out)"
    return
  fi
  if [ "$expect" -eq 0 ] && [[ "$out" != valid:* ]]; then
    bad "$name: exit 0 but output did not say 'valid:' (output: $out)"
    return
  fi
  if [ "$expect" -ne 0 ] && [[ "$out" != invalid:* ]]; then
    bad "$name: nonzero exit but output did not say 'invalid:' (output: $out)"
    return
  fi
  pass "$name ($value -> exit $status)"
}

# ---------------------------------------------------------------------------
# 1. The actual committed pin file value must validate. This is the control
#    that catches a regressed regex against the LIVE pin, not a synthetic one.
# ---------------------------------------------------------------------------
live_pin=$(tr -d '[:space:]' <lean-toolchain)
check "1 the committed lean-toolchain pin ($live_pin) is accepted" "$live_pin" 0

# ---------------------------------------------------------------------------
# 2. The pre-ADR-1594 pin shape (plain X.Y.Z, no suffix) still validates --
#    the corpus/import toolchain (v4.30.0) is exactly this shape and the
#    install script serves both pins.
# ---------------------------------------------------------------------------
check "2 a plain X.Y.Z pin (leanprover/lean4:v4.30.0)" "leanprover/lean4:v4.30.0" 0

# ---------------------------------------------------------------------------
# 3. The release-candidate shape the current cross-check pin actually uses.
#    This is the exact value that regressed CI on 792224e73.
# ---------------------------------------------------------------------------
check "3 a release-candidate pin (leanprover/lean4:v4.34.0-rc1)" \
  "leanprover/lean4:v4.34.0-rc1" 0

# ---------------------------------------------------------------------------
# 4-7. Malformed values must be REJECTED, by name -- a regex that accepts
#    everything would pass controls 1-3 vacuously.
# ---------------------------------------------------------------------------
check "4 missing the leading 'v'" "leanprover/lean4:4.34.0-rc1" 1
check "5 wrong project name" "leanprover/lean3:v4.34.0" 1
check "6 a non-numeric release-candidate segment" \
  "leanprover/lean4:v4.34.0-rcX" 1
check "7 an unrelated garbage string" "not-a-toolchain-pin" 1
check "8 empty string" "" 1

if [ "$fail" -ne 0 ]; then
  echo "toolchain-pin-regex: FAILED" >&2
  exit 1
fi
echo "toolchain-pin-regex: all controls passed"
