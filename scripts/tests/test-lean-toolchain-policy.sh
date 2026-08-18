#!/usr/bin/env bash
# Negative controls for the Lean TOOLCHAIN RESOLUTION POLICY.
#
# The defect these exist for, measured on the development host 2026-08-17: two
# Lean toolchains were installed (v4.30.0, the pin, and v4.34.0-rc1), and the two
# implementations of discovery DISAGREED about which to use --
# `scripts/check-lean-gate.sh` tried `command -v lean` first and found elan's
# default, `crates/axeyum-lean-kernel/tests/support/lean_probe.rs` sorted elan's
# toolchain directories newest-name-first and took the release candidate. Under
# 4.34, 21 of 77 `lean_crosscheck` families were rejected and the lean4export
# replay script did not elaborate at all. So the gate's verdict depended on an
# unstated fact about the machine, and nothing in its output named the checker.
#
# A guard nobody points at the wrong thing is not a guard. Each control below
# pushes the system into the exact state it is supposed to reject and requires
# the rejection, BY NAME -- not merely a nonzero exit, which a compile error also
# produces.
#
# It also refuses to pass vacuously: control 5 needs a SECOND, non-pinned
# toolchain to be installed, and if there is not one it says so and FAILS rather
# than reporting a green run over a question it could not ask.
#
# Usage: scripts/tests/test-lean-toolchain-policy.sh
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

GATE=./scripts/check-lean-gate.sh
PIN=$(tr -d '[:space:]' <lean-toolchain)
PIN_VERSION="${PIN##*:v}"
PIN_DIRECTORY=$(printf '%s' "$PIN" | sed 's|/|--|g; s|:|---|g')

fail=0
pass() { printf 'toolchain-policy: PASS  %s\n' "$1"; }
bad() {
  printf 'toolchain-policy: FAIL  %s\n' "$1" >&2
  fail=1
}

# ---------------------------------------------------------------------------
# Locate an installed toolchain that is NOT the pin, for the wrong-toolchain
# controls. Absence is reported, never assumed away.
# ---------------------------------------------------------------------------
pinned_bin=""
other_bin=""
other_version=""
for root in "${ELAN_HOME:-}" "$HOME/.elan/elan-home" "$HOME/.elan"; do
  [ -n "$root" ] && [ -d "$root/toolchains" ] || continue
  for directory in "$root"/toolchains/*/; do
    candidate="${directory}bin/lean"
    [ -x "$candidate" ] || continue
    name=$(basename "${directory%/}")
    if [ "$name" = "$PIN_DIRECTORY" ]; then
      [ -z "$pinned_bin" ] && pinned_bin="$candidate"
    elif [ -z "$other_bin" ]; then
      other_bin="$candidate"
      other_version=$("$candidate" --version 2>&1 | head -1)
    fi
  done
done

if [ -z "$pinned_bin" ]; then
  echo "toolchain-policy: cannot run -- the PINNED toolchain $PIN is not installed, so every" \
       "control below would be testing the absence path only." >&2
  exit 2
fi
echo "toolchain-policy: pin $PIN at $pinned_bin"
if [ -n "$other_bin" ]; then
  echo "toolchain-policy: non-pinned toolchain available for the wrong-toolchain controls:" \
       "$other_bin [$other_version]"
else
  echo "toolchain-policy: NO second toolchain is installed." >&2
fi

# ---------------------------------------------------------------------------
# 1. Resolution picks the pin, and says so.
# ---------------------------------------------------------------------------
gate_out=$($GATE --print-toolchain 2>/dev/null)
gate_bin=$(sed -n 's/^bin=//p' <<<"$gate_out")
gate_real=$(sed -n 's/^real=//p' <<<"$gate_out")
gate_version=$(sed -n 's/^version=//p' <<<"$gate_out")
if [ -z "$gate_bin" ]; then
  bad "1 the gate could not resolve any toolchain (--print-toolchain printed nothing)"
elif ! grep -q "version $PIN_VERSION," <<<"$gate_version"; then
  bad "1 the gate resolved a Lean that is not the pinned $PIN_VERSION: $gate_version"
else
  pass "1 the gate resolves the pinned $PIN_VERSION ($gate_bin)"
fi

# ---------------------------------------------------------------------------
# 2. The Rust probe resolves the SAME binary. This is the control that would
#    have caught the original defect: the two implementations agreeing is a
#    measurement, not a comment.
# ---------------------------------------------------------------------------
probe_log=$(cargo test -q -p axeyum-lean-kernel --test real_lean_kernel_replay -- --nocapture 2>&1)
probe_bin=$(sed -n 's/.*AXEYUM-LEAN-TOOLCHAIN [^ ]* bin=\(.*\) version=.*/\1/p' <<<"$probe_log" |
  head -1)
if [ -z "$probe_bin" ]; then
  bad "2 the Rust probe printed no AXEYUM-LEAN-TOOLCHAIN banner, so which Lean it used is unknown"
else
  probe_real=$(readlink -f "$probe_bin" 2>/dev/null || printf '%s' "$probe_bin")
  if [ "$probe_real" != "$gate_real" ]; then
    bad "2 shell gate and Rust probe DISAGREE: gate=$gate_real probe=$probe_real"
  else
    pass "2 shell gate and Rust probe resolve the same binary ($probe_real)"
  fi
fi

# ---------------------------------------------------------------------------
# 3. An unresolvable override stops the search. Without this, the negative
#    control `AXEYUM_LEAN_BIN=/nonexistent` would quietly find elan's toolchain.
# ---------------------------------------------------------------------------
out=$(AXEYUM_LEAN_BIN=/nonexistent-lean $GATE --print-toolchain 2>&1)
status=$?
if [ "$status" -eq 0 ]; then
  bad "3 an unresolvable AXEYUM_LEAN_BIN was silently replaced by a search hit"
elif ! grep -q 'no Lean matching the pin' <<<"$out"; then
  bad "3 an unresolvable AXEYUM_LEAN_BIN failed for an unnamed reason: $(head -1 <<<"$out")"
else
  pass "3 an unresolvable AXEYUM_LEAN_BIN fails, by name, without searching on"
fi

# ---------------------------------------------------------------------------
# 4. ...and AXEYUM_ALLOW_NO_LEAN=1 turns that into a LOUD skip, not a pass.
# ---------------------------------------------------------------------------
out=$(AXEYUM_LEAN_BIN=/nonexistent-lean AXEYUM_ALLOW_NO_LEAN=1 $GATE 2>&1)
status=$?
if [ "$status" -ne 0 ]; then
  bad "4 AXEYUM_ALLOW_NO_LEAN=1 did not produce the documented exit-0 skip"
elif ! grep -q 'SKIPPED -- 0 real-Lean checks ran' <<<"$out"; then
  bad "4 the no-Lean skip did not say that ZERO checks ran"
else
  pass "4 no toolchain + AXEYUM_ALLOW_NO_LEAN=1 is a loud skip that names the zero"
fi

# ---------------------------------------------------------------------------
# 5. THE WRONG TOOLCHAIN. Point both entry points at a Lean that is not the pin
#    and require each to refuse, by name.
# ---------------------------------------------------------------------------
if [ -z "$other_bin" ]; then
  bad "5 NOT RUN -- no non-pinned toolchain is installed, so the wrong-toolchain controls could" \
      "not be exercised. This is a failure and not a pass: install a second toolchain (e.g."
  echo "toolchain-policy:       elan toolchain install leanprover/lean4:v4.34.0-rc1) or run this" \
       "on a host that has one." >&2
else
  # 5a. The shell gate refuses, before running a single suite.
  out=$(AXEYUM_LEAN_BIN="$other_bin" $GATE --print-toolchain 2>&1)
  status=$?
  if [ "$status" -eq 0 ]; then
    bad "5a the gate ACCEPTED a non-pinned toolchain ($other_version)"
  elif ! grep -q 'TOOLCHAIN MISMATCH' <<<"$out"; then
    bad "5a the gate refused the non-pinned toolchain for an unnamed reason: $(tail -1 <<<"$out")"
  else
    pass "5a the shell gate refuses a non-pinned toolchain, naming both versions"
  fi

  # 5b. The Rust probe refuses too -- a suite run directly, without the gate,
  #     must not silently check a different claim.
  out=$(AXEYUM_LEAN_BIN="$other_bin" AXEYUM_REQUIRE_LEAN=1 \
    cargo test -q -p axeyum-lean-kernel --test real_lean_kernel_replay -- --nocapture 2>&1)
  status=$?
  if [ "$status" -eq 0 ]; then
    bad "5b the Rust probe ACCEPTED a non-pinned toolchain ($other_version) under REQUIRE_LEAN"
  elif ! grep -q 'TOOLCHAIN MISMATCH' <<<"$out"; then
    bad "5b the suite failed under a non-pinned toolchain for an unnamed reason"
  else
    pass "5b the Rust probe refuses a non-pinned toolchain, naming both versions"
  fi

  # 5c. ...and the refusal is the GUARD, not the environment. With the deviation
  #     stated the same suite passes, so 5b's failure cannot be dismissed as
  #     "4.34 just does not work here".
  out=$(AXEYUM_LEAN_BIN="$other_bin" AXEYUM_REQUIRE_LEAN=1 AXEYUM_LEAN_ALLOW_UNPINNED=1 \
    cargo test -q -p axeyum-lean-kernel --test real_lean_kernel_replay -- --nocapture 2>&1)
  status=$?
  if [ "$status" -ne 0 ]; then
    bad "5c AXEYUM_LEAN_ALLOW_UNPINNED=1 did not make the suite pass under $other_version, so 5b" \
        "proves only that this toolchain is broken here, not that the guard fired"
    tail -20 <<<"$out" >&2
  elif ! grep -q 'matches_pin=false' <<<"$out"; then
    bad "5c the stated-deviation run did not print matches_pin=false; the banner hides the fact" \
        "that a non-pinned Lean produced these verdicts"
  else
    pass "5c with the deviation stated the same suite passes, and every banner says matches_pin=false"
  fi
fi

if [ "$fail" -ne 0 ]; then
  echo "toolchain-policy: FAILED" >&2
  exit 1
fi
echo "toolchain-policy: OK -- resolution is pinned, stated, agreed between both entry points, and" \
     "refuses a non-pinned toolchain in both"
