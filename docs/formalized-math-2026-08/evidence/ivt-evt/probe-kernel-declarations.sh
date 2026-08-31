#!/usr/bin/env bash
# Probe the kernel environment for declarations, recording the REAL exit status
# per name. Positive controls run first so an empty answer cannot be mistaken
# for a negative result.
#
# NOTE on a bug this script had, and why it is written this way now: the first
# version did
#     out="$(cmd | head -2)"; st="${PIPESTATUS[0]}"
# which reports the status of the ASSIGNMENT, not of `cmd` -- so every probe
# printed status=0, including the ones where the tool correctly refused. That
# is the banned `echo "exit=$?" after a pipeline` idiom wearing a different
# hat. Run the command bare into a file, capture `$?` immediately, and only
# then read the file.
B=./target/release/examples/kernel_declaration_projection
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

probe() {
  local n="$1" st
  "$B" --require-declaration "$n" > "$TMP" 2>&1
  st=$?
  printf '%-34s status=%s  %s\n' "$n" "$st" "$(head -2 "$TMP" | tr '\n' '|' | cut -c1-140)"
}

echo "--- POSITIVE CONTROLS (must be status=0 and 'found') ---"
probe CReal.UniformlyContinuousOn
probe CReal.lt_cotrans
probe CReal.maxRange
probe CReal.ivt_approx

echo "--- NEGATIVES UNDER TEST (must be NONZERO status) ---"
probe CReal.ContinuousOn
probe CReal.Continuous
probe CReal.supOn
probe CReal.sup
probe CReal.le_total
probe CReal.lt_total
probe CReal.ivt_approx_at
probe CReal.evt_approx_max
probe CReal.evtSupOn
