#!/usr/bin/env bash
# The pre-push L0 block must actually run the gates it lists, and one of them
# must be the partition-edge gate.
#
# WHY. ADR-1546 measured the exact hole this control pins. The property "no
# `depends_on` edge crosses an evaluation partition" was enforced by
# `scripts/check-autogenesis-nursery.py`, registered in `scripts/check.sh` and
# the `justfile` and in NO hook. So a producer closed a fact whose dependency
# fused train and development and pushed it -- twice on 2026-09-01 -- with the
# property never evaluated at push time. A gate registered only in the
# ~10-minute aggregate is a gate that reports days late, and by then the
# finding had been absorbed into an exemption re-scoped 228 -> 230 -> 258 ->
# 274 in four days.
#
# So ADR-1550 put `check-partition-edges.py --baseline` in the L0 block, and
# this control is what makes that placement survive an edit. It is STATIC on
# purpose: running the hook would run the whole battery, and what went wrong
# was a missing line in a list, which is a property of the file.
#
# THE ARMS
#   A  the L0 loop exists and names at least three gates (a loop that lost its
#      list still `for`s over nothing and the block still prints its green
#      line).
#   B  every script the loop names EXISTS and is a real file -- a renamed gate
#      would otherwise fail the push for a reason nobody could act on, which
#      is how a fail-closed gate gets a skip switch added to it.
#   C  `check-partition-edges.py` is one of them, with `--baseline`. The bare
#      form audits all 198 recorded crossings at 27s and would be removed from
#      the hook within a day; the ratchet form is 0.13s. Naming the FLAG is
#      the point, not decoration.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

# `PREPUSH_L0_HOOK` points this control at a scratch copy of the hook so each
# arm can be driven to failure without editing the real one. Unset in every
# real run; a control whose guards were never seen to fire is decoration.
HOOK=${PREPUSH_L0_HOOK:-hooks/pre-push}
fail=0

if [ ! -f "$HOOK" ]; then
  echo "FAIL: $HOOK is absent -- this control has no subject." >&2
  exit 2
fi

# The block is `for l0_gate in \ "script args" \ ... ; do`. Take the quoted
# entries between the `for` line and the `do`, which is the list the loop
# actually iterates -- never a hand-maintained copy of it.
block=$(awk '/^for l0_gate in/{grab=1} grab{print} /^do$/{if (grab) exit}' "$HOOK")
gates=$(printf '%s\n' "$block" \
  | /usr/bin/grep -oE '"scripts/[^"]+"' \
  | tr -d '"')

count=$(printf '%s\n' "$gates" | /usr/bin/grep -c . || true)
if [ "$count" -lt 3 ]; then
  fail=1
  echo "FAIL: the pre-push L0 loop names $count gate(s); expected at least 3." >&2
  echo "      A loop whose list was emptied still runs, still prints" >&2
  echo "      'L0 safety gates passed', and checks nothing." >&2
fi

while IFS= read -r entry; do
  [ -n "$entry" ] || continue
  script=${entry%% *}
  if [ ! -f "$script" ]; then
    fail=1
    echo "FAIL: L0 gate '$script' does not exist." >&2
    echo "      The loop is fail-closed, so a renamed gate blocks every push" >&2
    echo "      with an error nobody can act on." >&2
  fi
done <<EOF
$gates
EOF

# ADR-1550. The gate AND its flag.
if ! printf '%s\n' "$gates" \
    | /usr/bin/grep -qx 'scripts/check-partition-edges.py --baseline'; then
  fail=1
  echo "FAIL: the L0 block does not run" >&2
  echo "      'scripts/check-partition-edges.py --baseline'." >&2
  echo "      ADR-1546 measured two partition-fusing edges pushed while the" >&2
  echo "      only gate for that property lived in the ~10-minute aggregate." >&2
  echo "      ADR-1550 put the per-edge ratchet here; the ratchet form is" >&2
  echo "      0.13s, the bare audit is 27s and would not survive in a hook." >&2
  echo "      It is listed: $(printf '%s' "$gates" | tr '\n' ' ')" >&2
fi

if [ "$fail" -eq 0 ]; then
  echo "PREPUSH_L0|gates=$count|partition_edges=present|PASS"
  exit 0
fi
echo "PREPUSH_L0|FAILED"
exit 1
