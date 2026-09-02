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
#   D-F  `check-development-partition.py`, `check-autogenesis-holdout-
#      isolation.py` and `check-holdout-adjacency.py` joined 2026-09-02: all
#      three were registered only in `scripts/check.sh`/`justfile` (the same
#      ~10-minute-aggregate hole ADR-1546 measured for the edge gate) and
#      `check-holdout-isolation`/`check-holdout-adjacency` are the exact two
#      gates ADR-1546's own table shows fusing evaluation partitions when
#      nothing runs them at push time.
#   G  `check-draw7-frozen-families.py` is one of them, with `--before`. This
#      one is worse than "aggregate-only": it was invoked by NOTHING at all
#      before 2026-09-02, not even `check.sh`. It is a DIFF gate (its default
#      `--before HEAD~1` only sees the tip commit of a push), so the arm
#      checks for the flag rather than a bare match -- a bare invocation would
#      silently miss every commit but the last in a batched push.
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

# ADR-1546 (arms D-F). Bare match: these three are plain state checks with no
# flag to lose.
for want in \
  "scripts/check-development-partition.py" \
  "scripts/check-autogenesis-holdout-isolation.py" \
  "scripts/check-holdout-adjacency.py"
do
  if ! printf '%s\n' "$gates" | /usr/bin/grep -qx "$want"; then
    fail=1
    echo "FAIL: the L0 block does not run '$want'." >&2
    echo "      ADR-1546's own table shows this is one of the two gates that" >&2
    echo "      already caught a real partition fusion, and it ran only in" >&2
    echo "      the ~10-minute aggregate -- days after the push it should" >&2
    echo "      have blocked." >&2
  fi
done

# arm G. `check-draw7-frozen-families.py` is a DIFF gate: naming the FLAG
# matters here even more than for arm C, because the gate's OWN default
# (`--before HEAD~1`) is wrong for a hook that must see a whole pushed range,
# not just its tip commit. A bare match would pass while the hook silently
# reverted to the single-commit default.
if ! printf '%s\n' "$gates" | /usr/bin/grep -qE '^scripts/check-draw7-frozen-families\.py --before '; then
  fail=1
  echo "FAIL: the L0 block does not run" >&2
  echo "      'scripts/check-draw7-frozen-families.py --before <ref>'." >&2
  echo "      This gate was invoked by NOTHING before 2026-09-02 -- not even" >&2
  echo "      check.sh -- and its bare form silently checks only HEAD~1," >&2
  echo "      missing every earlier commit in a batched push." >&2
  echo "      It is listed: $(printf '%s' "$gates" | tr '\n' ' ')" >&2
fi

if [ "$fail" -eq 0 ]; then
  echo "PREPUSH_L0|gates=$count|partition_edges=present|PASS"
  exit 0
fi
echo "PREPUSH_L0|FAILED"
exit 1
