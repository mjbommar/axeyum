#!/usr/bin/env bash
# Did MY turn leave the repository safe? One command, run before you finish.
#
# WHY THIS EXISTS. A lane finishing a turn has to satisfy about eight separate
# rules spread across CLAUDE.md, three plan docs and a retrospective: do not
# settle a held-out fact, do not leave a generated ledger stale, do not register
# an operation without moving its pin, regenerate what is downstream of the
# evaluation population. Measured 2026-08-21/22, a careful lane working for ten
# hours violated two of them without ever seeing either -- not through
# inattention, but because nothing in its loop reported on them.
#
# Rules a contributor must REMEMBER are a design defect. This is the same rule
# in the shape that works: a command whose exit status depends on the finding.
#
# ATTRIBUTION IS THE POINT, not just the pass/fail. This repository has many
# lanes writing at once and gates are routinely red for reasons that are not
# yours -- measured 2026-08-22, six autogenesis gates were already failing at
# HEAD before this lane touched anything. An agent that cannot tell "mine" from
# "already broken" does one of two harmful things: it panics and reverts good
# work, or it "fixes" a file another lane is mid-flight on. So every FAIL is
# re-run against the merge-base and labelled NEW or PRE-EXISTING.
#
# The base re-run only happens for gates that are actually failing, so a clean
# turn costs nothing extra.
#
# Usage:
#   scripts/check-lane-turn.sh            # attribute failures against origin/main
#   scripts/check-lane-turn.sh --no-blame # skip the base comparison (faster, blunter)
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

BLAME=1
[ "${1:-}" = "--no-blame" ] && BLAME=0

# Cheap, deterministic gates that cover the failure modes a turn can introduce.
# Deliberately NOT the whole aggregate gate: this must be fast enough that a lane
# actually runs it, and `just check` remains the thing that must pass to merge.
GATES=(
  "holdout-isolation|python3 scripts/check-autogenesis-holdout-isolation.py"
  "production-provenance|python3 scripts/gen-production-provenance-ledger.py --check"
  "theorem-production|python3 scripts/gen-theorem-production-ledger.py --check"
  "fact-ledger|python3 scripts/validate-facts.py"
  "nursery-split|python3 scripts/create-autogenesis-mathlib-nursery-split.py --check"
  "nursery|python3 scripts/check-autogenesis-nursery.py"
  "operations-registry|python3 scripts/validate-autogenesis-operations.py"
  "operations-registry-tests|python3 -m unittest scripts.tests.test_validate_autogenesis_operations"
  "plan-generated|python3 scripts/gen-plan.py --check"
  "adr-index|python3 scripts/gen-adr-index.py --check"
  "docs-links|./scripts/check-links.sh"
)

# Degrade cleanly outside a git checkout. `scripts/lane-snapshot.sh` extracts with
# `git archive | tar -x`, so a snapshot is a working TREE with no repository, and
# every git call here fails there. Left unhandled, `git diff` printed "fatal: not
# a git repository" into the report and the turn section silently stopped working
# -- found by this script's own control suite, which runs it in exactly that
# tree. A tool that cannot see git should say so, not emit a fatal and continue.
if git rev-parse --git-dir >/dev/null 2>&1; then
  HAVE_GIT=1
  BASE=$(git merge-base HEAD origin/main 2>/dev/null || git rev-parse HEAD)
else
  HAVE_GIT=0
  BASE=""
  BLAME=0
fi
SNAP=""
snapshot() {
  [ -n "$SNAP" ] && return 0
  SNAP=$(scripts/lane-snapshot.sh "$BASE" 2>/dev/null | tail -1)
  [ -d "$SNAP" ] || { SNAP=""; return 1; }
}

new=0 pre=0 pass=0
declare -a NEW_FAILURES=()
printf '%s\n' "--- gates ---"
for spec in "${GATES[@]}"; do
  name="${spec%%|*}"; cmd="${spec#*|}"
  if eval "$cmd" >/dev/null 2>&1; then
    printf '  PASS          %s\n' "$name"; pass=$((pass + 1)); continue
  fi
  label="FAIL"
  if [ "$BLAME" = 1 ] && snapshot; then
    if ( cd "$SNAP" && eval "$cmd" >/dev/null 2>&1 ); then
      label="FAIL (NEW)"; new=$((new + 1)); NEW_FAILURES+=("$name")
    else
      label="FAIL (PRE-EXISTING — not yours, do NOT 'fix' it blind)"; pre=$((pre + 1))
    fi
  else
    new=$((new + 1)); NEW_FAILURES+=("$name")
  fi
  printf '  %-12s  %s\n' "$label" "$name"
done
[ -n "$SNAP" ] && rm -rf "$SNAP"

# --- what your turn did to the two numbers that matter ----------------------
printf '%s\n' "--- your turn ---"
prov=$(python3 scripts/gen-production-provenance-ledger.py 2>/dev/null | tail -1)
printf '  %s\n' "${prov:-provenance ledger did not run}"

# A new operation naming exactly one fact is activity, not production. This is
# not an error and is not gated -- it is reported, because the whole finding of
# 2026-08-22 is that nine of them landed without anyone seeing the shape.
if [ "$HAVE_GIT" = 0 ]; then
  printf '  (no git repository here — cannot attribute changes to your turn)\n'
elif git diff --quiet "$BASE" -- artifacts/autogenesis/operations.json 2>/dev/null; then
  printf '  operations registry unchanged this turn\n'
else
  added=$(python3 - "$BASE" <<'PY' 2>/dev/null
import json, subprocess, sys
def load(ref):
    try:
        raw = subprocess.run(["git", "show", f"{ref}:artifacts/autogenesis/operations.json"],
                             capture_output=True, text=True, check=True).stdout
        return {o["id"]: len(o["applicability"]["fact_ids"]) for o in json.loads(raw)["operations"]}
    except Exception:
        return {}
before = load(sys.argv[1])
after = {o["id"]: len(o["applicability"]["fact_ids"])
         for o in json.load(open("artifacts/autogenesis/operations.json"))["operations"]}
new = {k: v for k, v in after.items() if k not in before}
widened = [k for k, v in after.items() if k in before and v > before[k]]
print(f"{len(new)}|{sum(1 for v in new.values() if v == 1)}|{len(widened)}")
PY
)
  IFS='|' read -r n_new n_single n_wide <<<"${added:-0|0|0}"
  printf '  operations added: %s (single-target: %s) · widened: %s\n' "$n_new" "$n_single" "$n_wide"
  if [ "${n_single:-0}" -gt 0 ] && [ "${n_wide:-0}" -eq 0 ]; then
    printf '  NOTE: every operation you added names ONE fact. That is activity, not\n'
    printf '        production, and it does not move the metric. Before landing, ask what\n'
    printf '        the next three targets share with this one -- applicability.fact_ids is\n'
    printf '        a list. See docs/autogenesis/228-capsule-lane-retrospective.md.\n'
  fi
fi

printf '%s\n' "--- verdict ---"
printf 'LANE_TURN|pass=%d|new_failures=%d|pre_existing_failures=%d|verdict=%s\n' \
  "$pass" "$new" "$pre" "$([ "$new" -eq 0 ] && echo SAFE || echo UNSAFE)"
if [ "$new" -gt 0 ]; then
  printf 'Your turn introduced: %s\n' "${NEW_FAILURES[*]}" >&2
  printf 'Fix these before you finish. Pre-existing failures are not yours.\n' >&2
  exit 1
fi
exit 0
