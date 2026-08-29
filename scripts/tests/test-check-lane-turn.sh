#!/usr/bin/env bash
# Controls for scripts/check-lane-turn.sh.
#
# The verdict is what a lane acts on, so both directions have to be shown. A
# check that always says SAFE is the failure this repository has shipped most
# often; a check that always says UNSAFE is worse, because it trains the reader
# to ignore it, and then a real breach reads exactly like the noise.
#
# The attribution cases matter as much as the verdict. Told "FAIL" without
# "PRE-EXISTING", an agent either reverts its own good work or edits a file
# another lane is mid-flight on -- both observed in this repository.
set -uo pipefail
cd "$(dirname "$0")/../.." || exit 2

pass=0 fail=0
ok()   { pass=$((pass+1)); printf '  ok    %s\n' "$1"; }
bad()  { fail=$((fail+1)); printf '  FAIL  %s\n' "$1"; }
check() { # name expected-substring actual
  case "$3" in (*"$2"*) ok "$1";; (*) bad "$1 (wanted '$2', got: $(printf '%s' "$3" | tr '\n' ' ' | cut -c1-160))";; esac
}

# A real detached WORKTREE, not a `lane-snapshot.sh` extract. The first version
# of this suite used a snapshot and five of eight cases failed for reasons that
# had nothing to do with the script: a snapshot is a working tree with no `.git`,
# so every attribution call failed, and cargo-backed gates could not run against
# it. That is not the environment a lane is ever in. Testing a tool in a
# situation it never meets measures the harness, not the tool.
W=/data0/axeyum/scratch/wt-lane-turn-controls-$$
git worktree add --detach "$W" HEAD >/dev/null 2>&1 || {
  printf '  SKIP  cannot create a worktree\n'; exit 0; }
trap 'git worktree remove --force "$W" >/dev/null 2>&1; git worktree prune' EXIT
cp scripts/check-lane-turn.sh scripts/check-autogenesis-holdout-isolation.py "$W/scripts/" 2>/dev/null

# --- 1. a clean turn is SAFE and exits 0 -----------------------------------
# Attribution ON, so anything already red at the base is excluded by the tool
# itself. That is the property under test: an untouched tree is SAFE even when
# gates are failing, because none of those failures are the lane's.
out=$( cd "$W" && timeout 2400 scripts/check-lane-turn.sh 2>&1 ); rc=$?
check "an untouched worktree reports SAFE" "verdict=SAFE" "$out"
[ "$rc" = 0 ] && ok "an untouched worktree exits 0" || bad "an untouched worktree exits 0 (got $rc)"
check "holdout isolation is checked at all" "holdout-isolation" "$out"

# --- 2. settling a held-out fact is caught and exits NONZERO ----------------
HO=$( cd "$W" && python3 -c "
import json
N=json.load(open('artifacts/autogenesis/nursery-v1.json'))
print(next(e['fact_id'] for e in N['entries'] if e['partition']=='held-out'))" )
FP="$W/artifacts/facts/$(printf '%s' "$HO" | sed 's/^F:/F-/').json"
cp "$FP" "$FP.bak"
python3 -c "
import json,pathlib,sys
p=pathlib.Path(sys.argv[1]); d=json.loads(p.read_text()); d['epistemic_status']='proved'
p.write_text(json.dumps(d,indent=2)+chr(10))" "$FP"
out=$( cd "$W" && timeout 2400 scripts/check-lane-turn.sh 2>&1 ); rc=$?
check "a settled held-out fact reports UNSAFE" "verdict=UNSAFE" "$out"
check "and names the gate that caught it"      "holdout-isolation" "$out"
[ "$rc" != 0 ] && ok "an unsafe turn exits nonzero" || bad "an unsafe turn exits nonzero (got $rc)"
mv "$FP.bak" "$FP"

# --- 3. the verdict returns to SAFE once repaired ---------------------------
# Without this, case 2 is satisfied by a check that is simply always UNSAFE.
out=$( cd "$W" && timeout 2400 scripts/check-lane-turn.sh 2>&1 )
check "repairing the breach restores SAFE" "verdict=SAFE" "$out"

# --- 4. a pre-existing failure is attributed, not blamed on the lane --------
# Break a gate in the BASE as well, by breaking it in a way the snapshot shares:
# the ledger pin. Blame mode re-runs at the merge-base, which for this snapshot
# is the same tree, so the failure must come back PRE-EXISTING rather than NEW.
# A generated ledger the LANE staled is the lane's problem, and must read NEW --
# the complement of case 1, where the same class of failure is not the lane's.
#
# This case only discriminates anything when the target gate is CLEAN before
# the corruption: `docs/plan/generated/theorem-production-ledger.md` tracks
# real theorem production, and production is expected to move it out of date
# on an ordinary day (measured 2026-08-29: distinct theorems 1448 -> 1770,
# unrelated to this worktree -- byte-identical file and `crates/` tree at
# HEAD and at merge-base with origin/main). Asserting "FAIL (NEW)" against an
# already-red gate is not a stronger check, it is a WRONG one: the tool is
# correctly reporting PRE-EXISTING because the failure genuinely is, at both
# ends of the comparison, for a reason that has nothing to do with the
# corruption appended below. So confirm the baseline is green first, exactly
# like case 1 does for the whole turn, and skip rather than assert a false
# expectation when it is not -- a SKIP here is honest; a FAIL would not be.
LED="$W/docs/plan/generated/theorem-production-ledger.md"
if [ -f "$LED" ] \
  && ( cd "$W" && python3 scripts/gen-theorem-production-ledger.py --check >/dev/null 2>&1 ); then
  cp "$LED" "$LED.bak"
  printf 'corrupted\n' >> "$LED"
  out=$( cd "$W" && timeout 2400 scripts/check-lane-turn.sh 2>&1 )
  check "a ledger the lane staled is attributed to the lane" "FAIL (NEW)" "$out"
  check "and makes the turn UNSAFE"                          "verdict=UNSAFE" "$out"
  mv "$LED.bak" "$LED"
elif [ -f "$LED" ]; then
  printf '  SKIP  theorem-production-ledger is already stale at this base (real production growth, not this worktree) -- case 4 cannot discriminate today\n'
fi

printf 'LANE_TURN_CONTROLS|pass=%d|fail=%d\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
