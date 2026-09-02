#!/usr/bin/env bash
# Controls for scripts/propose-nursery-refill.py.
#
# One case per guard, and each asserts BOTH that its own guard fired AND that no
# other guard fired -- so a guard that is deleted or weakened is killed by
# exactly one case, and a guard that over-fires is killed by every other case.
#
# The fixtures are synthetic and live in a scratch directory. Nothing here reads
# /nas3: the whole point of the tracked snapshot is that the GATE is
# host-independent, so the gate's controls must be too. `--remeasure` and
# `--names` are the NAS-dependent modes and are exercised only by the
# host-capability case at the end, which SKIPS rather than fails when the
# inventory is absent -- and says so, because a silent skip is a green-looking
# nothing.
#
# Case 0 is the FALSE-POSITIVE control and it runs on the real tree: a gate that
# fires on healthy input gets ignored, which is the same end state as no gate.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/propose-nursery-refill.py"
SNAPSHOT="$ROOT/artifacts/autogenesis/refill-headroom-v1.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

FAILURES=0
CASES=0
ALL_GUARDS=(R2 R3 R4 R5 R6)
# R3 is the QUEUE-SIZE finding (see case 0, below), not an artifact defect --
# mirrors ARTIFACT_GUARDS in scripts/tests/test-dispatchable-frontier.sh, which
# carved the same guard (there G7) out of its own real-tree false-positive
# control for the identical reason.
ARTIFACT_GUARDS=(R2 R4 R5 R6)

# The gate reads its paths from the module, so a fixture is exercised by
# swapping the snapshot file itself. It is restored by the EXIT trap of each
# case rather than left to the end, so an interrupted run cannot leave a mutated
# snapshot in the tree for another lane to trip over.
BACKUP="$WORK/snapshot.orig"
cp "$SNAPSHOT" "$BACKUP"
trap 'cp "$BACKUP" "$SNAPSHOT" 2>/dev/null; rm -rf "$WORK"' EXIT

# Guard-isolation base for every mutation case below (R2, R4, R5, R6, and the
# R3 boundary case). The REAL committed snapshot's `ready_families` has held at
# a single entry since the pool crossed R3's floor (see case 0): a case that
# mutates one unrelated field on top of that base trips R3 as well as its own
# guard, and "this case must kill exactly one" fails for every one of them --
# measured 2026-09-02, all of R2's six cases plus both R5 zero/total cases plus
# both R6 cases. A synthetic second ready-family entry restores isolation
# without touching what each case actually mutates. The name cannot collide
# with a real Mathlib module (so R4's own case, which adds a REAL owned module
# name, is unaffected), and its count is irrelevant -- `check()` only reads
# `len(ready_families)`, never validates each entry against PER_FAMILY.
HEALTHY="$WORK/snapshot.healthy"
python3 - "$BACKUP" "$HEALTHY" <<'PY'
import json, pathlib, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.loads(pathlib.Path(src).read_text())
d["ready_families"] = dict(sorted(d["ready_families"].items()))
d["ready_families"]["Zzz.Synthetic.HealthySpareFamily"] = 99
d["ready_family_count"] = len(d["ready_families"])
pathlib.Path(dst).write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
PY

run_with_snapshot() {
  # run_with_snapshot <label> <expected-exit> <expected-guard-or-NONE> <edit.py>
  local label="$1" want_exit="$2" want_guard="$3" edit="$4"
  CASES=$((CASES + 1))
  cp "$HEALTHY" "$SNAPSHOT"
  if [ -n "$edit" ]; then
    python3 - "$SNAPSHOT" <<PY
import json, pathlib, sys
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
$edit
p.write_text(json.dumps(d, indent=1, sort_keys=True) + "\n")
PY
  fi
  local out status
  out="$(python3 "$SCRIPT" 2>&1)"
  status=$?
  cp "$BACKUP" "$SNAPSHOT"
  local bad=0
  if [ "$status" -ne "$want_exit" ]; then
    echo "FAIL [$label]: exit $status, expected $want_exit"
    bad=1
  fi
  local g hits
  for g in "${ALL_GUARDS[@]}"; do
    hits="$(printf '%s\n' "$out" | /usr/bin/grep -cE "\b${g} [a-z-]+" || true)"
    if [ "$g" = "$want_guard" ]; then
      if [ "$hits" -eq 0 ]; then
        echo "FAIL [$label]: expected guard $g to fire, it did not"
        bad=1
      fi
    elif [ "$hits" -ne 0 ]; then
      echo "FAIL [$label]: guard $g also fired ($hits line(s)); this case must kill exactly one"
      bad=1
    fi
  done
  if [ "$bad" -ne 0 ]; then
    FAILURES=$((FAILURES + 1))
    echo "--- output [$label] ---"; printf '%s\n' "$out" | sed 's/^/    /'; echo "--- end ---"
  else
    echo "ok   [$label]"
  fi
}

# ---- case 0: FALSE-POSITIVE control ----------------------------------------
# The real tree's committed snapshot must fire no ARTIFACT guard (R2/R4/R5/R6)
# AND must actually be measuring something. A positive control runs in the
# same case: an empty report would satisfy every "guard did not fire"
# assertion above, which is the shape this repository calls an empty grep
# reported as a negative result.
#
# This does NOT also require R3 to stay silent. R3 is the QUEUE-SIZE finding
# -- "can the pool still refill the queue" -- and asserting exit 0 here made
# this a control over the size of the queue, not over false positives: it
# failed the day the pool crossed the floor for a reason that has nothing to
# do with a spurious guard. `scripts/tests/test-dispatchable-frontier.sh` hit
# the identical shape for its own G7 on 2026-08-30 and fixed it by asserting
# over ARTIFACT_GUARDS only (see its `real-tree-fires-no-artifact-guard`); this
# case had the same fix documented in docs/plan/status/321-queue-refill.md but
# it was never actually applied here -- confirmed 2026-09-02 by reproducing the
# red exit 1 on main, `git log`-ing the guard to `natural-logarithm`/pool-size
# drift rather than any code change to this file, and finding this test still
# demanded exit 0 in the committed source. R3 keeps its own dedicated coverage
# below (`R3-one-ready-family-cannot-refill`, `R3-no-ready-family-at-all`,
# `R3-two-ready-families-is-exactly-enough`), so no discriminating power is
# lost -- only the redundant, moving-target assertion.
CASES=$((CASES + 1))
OUT="$(python3 "$SCRIPT" 2>&1)"; STATUS=$?
BAD=0
if [ "$STATUS" -ne 0 ] && [ "$STATUS" -ne 1 ]; then
  echo "FAIL [real-tree-fires-no-artifact-guard]: exit $STATUS, expected 0 or 1"
  BAD=1
fi
for G in "${ARTIFACT_GUARDS[@]}"; do
  HITS="$(printf '%s\n' "$OUT" | /usr/bin/grep -cE "\b${G} [a-z-]+" || true)"
  if [ "$HITS" -ne 0 ]; then
    echo "FAIL [real-tree-fires-no-artifact-guard]: artifact guard $G fired on the real tree ($HITS line(s))"
    BAD=1
  fi
done
HITS="$(printf '%s\n' "$OUT" | /usr/bin/grep -cE '^READY FAMILIES +[0-9]+' || true)"
[ "$HITS" -ne 1 ] && {
  echo "FAIL [real-tree-fires-no-artifact-guard]: no READY FAMILIES line; the run"
  echo "               produced no report, so 'no guard fired' is not evidence of anything"
  BAD=1; }
if [ "$BAD" -ne 0 ]; then
  FAILURES=$((FAILURES + 1))
  echo "--- output [real-tree-fires-no-artifact-guard] ---"; printf '%s\n' "$OUT" | sed 's/^/    /'
else
  echo "ok   [real-tree-fires-no-artifact-guard] (exit $STATUS)"
fi

# ---- R2: the snapshot was measured against a screen this tree no longer has -
# One digest per input, because R2 loops and a loop that checked only the first
# key would pass three of these four.
for KEY in env_snapshot vocabulary registry used_source_names drawn_modules held_out_constructions; do
  run_with_snapshot "R2-stale-$KEY" 1 R2 \
    "d['input_digests']['$KEY'] = '0' * 64"
done

# ---- R3: the pool cannot refill the queue ----------------------------------
# The floor is 10 and the yield model gives 10 * (n - ceil(n/3)), so ONE ready
# family yields zero. This is the terminal condition for the whole flywheel and
# it is the guard the exit status exists for.
run_with_snapshot "R3-one-ready-family-cannot-refill" 1 R3 \
  "d['ready_families'] = dict(list(sorted(d['ready_families'].items()))[:1]); d['ready_family_count'] = 1"
run_with_snapshot "R3-no-ready-family-at-all" 1 R3 \
  "d['ready_families'] = {}; d['ready_family_count'] = 0"
# ...and the boundary on the other side: TWO families yield exactly the floor
# and must pass. A `<=` written for `<` in R3 fails here and nowhere else.
run_with_snapshot "R3-two-ready-families-is-exactly-enough" 0 NONE \
  "d['ready_families'] = dict(list(sorted(d['ready_families'].items()))[:2]); d['ready_family_count'] = 2"

# ---- R4: a proposed module is already owned by a family --------------------
# The generator's module->family map is flat, so drawing a module twice
# reassigns its candidates instead of adding any.
run_with_snapshot "R4-proposes-an-already-owned-module" 1 R4 \
  "import json, pathlib
ext = json.loads(pathlib.Path('$ROOT/artifacts/autogenesis/nursery-v2-extension.json').read_text())
owned = sorted({m for t in ext['family_modules'].values() for m in t})
d['ready_families'][owned[0]] = 99"

# ---- R5: vacuity, both directions ------------------------------------------
# 'Everything is ready' and 'nothing was screened' both read as a working
# measurement from the exit status alone.
run_with_snapshot "R5-every-module-is-ready" 1 R5 \
  "d['ready_families'] = {f'Fake.Module{i}': 11 for i in range(d['modules_in_inventory'])}
d['ready_family_count'] = len(d['ready_families'])"
run_with_snapshot "R5-zero-survivors-but-families-listed" 1 R5 \
  "d['survivors'] = 0"
run_with_snapshot "R5-module-total-is-not-a-count" 1 R5 \
  "d['modules_in_inventory'] = 0"

# ---- R6: the snapshot describes a pool the generator will not draw from ----
run_with_snapshot "R6-inventory-digest-drift" 1 R6 \
  "d['inventory_sha256'] = 'f' * 64"
run_with_snapshot "R6-record-count-drift" 1 R6 \
  "d['inventory_records'] = 1"

# ---- exit 2: an input that cannot be read is not a finding -----------------
CASES=$((CASES + 1))
mv "$SNAPSHOT" "$WORK/moved.json"
OUT="$(python3 "$SCRIPT" 2>&1)"; STATUS=$?
mv "$WORK/moved.json" "$SNAPSHOT"
if [ "$STATUS" -ne 2 ]; then
  echo "FAIL [missing-snapshot-is-exit-2]: exit $STATUS, expected 2"
  FAILURES=$((FAILURES + 1))
  printf '%s\n' "$OUT" | sed 's/^/    /'
else
  echo "ok   [missing-snapshot-is-exit-2]"
fi

# ---- the mirrored constants are re-read, not copied ------------------------
# If PER_FAMILY or FLOOR moves in the file that owns it, this gate must follow
# rather than keep answering the old question. Verified by pointing the script
# at a generator whose PER_FAMILY differs and checking the printed floor advice
# changes -- a copied constant would print the same number either way.
CASES=$((CASES + 1))
BASELINE="$(python3 "$SCRIPT" 2>&1 | /usr/bin/grep -oE 'the frontier floor is [0-9]+' || true)"
FRONTIER="$ROOT/scripts/check-dispatchable-frontier.py"
cp "$FRONTIER" "$WORK/frontier.orig"
sed -i 's/^FLOOR = 10$/FLOOR = 40/' "$FRONTIER"
RAISED="$(python3 "$SCRIPT" 2>&1 | /usr/bin/grep -oE 'the frontier floor is [0-9]+' || true)"
cp "$WORK/frontier.orig" "$FRONTIER"
if [ "$BASELINE" = "the frontier floor is 10" ] && [ "$RAISED" = "the frontier floor is 40" ]; then
  echo "ok   [floor-is-re-read-from-the-frontier-checker]"
else
  echo "FAIL [floor-is-re-read-from-the-frontier-checker]: baseline='$BASELINE' raised='$RAISED'"
  echo "               a copied constant prints the same number either way"
  FAILURES=$((FAILURES + 1))
fi

# ---- host capability: --remeasure needs /nas3 ------------------------------
# Reported explicitly either way. A skip that prints nothing is a green-looking
# nothing, which is the failure this whole suite is about.
CASES=$((CASES + 1))
INV="/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
if [ -r "$INV" ]; then
  # `--remeasure` reproducing the committed bytes is a claim about the
  # MEASUREMENT, not about the aggregate finding -- R3 can legitimately fire
  # on a byte-for-byte reproducible snapshot (that is exactly what case 0
  # tolerates), so this no longer requires exit 0. It still refuses exit 2:
  # that means an input could not be read, which is a real defect, not the
  # queue-size finding.
  OUT="$(python3 "$SCRIPT" --remeasure 2>&1)"; STATUS=$?
  if [ "$STATUS" -eq 2 ]; then
    echo "FAIL [remeasure-reproduces-the-committed-snapshot]: exit 2 -- an input"
    echo "               could not be read"
    FAILURES=$((FAILURES + 1))
    printf '%s\n' "$OUT" | sed 's/^/    /'
  elif [ -n "$(git -C "$ROOT" status --porcelain -- "$SNAPSHOT")" ]; then
    echo "FAIL [remeasure-reproduces-the-committed-snapshot]: the committed"
    echo "               snapshot is not byte-reproducible from the pinned"
    echo "               inventory -- someone edited it by hand, or forgot to"
    echo "               commit after running --remeasure"
    FAILURES=$((FAILURES + 1))
    printf '%s\n' "$OUT" | sed 's/^/    /'
  else
    echo "ok   [remeasure-reproduces-the-committed-snapshot] (exit $STATUS)"
  fi
else
  echo "SKIP [remeasure-reproduces-the-committed-snapshot]: no $INV on this host."
  echo "               The GATE above ran; only the regeneration path is unverified here."
fi

echo
if [ "$FAILURES" -ne 0 ]; then
  echo "propose-nursery-refill controls: $FAILURES of $CASES case(s) FAILED"
  exit 1
fi
echo "propose-nursery-refill controls: all $CASES case(s) passed"
