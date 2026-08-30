#!/usr/bin/env bash
# Controls for scripts/gen-autogenesis-statable-vocabulary.py.
#
# One case per guard, and each asserts BOTH that its own guard fired AND that no
# other guard fired -- so a guard that is deleted or weakened is killed by
# exactly one case, and a guard that over-fires is killed by every other case.
#
# Nothing here reads /nas3. `--refresh-cache` is the only NAS-dependent mode and
# is exercised by the host-capability case at the end, which SKIPS rather than
# fails when the inventory is absent -- and SAYS SO, because a silent skip is a
# green-looking nothing.
#
# Case 0 is the FALSE-POSITIVE control and it runs on the real tree, with a
# positive control in the same case: a run that produced no verdict line would
# satisfy every "guard did not fire" assertion, which is this repository's
# empty-grep-reported-as-a-negative-result shape.
#
# WHY THE MUTATIONS ARE CHOSEN THE WAY THEY ARE. V1 hashes the rows and V2 reads
# the coverage block, so a careless mutation trips both and proves nothing about
# either. V1's row mutation adds a constant that another row ALREADY witnesses,
# so `distinct_constants` does not move and only the digest does -- which is
# also the real-world case the guard exists for: a hand-appended row whose
# constants are redundantly witnessed is invisible to S2, S3 and S4.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/scripts/gen-autogenesis-statable-vocabulary.py"
VOCAB="$ROOT/artifacts/autogenesis/mathlib-statable-vocabulary-v1.json"
CACHE="$ROOT/artifacts/autogenesis/mathlib-statement-constants-v1.json"
WORK="$(mktemp -d)"

FAILURES=0
CASES=0
ALL_GUARDS=(V1 V2 V3 V4 V5)

# The artifact is a TRACKED file other lanes read, so every case restores it
# immediately rather than leaving it to the end. The EXIT trap is the backstop
# for an interrupted run: a mutated vocabulary left in the shared tree would
# fail the frontier gate for whoever ran it next, and look like their bug.
BACKUP="$WORK/vocabulary.orig"
cp "$VOCAB" "$BACKUP"
trap 'cp "$BACKUP" "$VOCAB" 2>/dev/null; rm -rf "$WORK"' EXIT

run_with_vocab() {
  # run_with_vocab <label> <expected-exit> <expected-guard-or-NONE> <edit.py>
  local label="$1" want_exit="$2" want_guard="$3" edit="$4"
  CASES=$((CASES + 1))
  cp "$BACKUP" "$VOCAB"
  if [ -n "$edit" ]; then
    python3 - "$VOCAB" <<PY
import json, pathlib, sys
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
$edit
p.write_text(json.dumps(d, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
PY
  fi
  local out status
  out="$(python3 "$SCRIPT" 2>&1)"
  status=$?
  cp "$BACKUP" "$VOCAB"
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
CASES=$((CASES + 1))
OUT="$(python3 "$SCRIPT" 2>&1)"; STATUS=$?
BAD=0
[ "$STATUS" -ne 0 ] && { echo "FAIL [healthy-real-tree-passes]: exit $STATUS"; BAD=1; }
HITS="$(printf '%s\n' "$OUT" | /usr/bin/grep -cE '^AUTOGENESIS_STATABLE_VOCABULARY\|rows=[0-9]+\|bridge=[0-9]+\|elaboration=[0-9]+\|expressed=[0-9]+\|elided=[0-9]+\|unrendered=[0-9]+\|cached=[0-9]+\|verdict=PASS' || true)"
[ "$HITS" -ne 1 ] && {
  echo "FAIL [healthy-real-tree-passes]: no verdict line; the run produced no"
  echo "               report, so 'no guard fired' is not evidence of anything"
  BAD=1; }
if [ "$BAD" -ne 0 ]; then
  FAILURES=$((FAILURES + 1))
  echo "--- output [healthy-real-tree-passes] ---"; printf '%s\n' "$OUT" | sed 's/^/    /'
else
  echo "ok   [healthy-real-tree-passes]"
fi

# ---- V1: the rows are not what the generator produced -----------------------
# The digest itself, and then the case it exists for: a row edited in a way that
# every OTHER gate accepts. `Nat` is witnessed by essentially every row, so
# adding it to one changes no derived count -- only the digest sees it.
run_with_vocab "V1-row-digest-does-not-match-the-rows" 1 V1 \
  "d['row_digest'] = '0' * 64"
run_with_vocab "V1-hand-appended-constant-redundantly-witnessed" 1 V1 \
  "row = next(r for r in d['settled'] if 'Nat' not in r['constants'])
row['constants'] = sorted(row['constants'] + ['Nat'])"
# ...and a row dropped, which is the drift direction S4 also sees. Listed here
# because V1 must not be satisfiable by a SUBSET of the generated rows.
#
# THE ROW REMOVED MUST BE BRIDGE-NEUTRAL, and picking one that is not cost a
# run. `Int.ModEq.neg` was the original choice and it witnesses `Neg.neg` and
# `Int.instNegInt`, so dropping it moves those two constants' witness counts and
# V5 fires alongside V1 -- a case that kills two guards no longer proves either
# one exists. Every constant of `Int.ModEq.refl` is in the kernel environment,
# so it contributes NOTHING to the bridge and V5 cannot see it go; its
# constants are also all witnessed by other rows, so `distinct_constants` does
# not move and V2 cannot see it either. Eight rows qualify; any of them works.
run_with_vocab "V1-a-row-removed" 1 V1 \
  "keep = [r for r in d['settled'] if r['source_name'] != 'Int.ModEq.refl']
d['settled'] = keep"

# ---- V2: the coverage block disagrees with the artifact ---------------------
# One case per counter, because a guard that compared only the dict's LENGTH,
# or only the first key, would pass four of these five.
for KEY in bridge_constants catalogued_propositions distinct_constants \
           open_propositions settled_propositions bridge_elaboration \
           bridge_expressed bridge_elided bridge_unrendered; do
  run_with_vocab "V2-stale-$KEY" 1 V2 \
    "d['coverage']['$KEY'] = d['coverage']['$KEY'] + 7"
done
# A coverage block that is absent entirely, not merely wrong.
run_with_vocab "V2-coverage-block-missing" 1 V2 "d.pop('coverage')"

# ---- V5: the provenance block is not its derivation -------------------------
# WHY THESE MUTATIONS. V5 and V2 both read derived quantities, so a mutation
# that moves a class ALSO moves a `bridge_<class>` counter and would trip both,
# proving nothing about either. Every case below therefore leaves the class
# HISTOGRAM intact:
#   * the two-constant SWAP exchanges an `elided` class for an `expressed` one
#     and back, so all four counters are unchanged and only V5 can see it. It is
#     also the real-world abuse: relabelling `Set.Ioi` as expressed is exactly
#     how an elision-backed constant would come to be quoted as sound.
#   * the witness-count edits do not touch `class` at all, so no counter moves.
# A guard comparing only the class labels, or only the key set, survives the
# last two -- which is why they are here.
run_with_vocab "V5-classes-swapped-between-two-constants" 1 V5 \
  "pr = d['bridge_provenance']
a = next(c for c, v in sorted(pr.items()) if v['class'] == 'elided')
b = next(c for c, v in sorted(pr.items()) if v['class'] == 'expressed')
pr[a]['class'], pr[b]['class'] = pr[b]['class'], pr[a]['class']"
run_with_vocab "V5-witness-count-inflated" 1 V5 \
  "pr = d['bridge_provenance']
c = sorted(pr)[0]
pr[c]['witnesses'] = pr[c]['witnesses'] + 5"
run_with_vocab "V5-rendered-witness-count-inflated" 1 V5 \
  "pr = d['bridge_provenance']
c = next(c for c, v in sorted(pr.items()) if v['class'] == 'unrendered')
pr[c]['rendered_witnesses'] = 3"
# A constant dropped from the block. The bridge still lists it, so the screen
# still admits it -- it simply has no recorded reason, which is the state this
# whole block exists to make impossible.
run_with_vocab "V5-a-bridge-constant-has-no-provenance" 1 V5 \
  "d['bridge_provenance'].pop(sorted(d['bridge_provenance'])[0])"
# ...and the block absent entirely, not merely wrong.
run_with_vocab "V5-provenance-block-missing" 1 V5 "d.pop('bridge_provenance')"

# ---- V3: the source pin moved without the constants -------------------------
run_with_vocab "V3-inventory-sha-repinned" 1 V3 \
  "d['source']['statement_inventory_sha256'] = '0' * 64"
run_with_vocab "V3-mathlib-tag-repinned" 1 V3 \
  "d['source']['mathlib_tag'] = 'v4.32.1'"

# ---- V4: the artifact names an environment snapshot that is not there --------
run_with_vocab "V4-dangling-environment-snapshot" 1 V4 \
  "d['environment_snapshot'] = 'artifacts/autogenesis/no-such-snapshot.json'"
# ...and an absolute path, which `(ROOT / named).is_file()` resolves AWAY from
# the repository. A guard written with a bare `pathlib.Path(named).is_file()`
# passes this and fails nothing else.
run_with_vocab "V4-absolute-path-escapes-the-repository" 1 V4 \
  "d['environment_snapshot'] = '/etc/hostname'"

# ---- the shape guards exit 2, not 1 -----------------------------------------
# A malformed artifact is an unreadable INPUT, deliberately distinct from a
# guard firing, so a broken file is never mistaken for a measured drift.
CASES=$((CASES + 1))
cp "$BACKUP" "$VOCAB"
python3 - "$VOCAB" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d['settled'] = []
p.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
PY
OUT="$(python3 "$SCRIPT" 2>&1)"; STATUS=$?
cp "$BACKUP" "$VOCAB"
if [ "$STATUS" -ne 2 ]; then
  echo "FAIL [empty-settled-list-is-exit-2]: exit $STATUS, expected 2"
  FAILURES=$((FAILURES + 1))
else
  echo "ok   [empty-settled-list-is-exit-2]"
fi

# ---- --write is a no-op on a tree that is already its own derivation --------
# This is what makes the generator safe to re-run, and it is the assertion that
# would fail first if the derivation and the committed artifact ever diverged.
CASES=$((CASES + 1))
OUT="$(python3 "$SCRIPT" --write 2>&1)"; STATUS=$?
BAD=0
[ "$STATUS" -ne 0 ] && { echo "FAIL [write-is-idempotent]: exit $STATUS, expected 0"; BAD=1; }
HITS="$(printf '%s\n' "$OUT" | /usr/bin/grep -cE '^UNCHANGED ' || true)"
[ "$HITS" -ne 1 ] && { echo "FAIL [write-is-idempotent]: expected UNCHANGED, got: $OUT"; BAD=1; }
if [ "$BAD" -ne 0 ]; then FAILURES=$((FAILURES + 1)); else echo "ok   [write-is-idempotent]"; fi

# ---- --write refuses a row it could not derive ------------------------------
# The honest degradation. A settled proposition absent from the cache must FAIL
# naming --refresh-cache, never be emitted with guessed constants.
CASES=$((CASES + 1))
CACHE_BACKUP="$WORK/cache.orig"
cp "$CACHE" "$CACHE_BACKUP"
python3 - "$CACHE" <<'PY'
import json, pathlib, sys
p = pathlib.Path(sys.argv[1]); d = json.loads(p.read_text())
d['constants'].pop('Int.ModEq.neg', None)
p.write_text(json.dumps(d, indent=2, sort_keys=True) + "\n")
PY
OUT="$(python3 "$SCRIPT" --write 2>&1)"; STATUS=$?
cp "$CACHE_BACKUP" "$CACHE"
BAD=0
[ "$STATUS" -ne 2 ] && { echo "FAIL [write-refuses-an-underived-row]: exit $STATUS, expected 2"; BAD=1; }
HITS="$(printf '%s\n' "$OUT" | /usr/bin/grep -cF -- '--refresh-cache' || true)"
[ "$HITS" -lt 1 ] && {
  echo "FAIL [write-refuses-an-underived-row]: the refusal must NAME the remedy"
  BAD=1; }
if [ "$BAD" -ne 0 ]; then
  FAILURES=$((FAILURES + 1))
  echo "--- output ---"; printf '%s\n' "$OUT" | sed 's/^/    /'
else
  echo "ok   [write-refuses-an-underived-row]"
fi
# ...and the vocabulary must be untouched by a refused write.
CASES=$((CASES + 1))
if /usr/bin/cmp -s "$VOCAB" "$BACKUP"; then
  echo "ok   [refused-write-leaves-the-artifact-alone]"
else
  echo "FAIL [refused-write-leaves-the-artifact-alone]: the artifact changed"
  FAILURES=$((FAILURES + 1))
fi

# ---- host capability: --refresh-cache ---------------------------------------
# Reported, never silently skipped.
CASES=$((CASES + 1))
INVENTORY="/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
if [ -r "$INVENTORY" ]; then
  cp "$CACHE" "$CACHE_BACKUP"
  OUT="$(python3 "$SCRIPT" --refresh-cache 2>&1)"; STATUS=$?
  if [ "$STATUS" -eq 0 ] && printf '%s\n' "$OUT" | /usr/bin/grep -qF 'UNCHANGED'; then
    echo "ok   [refresh-cache-is-idempotent-against-the-pinned-inventory]"
  else
    echo "FAIL [refresh-cache-is-idempotent-against-the-pinned-inventory]: exit $STATUS: $OUT"
    FAILURES=$((FAILURES + 1))
  fi
  cp "$CACHE_BACKUP" "$CACHE"
else
  echo "SKIP [refresh-cache-is-idempotent-against-the-pinned-inventory]: no"
  echo "     readable inventory at $INVENTORY. This host cannot re-derive the"
  echo "     cache; --write and --check do not need it, which is the point."
fi

echo
if [ "$FAILURES" -ne 0 ]; then
  echo "STATABLE_VOCABULARY_CONTROLS|cases=$CASES|failures=$FAILURES|verdict=FAIL"
  exit 1
fi
echo "STATABLE_VOCABULARY_CONTROLS|cases=$CASES|failures=0|verdict=PASS"
