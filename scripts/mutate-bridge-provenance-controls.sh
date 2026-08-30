#!/usr/bin/env bash
# Mutation controls for the bridge-provenance guards.
#
# Deletes one guard at a time and reports which test cases die. A guard nothing
# kills is a guard that is not tested; a mutation that kills MANY cases has not
# isolated anything. Both are reported as measured.
#
# NOT A GATE, and deliberately not in scripts/tests/: it EDITS TRACKED FILES in
# place, so running it in the shared checkout breaks every other lane's build
# for as long as a mutant is on disk, and the failures it causes look like their
# bug. Run it in an isolated worktree only. Restores both subjects on exit,
# including on ^C.
#
# Run from the repository root.
set -u -o pipefail

GEN="scripts/gen-autogenesis-statable-vocabulary.py"
FRONT="scripts/check-dispatchable-frontier.py"
GEN_T="scripts/tests/test-gen-autogenesis-statable-vocabulary.sh"
FRONT_T="scripts/tests/test-dispatchable-frontier.sh"
TMP="$(mktemp -d)"
cp "$GEN" "$TMP/gen.orig"
cp "$FRONT" "$TMP/front.orig"
trap 'cp "$TMP/gen.orig" "$GEN"; cp "$TMP/front.orig" "$FRONT"; rm -rf "$TMP"' EXIT

mutate() {
  # mutate <label> <subject-file> <orig-copy> <test-script> <old> <new>
  local label="$1" subject="$2" orig="$3" tests="$4" old="$5" new="$6"
  cp "$orig" "$subject"
  python3 - "$subject" "$old" "$new" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1]); s = p.read_text()
old, new = sys.argv[2], sys.argv[3]
n = s.count(old)
if n != 1:
    print(f"MUTATION-NOT-APPLIED count={n}")
    raise SystemExit(3)
p.write_text(s.replace(old, new))
PY
  if [ $? -ne 0 ]; then
    echo "!! [$label] mutation did not apply cleanly"
    cp "$orig" "$subject"
    return
  fi
  find . -name __pycache__ -prune -exec rm -rf {} + 2>/dev/null
  local out
  out="$(bash "$tests" 2>&1)"
  cp "$orig" "$subject"
  local dead
  dead="$(printf '%s\n' "$out" | /usr/bin/grep -oE '^FAIL \[[^]]+\]' | sort -u | tr '\n' ' ')"
  if [ -z "$dead" ]; then
    echo "SURVIVED [$label]  -- no case died"
  else
    local n
    n="$(printf '%s\n' "$dead" | tr ' ' '\n' | /usr/bin/grep -c 'FAIL' || true)"
    echo "killed-by [$label] ($n) $dead"
  fi
}

echo "=== generator: gen-autogenesis-statable-vocabulary.py ==="
mutate "M1-V5-comparison-deleted" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "    if recorded_provenance != derived_provenance:" \
  "    if False:"
mutate "M2-is_elaboration-instance-branch" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "    if INSTANCE_RE.match(last):
        return True" \
  "    if False:
        return True"
mutate "M3-is_elaboration-projection-branch" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "    return last in (tail[:1].lower() + tail[1:], tail.lower())" \
  "    return False"
mutate "M4-is_elaboration-allcaps-spelling" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "    return last in (tail[:1].lower() + tail[1:], tail.lower())" \
  "    return last in (tail[:1].lower() + tail[1:],)"
mutate "M5-unrendered-class-deleted" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "        elif not rendered:
            kind = \"unrendered\"" \
  "        elif False:
            kind = \"unrendered\""
# The const-side fallback that used to sit here was DELETED after it survived
# mutation: `kernel_tokens` already emits both the qualified name and its last
# component, so the only cases the const side reached were ones where a bare
# `Ioi` in some unrelated namespace would have counted as expressing `Set.Ioi`
# -- a loosening in the unsafe direction, untested, and now gone. What remains
# load-bearing is the TOKEN side, which is what lets a bridge constant with no
# namespace match a kernel rendering that has one.
mutate "M6-token-side-last-component" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "        out.add(name)
        out.add(name.rsplit(\".\", 1)[-1])" \
  "        out.add(name)"
mutate "M7-witness-count-zeroed" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "                      \"witnesses\": len(names)}" \
  "                      \"witnesses\": 0}"
mutate "M8-rendered-witness-count-zeroed" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "                      \"rendered_witnesses\": len(rendered)," \
  "                      \"rendered_witnesses\": 0,"
mutate "M9-provenance-coverage-emptied" "$GEN" "$TMP/gen.orig" "$GEN_T" \
  "    return {f\"bridge_{kind}\":
            sum(1 for v in provenance.values() if v[\"class\"] == kind)
            for kind in BRIDGE_CLASSES}" \
  "    return {}"

echo
echo "=== frontier: check-dispatchable-frontier.py ==="
mutate "N1-S7-comparison-deleted" "$FRONT" "$TMP/front.orig" "$FRONT_T" \
  "        elif recorded != derived:" \
  "        elif False:"
mutate "N2-S7-not-an-object-branch" "$FRONT" "$TMP/front.orig" "$FRONT_T" \
  "        if not isinstance(recorded, dict):" \
  "        if False and not isinstance(recorded, dict):"
mutate "N3-suspect-bridge-filter-emptied" "$FRONT" "$TMP/front.orig" "$FRONT_T" \
  "            if isinstance(v, dict) and v.get(\"class\") in (\"elided\", \"unrendered\")}" \
  "            if isinstance(v, dict) and v.get(\"class\") in ()}"
mutate "N4-S7-skipped-when-other-guards-fired" "$FRONT" "$TMP/front.orig" "$FRONT_T" \
  "    if facts and catalog and not fails:" \
  "    if facts and catalog:"
echo
echo "MUTATION_CONTROLS_DONE"
