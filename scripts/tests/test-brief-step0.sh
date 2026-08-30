#!/usr/bin/env bash
# Controls for `scripts/brief-step0.py`. One case per guard, and each case was
# mutation-verified to be the ONLY one that dies when its guard is deleted --
# see the table at the bottom of this file.
#
# The subject is driven against FIXTURE snapshots through
# `AXEYUM_BRIEF_STEP0_CACHE`, and against a FIXTURE projection binary through
# `AXEYUM_BRIEF_STEP0_PROJECTION_BIN`, so these controls take no cargo lock, do
# not build the kernel, and cannot disturb a real cached snapshot. They run in
# about a second.
#
# `--no-shape-search` everywhere: section 2 shells out to a kernel binary, which
# is the one part of this tool that costs seconds, and none of these guards live
# there.
set -uo pipefail
cd "$(dirname "$0")/../.."

SUBJECT=scripts/brief-step0.py
pass=0
fail=0

note() { echo "  $*"; }
ok()   { pass=$((pass + 1)); echo "ok   - $1"; }
bad()  { fail=$((fail + 1)); echo "FAIL - $1"; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

TREE="$(git rev-parse "HEAD:crates/axeyum-lean-kernel" 2>/dev/null || echo unknown)"

# A rendered `Nat.add_comm`, byte-for-byte the shape the real projection emits.
# The subject's built-in probe must retrieve it, so a fixture WITHOUT it is how
# the vacuity guard is exercised.
ADD_COMM_TYPE='((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} AxNat (AxNat.add x0 x1) (AxNat.add x1 x0)))'
JUNK_TYPE='((x0 : AxNat) -> AxNat.Zzz x0)'

# write_snapshot <cache-dir> <tree-in-filename> <kernel_tree> <binary_stale> <with-add-comm>
write_snapshot() {
  local dir="$1" fname="$2" tree="$3" stale="$4" withprobe="$5"
  mkdir -p "$dir"
  ADD_COMM_TYPE="$ADD_COMM_TYPE" JUNK_TYPE="$JUNK_TYPE" \
  python3 - "$dir/snapshot-$fname.json" "$tree" "$stale" "$withprobe" <<'PY'
import json, os, sys
path, tree, stale, withprobe = sys.argv[1:5]
decls = [{"name": "Nat.zzz_placeholder", "kind": "theorem",
          "type": os.environ["JUNK_TYPE"], "groups": ["nat"]}]
if withprobe == "yes":
    decls.append({"name": "Nat.add_comm", "kind": "theorem",
                  "type": os.environ["ADD_COMM_TYPE"], "groups": ["nat"]})
json.dump({
    "schema_version": 1, "kind": "axeyum-brief-step0-snapshot",
    "kernel_tree": tree, "binary_stale": stale == "yes",
    "binary": "/fixture/kernel_declaration_projection",
    "binary_built_at": "2020-01-01T00:00:00+0000",
    "built_at": "2020-01-01T00:00:00+0000", "build_seconds": 0.0,
    "declaration_count": len(decls),
    # An EMPTY leaf list makes every leaf in today's sources read as new, which
    # is how the by-leaves STALE path is reached without any kernel build.
    "name_leaves": [], "declarations": decls,
}, open(path, "w"))
PY
}

run() { # run <cache-dir> <args…>
  local cache="$1"; shift
  AXEYUM_BRIEF_STEP0_CACHE="$cache" python3 "$SUBJECT" "$@" 2>&1
}

# --------------------------------------------------------------------------
# GUARD 1 (vacuity): a snapshot that cannot retrieve the built-in probe must be
# UNANSWERABLE, not a source of ABSENT verdicts. This is THE failure this
# repository cares most about -- an empty answer from a broken query reads
# exactly like a strong negative result -- and it is the one a caching layer
# makes easy to reintroduce.
C="$WORK/c1"; write_snapshot "$C" "$TREE" "$TREE" no no
out="$(run "$C" F:int-gcd-comm --no-shape-search)"; st=$?
if [ "$st" -eq 3 ] && [[ "$out" == *"UNANSWERABLE"* ]] && [[ "$out" != *"verdict: ABSENT"* ]]; then
  ok "a snapshot that fails the control probe exits 3 and prints NO verdict"
else
  bad "probe failure must exit 3 with no verdict, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 2 (STALE is not fresh): a snapshot built from a different kernel tree
# must exit 4, so a caller cannot consume a stale answer by ignoring a line of
# prose. A stale prebuilt reported a landed lemma ABSENT on 2026-08-27 and a
# 96 MB output from code that had since gained a size cap; staleness has to be
# in the exit status.
C="$WORK/c2"; write_snapshot "$C" "deadbeefdeadbeef" "deadbeefdeadbeef" no yes
out="$(run "$C" F:int-gcd-comm --no-shape-search)"; st=$?
if [ "$st" -eq 4 ] && [[ "$out" == *"SNAPSHOT   STALE"* ]]; then
  ok "a snapshot from another kernel tree is STALE and exits 4"
else
  bad "stale snapshot must exit 4, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 3 (nothing resolved is a failure): a run that reported on no target at
# all must not exit 0. Otherwise a typo'd fact id produces a green, empty,
# quotable "step 0 done".
C="$WORK/c3"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" zzqqxx-no-such-fact --no-shape-search)"; st=$?
if [ "$st" -eq 1 ] && [[ "$out" == *"UNRESOLVED"* ]] && [[ "$out" == *"facts loaded"* ]]; then
  ok "an unresolvable target exits 1, says UNRESOLVED, and prints the fact count"
else
  bad "unresolved target must exit 1 with a positive control, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 4 (the duplicate-basename trap): `gcd.rs` exists in BOTH `nat_prelude/`
# and `int_prelude/`. Three successive triages plus a brief looked only at
# `int_prelude/crt.rs` and concluded the Chinese Remainder machinery did not
# transport, while `nat_prelude/crt.rs` carried exactly what was needed. Naming
# one path is worse than naming none.
C="$WORK/c4"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:int-gcd-comm --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"SHARED BASENAME"* ]] \
   && [[ "$out" == *"nat_prelude/gcd.rs"* ]] && [[ "$out" == *"int_prelude/gcd.rs"* ]]; then
  ok "a basename in two preludes is flagged and BOTH paths are printed"
else
  bad "shared basename must name both paths, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5 (held-out): dispatching a blind-evaluation row spends the whole
# statement-shape family, not one row -- 19 of 76 propositions for one theorem
# on 2026-08-21 (ADR-0542). The brief must say so before a lane is aimed at it.
C="$WORK/c5"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-clog-antitone-left-44a87771 --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"HELD-OUT"* ]]; then
  ok "a held-out fact is reported as blind-evaluation population"
else
  bad "held-out fact must be flagged, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 6 (mutation control): a deliberately perturbed row is often FALSE and
# never closable. It is a separate guard from held-out because the two
# populations overlap and the mutation test runs first; folding them would let
# a non-held-out mutation control through.
C="$WORK/c6"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-mutation-1432b2277cf2cc26c1d11cd6 --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"MUTATION CONTROL"* ]]; then
  ok "a mutation negative control is reported as never closable"
else
  bad "mutation control must be flagged, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 7 (a stale BINARY may not be stamped with today's tree): the projection
# example indexes the environment it was COMPILED against. The subject walked
# into this on its own first run -- it produced a snapshot from a 40-hour-old
# binary and stamped it with the current tree sha, so the freshness check
# reported EXACT about an answer missing 288 declarations.
cat > "$WORK/fake-projection" <<'SH'
#!/bin/sh
printf 'nat\ttheorem\tNat.fixture\t0\t\t\t\t((x0 : AxNat) -> AxNat.Zzz x0)\n'
SH
chmod +x "$WORK/fake-projection"
touch -d '2000-01-01' "$WORK/fake-projection"
C="$WORK/c7"; mkdir -p "$C"
out="$(AXEYUM_BRIEF_STEP0_CACHE="$C" \
       AXEYUM_BRIEF_STEP0_PROJECTION_BIN="$WORK/fake-projection" \
       python3 "$SUBJECT" --refresh 2>&1)"; st=$?
if [ "$st" -ne 0 ] && [[ "$out" == *"COMPILED against"* ]]; then
  ok "--refresh REFUSES a projection binary older than the kernel sources"
else
  bad "stale binary must refuse the refresh, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 8 (an accepted stale binary is stamped UNMATCHABLE): when the refusal
# is overridden, the snapshot must not be able to masquerade as current. The
# stamp is not a tree sha, so `load_snapshot` can never report EXACT for it --
# an in-band boolean would be one more line for a reader to skip.
C="$WORK/c8"; mkdir -p "$C"
AXEYUM_BRIEF_STEP0_CACHE="$C" AXEYUM_BRIEF_STEP0_PROJECTION_BIN="$WORK/fake-projection" \
  python3 "$SUBJECT" --refresh --allow-stale-binary > /dev/null 2>&1
if ls "$C"/snapshot-stale-binary-*.json > /dev/null 2>&1 \
   && ! ls "$C"/snapshot-"$TREE".json > /dev/null 2>&1; then
  ok "an accepted stale binary is stamped unmatchable, never with the tree sha"
else
  bad "stale-binary snapshot must not carry the current tree sha"
  note "$(ls "$C")"
fi

# --------------------------------------------------------------------------
# FALSE-POSITIVE CONTROL. A healthy run -- fresh snapshot, resolvable target,
# nothing blocked -- must exit 0 and must NOT print any of the alarm words.
# This is what distinguishes the eight guards above from a subject that simply
# refuses everything, and it must survive every one of the eight mutations.
C="$WORK/fp"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-add-eq-zero-64233539 --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"SNAPSHOT   EXACT"* ]] \
   && [[ "$out" == *"DISPATCHABLE"* ]] && [[ "$out" != *"UNANSWERABLE"* ]] \
   && [[ "$out" != *"STALE"* ]]; then
  ok "false-positive control: a healthy run exits 0 with no alarm"
else
  bad "a healthy run must exit 0 with no alarm, got exit $st"; note "$out"
fi

echo "brief-step0 controls: pass=$pass fail=$fail"
[ "$fail" -eq 0 ]

# --------------------------------------------------------------------------
# MUTATION TABLE. Each guard was deleted in a `cp -r`'d scratch copy of the
# repository -- never in the shared checkout, and never in a tracked source --
# and this suite re-run. Every row killed EXACTLY the control named, and the
# false-positive control survived all eight.
#
#   guard deleted                                        | control that dies
#   -----------------------------------------------------|------------------
#   the `if not ok: return 3` probe gate                  | GUARD 1
#   the `state == "STALE" -> exit 4` branch               | GUARD 2
#   the `if not resolved: return 1` branch                | GUARD 3
#   the `len(paths) > 1` SHARED BASENAME flag             | GUARD 4
#   the `fact_id in held` verdict                         | GUARD 5
#   the `-mutation-` / `fact_id in mutation` verdict      | GUARD 6
#   the `binary_stale and not allow_stale_binary` raise   | GUARD 7
#   the `sha = f"stale-binary-{…}"` restamp               | GUARD 8
