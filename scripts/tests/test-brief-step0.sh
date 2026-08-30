#!/usr/bin/env bash
# Controls for `scripts/brief-step0.py`. One case per guard, each guard deleted
# in a scratch copy and the kill set recorded -- see the two tables at the
# bottom of this file. The kill sets are reported AS MEASURED: most rows kill
# exactly one case, two rows in the held-out family kill more, and the tables
# say which and why rather than rounding to the tidier claim.
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
# `Int.gcd_comm`'s real rendered type. `F:int-gcd-comm`'s `formal.statement` is
# itself a KERNEL RENDERED TYPE rather than Lean surface -- the ledger carries
# both dialects -- so this is the fixture for the dialect guard.
GCD_COMM_TYPE='((x0 : Int) -> ((x1 : Int) -> Eq.{1} AxNat (Int.gcd x0 x1) (Int.gcd x1 x0)))'

# write_snapshot <cache-dir> <tree-in-filename> <kernel_tree> <binary_stale> <with-add-comm>
write_snapshot() {
  local dir="$1" fname="$2" tree="$3" stale="$4" withprobe="$5"
  mkdir -p "$dir"
  ADD_COMM_TYPE="$ADD_COMM_TYPE" JUNK_TYPE="$JUNK_TYPE" GCD_COMM_TYPE="$GCD_COMM_TYPE" \
  python3 - "$dir/snapshot-$fname.json" "$tree" "$stale" "$withprobe" <<'PY'
import json, os, sys
path, tree, stale, withprobe = sys.argv[1:5]
decls = [{"name": "Nat.zzz_placeholder", "kind": "theorem",
          "type": os.environ["JUNK_TYPE"], "groups": ["nat"]}]
if withprobe == "yes":
    decls.append({"name": "Nat.add_comm", "kind": "theorem",
                  "type": os.environ["ADD_COMM_TYPE"], "groups": ["nat"]})
    decls.append({"name": "Int.gcd_comm", "kind": "theorem",
                  "type": os.environ["GCD_COMM_TYPE"], "groups": ["integer"]})
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
# GUARD 5 (held-out is REFUSED, not merely annotated): dispatching a
# blind-evaluation row spends the whole statement-shape family, not one row --
# 19 of 76 propositions for one theorem on 2026-08-21 (ADR-0542). This used to
# be an annotation in section 4, printed AFTER section 1's already-proved
# verdict, and on 2026-08-29 a sweep read that verdict and closed ten
# preregistered held-out rows (92a61164e). The warning arrived after the leak.
#
# The fixture is a `natural-square-root` row deliberately: `natural-logarithm`
# was this case's fixture until 2026-08-30 and is no longer held-out, which is
# exactly the kind of silent fixture rot that makes a control stop discriminating.
C="$WORK/c5"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-sqrt-le-self-1ed5eb85 --no-shape-search)"; st=$?
if [ "$st" -eq 5 ] && [[ "$out" == *"REFUSED: HELD-OUT"* ]]; then
  ok "a held-out fact is REFUSED with exit 5, not annotated and answered"
else
  bad "held-out fact must be refused with exit 5, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5b (the refusal WITHHOLDS the proof route): the exit status is not the
# protection -- the withheld sections are. Naming the declaration whose rendered
# type matches a blind proposition IS the proof route, and so is a shape near
# miss and so is "read these modules". A refusal that still printed section 1
# would spend the row exactly as before while looking careful.
C="$WORK/c5b"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-sqrt-le-self-1ed5eb85 --no-shape-search)"
if [[ "$out" != *"1. ALREADY IN THE ENVIRONMENT"* ]] \
   && [[ "$out" != *"2. NEAR MISSES"* ]] \
   && [[ "$out" != *"3. MODULES TO READ"* ]] \
   && [[ "$out" != *"formal.statement:"* ]]; then
  ok "a refused target prints no retrieval section and no formal.statement"
else
  bad "refusal must withhold sections 1-3"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5c (the refusal is not "refuse everything"): a row in a family the
# ADR-0542 ledger has amended OUT of held-out must be answered in full. Without
# this case, GUARD 5 and 5b are both satisfied by a tool that refuses every
# target, which would be useless and would look rigorous.
#
# `natural-divisibility` was amended on 2026-08-30 -- its rows were never blind
# (preregistered 2026-08-29 against theorems admitted 2026-08-13..24).
C="$WORK/c5c"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-dvd-mod-iff-2d082f10 --no-shape-search --allow-stale)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"1. ALREADY IN THE ENVIRONMENT"* ]] \
   && [[ "$out" != *"REFUSED"* ]]; then
  ok "an amended-out-of-held-out row is answered in full, not refused"
else
  bad "amended row must be answered, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5d (fail-closed): `blocked_report` degrades to UNANSWERABLE and keeps
# going, which is right for a section that only annotates. It is wrong for the
# check that decides whether the retrieval sections run at all -- a frontier
# module that failed to import would read as "not held-out" and publish a proof
# route for a blind row. An unreadable partition is not a licence to report.
C="$WORK/c5d"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(AXEYUM_BRIEF_STEP0_CACHE="$C" python3 - "$SUBJECT" \
        F:ml430-nat-sqrt-le-self-1ed5eb85 --no-shape-search 2>&1 <<'PY'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("b0", sys.argv[1])
b0 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b0)
b0.load_frontier_module = lambda root: None
sys.argv = [sys.argv[1]] + sys.argv[2:]
sys.exit(b0.main())
PY
)"; st=$?
if [ "$st" -eq 5 ] && [[ "$out" == *"REFUSED: UNANSWERABLE"* ]] \
   && [[ "$out" != *"1. ALREADY IN THE ENVIRONMENT"* ]]; then
  ok "an unreadable partition refuses rather than reporting a proof route"
else
  bad "unreadable partition must fail closed, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5e (an EMPTY held-out population is a broken query, not a clean bill):
# if the manifests parse but contribute no held-out ids, `fact_id in held` is
# False for every target and the refusal never fires -- the guard reports
# "nothing is blind" with exactly the output it produces when it works. The
# holdout-isolation gate fails closed on this for the same reason.
C="$WORK/c5e"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(AXEYUM_BRIEF_STEP0_CACHE="$C" python3 - "$SUBJECT" \
        F:ml430-nat-sqrt-le-self-1ed5eb85 --no-shape-search 2>&1 <<'PY'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("b0", sys.argv[1])
b0 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b0)
real = b0.load_frontier_module
def empty(root):
    module = real(root)
    module.load_partitions = lambda *a, **k: (set(), set())
    return module
b0.load_frontier_module = empty
sys.argv = [sys.argv[1]] + sys.argv[2:]
sys.exit(b0.main())
PY
)"; st=$?
if [ "$st" -eq 5 ] && [[ "$out" == *"pass vacuously"* ]] \
   && [[ "$out" != *"1. ALREADY IN THE ENVIRONMENT"* ]]; then
  ok "an empty held-out population is UNANSWERABLE, not everything-dispatchable"
else
  bad "empty held-out population must fail closed, got exit $st"; note "$out"
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
# This is what distinguishes the nine guards above from a subject that simply
# refuses everything, and it must survive every one of the nine mutations.
C="$WORK/fp"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:ml430-nat-add-eq-zero-64233539 --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"SNAPSHOT   EXACT"* ]] \
   && [[ "$out" == *"DISPATCHABLE"* ]] && [[ "$out" != *"UNANSWERABLE"* ]] \
   && [[ "$out" != *"STALE"* ]]; then
  ok "false-positive control: a healthy run exits 0 with no alarm"
else
  bad "a healthy run must exit 0 with no alarm, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 9 (the ledger carries TWO statement dialects): some `formal.statement`s
# are kernel rendered types, not Lean surface. Running one through the surface
# normalizer is not merely imprecise -- `->` becomes `sub` and `lt` (from `-`
# and `>`), `x0`/`x1` become constants -- and `F:int-gcd-comm` scored 0.18
# against its OWN declaration, printing a confident ABSENT. That is a wrong
# answer wearing a result's clothes, which is the failure this whole tool
# exists to stop producing.
C="$WORK/c9"; write_snapshot "$C" "$TREE" "$TREE" no yes
out="$(run "$C" F:int-gcd-comm --no-shape-search)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"dialect: kernel-rendered"* ]] \
   && [[ "$out" == *"[1.00] Int.gcd_comm"* ]]; then
  ok "a kernel-rendered formal.statement retrieves its own declaration at 1.00"
else
  bad "rendered-dialect statement must retrieve its own declaration, got exit $st"
  note "$out"
fi

echo "brief-step0 controls: pass=$pass fail=$fail"
[ "$fail" -eq 0 ]

# --------------------------------------------------------------------------
# MUTATION TABLE. Each guard was deleted in a `cp -r`'d scratch copy of the
# repository -- never in the shared checkout, and never in a tracked source --
# and this suite re-run. Every row killed EXACTLY the control named, and the
# false-positive control survived all nine.
#
#   guard deleted                                        | control that dies
#   -----------------------------------------------------|------------------
#   the `if not ok: return 3` probe gate                  | GUARD 1
#   the `state == "STALE" -> exit 4` branch               | GUARD 2
#   the `if not resolved: return 1` branch                | GUARD 3
#   the `len(paths) > 1` SHARED BASENAME flag             | GUARD 4
#   the `-mutation-` / `fact_id in mutation` verdict      | GUARD 6
#   the `binary_stale and not allow_stale_binary` raise   | GUARD 7
#   the `sha = f"stale-binary-{…}"` restamp               | GUARD 8
#
# HELD-OUT REFUSAL (GUARDs 5, 5b, 5c, 5d, 5e), measured 2026-08-30 in a
# `copytree`'d scratch root with `__pycache__` cleared between iterations.
# Baseline 14 cases green; NO mutant survived. Kill sets are reported as
# measured rather than rounded to "exactly one", because two of them are not:
#
#   guard deleted                                | controls that die
#   ---------------------------------------------|------------------------
#   `is_held_out` -> `return False`              | GUARD 5, GUARD 5b
#   the `module is None` raise                   | GUARD 5d   (only)
#   the empty-population raise                   | GUARD 5e   (only)
#   the `if refused: return 5` branch            | GUARD 5, 5d, 5e
#
# Row 1 kills two because refusing and withholding are one branch: 5 asserts
# the refusal, 5b asserts that sections 1-3 are gone, and no code change can
# separate them. Row 4 kills three because the exit status is one guard with
# three independent witnesses -- which is the point, not a shared-rejection
# defect: rows 2 and 3 each kill ONLY their own case, so the two fail-closed
# guards are demonstrably not rejecting through the held-out test.
#
# GUARD 5c is the false-positive control for this family and dies under NONE of
# the four: without it, a tool that refused every target would satisfy 5, 5b,
# 5d and 5e and be useless.
