#!/usr/bin/env bash
# Post-merge hygiene: the four things that have actually gone wrong when a
# coordinator merges a lane branch, in one command that takes ~2 seconds.
#
# Why this exists. Merging lane branches is the coordinator's most frequent
# operation and the full gate is ~10 minutes, so it is not run per merge. Each
# check below corresponds to a defect that reached a commit on this repository
# BECAUSE the cheap check was skipped:
#
#   1. CONFLICT MARKERS COMMITTED. Twice. Ten JSON fact files kept their markers
#      because the resolver was only ever run on `*.rs`; and
#      `docs/research/09-decisions/README.md` was committed with markers while
#      resolving an ADR-index conflict. Both turned gates red downstream and
#      neither is visible in `git show --stat`.
#   2. DUPLICATE ADR NUMBERS. Concurrent lanes allocate a number by looking at
#      the tree, so two lanes starting within an hour pick the same one. It
#      happened TWICE IN A ROW on 2026-08-30 (0617, then 0618), each costing a
#      rename plus a reference sweep. `gen-adr-index.py --check` catches it and
#      is wired into the full gate -- which is exactly the gate not being run.
#   3. STALE GENERATED FILES. `PLAN.md` and the ADR index are generated and are
#      the two files every lane touches. `gen-plan.py` sat exiting 1 for hours
#      while being run as `>/dev/null 2>&1`, so `PLAN.md` was never regenerated
#      and was committed repeatedly as though it had been.
#   4. A PINNED-INVENTORY COUNT BROKEN BY A CLEAN MERGE. Two lanes can each
#      correctly bump a pinned length and git merges both entries without
#      conflict, leaving the declared size one short. Eight times in one day.
#
# Exit 0 only when all four pass. Each failure names its own remedy.
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0
note() { printf '  %s\n' "$1"; }

# --- 1. conflict markers in tracked files ------------------------------------
# Only tracked files, and only real markers at line start. `git grep` skips
# .gitignore'd trees, which is what keeps this fast in a repo with 200 worktrees.
markers=$(git grep -lE '^(<<<<<<< |>>>>>>> |={7}$)' -- \
            ':!*.md.orig' ':!scripts/tests/*' 2>/dev/null | /usr/bin/grep -c . || true)
if [ "$markers" -ne 0 ]; then
  fail=1
  echo "FAIL: $markers tracked file(s) contain conflict markers:"
  git grep -lE '^(<<<<<<< |>>>>>>> |={7}$)' -- ':!*.md.orig' ':!scripts/tests/*' | sed 's/^/    /'
  note "A generated file (PLAN.md, the ADR index README) is fixed by RE-GENERATING,"
  note "never by hand-editing the markers out."
fi

# --- 2. duplicate ADR numbers -------------------------------------------------
if ! adr_out=$(python3 scripts/gen-adr-index.py --check 2>&1); then
  fail=1
  echo "FAIL: gen-adr-index.py --check"
  printf '%s\n' "$adr_out" | /usr/bin/grep -E 'ADR_INDEX' | sed 's/^/    /'
  note "Two lanes probably picked the same ADR number. Renumber the NEWER one,"
  note "sweep inbound references, and re-run gen-adr-index.py."
fi

# --- 3. generated files are current ------------------------------------------
if ! plan_out=$(python3 scripts/gen-plan.py --check 2>&1); then
  fail=1
  echo "FAIL: gen-plan.py --check"
  printf '%s\n' "$plan_out" | tail -3 | sed 's/^/    /'
  note "Run scripts/gen-plan.py and commit PLAN.md. Note it exits nonzero when a"
  note "lane status doc puts prose BEFORE its first plan-section marker."
fi

# --- 4. pinned inventory counts: DELIBERATELY NOT CHECKED HERE ---------------
# A clean merge of two correct pin increments leaves the declared size one
# short, and that happened eight-plus times in one day -- so a guard here looked
# obviously right. It is not, because THERE ARE NO LIVE PINNED-INVENTORY ARRAYS
# IN THE TREE. `creal_tests.rs`'s 432-entry array was sharded away; the only
# `git grep` hit for its shape is `creal/inventory.rs:8`, a `//!` line QUOTING
# the deleted declaration in module prose.
#
# The first draft of this script grepped for it, matched that comment, and
# reported the file as having a wrong count. `recount-pinned-inventory.py`
# itself answers "no pinned inventory array found" and exits **2** -- its code
# for UNANSWERABLE, deliberately distinct from a wrong count -- which the draft
# read as a failure.
#
# Two lessons, both already in CLAUDE.md and both re-learned here on the exact
# line it names: a survey grep matches code-shaped text in doc comments, and a
# guard with zero subjects cannot fail no matter how it is written. When the pin
# shape returns (`nat_prelude_tests.rs` is the likely site), gate it with
# `recount-pinned-inventory.py --check`, treat exit 2 as "no subject" rather
# than as a failure, and mask comments before grepping for the shape.
pins="n/a (no live pin sites; see the note above)"

if [ "$fail" -eq 0 ]; then
  echo "MERGE_HYGIENE|markers=0|adr_index=ok|generated=current|pinned_inventories=$pins|PASS"
  exit 0
fi
echo "MERGE_HYGIENE|FAILED"
exit 1
