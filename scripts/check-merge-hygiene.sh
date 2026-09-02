#!/usr/bin/env bash
# Post-merge hygiene: the things that have actually gone wrong when a
# coordinator merges a lane branch, in one command.
#
# FIVE are listed below and FOUR are enforced. The fifth is written down with
# the reason it is not gated (there are no live subjects, so a guard for it
# could not fail), because a header claiming five while the body enforces four
# is exactly the kind of gap this file exists to close.
#
# COST: guards 1-3 are ~2 seconds. Guard 4 runs `fact-frontier.py --json` over
# the whole ledger and is ~15 seconds on s4, so the whole command is ~20. Stated
# here rather than left as a surprise: this file advertised ~2 seconds while
# that guard was added, and an unexpectedly slow gate is a gate that stops being
# run.
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
#   4. A STALE FRONTIER SHAPE CENSUS. The census is a pure function of the fact
#      ledger, so a merge that lands or flips facts invalidates it while
#      touching neither the script nor the artifact -- invisible in
#      `git show --stat`, and the artifact's whole job is to tell the next
#      producer designer what the frontier is shaped like.
#   5. A PINNED-INVENTORY COUNT BROKEN BY A CLEAN MERGE. Two lanes can each
#      correctly bump a pinned length and git merges both entries without
#      conflict, leaving the declared size one short. Eight times in one day.
#
# Exit 0 only when all four enforced checks pass. Each failure names its own
# remedy.
set -u
# `AXEYUM_MERGE_HYGIENE_ROOT` points the SHIPPED script at a throwaway tree, so
# the controls in `scripts/tests/test_check_merge_hygiene.py` drive these guards
# to failure without re-implementing them and without dirtying the real
# checkout. Same device as `AXEYUM_KERNEL_SUITES_ROOT`. Unset in every real run.
cd "${AXEYUM_MERGE_HYGIENE_ROOT:-$(dirname "$0")/..}" || exit 2
fail=0
note() { printf '  %s\n' "$1"; }

# --- 1. conflict markers in tracked files ------------------------------------
# Only tracked files, and only real markers at line start. `git grep` skips
# .gitignore'd trees, which is what keeps this fast in a repo with 200 worktrees.
#
# THE EXCLUSION IS `scripts/tests/fixtures/`, NOT `scripts/tests/`. The first
# draft excluded the whole controls directory, which is where every control
# suite in this repository lives -- so a conflict-marker-shaped defect committed
# into a control suite was invisible to the gate whose controls those are.
# Measured 2026-08-30: zero tracked files under `scripts/tests/` contain a
# marker today, so narrowing it costs nothing and closes the hole. A control
# that genuinely needs marker text as DATA writes it under `fixtures/`, or
# builds it at runtime from repeated characters (which is what
# `test_check_merge_hygiene.py` does, so that this gate's own controls are
# scanned by it rather than exempt from it).
marker_re='^(<<<<<<< |>>>>>>> |={7}$)'
marker_paths=(':!*.md.orig' ':!scripts/tests/fixtures/*')
markers=$(git grep -lE "$marker_re" -- "${marker_paths[@]}" 2>/dev/null | /usr/bin/grep -c . || true)
if [ "$markers" -ne 0 ]; then
  fail=1
  echo "FAIL: $markers tracked file(s) contain conflict markers:"
  git grep -lE "$marker_re" -- "${marker_paths[@]}" | sed 's/^/    /'
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

# --- 4. the frontier shape census is current ---------------------------------
# Same class of defect as guard 3, on an artifact a merge moves silently. The
# census is a pure function of the fact ledger, and a merge that lands or flips
# facts changes it while touching neither the census script nor its artifact --
# so `git show --stat` shows nothing and a stale census keeps telling the next
# producer designer that the frontier has a shape it no longer has.
#
# THREE outcomes, not two. Exit 2 is the census saying it could not compute an
# answer (no frontier), which must NOT be a failure: a gate that reports
# "disagrees" when its subject was unavailable is wrong about its own subject,
# which this repository has shipped three times in one day.
census_out=$(python3 scripts/frontier-shape-census.py --check 2>&1)
census_rc=$?
if [ "$census_rc" -eq 0 ]; then
  census="current"
elif [ "$census_rc" -eq 2 ]; then
  census="not-answerable"
else
  fail=1
  echo "FAIL: frontier-shape-census.py --check"
  printf '%s\n' "$census_out" | tail -4 | sed 's/^/    /'
  note "Run scripts/frontier-shape-census.py and commit"
  note "artifacts/autogenesis/frontier-shape-census-v1.json."
fi

# --- 5. pinned inventory counts: DELIBERATELY NOT CHECKED HERE ---------------
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
  echo "MERGE_HYGIENE|markers=0|adr_index=ok|generated=current|shape_census=$census|pinned_inventories=$pins|PASS"
  exit 0
fi
echo "MERGE_HYGIENE|FAILED"
exit 1
