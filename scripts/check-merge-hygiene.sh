#!/usr/bin/env bash
# Post-merge hygiene: the things that have actually gone wrong when a
# coordinator merges a lane branch, in one command that takes a few seconds.
#
# NINE are listed below and EIGHT are enforced. The pinned-inventory one is
# written down with the reason it is not gated (there are no live subjects, so
# a guard for it could not fail), because a header claiming more checks than
# the body enforces is exactly the kind of gap this file exists to close.
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
#   5. THE IMPORT BACKLOG AND PRODUCTION-PROVENANCE LEDGERS WENT STALE AND
#      STAYED THAT WAY (ADR-1511). Both derive from `artifacts/facts/*.json`
#      alone -- no cargo, no kernel build -- so their `--check` costs ~0.1s and
#      there was never a real reason to leave it out of the cheap gate. It was
#      only ever wired into `scripts/check.sh`/`just check`, the ~10-minute
#      gate nobody runs per merge, and both drifted for days (147 -> 213 rows,
#      2,054 -> 2,343 facts) with the red `--check` visible only there.
#   6. THE THEOREM-COUNTING LEDGERS WENT STALE FOR THE SAME REASON, BUT THEIR
#      REAL `--check` NEEDS A RELEASE KERNEL BUILD (~40s warm, ~3 minutes cold
#      -- measured 2026-09-01 building `prelude_theorem_inventory` from
#      scratch in a fresh worktree) so it cannot live in a ~2-second gate and
#      was deliberately NOT added here whole. What CAN run here for free is a
#      cross-consistency check: `theorem-production-ledger.md`'s distinct
#      count and `ledger-coverage.json`'s `kernel_theorems` count are two
#      committed artifacts derived from the SAME kernel measurement
#      (`prelude_theorem_inventory --include-constructed`) and must agree
#      exactly. They already silently diverged once -- when the kernel grew an
#      `ipc` prelude group on 2026-08-31, `gen-theorem-production-ledger.py`
#      caught it (its own coverage guard, ADR-1511) but nothing forced anyone
#      to notice before merging. This is a NECESSARY, not sufficient,
#      condition for freshness: two stale artifacts regenerated together still
#      agree with each other while both disagree with the true kernel state.
#      The real check remains `gen-theorem-production-ledger.py --check` /
#      `gen-ledger-coverage.py --check` in `scripts/check.sh` and `just check`
#      -- run those before trusting an absolute count, not just this ratchet.
#
#   7. A GENERATED SOURCE FILE, not a generated document.
#      `crates/axeyum-lean-kernel/src/creal/steps_generated.rs` is the `STEPS`
#      build table the creal prelude runs, with its `requires`/`provides`
#      measured from `creal.rs` and its 49 modules rather than written by hand
#      (lane `creal-split-2`). It is here because `creal.rs` has the highest
#      edit rate in the repository -- so it is the generated file most likely
#      to be merged stale -- and because a stale one is SILENT: the build
#      succeeds with a dependency graph missing whatever the merge added,
#      which is exactly the under-constrained preflight the generator
#      replaced (the hand-written table it succeeded named 3,934 of 4,831
#      real edges). ~1.1s, pure Python over the source, no cargo.
#
#   8. THE SECOND GENERATED SOURCE FILE, AND THE ONE THAT PROVED THE RULE.
#      `crates/axeyum-py/src/kernel/prelude_fields.rs` is the Python binding's
#      `{field name -> NameId}` table for all nine preludes, generated because
#      Rust has no reflection. When lane `creal-split-2` moved `CRealPrelude`'s
#      per-module names behind ADR-1512 registries (8dd580a1c), main stopped
#      compiling; the regeneration that fixed that ALSO silently deleted 69 of
#      `creal`'s 606 names from the Python surface, because the generator
#      matched flat `pub <n>: NameId` lines only. Nothing caught it -- measured
#      2026-09-01, `gen-py-prelude-fields.py --check` was registered in NO gate
#      (`scripts/check.sh`, this file, the `justfile`, `hooks/pre-push`: zero
#      hits), which is exactly why the stale file reached main. ~0.3s, pure
#      Python plus one `rustfmt`, no cargo. Its exit 2 means "no `rustfmt`, so
#      the question cannot be answered" and is reported, not failed.
#
# Exit 0 only when all eight enforced checks pass. Each failure names its own
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

# `crates/axeyum-lean-kernel/src/creal/steps_generated.rs` is a GENERATED
# SOURCE FILE -- the `STEPS` table the creal prelude builds against, whose
# `requires`/`provides` are measured from `creal.rs` and its modules rather
# than written by hand. It is here for the same reason PLAN.md is: `creal.rs`
# has the highest edit rate in the repository, so it is the generated file most
# likely to be merged stale, and a stale one silently under-constrains the
# build order -- the exact defect the generator replaced. ~1.1s, pure Python,
# no cargo. `--strict` makes the exit depend on the finding and `--self-check`
# is its positive control.
if ! creal_out=$(python3 scripts/creal-declare-deps.py --check --strict --self-check 2>&1); then
  fail=1
  echo "FAIL: creal-declare-deps.py --check --strict --self-check"
  printf '%s\n' "$creal_out" | sed 's/^/    /'
  note "Run scripts/creal-declare-deps.py and commit BOTH"
  note "crates/axeyum-lean-kernel/src/creal/steps_generated.rs and"
  note "artifacts/refactor/creal-declare-deps.json."
fi

# `crates/axeyum-py/src/kernel/prelude_fields.rs` is the OTHER generated source
# file, and it is the one that proved the rule. The registry split (8dd580a1c)
# changed `CRealPrelude`'s shape; the generator matched flat `pub <n>: NameId`
# lines only, so the regeneration that unbroke main dropped 69 of `creal`'s 606
# names from the Python binding and no gate said a word -- because
# `gen-py-prelude-fields.py --check` was registered in NO gate at all
# (`check.sh`, this file, the justfile, `hooks/pre-push`: zero hits). ~0.3s,
# pure Python plus one `rustfmt`, no cargo.
#
# EXIT 2 IS "CANNOT ANSWER", NOT A FAILURE. The committed file is `rustfmt`'s
# fixed point, so on a host without `rustfmt` the comparison is against a
# different text and every tree would read as stale. The generator says so and
# exits 2; reporting that is honest, turning it red is noise.
py_fields_out=$(python3 scripts/gen-py-prelude-fields.py --check 2>&1)
py_fields_rc=$?
py_fields_state=current
if [ "$py_fields_rc" -eq 2 ]; then
  py_fields_state="skipped (no rustfmt)"
  note "gen-py-prelude-fields.py --check: SKIPPED (rustfmt not on PATH)"
elif [ "$py_fields_rc" -ne 0 ]; then
  fail=1
  echo "FAIL: gen-py-prelude-fields.py --check"
  printf '%s\n' "$py_fields_out" | sed 's/^/    /'
  note "Run scripts/gen-py-prelude-fields.py and commit"
  note "crates/axeyum-py/src/kernel/prelude_fields.rs. A prelude gained, lost or"
  note "MOVED a name -- an ADR-1512 registry move shrinks the table silently."
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

# --- 5. import backlog and production-provenance ledgers -------------------
# Both derive from `artifacts/facts/*.json` alone -- no cargo, no kernel
# build -- so `--check` costs ~0.1s each (measured 2026-09-01) and there was
# no real reason to leave them out of the cheap gate. See point 5 above.
if ! import_out=$(python3 scripts/gen-import-backlog.py --check 2>&1); then
  fail=1
  echo "FAIL: gen-import-backlog.py --check"
  printf '%s\n' "$import_out" | sed 's/^/    /'
  note "Run scripts/gen-import-backlog.py and commit artifacts/import-backlog.json."
fi

if ! provenance_out=$(python3 scripts/gen-production-provenance-ledger.py --check 2>&1); then
  fail=1
  echo "FAIL: gen-production-provenance-ledger.py --check"
  printf '%s\n' "$provenance_out" | sed 's/^/    /'
  note "Run scripts/gen-production-provenance-ledger.py and commit"
  note "docs/plan/generated/production-provenance-ledger.md."
fi

# --- 6. theorem-ledger cross-consistency (a NECESSARY, not sufficient, ------
#        freshness check -- see point 6 above for why the real --checks stay
#        in scripts/check.sh / just check rather than living here whole) ----
# `theorem-production-ledger.md`'s distinct count and `ledger-coverage.json`'s
# `kernel_theorems` count are two committed artifacts derived from the SAME
# kernel measurement and must agree exactly. Comparing two committed files
# costs no cargo and no kernel build. This is the check that would have
# caught the `ipc` prelude gap (ADR-1511) at merge time rather than only when
# someone happened to run the full gate.
theorem_ledger="docs/plan/generated/theorem-production-ledger.md"
coverage_json="artifacts/ledger-coverage.json"
if [ -f "$theorem_ledger" ] && [ -f "$coverage_json" ]; then
  ledger_count=$(/usr/bin/grep -oE '\*\*[0-9]+ distinct theorems\*\*' "$theorem_ledger" \
    | /usr/bin/grep -oE '[0-9]+' | head -1)
  coverage_count=$(python3 -c "
import json
print(json.load(open('$coverage_json'))['counts']['overall']['kernel_theorems'])
" 2>/dev/null)
  if [ -z "$ledger_count" ] || [ -z "$coverage_count" ]; then
    fail=1
    echo "FAIL: theorem-ledger cross-consistency (could not read one or both counts)"
    note "ledger_count=${ledger_count:-<unreadable>} coverage_count=${coverage_count:-<unreadable>}"
    note "Regenerate both: python3 scripts/gen-theorem-production-ledger.py and"
    note "python3 scripts/gen-ledger-coverage.py."
  elif [ "$ledger_count" != "$coverage_count" ]; then
    fail=1
    echo "FAIL: theorem-ledger cross-consistency"
    note "$theorem_ledger says $ledger_count distinct theorems;"
    note "$coverage_json says kernel_theorems=$coverage_count. They derive from"
    note "the SAME kernel measurement and must agree -- one of the two was"
    note "regenerated without the other. Regenerate both and re-commit:"
    note "  python3 scripts/gen-theorem-production-ledger.py"
    note "  python3 scripts/gen-ledger-coverage.py"
    note "This does NOT confirm either number is fresh against the true kernel"
    note "state -- only that the two committed artifacts agree. The real"
    note "freshness check is gen-theorem-production-ledger.py --check /"
    note "gen-ledger-coverage.py --check, in scripts/check.sh and just check"
    note "(needs a release kernel build: ~40s warm, ~3min cold -- too expensive"
    note "for this gate)."
  fi
else
  note "theorem-ledger cross-consistency: SKIPPED (one or both artifacts absent)"
fi

if [ "$fail" -eq 0 ]; then
  echo "MERGE_HYGIENE|markers=0|adr_index=ok|generated=current|creal_steps_table=current|py_prelude_fields=$py_fields_state|pinned_inventories=$pins|import_backlog=ok|production_provenance=ok|theorem_ledger_consistency=ok|PASS"
  exit 0
fi
echo "MERGE_HYGIENE|FAILED"
exit 1
