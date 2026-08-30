# Notes: 248-pin-recount-shapes

Detail moved out of [`../status/248-pin-recount-shapes.md`](../status/248-pin-recount-shapes.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Whole-tree, using the new engine over `git ls-files '*.rs'`, filtered to element
types `crate::NameId` / `NameId` / `&str` / `(&str, crate::NameId, &str)`:
**72 pinned-array definition sites**, all internally consistent. The design
review surveyed a kernel-shaped subset and reported 12.

| shape | sites | correct with the OLD engine | correct now |
| --- | --- | --- | --- |
| `[&str; N]` | 62 | 3 | 62 |
| `[NameId; N]` | 6 | 6 | 6 |
| `[crate::NameId; N]` | 4 | 4 | 4 |
| `[(&str, crate::NameId, &str); N]` | **0** | — | — |
| total | **72** | **13** | **72** |

The "old engine" column is the shape-independent engine with only the
string-masking fix reverted, measured in a scratch copy — not the original
line-shape tool, which recognized `let expected: [(&str, crate::NameId, &str);
N]` and therefore **0 of these 72**. The 3 accidental successes are arrays whose
entries are identifiers rather than literals (`const ROOTS: [&str; 2] =
[POS_BRANCH, NEG_BRANCH];`), so nothing was masked away.

The distinction that matters is not the shape — it is **whether a lane's ordinary
work adds a row.** Only a growing list can produce the documented merge failure
(two lanes each bump the pin correctly against their own base; git merges the
entry lines cleanly and leaves the declared size short).

### Growing lists — a lane's work adds rows here

| site | shape | N | authority-derived assertion covering completeness |
| --- | --- | --- | --- |
| `int_prelude_tests.rs:186` `derived_laws` | `[crate::NameId; N]` | 156 | `every_int_declaration_is_checked_and_axiom_free` |
| `int_prelude_tests.rs:352` `derived_lemmas` | `[crate::NameId; N]` | 28 | same |
| `int_prelude_tests.rs:396` `definition_names` | `[crate::NameId; N]` | 27 | same |
| `int_prelude_tests.rs:434` `asserted_laws` | `[crate::NameId; N]` | 0 | `the_only_trusted_declarations_are_the_asserted_laws` |
| `complex/complex_tests.rs:3010` `EXPECTED_STEP_ORDER` | `[&str; N]` | 91 | `steps_table_matches_recorded_extraction` (slice `assert_eq!` against `STEPS`) |

The four `int_prelude_tests.rs` lists are read by
`every_int_declaration_is_checked_and_axiom_free`, which enumerates
`k.environment().iter()`, filters to `Definition`/`Theorem` under `Int.`, and
fails naming anything absent from the union of all four. That is the assertion
CLAUDE.md's `creal` resolution points at, in this file, already landed, and its
own doc comment records that it found `definition_names` missing **entirely**
and two unlisted `natAbs` theorems.

`EXPECTED_STEP_ORDER` is compared with `assert_eq!(labels.as_slice(),
EXPECTED_STEP_ORDER.as_slice())` against `super::STEPS`.

### Fixed lists — load-bearing, and a lane never grows them

| site | shape | N | what the pin does |
| --- | --- | --- | --- |
| `ordered_ring.rs:71` `RING_BINDER_NAMES` | `[&str; N]` | 30 | positionally aligned with `ring_telescope() -> [NameId; 30]`; `.len()` feeds `pub const SETOID_RING_BINDERS` and `RING_LAW_BINDERS` |
| `ordered_ring.rs:112` `SETOID_RING_BINDER_NAMES` | `[&str; N]` | 39 | aligned with `setoid_ring_telescope() -> [NameId; 39]` |
| `ordered_ring.rs:893` `setoid_ring_telescope` | `[NameId; N]` | 39 | the other half of that alignment — **the design review missed this site** |
| `ordered_ring.rs:942` `ring_telescope` | `[NameId; N]` | 30 | returns `RingSignature::declarations()`, itself `[NameId; 30]` |
| `creal.rs:6346`, `rat_prelude.rs:1719`, `arith_prelude.rs:232`, `rat_prelude/model.rs:98` | `[NameId; N]` | 22 | the 22 ordered-commutative-ring laws |
| `complex.rs:1417` `ring_laws` | `[NameId; N]` | 9 | the commutative-ring laws over ℂ |
| `axreal_call_site_guard.rs:56` `FLAGGED_CALLS` | `[&str; N]` | 2 | two identifiers the guard keeps out of shipped code |
| `theorem_composition.rs:32` | `[&str; N]` | 3 | the declaration-exact Lean 4.30 `Acc` package SHA-256s |
| 54 further sites in `axeyum-lean-import/examples/`, `axeyum-cas`, fuzz alphabets | `[&str; N]` | small | per-capsule hash/label/root lists and fixed test domains |

`30` is not a choice: CLAUDE.md records it as the **floor for an axiomatized
ordered field**, since `AxReal`'s carrier is opaque and every operation and law
must be assumed. `39 = 30 + 9` equality-slot binders. These pins tie two arrays
to one length at the type level, which is exactly what makes the positional
hand-off in `specialize_setoid_to_eq` safe.

### Four corrections to the design review

1. **The "covered" row is wrong: there are ZERO sites of the tuple shape.**
   `creal/inventory.rs`'s `[(&str, crate::NameId, &str); 432]` is a **prose
   quote inside `//!` module docs**, explaining why that pin was deleted. The
   existing control suite already knew this — its last case is literally named
   `no_real_file_currently_uses_this_pin_shape` and it passes. So the tool
   covered **one of four shapes and zero of twelve real sites**, which is worse
   than the review states, and is why nobody noticed it had stopped working.
2. **`inductive_tests.rs` has no pinned list.** Both `[crate::NameId; 2]`
   occurrences are components of a function's return **tuple type**
   (`-> (NameId, NameId, [NameId; 2])`), with no array literal following. The
   new engine correctly declines them — that is what
   `a_bare_type_annotation_is_not_a_pin` pins.
3. **`ordered_ring.rs` has three sites, not two** (the `[NameId; 39]` telescope
   at line 893 is the one that makes the other two load-bearing).
4. **`geometry_corpus.rs` / `geometry_certify.rs` carry `[&str; 7]` and
   `[&str; 4]`** — fixed test domains (`["a","b","c","p","x","y","z"]`), not
   growable inventories.

## Deliverable 2 — per-site judgment

The question the brief asks, per site: **what would this pin catch that nothing
else catches?**

### `int_prelude_tests.rs` ×4 — DELETE the pin, keep the lists

*What the pin catches: nothing.* No code compares these lengths against
anything derived from the kernel. The number was never derived from an
authority — somebody wrote `156` because there were 156 entries. It constrains
the list against itself, which is precisely the reasoning CLAUDE.md used to
delete `creal_tests.rs`'s 432-entry pin.

*What subsumes it:* `every_int_declaration_is_checked_and_axiom_free` reads
`kernel.environment()` and fails on any `Int.` `Definition`/`Theorem` absent
from the union of the four lists. That covers the direction that matters
(a declaration nobody listed) which the pin **cannot see at all**, and it
covers the merge-drop direction (an entry lost in a merge) too, because the
declaration is still live and now unlisted.

*What it costs:* it is the exact site of today's incident — lane 151→153, HEAD
151→154, merged list 156, declared 154, clean merge, broken build. Five lanes
are live in this file right now.

*Prior art in the same tree:* `nat_prelude_tests.rs`'s `theorem_names` is
already `fn theorem_names(p: &NatPrelude) -> Vec<NameId> { vec![ ... ] }`, has
the same `every_nat_declaration_is_checked_and_axiom_free` backstop, and is
being edited by several of the same lanes **without this friction**. The house
pattern already exists; `int_prelude_tests.rs` simply predates it.

*Recipe* (four functions, two lines each):

```
-fn derived_laws(p: &IntPrelude) -> [crate::NameId; 156] {
-    [
+fn derived_laws(p: &IntPrelude) -> Vec<crate::NameId> {
+    vec![
 ...
-    ]
+    ]
 }
```

`asserted_laws` becomes `-> Vec<crate::NameId> { Vec::new() }`. Every consumer
already uses `.into_iter()`, `.chain(...)` and `.collect()`, all of which are
`Vec`-compatible; the doc comment on `asserted_laws` ("expected to shrink and
must never grow") stays true and stays enforced by
`the_only_trusted_declarations_are_the_asserted_laws`, which reads the
environment.

### `complex_tests.rs` `EXPECTED_STEP_ORDER` — DELETE the pin, keep the list

*What the pin catches: nothing.* `assert_eq!` on two slices already fails on a
length mismatch, with a message naming the position — strictly better than a
compile error. The **list** is a golden record of the pre-refactor hand-written
call sequence and is genuinely load-bearing; only the `91` is not.

*Recipe:* `const EXPECTED_STEP_ORDER: &[&str] = &[ ... ];` and drop the
`.as_slice()` at the single use site (line 3113).

### `ordered_ring.rs` ×4, and the `[NameId; 22]` / `[NameId; 9]` law arrays — KEEP

*What the pin catches:* a length disagreement between two arrays that are read
**positionally against each other** — zipped at `ordered_ring.rs:362`/`:367`,
and at `:1004` indexed as `RING_BINDER_NAMES[position]` where `position`
enumerates `ring_telescope()`. That second form would **panic at runtime** if
the two lengths ever diverged; the pin is what makes the divergence
unrepresentable. `RING_BINDER_NAMES.len()` is additionally consumed by two
`pub const`s (`SETOID_RING_BINDERS`, `RING_LAW_BINDERS`). These
are architectural constants (30 = the ordered-field floor, 39 = 30 + 9, 22 = the
ring laws), not inventories, and no lane's ordinary work adds a row. Zero merge
friction, real diagnostic value. The tool now covers them, which is the right
outcome for this class.

### `axreal_call_site_guard.rs`, `theorem_composition.rs`, and the ~60
`axeyum-lean-import` capsule constants — KEEP

Fixed pinned data (flagged identifiers, package SHA-256s, per-capsule hash and
label lists). They change only when the thing they pin changes, which is the
point. Now covered by the tool at no cost.

## Deliverable 3 — what was executed, and what was not

**Executed:** the engine (`ce173137b`) and the controls (`ed8335521`). This was
the brief's stated first priority and it unblocks the merge path for the five
running lanes immediately — `python3 scripts/recount-pinned-inventory.py
crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs` now reports
`156/28/27/0` and rewrites any that moved.

**NOT executed: the two pin deletions.** Both are Rust changes and the brief
conditions them on "only where the tests still pass". This worktree has **no
`target/` directory**, so any `cargo` invocation here is a full cold workspace
build behind the host-wide `cargo-serialized.sh` flock — the mechanical cause
CLAUDE.md identifies for the tenth subagent stall (83 GB across 125 worktrees,
each paying a cold build before a single test runs). Spending that on a
cosmetic pin removal, while five lanes contend for the same lock, is the wrong
trade; and shipping an unverified Rust edit is the failure
`cargo-check-is-not-the-kernel-gate` names. So the recipes above are handed to
the coordinator, who re-verifies before merging anyway.

The `int_prelude_tests.rs` conversion should land **after** the five concurrent
lanes merge, not before: it touches the same signature lines they are bumping,
and doing it during the merge window trades a silent breakage for a noisy
conflict in every one of them at once. Doing it after costs one conflict, in
one lane, resolved by taking the `Vec` side — and removes the friction for good.

## Suggested follow-up (not done here)

`scripts/recount-pinned-inventory.py --check` over the growing files is a
one-line gate step and would turn today's post-merge compile error into a
pre-merge diagnostic naming the file, the line, and both numbers. It is not
wired into `just check` or `check.sh` by this lane, because a pin deletion would
then need the gate updated in the same commit and the deletions are deferred
above.

## Landed changes

| commit | what |
| --- | --- |
| `ce173137b` | shape-independent counting engine; masking; multi-pin support; `single`/`wrapped` measured on masked text |
| `ed8335521` | six new controls, each mutation-verified in a scratch `copytree`; measured kill matrix and its two honest caveats recorded in the suite header |
