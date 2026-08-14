# Diary: sharding `nat_prelude.rs`

Lane: `nat-shard`. Date: 2026-08-14.

`crates/axeyum-lean-kernel/src/nat_prelude.rs` was 9,969 lines in one file with
one writer. Every proof-route fact and the whole formalization backlog goes
through it, so it was the last refactor gating parallel *mathematical* work.
This note records the grouping, the visibility changes, what was not a clean
seam, and what I would tell the next person.

## Result

| file | lines | contents |
|---|---|---|
| `nat_prelude.rs` (parent) | 713 | module doc, `NatPrelude` handle struct, `build_nat_prelude`, module wiring |
| `nat_prelude/order.rs` | 1,725 | `declare_order` — `Nat.le`, monotonicity, totality, `lt_well_founded` |
| `nat_prelude/modular.rs` | 1,440 | the `declare_mod_*` cluster — `Nat.modEq` and its closure laws |
| `nat_prelude/division.rs` | 1,403 | `declare_euclidean_division` + the executable-division spec proof |
| `nat_prelude/divisibility.rs` | 1,063 | `declare_divisibility` — `Nat.dvd` and its laws |
| `nat_prelude/ops.rs` | 949 | `NatState`, `NatOps`, `NatDev` — the proof-construction layer |
| `nat_prelude/algebra.rs` | 741 | additive, multiplicative, subtraction, finite-sum theorems |
| `nat_prelude/defs.rs` | 702 | arithmetic/`beq`/`sub`/`sumRange`/div-state definitions + defining equations |
| `nat_prelude/bezout.rs` | 680 | `declare_gcd_bezout` and its balanced-witness helpers |
| `nat_prelude/gcd.rs` | 577 | `declare_executable_gcd`, `gcd_semantics`, `dvd_gcd_semantics` |
| `nat_prelude/helpers.rs` | 153 | shared `Iff`/`And`/`dvd` proof-term combinators |

`nat_prelude/nat_prelude_tests.rs` (3,431 lines) was already a submodule and was
not touched.

## The grouping, and where it departs from the brief

The brief's measured grouping was right about the seams; I split two of its
clusters further and merged nothing.

- **The gcd cluster became two files, not one.** The brief measured
  `executable_gcd + gcd_semantics + gcd_bezout + dvd_gcd_semantics` at ~2,300
  lines as a unit. But the call graph splits cleanly: the Bezout development
  (`bezout_*_exists`, `left_sum*`, `prove_bezout_*`, `eliminate_bezout`,
  `declare_gcd_bezout`) calls *nothing* in the gcd-characterization development
  and vice versa — the only shared symbol is `and_left`, which lives in
  `helpers.rs` anyway. Two 577/680-line files with zero coupling beat one
  1,257-line file, and Bezout is exactly the kind of thing a lane extends
  (Gauss lemma, coprimality) without wanting to touch gcd's unfolding equations.
- **`gcd_fix_parts` / `gcd_fix_equation` / `declare_dvd_gcd_semantics` moved
  back next to `declare_gcd_semantics`,** even though they sit ~700 lines later
  in the original file. They are the same development, interleaved with Bezout
  only by accident of when each was written. Grouping by call graph rather than
  by line number let all three become module-private again.
- **`ops.rs` is the one non-topical file** and it had to be extracted first:
  `NatDev`/`NatOps` are named by every other module, so nothing else can move
  until they have a home.
- **`defs.rs` is discontiguous in the original** (lines 684-1238 plus
  `declare_defining_equations` at 2663-2785). The defining-equation theorems are
  `Eq.refl` proofs *about the definitions* and belong with them; they were
  separated only because `declare_modular_congruence` was inserted between.

## Visibility changes — three classes, all of them narrow

Rust makes a parent module's private items visible to its descendants, so the
direction that needed no work at all was children reading the parent. The work
was the other direction. Twenty-seven functions became `pub(super)`; nothing
became `pub` or `pub(crate)` that was not already.

1. **Entry points the parent calls (22 functions).** Every `declare_*` that
   `build_nat_prelude` invokes: `declare_arithmetic`, `declare_order`,
   `declare_divisibility`, and so on. Purely mechanical.
2. **Genuine sibling coupling (5 functions).**
   - `division::declare_executable_division_spec` — called by `divisibility`,
     *not* by the parent. This one is a real dependency between developments:
     the divisibility laws are stated against the executable remainder.
   - `helpers::{apply_nat_function_equality, iff_forward, iff_reverse, and_left,
     and_right, transport_dvd_left, transport_dvd_right}` — 7 combinators used
     by `divisibility`, `gcd`, and `bezout`. This is why `helpers.rs` exists at
     all; inlining them into any one topic module would have forced a
     topic-to-topic dependency for no reason.
   - `bezout::{bezout_tail_exists, bezout_after_mp_exists}` — see below.
3. **Type re-export.** `NatState`/`NatOps`/`NatDev` moved to `ops.rs` and the
   parent carries `pub use ops::{NatDev, NatOps, NatState};` so
   `crate::NatOps` and the two `tests/rado_*.rs` integration suites keep working
   unchanged. No public path moved.

I verified the visibility is as narrow as compiles by checking each
`pub(super)` name for a call site outside its own file. One was over-broad on
the first pass (`left_sum`) and is now private again; see below for why the
check initially lied.

## What was NOT a clean seam

- **`ops.rs` and `bezout.rs` are mutually dependent.** `NatOps` has default
  methods that build Bezout statement types, so the trait calls
  `bezout_tail_exists` and `bezout_after_mp_exists`, while `bezout.rs` of course
  calls the trait. Rust is fine with a module cycle, so this compiles, but it is
  the one place where "one file per topic" does not describe the truth: the
  generic proof layer knows about one specific number-theoretic development.
  A future lane that wants `ops.rs` to be genuinely topic-free should move
  `mod_eq_*`/`bezout_*` *statement builders* out of the `NatOps` trait into the
  modules that own those relations. I did not do it here because it would change
  the public `NatOps` surface, which is not a semantically null refactor and
  would have put the control diff at risk.
- **Identifier-collision made the mechanical checks unreliable.** `left_sum` is
  both a top-level function in the Bezout development and a local `let` binding
  in four places in `modular.rs`. A word-boundary grep therefore "proved"
  cross-module use and produced both a bogus `pub(super)` and a bogus
  `use super::bezout::left_sum;`. The compiler caught the import (unused import
  is a warning, and `-D warnings` promotes it) but it would *never* have caught
  the over-broad visibility, because Rust does not warn about a `pub(super)` that
  nothing outside the module uses. I re-ran the analysis requiring a call site
  (`name\s*\(`) rather than a bare mention, which is what the original
  cross-reference used. If you automate this kind of move: match call sites, not
  identifiers.
- **One doc link broke and only rustdoc found it.** `NatDev`'s doc comment says
  "[`build_nat_prelude`] uses it to prove the prelude's own theorems". Once
  `NatDev` moved into a child module that link no longer resolved. `cargo build`,
  `cargo test`, and `cargo clippy` were all completely green with it broken; only
  `RUSTDOCFLAGS="-D warnings" cargo doc` failed. It now carries an explicit
  `super::build_nat_prelude` path in the link target. Anyone moving documented
  items between modules in this repo should run the doc gate, not just the test
  and lint gates.
- **A near miss on lint attributes.** The parent's
  `#![allow(clippy::many_single_char_names, similar_names, too_many_lines,
  type_complexity)]` is what makes these proof scripts lint-clean. Lint levels
  are scoped by the *module tree*, not the file, so it keeps applying to
  out-of-line children and no `allow` had to be duplicated. Had that not been
  true, the split would have needed the same four-line attribute block copied
  into ten files, and any future file added without it would fail clippy for
  reasons unrelated to its content.

## Controls

Semantically this refactor is null by construction — no proof term, statement,
or declaration order changed. That claim is checked, not asserted:

| control | result |
|---|---|
| `nat_theorem_inventory` before/after diff | **empty**, 119 theorems, same names and same canonical `render_lean` types |
| `nat_axiom_inventory` | `nat: axiom=0 opaque=0 quotient=0 total_trusted=0` |
| `cargo test -p axeyum-lean-kernel` | 369 passed, 0 failed |
| `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings` | clean |
| `RUSTDOCFLAGS="-D warnings" cargo doc` (added) | clean, after the link repair above |

Every one of the ten commits was gated on `cargo clippy --lib -- -D warnings`
before it was made — but see the next section: nine of the ten actually compile
on their own, and the gate could not have told me which.

## The gate that passed over a commit that does not build

Worth writing down, because it is the same shape as the gate failures `04` is
about.

The replay ran, for each stage: regenerate the tree, `cargo clippy -- -D
warnings`, then `git add`/`git commit` with an explicit pathspec of *the parent
and the one new module*. That pathspec is the bug. When `bezout.rs` was
extracted at stage 10, the generator also had to rewrite one line in the
already-committed `ops.rs` (`use super::{bezout_tail_exists, …}` became
`use super::bezout::{…}`, because those functions were no longer in the parent).
The pathspec did not list `ops.rs`, so that line stayed in the worktree and out
of the commit. `ae589be97` does not build.

The lint gate passed because **it ran against the worktree, which had the fix**.
An exit-0 gate immediately before `git commit` says nothing about what the commit
contains when the pathspec is narrower than the change. The repo's hygiene rule
warns that a pathspec is *not sufficient* because `git add <file>` sweeps in
another lane's hunks; this is the opposite failure and it is not covered by that
warning — a pathspec that is too narrow silently drops your own hunks.

I found it from `git status` afterwards, not from any gate. It is repaired in a
follow-up commit rather than by amending, because rewriting history in a shared
checkout is not allowed. I then checked every commit statically — for each, does
every `use super::NAME` resolve to an item actually present in the parent at that
commit — and `ae589be97` is the only one affected.

The transferable rule: when a refactor moves a symbol, the commit must include
*every* file whose import path changed, not just the source and destination. If
you script staged commits, derive the pathspec from `git status` at that stage
rather than writing it out by hand.

## Honest feedback

- **The acceptance control is the reason this was safe to do.** A 9,969-line
  move of hand-written proof scripts is exactly the change where "it compiles and
  the tests pass" is weak evidence: the tests check the environment the prelude
  builds, but a mis-ordered declaration or a dropped theorem could still have
  slipped past into something that type-checks. Byte-identical canonical types
  for all 119 theorems is a real control. More of this repo's refactors should
  ship with one.
- **I did the split twice on purpose.** The first pass was one big edit, taken
  all the way through the four controls to establish that the target state is
  good. Only then did I reset to `HEAD` and replay the same split as ten
  per-module commits, gating each. The alternative — trying to get a clean
  ten-commit history on the first attempt — means debugging import resolution at
  ten different intermediate states where half the functions are still in the
  parent. Doing it in this order cost one extra build cycle and removed all of
  that risk.
- **Is one file per topic the right end state?** For nine of the ten, yes: they
  are 150-1,725 lines with a single subject and near-zero coupling.
  `order.rs` at 1,725 lines is the one that will want splitting again, and it
  has a natural line (the `Nat.le` inductive and its basic laws, versus the
  arithmetic-monotonicity theorems and `lt_well_founded` built on top). I left it
  whole because `declare_order` is a single function — splitting it is real
  editing, not a move, and would have put the control diff at risk in a commit
  whose whole value is that the control diff is empty. That is a good next task
  for whoever owns the order fragment.
- **The coupling that should stay is `helpers.rs`.** It is tempting to fold
  seven small combinators into their callers, but three separate developments
  use them, and duplicating them is how two copies drift apart.
