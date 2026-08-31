# ADR-1225: Prelude inventory ownership comes from the build-order diff, not from a namespace prefix

Status: accepted
Date: 2026-08-31
Index-summary: Every "every X is checked and axiom-free" kernel test filters the
environment by a hand-written NAMESPACE PREFIX, so 27 declarations a prelude
introduces outside its own namespace are invisible to its own completeness
guard. Ownership is now derived from the `DEPENDS_ON` build-order diff, and the
partition is asserted exhaustive.
Index-status: accepted


## Context

`CLAUDE.md` states the rule and the repository has paid for it once:

> Any test named "every X" must derive its X from the authority, not from a
> literal. If the list is maintained by hand, the test measures the maintainer's
> memory.

`creal_tests.rs`'s `every_creal_declaration_is_checked_and_axiom_free` looped
over a hand-maintained array. One assertion against `kernel.environment()` found
**twelve** unchecked declarations, seven long-standing, including the whole
Bishop-completeness `limit` family. Every other prelude grew the same
environment-derived `unlisted` assertion afterwards.

**The survey for this ADR found that fix is already in place everywhere it was
said to be missing.** `nat_prelude_tests.rs`, `int_prelude_tests.rs`,
`rat_prelude_tests.rs`, `complex_tests.rs` and `creal_point_tests.rs` all carry
it today; `prelude_tests.rs` (logic) reaches the same conclusion by a stronger
route (`logic_prelude_with_accessibility_declares_no_axioms` scans the whole
environment for anything assumed, and finding none makes every footprint in it
empty by construction).

What the fix did **not** do is stop using a literal. Each of those assertions
filters `kernel.environment()` with `starts_with("Nat.")`, `starts_with("Int.")`,
`starts_with("Rat.")`, and so on — and the prefix is as hand-written as the name
list it replaced. So the guard is blind in exactly the direction the repository
already knows preludes behave: `int_prelude/wilson.rs` declares `Nat.inverseIndex`
into the `Nat` namespace from the *Int* prelude, and that is documented in
`CLAUDE.md` as its own incident.

Measured 2026-08-31 across all ten preludes, **27 introduced `Definition`/
`Theorem` declarations sit outside their introducing prelude's filter**:

| introducing prelude | outside its own filter | already covered elsewhere? |
| --- | --- | --- |
| `nat` | `Max.max`, `Min.min`, `Squarefree`, `instMinNat` | **no** |
| `cpoint` | `CReal.add_right_cancel` | **no** (`creal` never declares it, so `creal`'s guard cannot see it) |
| `characterization` | `Nat.Peano.iter`, `Int.Characterization.iter` | **no** — `the_characterization_package_builds_and_every_witness_is_axiom_free` iterates `package.entries`, which is 32 `Theorem`s, and these are the package's two `Definition`s |
| `integer` | 14 `Nat.*` (Wilson, Bezout), 8 `Rat.*` | yes — `nat_namespace_declarations_made_by_the_int_prelude_are_axiom_free` and `rat`'s own guard respectively |

The `nat` case is the sharpest: those four names *are* in `definition_names`, so
`every_promised_name_is_admitted_with_the_expected_kind` checks their kind — but
`every_nat_declaration_is_checked_and_axiom_free`'s per-declaration loop begins
`if !shown.starts_with("Nat.") || !listed.contains(name) { continue; }`, so it
skips all four, and a *new* declaration outside `Nat.` would be invisible to its
`unlisted` assertion as well.

## Decision

Ownership of a declaration is the **prelude that introduced it**, computed by
diffing each prelude's full declaration set against the one below it in
`DEPENDS_ON` — the function `cross_prelude_collision_tests.rs` already has for
the collision gate, written for exactly this reason and documented there as
answering "declared by the `nat` prelude" rather than "declared under `Nat.`".

`every_declaration_a_prelude_introduces_is_checked_and_axiom_free` asserts, over
all ten preludes and with no namespace string anywhere in it:

1. every introduced declaration is `Definition`/`Theorem`/`Inductive`/
   `Constructor`/`Recursor`, never `Axiom`/`Opaque`/`Quotient`, unless
   `ASSUMED_BY` licenses that prelude;
2. the licensed count is **exact in both directions** — an axiom leaving
   `axreal` changes the trusted base as much as one arriving;
3. every introduced `Definition`/`Theorem` rests on nothing assumed;
4. the ownership partition is **exhaustive**: every declaration in any prelude's
   environment is introduced by exactly one prelude on that prelude's own
   dependency chain.

## Alternatives rejected

**A per-file owned-prefix set.** `rat_prelude/matrix_det.rs` would declare it
owns `Rat.det*`, `Rat.mat*`, `Rat.altSign`, asserted exhaustive against the
`Rat.` environment. This makes the *prefix list* the hand-maintained literal
instead of the name list — the same defect one level up — and it fails in the
direction that reads as safe: a declaration matching no owned prefix is silently
owned by nobody, and the guard stays green.

**Deriving the declaring FILE.** Not available. `Kernel` stores name, type,
value and kind and no provenance; a sibling lane measured source-scanning at
76.7% attribution, dropping to 57.3% with 628 spurious ambiguities once
`.lemma` is counted (`.lemma` builds a term *reference*, not a declaration).
Prelude granularity is what the kernel can actually answer, and it is enough —
every declaration belongs to exactly one prelude's introduced set.

**Replacing the per-prelude guards.** Not done. They check more than
axiom-freedom (rendered statements, declaration kinds, `Nat`-machinery presence)
and they fail closer to the file a lane is editing. The new gate is the
backstop that no prefix can leak past.

## Consequences

- 2,581 introduced declarations checked from the authority (measured
  2026-08-31: `logic` 43, `nat` 902, `axreal` 0, `integer` 311,
  `characterization` 34, `rat` 365, `string` 86, `creal` 580, `complex` 146,
  `cpoint` 114). The only trusted declarations anywhere are `axreal`'s 30.
- **The gate surfaced no violation on its first run**, unlike the `creal` fix
  that motivated it. That is the honest result and it has a reason: nine of the
  ten environments carry nothing assumed at all, so every footprint in them is
  empty by construction. What the gate adds is that seven declarations no
  completeness guard was watching are now watched, and that adding an eighth
  outside a namespace cannot go unnoticed.
- Footprints are computed per declaration only for a prelude whose environment
  holds something trusted; otherwise emptiness follows from the scan, and the
  "nothing trusted here" fact is recorded and asserted rather than assumed
  (`Kernel::axiom_footprint` walks the closure from scratch on each call, which
  over `creal`'s 2,261 declarations is quadratic).
- Cost: the gate builds all ten preludes, as the collision gate beside it
  already does. Measured in the same `--lib` run, the two together finished in
  **178 s** against **183 s** for the collision gate alone before this change —
  they run concurrently, so wall time did not move.
- Five negative controls drive the same `inventory_report` over kernels mutated
  through `Kernel::add_declaration`, and cover `logic` + `nat` only so they run
  in ~5 s. Seven mutations registered as `prelude-inventory-ownership` in
  `scripts/tests/mutation_controls.py`; each killed exactly one test.
- The gate runs in `scripts/check.sh` step `test` and `just check` via
  `scripts/check-workspace-tests.sh` (`cargo test --workspace --all-features`),
  confirmed by reading the registered command rather than assuming it.

## What this ADR corrects in the brief that produced it

- `nat_prelude_tests.rs`'s `theorem_names` and `complex_tests.rs`'s `named`
  array were flagged as still needing an environment-derived assertion. Both
  have had one since before this lane started.
- `the_determinant_toolkit_is_axiom_free` does iterate a hand list, but its
  completeness gap was already closed one level up: every `Rat.` declaration is
  covered exhaustively by `every_rat_declaration_is_checked_and_axiom_free`. The
  det toolkit needed no per-file owned-prefix mechanism, and the naming problem
  the brief posed does not have to be solved at file granularity at all.
