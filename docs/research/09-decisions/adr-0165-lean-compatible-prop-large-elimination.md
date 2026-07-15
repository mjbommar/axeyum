# ADR-0165: Lean-compatible `Prop` large elimination

Status: accepted
Date: 2026-07-15

## Context

ADR-0036 makes fidelity to Lean's kernel a soundness obligation. The incident
recorded in
[`09-P0-kernel-unsoundness.md`](../../prover-track/research/09-P0-kernel-unsoundness.md)
showed that the obligation was violated: every inductive recursor received a
fresh motive universe, including a two-constructor proposition. Combined with
the kernel's intentional proof irrelevance and impredicative `Prop`, that let a
closed exploit pass `add_declaration` as `theorem bad : False`.

The fix must not reject valid propositions or disable legitimate elimination
for syntactic subsingletons such as `False`, `True`, `And`, `Iff`, and `Eq`.
It must also handle universe-polymorphic result sorts conservatively: a family
whose result level can become zero cannot receive a universally computational
recursor merely because another instantiation inhabits `Type`.

This closes the large-elimination question raised by ADR-0036 and the P3.6p
soundness stop in `PLAN.md`/`STATUS.md`.

## Decision

Adopt Lean's syntactic-subsingleton test at the trusted `add_inductive` gate and
make the generated recursor's universe shape reflect the result.

An inductive may eliminate into an arbitrary `Sort v` when either:

1. its result universe is provably nonzero for every universe assignment; or
2. it may inhabit `Prop`, but has no constructors; or
3. it may inhabit `Prop`, has exactly one constructor, and every non-parameter
   constructor field whose type does not inhabit `Prop` is itself an **exact
   argument** of the constructor result application.

The exact-argument condition deliberately does not accept a field merely
because it occurs beneath an index expression. `I (f n)` does not expose `n`
unless `f` is known injective, and the kernel does not assume that fact.

For every other potentially-`Prop` family, keep the inductive and constructors
but generate a recursor whose motive codomain is fixed at `Sort 0`. Such a
recursor exposes only the inductive's own universe parameters; it does not mint
the fresh leading elimination parameter. Consequently `Or` and `Exists` retain
ordinary elimination into propositions while data extraction is ill-typed.

Use `level_is_nonzero`, not a literal-level check, for the result universe.
Infer every constructor field's domain sort in its opened local context and use
`level_is_zero` to recognize proof fields. Preserve the existing generated-type
self-check and declaration rollback behavior.

Pin the external compatibility gate to Lean 4.30.0. CI must run a dedicated
test with `AXEYUM_REQUIRE_LEAN=1`; absence of the binary is a failure there. The
test renders `True` and a two-constructor `Two : Prop` as real Lean `inductive`
commands, applies Lean's regenerated restricted `Two.rec`, and requires its
iota rule to type-check the final equality proof.

## Evidence

Implementation commit `d26ad887` applies the criterion and activates the former
exploit as a negative regression. Commit `a10c8cde` adds the pinned mandatory
real-Lean CI job.

Focused evidence:

- `cargo test -p axeyum-lean-kernel --all-features`: 177 unit tests, four active
  integration tests, and doctests pass; the former exploit's complete term
  fails inference and the trusted declaration gate rejects it.
- The generated boundary matrix varies zero through three constructors and
  zero through two proof/data fields, checking the expected recursor universe
  profile for every cell.
- Positive metadata gates retain a fresh elimination universe for `False`,
  `True`, `And`, `Iff`, `Eq`, an index-exposed data field, and a direct-recursive
  proof-field accessibility backbone. `Or`, `Exists`, a hidden data witness,
  a nested-only index occurrence, and a potentially-Prop multi-constructor
  universe-polymorphic family are restricted.
- The same test fixtures that intend computational polymorphic datatypes now
  declare provably nonzero result universes (`Sort (u+1)`), exposing rather than
  masking the distinction between a datatype and a sort-polymorphic family.
- `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings`
  passes.
- With the pinned executable,
  `AXEYUM_REQUIRE_LEAN=1 AXEYUM_LEAN_BIN=<lean-4.30.0>/bin/lean cargo test -p
  axeyum-lean-kernel --test real_lean_inductive_crosscheck -- --nocapture`
  passes. The emitted module contains real `inductive True`/`inductive Two`
  commands, `@Two.rec`, no recursor axiom, and no `sorryAx`.

The implementation was checked directly against the corresponding primary
reference code in `references/lean4/src/kernel/inductive.cpp` and the independent
Rust port in `references/nanoda_lib/src/inductive.rs`.

## Alternatives

Disabling proof irrelevance was rejected: it is an intentional Lean semantic
and would avoid the symptom by changing the theory. Rejecting all
multi-constructor propositions was rejected because `Or` is perfectly valid;
only its elimination universe is restricted. Restricting every proposition to
`Prop` was rejected because it breaks valid `False`/singleton elimination and
the `Eq` transport routes used by reconstruction. Treating any syntactic
occurrence beneath an index as exposed was rejected as unsound. Testing only
the old exploit was rejected because it would leave constructor-count, hidden
field, exact-index, and universe-polymorphic boundaries unguarded.

Keeping the real-Lean check optional in all environments was rejected because
that recreates the skip-as-success failure mode. Requiring Lean for every local
Rust test was also rejected: the dedicated CI job is mandatory, while local
development gets a visible skip unless it opts into the same strict flag.

## Consequences

The historical derivation of `False` is contained, and the P3.6/P3.7
kernel-backed assurance lane may resume subject to the ordinary full-workspace
gates. Restricted recursors have a deliberate public representation change:
callers must no longer supply a nonexistent motive-universe argument to
`Or.rec`/`Exists.rec`-shaped declarations.

The full Lean `Acc` declaration is not yet admitted by this kernel because
recursive indexed inductives remain explicitly deferred. The large-elimination
criterion itself is covered by a direct-recursive proof-field `AccLike`
backbone; when recursive indexed families land, `Acc` must pass the same
positive profile before that capability is accepted.

The dedicated external gate proves the flat-inductive path is non-vacuous. The
broader solver reconstruction harness still permits a visible local skip, and
the exporter still falls back to axioms for parametric/indexed inductives. Those
are explicit remaining assurance-width tasks, not reasons to weaken this
soundness boundary.
