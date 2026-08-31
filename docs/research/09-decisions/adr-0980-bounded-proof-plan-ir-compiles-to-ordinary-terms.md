# ADR-0980: A bounded proof-plan IR, compiled to ordinary kernel terms

Status: accepted
Date: 2026-08-31

## Context

L3 phase D5 (`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`)
asks for a small inspectable proof-plan representation above raw `ExprId`
construction — apply, exact, rewrite, symmetry, transitivity, constructor,
eliminate, induction, witness, and checked computation — compiled to
ordinary kernel terms, with the explicit constraint: **do not teach the
kernel the plan language**.

Three `nat_prelude` files (`dvd_add_iff_left.rs`, `gcd_dvd_mirrors.rs`,
`gcd_mul_right_mirrors.rs`) each carried a hand-copied local pair —
`pred_iff_of_eq` (lift an `Eq` proof through a one-hole `Prop`-valued
context into an `Iff`) and `iff_trans`/`iff_symm` — the same construction,
duplicated by convention rather than shared (see those files' now-updated
module docs, and `mod_mul_lemmas.rs`'s doc, which used to describe the
convention).

## Decision

Add `crates/axeyum-lean-kernel/src/proof_plan.rs`: a `Plan` enum with
exactly the ten node shapes the phase names (`Exact`, `Apply`, `Rewrite`,
`Symmetry`, `Transitivity`, `Constructor`, `Transport`, `Eliminate`,
`Induction`, `Witness`, `Compute` — `Transport` is the bare `Eq.rec`
eliminator `Rewrite`/`Symmetry` are both expressible as, kept as a separate
node because some call sites need an arbitrary base case rather than a
self-evident one), a `Template` type for the one shared "motive"
representation every node that needs one uses, and a `compile` function
that walks a `Plan` and calls the same public `NatOps` builder methods
(`congr`, `trans`, `symm`, `transport`, `const_app`, …) every hand-written
`declare_*` function in this crate already calls.

Three convenience wrappers (`iff_lift`, `iff_chain`, `iff_flip`) restore a
one-line call at the overwhelmingly common use site — the `pred_iff_of_eq`/
`iff_trans`/`iff_symm` shape — while still routing through `compile` and the
same `Plan` nodes underneath.

`theorem_plan` is the `Plan`-based sibling of the existing
`NatOps::try_theorem`: it compiles the plan, then — unlike `try_theorem`,
which trusts `add_declaration` to catch a leaked free variable as an opaque
`KernelError::UnboundFVar { id }` — checks the fully-bound type and value
with `Kernel::has_fvars` and declines with a named
`PlanError::UnboundFreeVariable { site }` before the kernel is ever asked.
This is the concrete instance of "a plan language that gets binder scope
right automatically is a large part of the value" the phase brief names.

## What is compiled and which side of the TCB it is on

This is the same argument ADR-0965 (the D1 declarative declaration spec
pilot) makes, carried from *definitions with no proof body* to *proof terms
re-checked end to end*, because the two phases sit on the same trust
boundary from different sides:

`compile` produces an ordinary `ExprId` proof term via the SAME builder
methods a hand-written `declare_*` function calls — it does not add a `Plan`
variant to `crate::env::Declaration`, does not skip
`Kernel::add_declaration`'s own check, and does not special-case anything at
admission time based on how a term was built. The kernel's type-checker
re-derives the proof from scratch either way and has no notion of "plan" at
all. So a bug in a `Plan` value or in `compile` produces one of two things,
exactly as a bug in hand-written Rust would: a kernel REJECTION (the
`KernelError` the caller already has to handle), or a proof of the WRONG
STATEMENT (caught the same way any wrong hand-built proof is — the statement
just does not say what the caller intended). It cannot produce a false
theorem past the trusted gate, because nothing about how a term was
assembled changes what `add_declaration` checks it against.

Concretely, for the three rewritten families:
`crates/axeyum-lean-kernel/examples/proof_plan_digest_probe.rs` renders each
affected theorem's admitted type and value through `Kernel::render_lean` and
hashes the pair with SHA-256. Run against this working tree and against a
`scripts/lane-snapshot.sh HEAD` build of the pre-refactor commit, the digest
for all six affected theorems (`dvd_add_iff_left`, `dvd_mod_iff_gen`,
`dvd_iff_mod_eq_zero`, `dvd_gcd_mul_iff_dvd_mul`, `dvd_mul_gcd_iff_dvd_mul`,
`dvd_gcd_mul_gcd_iff_dvd_mul`) is byte-identical, and `axiom_footprint` is 0
in both — the ADR-0965 pilot's "identical declaration identity/order/type/
value digests" bar, met here for proof terms rather than a `Definition`'s
value.

## Consequences

- Three files became shorter without changing theorem identity or
  footprint: `dvd_add_iff_left.rs` 116 → 71 lines, `gcd_dvd_mirrors.rs`
  476 → 423 lines, `gcd_mul_right_mirrors.rs` 273 → 217 lines — by deleting
  the duplicated local `pred_iff_of_eq`/`iff_trans`/`iff_symm` and replacing
  each call site with a one-line `proof_plan::iff_lift`/`iff_chain`/
  `iff_flip` call.
- Malformed plans decline with a typed `PlanError` before the kernel is
  asked: an empty `Transitivity` chain, an `Eliminate` with zero cases, a
  `Compute` step whose two sides are not defeq (checked against
  `Kernel::def_eq` before any term is built), and a leaked free variable in
  either the final theorem type or value (checked with `Kernel::has_fvars`).
  All five are mutation-verified in `proof_plan::tests` — each guard
  deleted, exactly one test observed to die, then reverted — see
  `docs/plan/status/l3-d5-proof-plan-ir.md` for the kill table.
- Unlike ADR-0965's pilot, this phase needed no `gen-proof-plan.py`
  code-generation counterpart: a `Plan` value is built directly in the Rust
  `declare_*` functions that use it (an ordinary Rust value, not a wire
  format read from `artifacts/proof-plan/`), so `scripts/check-proof-plan.py`
  is a check-only gate.
- `Template` is deliberately narrow: a named constant applied to fixed
  arguments with the hole variable repeated at zero or more positions, plus
  a dedicated `EqNat` shape for `Eq`'s universe-polymorphic level argument
  (which the generic `App` shape cannot carry, since `NatOps::const_app` is
  restricted to universe-monomorphic constants). A dependent motive over a
  compound scrutinee is out of scope, same as ADR-0965's interpreter DSL.
- This does not touch `int_prelude/`, `nat_prelude/bitwise.rs`, or any
  `nthRoot`/quadratic-residue file a sibling lane owns this session; the new
  Rust lives in one new top-level module (`proof_plan.rs`), one new example,
  and edits to exactly the three files it shortens.
