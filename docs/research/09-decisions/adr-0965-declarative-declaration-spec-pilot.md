# ADR-0965: A declarative declaration specification, piloted on one subsystem

Status: accepted
Date: 2026-08-31

## Context

L3 phase D1 (`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`)
asks for a versioned typed specification for names, universes, binders,
definitions, equations, public theorem signatures, dependencies, and build
phase — generating repetitive Rust accessors, Python types, Lean rendering
metadata, inventory registration, and basic equation/mutation tests, piloted
on one newly added small subsystem rather than a rewrite of the whole
library.

The measured problem is `creal.rs`: 441 fields, 364 linear `declare_*`
calls, one file fusing a name registry, a field struct, build ORDER, and
dispatch (2026-08-27 architecture review). The same fusion pattern (struct
field + `name_str` interning call + `declare_*_all` dispatch call, three
places, one hand-maintained) is present in every prelude file, including
the much smaller `nat_prelude.rs`.

## Decision

Pilot the spec on `Nat.squarefreeAux` / `Squarefree`
(`crates/axeyum-lean-kernel/src/nat_prelude/squarefree.rs`, landed
2026-08-30, two `Definition`s, zero theorems) — the smallest available real
subsystem, chosen specifically because a pure-`Bool`-valued definition has
no proof body, so a spec-driven generator for it cannot smuggle proof
content past the kernel: the kernel's type-checker is still the sole
admission gate for both the hand-written and the generated declaration.

Concretely:

- `artifacts/declaration-spec/schema.json` — the versioned schema for a
  declaration-spec file (names, binders, universes, an expression DSL for
  types/values, dependencies, build phase, equations).
- `artifacts/declaration-spec/nat-squarefree.json` — the pilot spec,
  describing the same two declarations `squarefree.rs` builds by hand.
- `crates/axeyum-lean-kernel/examples/declaration_spec_pilot.rs` — a
  generic interpreter (not per-declaration codegen) that walks the spec's
  expression trees and calls the same public `NatOps` builder methods
  `squarefree.rs` calls by hand, declaring the result under shadow names in
  the SAME kernel instance as the hand-built prelude, then compares the
  resulting `ExprId`s directly (this kernel hash-conses expressions, so
  structurally identical terms intern to the identical `ExprId`) and a
  SHA-256 digest of each declaration's rendered type/value as a
  portable secondary check.
- `scripts/gen-declaration-spec.py` — validates every spec (duplicate
  names within the spec corpus AND against a snapshotted full kernel name
  inventory, missing/invalid build phase, dependency cycles) and emits
  generated Python types and a generated Rust name/equation table that the
  example `include!`s and actually compiles against, so "generated" is not
  decorative.
- `scripts/check-declaration-spec.py` — the pre-merge gate: runs the
  generator's guards over the pilot spec and three adversarial negative
  fixtures (a cross-prelude duplicate name reproducing the real
  `Nat.inverseIndex` collision, a missing build phase, a dependency cycle),
  then runs the Rust comparison and requires a affirmative digest-match
  marker in its output. Fails on an empty spec corpus, a skipped
  comparison, or zero declarations checked.

## What is generated and which side of the TCB it is on

Everything the generator emits is registration boilerplate: name strings,
phase numbers, a Python mirror of the same data, and a Rust constant table
of (namespace, local name, kind) triples plus (input, output) equation
pairs. None of it is a proof term. The interpreter that turns a spec's
expression DSL into `ExprId`s is hand-written, generic, reusable
infrastructure — the same status as `NatOps`'s existing builder methods it
calls — and it produces a `Definition`, which has no proof body: the kernel
accepts a `Definition` once its value type-checks against its stated type,
which is true of any total function of the right type, well-typed or not
"correct" (see this crate's CLAUDE.md: "the trusted gate cannot tell you a
`Definition` is wrong"). So a bug in either the spec or the interpreter
produces a kernel REJECTION or a wrong VALUE, exactly as a bug in
hand-written Rust would — it cannot produce a false theorem, because there
is no theorem here. The pilot is deliberately scoped to a subsystem with
this property; a future pilot on a *theorem*-bearing subsystem would need a
different argument, most likely: the spec may describe a theorem's public
*signature* (for accessor/inventory generation) but never its proof term,
which must stay hand-written Rust reviewed and checked exactly as today.

## Consequences

- Adding a new pure-definition subsystem this shape covers becomes a spec
  file plus zero new Rust, instead of three separate hand-maintained
  surfaces (struct field, name interning line, dispatch call) — see
  `docs/plan/status/l3-d1-declaration-spec.md` for the measured reduction
  on the pilot.
- The interpreter's expression DSL is deliberately narrow (covers exactly
  what the pilot subsystem needs: arrow types, non-dependent lambdas,
  `Nat.rec` with a non-dependent motive, and the primitive `NatOps`
  arithmetic/boolean operations). Extending it to cover induction with a
  dependent motive, existentials, or other prelude carriers is future work
  and is NOT claimed here.
- This does not touch `nat_prelude.rs`, `int_prelude.rs`, or any file a
  sibling theorem-proving lane owns; the pilot's Rust lives entirely in a
  new example binary plus a new dev-dependency (`serde_json`, already used
  elsewhere in the workspace) in `axeyum-lean-kernel/Cargo.toml`.
