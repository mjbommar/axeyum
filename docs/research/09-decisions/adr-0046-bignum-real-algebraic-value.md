# ADR-0046: Bignum `Value::RealAlgebraic` — unconditional arbitrary-precision storage

Status: accepted
Date: 2026-06-21

## Context

[ADR-0044](adr-0044-algebraic-field-arithmetic.md) gave `RealAlgebraic` exact
field arithmetic and [ADR-0045](adr-0045-bignum-algebraic-path.md) added a
**feature-gated bignum *retry*** for the intermediate resultant/Sturm
computation — but the stored representation stayed `poly: Vec<i128>` + `i128`
`Rational` interval, so a combination whose *final* minimal polynomial exceeds
`i128` still declined (ADR-0045 named the full fix a deferred slice). That
ceiling is the live limiter on the multivariate engine: the algebraic-grid lift
([commit `d3f8cfe`](adr-0044-algebraic-field-arithmetic.md)) decides
all-equality 2-variable coupled systems, but `x²+y²=4 ∧ x·y=1` — whose
coordinates are the degree-4 nested radicals `±√(2±√3)` — stays a sound
`Unknown` because the grid's `(α,β)` pair test combines degree-4 algebraic
numbers into intermediate min-polynomials that overflow `i128` *storage* (not the
eval-interpolation determinant, which is now polynomial-time after commit
`3333c2a`). Removing the storage ceiling is what turns these declines into
decisions.

## Decision

Change `Value::RealAlgebraic` to **native arbitrary precision** — `poly:
Vec<BigInt>`, `lo: BigRational`, `hi: BigRational` — and make `num-bigint` /
`num-rational` **unconditional** dependencies of `axeyum-ir`, removing the
`bignum` feature gate introduced in ADR-0045.

### Why unconditional (amending ADR-0045's gate)

`Value` is the always-compiled core IR enum; a feature-conditional coefficient
type would force `#[cfg]` into every `RealAlgebraic` method and match arm — far
worse than one always-present dependency. `num-bigint`/`num-rational` are **pure
Rust** (MIT/Apache, `cargo deny`-clean), so they satisfy the project's actual
hard rule — *no C/C++ in the default build* — which never forbade pure-Rust
dependencies. ADR-0045's feature gate was a minimalism preference for non-NRA
embedders; a clean core representation outweighs it. This is `axeyum-ir`'s first
unconditional dependency, and it is a deliberate, recorded choice.

### What collapses (a simplification, not just a widening)

The ADR-0044/0045 **i128-fast-path + bignum-retry** split disappears: field
arithmetic (`add`/`mul`/`neg`/`sub`) now computes directly in `BigRational` via
the `poly_big.rs` primitives, which become *the* algebraic primitives. No
overflow decline on the algebraic path; fewer code paths; the headline coupled
systems decide. The core `i128` `Rational` (used pervasively in LRA, models,
evaluation) is **untouched** — only `RealAlgebraic`, which appears solely in NRA
witnesses (rare), pays the bignum cost.

### Soundness — a representation change, never a logic change

The one-root-in-`(lo,hi)` invariant is still established by `new`/`new_big` (the
strict opposite-nonzero-sign-change check, now via `big_sign`), and every Sat
still replay-checks while every Unsat route keeps its exhaustiveness gate.
Widening the number type can only convert a precision-induced `Unknown` into a
decision — it can **never flip a verdict**. The guarantee is enforced
mechanically: every pre-existing test must pass unchanged (i128-constructed
algebraics behave bit-identically), and the verdict diff must show *only*
`Unknown → {Sat, Unsat}` upgrades, no `sat ↔ unsat` flip.

### Compatibility

`new(Vec<i128>, Rational, Rational)` stays as a convenience that lifts to bignum
(so the solver's i128 root-isolation call sites are unchanged); `new_big` is the
native bignum constructor. `defining_poly()` returns `&[BigInt]`; a
`defining_poly_i128() -> Option<Vec<i128>>` lets the solver's i128 NRA paths
convert-or-decline gracefully.

## Evidence

- `x²+y²=4 ∧ x·y=1` now decides **Sat** with the `√(2±√3)` witnesses, replayed
  by independent `eval` of both original assertions (the test
  `multi_coupled_algebraic_x_declines_not_unsat` flips from a `!Unsat` decline to
  an asserted Sat + replay).
- The regression wall: `axeyum-ir`, `axeyum-solver`, `axeyum-rewrite` suites pass
  unchanged (`√2`, `√3`, `√2+√3 = x⁴−10x²+1`, `√2·√3 = √6`, the grid SAT/UNSAT
  cases, the differential determinant tests), with a verdict diff showing no
  `sat ↔ unsat` flip. `cargo deny` confirms the now-unconditional num crates.

## Alternatives

- **Keep the feature gate, make the coefficient type `cfg`-conditional.**
  Rejected: `#[cfg]` in every method/match arm of a core enum is unmaintainable
  and error-prone; one unconditional pure-Rust dep is cleaner.
- **Keep i128 storage, decline on final overflow (status quo).** Rejected: it is
  exactly the ceiling blocking the multivariate engine's headline cases.
- **Make the core `Rational` bignum too.** Rejected (as in ADR-0045): it is on
  the LRA/model hot path; arbitrary precision there is an unwarranted slowdown.
  Only `RealAlgebraic` widens.

## Consequences

- Easier: higher-degree algebraic witnesses and combinations decide; the grid
  lift and future ≥3-variable projection are no longer storage-bounded; the
  algebraic code path is simpler (one precision, no retry).
- Structural: `axeyum-ir` gains its first unconditional dependency (pure Rust,
  scoped in effect to the rare `RealAlgebraic` value); ADR-0045's `bignum`
  feature is removed.
- Bounded: algebraic operations remain degree/round-capped → graceful `unknown`,
  never OOM; the solver's i128 NRA sub-paths convert-or-decline on a
  too-large `defining_poly`.
