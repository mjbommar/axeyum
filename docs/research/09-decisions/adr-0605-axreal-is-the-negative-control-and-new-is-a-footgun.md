# ADR-0605: `axreal` is retained as the negative control, and `LraReconstructCtx::new` is a footgun

Status: accepted
Date: 2026-08-27
Index-summary: The 30-axiom AxReal package is kept deliberately — it is the negative control axiom-freedom is measured against and the instantiation that proves the ring-interface generalization is real — but the default reconstruction constructor still selects it, so a caller reaching for the obvious name silently inherits 30 axioms.
Index-status: accepted

## Context

The 2026-08-27 architecture review flagged `axreal` (30 axioms,
`originated = 0`) as a decision being made **by default**: neither deliberately
retained as the negative control nor deliberately deleted as dead weight.
Investigating it produced a second, sharper finding.

Measured on this tree:

- `axreal: theorems=32 axiom_free=32 axiom_bearing=0 originated=0`.
- `AxReal` is referenced from solver reconstruction
  (`reconstruct/arithmetic/{ordered_ring,signature}.rs`), which at first reading
  contradicts CLAUDE.md's "no shipped route reaches them".
- It does not, and the reason is the design: `ordered_ring.rs` generalizes a
  refutation over an **abstract ordered-ring interface** so the conclusion stops
  being a statement *about* `AxReal`; consumers then instantiate. Three
  instantiations exist in `reconstruct/arithmetic.rs`:
  `RingSignature::from(arith)` (the **AxReal** package),
  `RingSignature::from(int)`, and `RingSignature::from(creal)`.
- `tests/farkas_over_the_integers.rs` asserts
  `at_int.axiom_footprint.is_empty()` — the integer instantiation is
  axiom-free, and that is the shipped shape.
- `ordered_ring.rs:794` records the migration: *"Until 2026-08-18 this route
  built `LraReconstructCtx::new`"* — i.e. the routes were moved OFF the
  AxReal instance deliberately.

## Decision

1. **`axreal` is RETAINED, deliberately.** It is not dead weight. It plays two
   load-bearing roles: (a) the negative control every axiom-freedom
   measurement is read against — ADR-0515's role, and the reason "0 axioms" is
   a claim rather than a tautology; and (b) the instantiation that demonstrates
   the ring-interface generalization is genuine rather than cosmetic, since a
   generalization no one could instantiate at an axiomatized package would
   prove nothing. **30 is the floor for an axiomatized ordered field** (an
   opaque carrier makes every operation and law an assumption), so the number
   is a property of the construction, not a dial.
2. **The headline claim stands, with its mechanism stated precisely.** Shipped
   reconstruction routes instantiate at CONSTRUCTED carriers (`int`, `creal`)
   and are asserted axiom-free by test. "Declared but not reached" is accurate;
   "not present" would not be.
3. **`LraReconstructCtx::new` selecting the AxReal signature is a hazard and is
   to be fixed.** A caller reaching for the obvious constructor name silently
   inherits 30 axioms, in exactly the direction that would corrupt this
   project's headline metric. The obvious name must not be the axiom-bearing
   one. Acceptable remedies, in order of preference: rename the AxReal
   constructor so the choice is explicit at every call site; and/or add a guard
   test asserting that no shipped (non-test) call site uses the AxReal
   signature. **A guard alone is weaker than a rename** — it catches
   regressions but leaves the trap loaded for a reader.

## Consequences

- The `axreal` prelude and its 30 axioms stay, and the generated Lean axiom
  ledger keeps reporting them as the one nonzero row. That row is now
  documented as intentional.
- One code change is owed (item 3). Until it lands, the safety of the headline
  metric rests on every caller happening to choose the right constructor —
  which is a convention, not a guarantee, and conventions have failed in this
  repository before.
- The review's §4 item "axreal's role" is closed; the other two (ADR-0603's
  family beyond IVT/EVT, suite wall-clock) remain open.

## Amendment (2026-08-27, lane axreal-rename): item 3 landed

`6bdb1e35f` renamed `LraReconstructCtx::new`/`::try_new` to
`new_over_axreal`/`try_new_over_axreal` (matching the existing
`try_new_over_integers`/`try_new_over_constructed_reals` convention) and
**removed** the `Default` impl rather than repointing it at a constructed
carrier — a silently-changed default is its own hazard, and this ADR already
ranked a rename above a guard alone. There is now no no-argument constructor
on `LraReconstructCtx` at all; every caller names its carrier explicitly.
Both remedies landed together: `reconstruct::arithmetic::axreal_call_site_guard`
(three tests — a positive control, a negative control, and the real gate over
`src/reconstruct/`'s on-disk tree) asserts no shipped call site can pick the
AxReal signature again, proved discriminating by temporarily reintroducing
such a call and confirming exactly that gate went red. `axreal`'s 30
declarations are untouched. Full account:
[`docs/plan/status/140-axreal-constructor-rename.md`](../../plan/status/140-axreal-constructor-rename.md).
