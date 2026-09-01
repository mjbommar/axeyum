# Lane: abstraction-mechanism — can a statement quantify over a *structure*?

<!-- plan-section: lane-status -->

**WIP, 2026-09-01.** Driver:
[`2026-09-01-the-abstraction-question-has-never-been-asked.md`](../../research/11-design-review/2026-09-01-the-abstraction-question-has-never-been-asked.md)
and `docs/curriculum/foundational-books/axler.md`, which tags roughly half of
Axler's chapters `X-TA` — unavailable because the statement cannot be *written*,
not because it is hard to prove.

**First measurement, before any probe compiles.** The kernel already admits
dependent records with proof fields and universe-polymorphic type parameters:

- `Rat` (`int_prelude/rat.rs:106`) is a one-constructor inductive in `Type 1`
  whose constructor carries **two data fields and two proof fields**
  (`1 ≤ den`, `gcd (natAbs num) den = 1`). That is a structure with laws.
- `Complex` (`complex.rs:3996`) is a one-constructor inductive in `Type 0` with
  projections taken by large elimination.
- `Exists.{u}` and `Acc.{u}` (`prelude.rs:1307`, `:1384`) are
  universe-polymorphic inductives taking a `Sort u` **parameter**.

So the pieces of a bundled structure exist. What is untested is a carrier as a
**field** rather than a parameter — a bundle living one universe up — and
whether `add_declaration` will take `∀ (F : Field), <law>`. That is the probe.

ADR number taken: **1495**.

<!-- plan-section: landed-changes -->
