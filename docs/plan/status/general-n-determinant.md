# Lane: general-n-determinant

<!-- plan-section: lane-status -->

**Status:** landed — `Rat.det`, the determinant at general `n`, with symbolic
agreement against `Rat.det2`/`Rat.det3` and four discriminating evaluations.

Target from [ADR-1075](../../research/09-decisions/adr-1075-the-curriculum-graph-measures-scenarios-not-the-kernel.md)
and `docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`:
linear algebra's keystone is the determinant at general `n` (cofactor
recursion over the bound), not the matrix layer, which had already landed.
Decision recorded in
[ADR-1120](../../research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md).

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` — 15 declarations,
every one axiom-free, read from `kernel.environment()`:

| declaration | kind | what it is |
| --- | --- | --- |
| `Rat.matSkip` | definition | `if p <= x then x+1 else x`, the injection `[0,n) -> [0,n+1)` missing `p` |
| `Rat.matMinor` | definition | `A (matSkip i r) (matSkip j c)` — deleting a row and a column as an index reindex |
| `Rat.altSign` | definition | `(-1)^j` by `Nat.rec`, so both equations are `Eq.refl` |
| `Rat.altSign_zero` / `_succ` | theorems | the defining equations |
| `Rat.det` | definition | cofactor expansion along row 0; the `Nat.rec` motive is the FUNCTION type `(Nat -> Nat -> Rat) -> Rat` |
| `Rat.det_zero` / `det_succ` | theorems | the defining equations |
| `Rat.det_one` | theorem | `det A 1 = A 0 0` |
| `Rat.det_eq_det2` | theorem | `forall A, det A 2 = det2 (A 0 0) (A 0 1) (A 1 0) (A 1 1)` |
| `Rat.det_eq_det3` | theorem | `forall A, det A 3 = det3 (A 0 0) ... (A 2 2)` |
| four `*_eval_*` | theorems | discriminating evaluations at concrete matrices |

Facts: `F:rat-det-general-n-eq-det2`, `F:rat-det-general-n-eq-det3`,
`F:rat-det-general-n-evaluates`.

## Verification run in this lane

- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **149 passed, 0
  failed**, 208 s. Prelude build 13.25 s.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `rustfmt --edition 2024 --check` on every touched file — clean.
- `python3 scripts/validate-facts.py` — 2,385 facts, 0 errors.
- `python3 scripts/check-settled-fact-statements.py` — PASS, drifted 0.
- **Mutation-verified**, each restored with `git diff` empty afterwards:
  swapping `matSkip`'s branches makes the build fail at `Rat.det_eq_det2`;
  changing `det_eval_example`'s value 13 -> 12 makes it fail there. Both
  classes of evidence are load-bearing.

## Not proved, and why

Multiplicativity, transpose invariance, expansion along a general row, and
`det matId n = 1` at symbolic `n` all need an induction relating the minor
structure across dimensions. A closed Leibniz form is not merely unproved but
**not expressible** here — it quantifies over permutations of `[0,n)` and this
kernel has no type in which to write that sum. See ADR-1120.

**CORRECTED 2026-08-31 (ADR-1310).** "Not expressible" is wrong. A sum does not
need its index set to exist as a type — it needs a **fold**, and a fold is a
function. `Int.sumMaps` folds over an entire function space by `Nat.rec` with a
higher-order motive (the same device `Rat.det` itself uses), and
`Int.prodRange_sumRange_expand` — the Cauchy–Binet expansion step — is admitted
axiom-free. So a Leibniz-shaped sum is a writable term; what remains unproved is
that it agrees with `Rat.det`, plus general-row expansion, the alternating
property and the sign under a row swap. Three theorems, not a missing type.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `matrix_det.rs` | `Rat.det`, the determinant at GENERAL `n` by cofactor expansion along row 0 — 15 axiom-free declarations. A matrix stays a function plus a bound (no `List`/`Finset`/`Prod` in this kernel) and the minor is an index reindex; the `Nat.rec` motive is the FUNCTION type `(Nat -> Nat -> Rat) -> Rat`, because the recursive call is at the minor rather than the same matrix. Correctness rests on `det_eq_det2`/`det_eq_det3` — agreement with the independently written fixed-arity determinants, SYMBOLICALLY in a universally quantified matrix — plus four discriminating evaluations. Mutation-verified: swapping `matSkip`'s branches is caught by `det_eq_det2`; a wrong stated numeral is caught by the evaluation. `rat_prelude::` 149 passed, 0 failed. ADR-1120. |
