# CAD parameterization gate

Status: N1a/N1b accepted; N1c remains staged
Date: 2026-07-20
Baseline: Axeyum `12f85d19`

## Decision

The repetition in `nra_real_root.rs` is real, but it is not one triplicated
algorithm. Parameterize only the rational mechanics whose inputs, visit order,
decline points, and outputs are already identical. Keep strict open-cell
coverage, non-strict rational-section coverage, and algebraic value-domain
lifting as explicit policies or separate implementations.

The first authorized implementation slice, **N1a**, is deliberately small:

1. replace the duplicated rational substitution-and-univariate-decision bodies
   in `decide_strict_cell` and `decide_nonstrict_cell` with one private helper;
2. retain the two named wrappers, comparator flow, `Option` decline behavior,
   `CellOutcome`, and first-witness ordering; and
3. make no projection, sampling, budget, timeout, algebraic, or public-API
   change in the same checkpoint.

This is an implement decision for N1a, not authorization for a generic CAD
engine. The later candidates below require their own checkpoint and the same
gate. Algebraic traversal is explicitly deferred.

## Measured census

The baseline file is 7,544 lines / 333,529 bytes. The relevant physical ranges
are a map of review cost, not a claim that every line is mechanically
duplicated.

| Lane | Baseline range | Approximate size | What is shared or distinct |
|---|---:|---:|---|
| strict two-variable setup | 2,894--2,933 | 40 lines | coprime split and two deterministic axis orientations |
| strict two-variable projection/lift | 2,934--3,061 | 128 lines | projection and root preparation repeat the non-strict path; open cells only |
| strict rational cell decision | 3,074--3,205 | 132 lines | same substitution/constant/univariate mechanism as the rational non-strict cell |
| non-strict two-variable setup | 3,206--3,246 | 41 lines | same setup shape, but different comparator precondition |
| non-strict two-variable projection/lift | 3,247--3,385 | 139 lines | same projection mechanics; visits open cells and every critical section |
| non-strict rational cell decision | 3,386--3,468 | 83 lines | same rational mechanism as the strict cell |
| algebraic two-variable section | 3,469--3,565 | 97 lines | exact algebraic field evaluation and resultant-derived fiber boundaries; distinct |
| strict rational N-variable visitor | 3,737--3,829 | 93 lines | open rational cells only |
| shared N-variable projection | 3,848--4,304 | 457 lines | already shared as `project_strict`; the name is historical |
| strict N-variable front door | 4,305--4,401 | 97 lines | rational witness loop over the open-cell visitor |
| non-strict rational N-variable visitor | 4,426--4,516 | 91 lines | open cells plus rational sections; algebraic critical values decline |
| non-strict rational N-variable front door | 4,517--4,600 | 84 lines | rational witness loop over the all-cell visitor |
| non-strict algebraic N-variable front door | 4,601--4,660 | 60 lines | mixed `Value` witness loop; does not use the rational lane's top-level coprime split |
| algebraic value-domain traversal | 4,661--4,877 | 217 lines | resultant-derived fibers, root coarsening, and rational/algebraic coordinates |

The census yields three increasingly risky opportunities:

- **N1a, authorized:** share rational cell substitution and univariate
  decision. This removes exact operational duplication without abstracting
  coverage.
- **N1b, candidate:** share two-variable projection/root preparation behind a
  private result type. The strict caller's current entry deadline poll and the
  non-strict caller's current polling behavior must remain byte-for-byte in
  control-flow position; sampling stays in the wrappers.
- **N1c, candidate:** parameterize the two rational N-variable visitors with an
  explicit `CellSelection::{OpenOnly, OpenAndRationalSections}` policy. Budget
  charges, variable order, nullification declines, and sample order must remain
  visible in the policy, not hidden in callbacks.

Do not fold `visit_all_cells_value` into N1c. It carries `Value` rather than
`Rational`, derives fiber boundaries against algebraic minimal polynomials,
coarsens algebraic roots, and has different top-level polynomial preparation.
Those are semantic differences, not incidental duplication.

## Invariants the refactor must preserve

1. **Cell coverage.** Strict conjunctions are exhaustive over open cells.
   Mixed/non-strict conjunctions additionally require every critical zero-cell.
2. **Algebraic decline and fallback.** The rational N-variable lane declines on
   the first algebraic critical value. Only the algebraic fallback may decide
   that section. A decline must never become `Unsat`.
3. **Witness domain and replay.** Rational lanes produce rational coordinates;
   algebraic lanes may produce exact algebraic coordinates. Every `Sat` still
   reaches the existing replay against the original assertions.
4. **Deterministic first witness.** Preserve BTree variable order, the two-axis
   orientation order, open-cell-before-section order, root ordering, and the
   first `Sat` returned. Verdict parity alone is insufficient because model
   choice is observable.
5. **Completeness guards.** Preserve nullification, vanished resultant or
   discriminant, isolation, overflow, field-sign, and cell-cap declines.
6. **Budget accounting.** Keep every `CellBudget::charge` at the same visit
   boundary. Moving a charge changes which cells fit under the cap.
7. **Deadline behavior.** `decide_real_poly_constraint` scopes a thread-local
   deadline and isolation/projection paths poll it. Do not add, remove, or move
   polls in N1a. The strict two-variable entry currently has an explicit poll;
   the non-strict entry does not, an asymmetry N1b must preserve unless a
   separate behavior-change ADR authorizes otherwise.
8. **Polynomial preparation.** Rational front doors use `coprime_split`; the
   algebraic N-variable fallback currently de-duplicates original polynomials
   without that top-level split. Do not normalize this difference inside a
   structural refactor.

## Preregistered acceptance gate

Each implementation slice is accepted only if all applicable layers pass under
the bounded memory profile.

### Exact behavior controls

- Add fixed named fixtures that compare the full `CheckResult`, including model
  values, before and after the slice. Cover strict two-variable, non-strict
  rational-section, strict N-variable, non-strict rational N-variable, and
  algebraic-fallback witnesses. N1a must at minimum cover the first two.
- Keep the existing focused `nra_real_root` fixtures for open quarter-disk,
  non-convex region, disjoint/contradictory strict systems, thin boundaries,
  `Ne`, three-variable strict systems, mixed/non-strict boundaries, algebraic
  critical SAT/UNSAT, and the seed-1117 wrong-`Unsat` regression.
- Require identical verdict and model for the fixed fixtures. An `Unknown`
  remains `Unknown`; it may not be strengthened as part of the refactor.

### Differential controls

- Run `nra_differential_fuzz_disagree_zero` over its fixed 2,000 seeds against
  Z3. Require zero verdict disagreements and zero replay violations.
- Treat the fuzzer's outer four-second worker timeout count as diagnostic, not
  an exact equivalence oracle: wall-clock scheduling can vary. Investigate any
  material regression, but use the fixed fast fixtures for exact classification
  and model parity.
- Preserve direct replay of every returned `Sat`; oracle agreement alone is not
  sufficient.

### Mutation controls

Before accepting the first slice that touches each mechanism, temporarily make
and revert these mutations, recording the named control that fails:

- skip critical zero-cells: a non-strict boundary SAT fixture must fail;
- turn an algebraic-critical decline into `Unsat`: an algebraic SAT fixture must
  fail;
- reverse open-cell/section or axis order: an exact-model fixture must fail; and
- remove a deadline poll: a zero/tiny-deadline control must fail.

N1a does not touch sampling, algebraic fallback, or deadlines, so only the
rational-cell exact-model controls are mandatory for that checkpoint. The other
mutations become mandatory when N1b/N1c reaches the corresponding mechanism.

### Repository gates

- focused NRA integration tests and the 2,000-seed differential fuzzer;
- all current all-feature `axeyum-solver` library tests;
- strict all-target Clippy;
- warning-denied full and minimal-`qfbv` rustdoc;
- formatting and documentation-link checks; and
- kernel OOM audit after the bounded runs.

## Staged trajectory

Proceed with N1a as one add/commit/push checkpoint. Re-measure the file and
review the resulting helper surface before authorizing N1b. N1b may extract
projection/root preparation while leaving strict and non-strict sampling in
separate wrappers. N1c is optional and should proceed only if the explicit cell
policy is easier to audit than the two 90-line visitors. Algebraic
genericization has no current authorization.

## N1a result

N1a landed as the gate specified. One private `decide_rational_cell` owns the
rational substitution, constant folding, residual conversion, and univariate
decision. `decide_strict_cell` and `decide_nonstrict_cell` remain named wrappers;
their callers and every projection, sample, budget, deadline, algebraic, and
replay path are unchanged.

The production file falls from 7,544 lines / 333,529 bytes to 7,521 lines /
332,505 bytes. The modest reduction is the intended result of preserving the
two semantic wrappers and their documentation rather than maximizing line-count
movement.

Two pre/post exact-result controls pin the complete deterministic models:

- strict quarter-disk: `x = 1, y = 1`; and
- non-strict rational boundary: `x = 1, y = 0`.

All 86 focused NRA tests pass. The fixed 2,000-seed Z3 sweep reports 1,807
joint decisions, 1,807 agreements, 1,293 independently replayed SAT models,
zero Z3 skips, and `DISAGREEMENTS: 0`; two outer worker timeouts are diagnostic.
All 891 all-feature solver-library tests, strict all-target Clippy, both
warning-denied rustdoc profiles, formatting of the touched Rust files, link
checks, and the kernel OOM audit pass under the bounded profile.

This evidence accepts N1a only. N1b still needs a pre-change review of the
strict-only entry poll and an exact projection-result seam; it must not become a
sampling refactor. N1c and algebraic genericization remain unauthorized.

## N1b result

N1b also landed within the gate. One private `two_var_critical_roots` helper now
owns the two-variable leading-coefficient/discriminant/resultant projection,
root isolation, exact sort/deduplication, and cell-cap check. It owns no timeout
poll and performs no sampling. `strict_cad_along` retains its explicit entry
poll; `nonstrict_cad_along` retains its previous absence of that caller-level
poll. Both retain their distinct cell enumeration and lifting bodies.

An exact unit control projects `p = y² - x` and `q = y - 1` along `y` and pins
the ordered critical roots to `[0, 1]`. A temporary mutation removing the strict
entry poll makes `strict_two_var_entry_poll_precedes_projection` fail; restoring
the poll makes it pass. The two N1a exact models remain unchanged.

All 86 focused NRA tests pass. The fixed 2,000-seed Z3 sweep reproduces N1a's
entire tally exactly: 1,807 joint decisions and agreements, 191 structural
`Unknown`s, two diagnostic outer timeouts, 1,293 independently replayed SAT
models, 75 algebraic replay declines adjudicated by Z3, zero Z3 skips, and
`DISAGREEMENTS: 0`. All 893 all-feature solver-library tests, strict all-target
Clippy, both warning-denied rustdoc profiles, touched-file formatting, and the
kernel OOM audit pass under the bounded profile.

The file is now 7,485 lines / 330,162 bytes, down 36 lines from N1a and 59 lines
across N1a--N1b. N1c remains optional: parameterizing the two roughly 90-line
rational N-variable visitors is justified only if an explicit cell-selection
policy is easier to audit than the present duplication. Algebraic traversal
remains outside that decision.
