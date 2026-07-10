# ADR-0079: Finite Scalar Array Admission

Status: accepted
Date: 2026-07-10

## Context

The canonical array route introduced by ADR-0071 through ADR-0078 used only
the exact scalar `BvTheory`, generic array projection, and evaluator replay, but
its admission gate required both array components to be bit-vectors. That gate
excluded `Bool` indices and elements even though all downstream mechanisms
already represent and check them. The exclusion left two measured public rows
on fallback paths, including QF_ABV `issue5925`, an UNSAT store/select formula
over `(Array Bool Bool)`.

This refines the answered array-rollout question in the
[research register](../08-planning/research-questions.md) without adding an IR
operator or changing array semantics. The broader structural-parent, warm-model,
and proof work remains in P2.2.

## Decision

The canonical ABV/AUFBV `CdclT` route admits arrays whose index and element are
each `Bool` or `BitVec`; every other component sort remains outside this route.

Feature discovery keeps two distinct facts:

- `has_non_bv_array` preserves legacy fallback routing for every array that is
  not BV-indexed and BV-valued.
- `has_non_bool_bv_array` gates only the canonical route and rejects `Int`,
  `Real`, uninterpreted, datatype, and floating-point components.

The Bool-only UF+array fragment may enter canonical AUFBV even when no bit-vector
term appears. SAT still requires function-then-array projection and evaluation
of every original assertion. Non-BV/BV arrays use `GenericArrayValue`; no new
model representation is introduced.

## Evidence

- The exact public QF_ABV `issue5925` row changes from `unknown` to `unsat` on
  `abv-online-cdclt` in 18-20 ms. Its contradiction is checked through the same
  canonical relaxation/lemma discipline as BV arrays.
- Public QF_AUFBV `issue4240`, `(Array BV8 Bool)`, changes from `unknown` to a
  replay-checked `sat` in about 5 ms. `issue5743`, `(Array BV1 Bool)`, remains a
  replay-checked `sat` and now decides canonically in under 1 ms.
- A direct four-shape gate covers Bool->Bool, Bool->BV3, BV3->Bool, and BV3->BV3
  model projection and original-term replay. An Int->Bool negative control is
  rejected by canonical admission.
- The expanded 128-seed, 12-shape matrix performs 384 new comparisons: direct
  online and front-door verdicts against an analytic oracle, plus direct online
  against Z3. Together with the existing 768 BV-array comparisons, all 1,152
  comparisons are clean. SAT models replay; `DISAGREE=0`.
- All 797 solver library tests, 12 route-trace tests, strict clippy, and rustdoc
  with warnings denied pass.
- The current host was under sustained disk I/O load during the exact 1-second
  corpus reruns. The artifacts remain sound (`DISAGREE=0`, replay failures=0)
  but aggregate counts fell to QF_ABV 186/193 and QF_AUFBV 48/53 because four
  previously decided boundary rows timed out. Artifact-to-artifact comparison
  isolates the two intended logical gains above; a low-load aggregate remeasure
  remains required before replacing ADR-0078's 187/193 and 49/53 baseline.

## Alternatives

- **Keep BV/BV-only admission.** Rejected because it duplicates no semantic or
  representation boundary and leaves measured finite-domain rows undecided.
- **Admit every `ArraySortKey`.** Rejected because exact scalar theory, model
  lifting, and replay support have not been established for all component
  theories on this route.
- **Add a separate Bool-array solver.** Rejected because Bool is already an
  exact scalar in the shared theory and generic model machinery; another route
  would duplicate the array protocol.

## Consequences

Finite scalar arrays now mean Bool/BitVec components throughout canonical
admission, while fallback routing remains unchanged. The route gains two public
decisions and a mixed-component differential belt without widening trust.

This is a measured-leaf breadth increment, not the next structural-array
keystone. Work resumes on store/ITE/default/ROW parent events with dynamic
in-search insertion, non-symbol and warm class models, full proof logging, and a
low-load public aggregate remeasure.
