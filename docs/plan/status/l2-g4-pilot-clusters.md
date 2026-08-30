# Lane: l2-g4-pilot-clusters — L2 phase G4, pilot clusters + graph-ranking verdict

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, l2-g4-pilot-clusters, 2026-08-30).**

## Signal check (done before designing any pilot)

Population `mathlib-group-defs-v1` is the ONLY joined population that exists
(`artifacts/declaration-graph/populations/`, `artifacts/graph-join/`,
`artifacts/infrastructure-frontier/` each contain exactly one). Its frontier
(ADR-0845) has 4 language-infrastructure rows, 0 proof-producer rows, 1
theorem-dominator row, 0 dependency-ready-leaf rows — over a population that is
Mathlib's *group-definitions* neighbourhood (`Mathlib.Algebra.Group.Defs` and
friends), not finite collections/big operators and not linear
algebra/polynomials/analysis.

Verdict: **outcome 1 for category 2 (shared producer), a narrowed outcome 1
for category 1 (high-degree missing substrate, using the roadmap's explicit
"or another" clause), and outcome 3 for category 3 (destination bridge).**

- Category 2 has a clean, single, well-evidenced candidate: row
  `IF-LANG-53e5bef137` (generic `congrArg`). Running it as specified.
- Category 1 has no finite-collections/big-operator candidate in this
  population at all, but does have a genuine "another high-degree missing
  substrate": the bundled-structure/typeclass gap behind rows
  `IF-LANG-dce29ad3f7` (Semigroup/mul_assoc), `IF-LANG-4f071ea9a3`
  (CommMagma/mul_comm), `IF-LANG-d629d21781` (IsLeftCancelMul). Running a
  BOUNDED probe of this (see pilot 1 below) rather than the full bundled-
  structure mechanism, which needs new kernel type-theory primitives
  (`Structure`/typeclass — this kernel's complete inductive list is
  `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le` +
  `Nat.Fin` + `Char`; there is no `Prod`, let alone a record/typeclass
  mechanism) and is out of session scope by itself.
- Category 3 (linear algebra/polynomials/analysis bridge): **zero candidates
  in this population**, and building a new population there requires the full
  G0→G3 pipeline (module baseline → declaration graph → join → frontier) over
  a *different* Mathlib subtree, which is out of this lane's edit scope
  (`artifacts/declaration-graph/`, `artifacts/graph-join/`,
  `artifacts/infrastructure-frontier/` are explicitly off-limits) and is not
  "genuinely cheap" — it is a second G0-G3 run. Reported as outcome 3 for this
  category alone: **the ranking cannot yet be evaluated for a
  linear-algebra/polynomial/analysis destination bridge.** What would make it
  evaluable: a second joined population rooted at a Mathlib module actually on
  that path (e.g. `Mathlib.Algebra.Polynomial.Basic` or
  `Mathlib.LinearAlgebra.Basic`), run through G0-G3 by the lane(s) that own
  those artifacts.

So **two pilots run, not three**, both preregistered below before any pilot
work started (this file's first commit predates both pilots' work — check
`git log --follow` on this path).

## Pilot 1 — category 1 (high-degree missing substrate), BOUNDED PROBE

- Graph-selected target: row `IF-LANG-dce29ad3f7` — can this kernel even
  STATE a carrier-generic associativity/commutativity proposition without a
  bundled `Structure`, using a raw `∀ (α : Sort) (op : α→α→α), …`
  quantification? (A narrower, session-sized question than "build bundled
  Semigroup", which needs new kernel primitives this lane will not add.)
- Local-ready alternative: the simplest currently-open dispatchable mirror,
  `F:ml430-nat-and-self-06a84ccc` (`Nat.land n n = n`), picked from
  `scripts/check-dispatchable-frontier.py`'s 21-item DISPATCHABLE list with no
  graph input at all (alphabetically/complexity-simplest of the untaken 9;
  sibling lane `draw9-first-theorems` already took `and_comm`/`and_assoc`/
  `and_le_left`/`and_le_right`/`dist_*` — confirmed via `git log`).
- Preregistered metric (reusing `IF-LANG-dce29ad3f7`'s row, sharpened to the
  bounded question): does a term of shape
  `∀ (α : Sort 1) (op : α→α→α), (∀ a b c, op (op a b) c = op a (op b c)) →
  ∀ a b c, op (op a b) c = op a (op b c)`
  (deliberately trivial content — this tests STATABILITY and kernel
  acceptance, not new mathematics) pass `Kernel::add_declaration`?
  Baseline: no such carrier-polymorphic statement exists anywhere in the
  kernel today (checked: `grep -rn 'Sort 1).*op.*op' crates/axeyum-lean-kernel/src` → 0).
  Expected direction: PASSES (kernel already has the Pi/Sort machinery for
  this; the gap is that nobody wrote it, not that the kernel cannot express
  it) — if it does not pass, that is real evidence the substrate gap is
  deeper than "nobody built it yet".

## Pilot 2 — category 2 (shared congruence producer)

- Graph-selected target: row `IF-LANG-53e5bef137` — build a carrier-generic
  `congrArg`-shaped helper (explicit carrier-type parameter instead of a
  hardcoded `nat_ty()`/`bool_ty()`), reusable across the ≥4 existing
  per-carrier duplicates (`NatOps::congr`, `congr_nat_to`, `congr_bool_to_nat`
  ×3, `congr_at`, `congr_arg_str`, `congr_append_left/right` ×3 in
  `string_prelude`, `congr_at` in `characterization`).
- Local-ready alternative: same dispatchable-queue pick as pilot 1
  (`F:ml430-nat-and-self-06a84ccc`) — a lane without graph input would spend
  the same slot proving one more mirror theorem rather than building shared
  infrastructure.
- Preregistered metric, reusing row `IF-LANG-53e5bef137` but measured FRESH
  (the row's own recorded baseline of 1 is already stale — see below): count
  of files matching `congr_nat_to|congr_bool_to_nat` under
  `crates/axeyum-lean-kernel/src`.
  **Fresh baseline measured now (before pilot work): 4** (`nat_prelude_tests.rs`,
  `xor_algebra.rs`, `bitwise.rs`, `binary_rec.rs`) — the row's recorded
  baseline of 1 was already stale by the time this lane started, from
  concurrent lane activity the same day. This drift is itself a finding
  about how fast a "baseline" ages here.
  Direction actually tested: does landing a generic helper let a NEW
  congr-shaped proof obligation be discharged WITHOUT adding a new
  per-carrier duplicate (i.e., the count of carrier-specific congr helpers
  does not grow by one more when the pilot's own proof work needs one)?

## Constraints honoured

- `artifacts/autogenesis/` untouched; `check-autogenesis-holdout-isolation.py`
  run before starting (`held_out=136, verdict=PASS`) and will be re-run at
  close.
- No files under `artifacts/infrastructure-frontier/`, `artifacts/graph-join/`,
  `artifacts/declaration-graph/`, `artifacts/module-baseline/` touched.
- Sibling lane `draw9-first-theorems` targets checked via `git log --all
  --oneline` before picking any dispatchable mirror; `and_self` was untouched
  by it at lane start.

<!-- plan-section: landed-changes -->

| 2026-08-30 | l2-g4-pilot-clusters | preregistration committed before any pilot work: 2 pilots run (not 3), category 3 reported as not-yet-evaluable with reasons |
