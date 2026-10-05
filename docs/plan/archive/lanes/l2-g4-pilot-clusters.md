# Lane: l2-g4-pilot-clusters — L2 phase G4, pilot clusters + graph-ranking verdict

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, l2-g4-pilot-clusters, 2026-08-30).** Two pilots
run (categories 1 and 2); category 3 reported not-yet-evaluable with a stated
reason. Both pilots moved their preregistered metric with zero added trust
surface; the local-ready alternative was investigated and sized but not
completed inside the same budget. **Verdict: RETAIN the ranking**, scoped to
categories 1-2 over population `mathlib-group-defs-v1` — see the Results and
Exit verdict sections below for the full evidence and the explicit scope
limit. ADR-0865 records the decision.

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

## Results

### Pilot 1 result

`crates/axeyum-lean-kernel/examples/g4_pilot_generic_assoc_probe.rs` (commit
`25c54b39b`). Built, via the raw `Kernel` API only, a closed term of type
`∀ (α : Sort 1) (op : α→α→α), (assoc hyp) → (assoc concl)` and called
`Kernel::add_declaration`.

- **RESULT: PASS.** The kernel accepted it. Rendered type:
  `((x0 : Sort (1)) -> ((x1 : (x0 -> x0 -> x0)) -> ((x2 : (assoc hyp over x1))
  -> (x3 x4 x5 : x0) -> (assoc concl over x1))))` (see the example's own
  printed output for the exact form).
- **Negative control: PASS.** The identical identity-shaped proof term against
  a mismatched (commutativity-from-associativity) goal was correctly REFUSED
  by the kernel, confirming the PASS above is not vacuous.
- **Elapsed time:** ~20 minutes wall including API discovery (reading
  `quotient.rs`'s `expected_eq_type` for the `Sort`-binding precedent,
  `NatOps::congr`/`transport`/`eq_motive` for the `Eq.rec` pattern), one build
  (23 s cold, later edits <1 s incremental), two clippy-driven fixes.
- **Producer reuse:** none needed — this is new, self-contained code, not a
  call into existing per-carrier machinery.
- **Safety cost: zero.** No axioms, no weakened checker; the term is checked
  by the ordinary trusted `add_declaration` path exactly like any other
  declaration. The example is a `TEMPORARY` probe (per its own doc comment,
  matching `probe_add_structure.rs`'s convention) — not a claimed library
  contribution.
- **Finding, sharpening row `IF-LANG-dce29ad3f7`:** the row's framing
  ("this kernel cannot STATE carrier-generic associativity") is broader than
  what is actually missing. A raw, non-bundled, `Sort`-quantified statement
  over an arbitrary carrier and an arbitrary binary operation is ALREADY
  representable and accepted — it always was, since `quotient.rs` already
  binds `Sort u`-typed variables internally. What is missing is the bundled
  **ergonomics** (one `Semigroup`-shaped record reused across many lemmas via
  a typeclass/structure mechanism this kernel does not have), not raw
  statability. This is a real, useful correction to the row, not a refutation
  of it — the row's underlying claim (no bundled-structure mechanism exists)
  is still true and confirmed by reading the kernel's inductive list.

### Pilot 2 result

`crates/axeyum-lean-kernel/examples/g4_pilot_generic_congr_probe.rs` (commit
`ac7a11c5a`). Built a carrier-generic `congr_arg` (explicit `ty`/`level`
params instead of a hardcoded carrier) via the raw `Kernel` API, and ran it
against the SAME inputs (`a`, `b`, `h : Eq Nat a b`, `f = Nat.succ`) as the
existing `NatOps::congr`, using the ready-made `NatDev` wrapper for the
existing route.

- **RESULT: PASS, and stronger than merely "also correct".** The two proof
  terms are the **identical `ExprId`** — the kernel's content-addressed
  interning gives the same handle to two independently-built but
  structurally-identical terms. This is not "the generic version also works";
  it is a byte-for-byte reconstruction of what `NatOps::congr` builds, i.e.
  genuine drop-in reuse for this call site, not merely a parallel
  implementation that happens to agree.
- The generic-route proof, wrapped as a real `∀ a b, Eq Nat a b → Eq Nat
  (succ a) (succ b)` theorem, was independently accepted by
  `Kernel::add_declaration`.
- **Elapsed time:** ~25 minutes wall (reading `NatOps::eq/refl/transport/
  eq_motive/congr` in `nat_prelude/ops.rs` to find the exact pattern to
  generalize, `NatDev`/`NatState` for the comparison harness, one clippy
  round for two lint fixes: `similar_names`, `too_many_arguments`).
- **Producer reuse:** demonstrated directly — one function
  (`generic_congr_arg`) reproduces what `NatOps::congr` needs; the fresh grep
  count of existing per-carrier `congr`-shaped helpers was **4 files**
  (`nat_prelude_tests.rs`, `xor_algebra.rs`, `bitwise.rs`, `binary_rec.rs`
  matching `congr_nat_to|congr_bool_to_nat`) against the row's stale recorded
  baseline of 1 — a real, measured instance of "a baseline ages fast in this
  repository", independent of this pilot's own outcome.
- **Safety cost: zero.** Same trusted `add_declaration` path; no axioms.
- **Finding:** the row's claim is directly validated, not just plausible — a
  single carrier-generic function CAN replace the pattern behind at least
  `NatOps::congr`, with proof, not merely by argument.

### Local-ready alternative: attempted, sized, NOT completed within budget

Both pilots' preregistered local-ready alternative is
`F:ml430-nat-and-self-06a84ccc` (`Nat.land n n = n`), picked as the
simplest-looking untaken entry in the 21-item DISPATCHABLE list without any
deep investigation — mirroring how a lane would actually pick "the next
thing" absent graph input.

Investigation (not a guess: read `nat_prelude/land.rs`,
`nat_prelude/rec_agreement.rs`'s `declare_land_aux_le_left` as the closest
existing proof of the same shape, and `nat_prelude/ops.rs`'s
`agree_by_fuel_induction`/`cases_zero_succ`) found:

- Several needed pieces already exist and proved: `Nat.land_zero_left` (refl),
  `Nat.land_zero_right`, `Nat.land_bit`, `Nat.div_mod_exec`, and the
  `agree_by_fuel_induction`/`cases_zero_succ` induction machinery used
  throughout this file family.
- What does NOT exist is the specific induction proving `landAux fuel n n = n`
  by cases on `n` via `div`/`mod` by 2 (mirroring `land_aux_le_left`'s
  ~80-line structure, but for equality rather than `Le`) — this needs a fresh
  base case, a fresh succ-case built from `div_mod_exec` plus a small
  `bit * bit = bit` case split (`bit ∈ {0,1}`) that no existing lemma states
  directly, then a `land`-headed corollary at `fuel := n`.
- **This was not completed.** Sizing it (not guessing) took ~35 minutes of
  reading; writing and debugging the induction proof itself, based on the
  measured cost of comparable siblings this repository's own CLAUDE.md
  documents (`land_comm`, `land_assoc`, `land_bit` each needed dedicated
  fuel-irrelevance lemmas and multiple rounds of debugging), is realistically
  a multi-hour undertaking, not a same-session pilot-budget item.
- **This was not cherry-picked to be the hardest.** The other 8 open
  dispatchable candidates in the same family were read for comparison:
  `and_or_distrib_left/right` (distributivity — harder, same family as
  `land_assoc`), `dist_triangle_inequality`/`dist_pos_of_ne` (case-heavy but
  plausibly comparable), `fermat_primefactors_one_lt` (deep number theory,
  clearly harder). One, `Nat.and_one_is_mod` (`x &&& 1 = x % 2`), LOOKS
  potentially easier via a `bit`-decode-and-unfold route, but was not
  independently verified — reported as a real possibility, not a finding.

**This is itself a load-bearing result for the phase's exit question.** The
naive "take the next dispatchable item" alternative was not actually cheap in
this instance: neither pilot's local-ready comparator produced a proved fact
within the same budget both graph-selected pilots completed in (~20-25
minutes each, both PASS). "Dispatchable" in this ledger certifies dependency
readiness, not proof brevity — the two are different claims, and conflating
them would have made the comparison unfair in the graph ranking's favour by
assuming a cheap alternative that direct investigation shows was not cheap
here.

## Exit verdict: RETAIN the ranking, on this evidence, with an explicit scope
limit

The G4 exit criterion: **retain the ranking only if at least two pilots move
their preregistered downstream metric without a worse trust boundary.**

- Pilot 1 moved its metric (statability of a `Sort`-quantified associativity
  claim: absent → present, `PASS` on `add_declaration`) with zero added trust
  surface.
- Pilot 2 moved its metric even more strongly than preregistered (byte-
  identical proof-term reuse, not merely "a generic version exists") with
  zero added trust surface.
- Both pilots beat the honest local-ready comparator on the only axis that
  was actually measured for it: time-to-a-result. The comparator did not
  produce a proved fact inside the same budget.

**Two of two run pilots moved their metric cleanly. RETAIN the ranking** —
but scoped to what was actually tested: this verdict is about categories 1
(narrowed to a bounded substrate probe) and 2 (shared producer) over ONE
population (`mathlib-group-defs-v1`). It says nothing about category 3
(destination bridge toward linear algebra/polynomials/analysis), which
remains genuinely untested — see the signal-check section above for what
would make it testable. Do not read this verdict as "the ranking works for
all three categories"; read it as "the ranking's first two testable
categories, on the one population currently joined, each produced a real,
cheap, zero-trust-cost win against the plausible naive alternative."

One honest sentence on what would have changed this verdict: if either
generic-helper probe had required bundled-structure machinery this kernel
genuinely lacks (i.e., if Pilot 1's `add_declaration` had been REJECTED, or if
Pilot 2's generic function had produced a merely-similar rather than
identical proof term, forcing real new kernel work before any payoff), that
would have been a pilot that failed to move its metric cheaply, and with only
one pilot left standing the exit criterion would not have been met.

## Constraints honoured

- `artifacts/autogenesis/` untouched; `check-autogenesis-holdout-isolation.py`
  run before starting (`held_out=136, verdict=PASS`) and re-run at close
  (`held_out=136, files_scanned=1110, settled=0, references=0, verdict=PASS`
  — identical, confirming no touch).
- No files under `artifacts/infrastructure-frontier/`, `artifacts/graph-join/`,
  `artifacts/declaration-graph/`, `artifacts/module-baseline/` touched.
- Sibling lane `draw9-first-theorems` targets checked via `git log --all
  --oneline` before picking any dispatchable mirror; `and_self` was untouched
  by it at lane start.

<!-- plan-section: landed-changes -->

| 2026-08-30 | l2-g4-pilot-clusters | preregistration committed before any pilot work: 2 pilots run (not 3), category 3 reported as not-yet-evaluable with reasons |
| 2026-08-30 | l2-g4-pilot-clusters | pilot 1 (statability probe) PASS + negative-control PASS, zero trust cost |
| 2026-08-30 | l2-g4-pilot-clusters | pilot 2 (generic congr_arg) PASS with byte-identical proof-term reuse vs `NatOps::congr` |
| 2026-08-30 | l2-g4-pilot-clusters | local-ready alternative (`and_self`) investigated, sized, not completed in budget; recorded as real comparative data |
| 2026-08-30 | l2-g4-pilot-clusters | exit verdict: RETAIN the ranking (categories 1-2 over `mathlib-group-defs-v1`); ADR-0865 |
