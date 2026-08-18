# Lane: capability-assurance — the strand's own metric was unmeasurable

<!-- plan-section: lane-status -->

**The mathematics strand's primary metric drifted 4 → 11 areas unnoticed**
(`WIP`, capability-assurance, 2026-08-17). Detail:
[`01-decide-vs-certify.md`](../../mathematics-2026-08/01-decide-vs-certify.md).

```
CAPABILITY_ASSURANCE|entries=101|areas=23|external=36|self=48|differential=2|unclassified=15
```

It asks "can a third party check without trusting us?" and calls that the
strand's primary metric — but the answer lived in 101 prose `evidence` fields,
so nobody could count it. Seven areas beyond the documented four had gained
external checking, mostly via Carcara. Agreement with an oracle is tiered
separately so it cannot inflate the number; 15 entries stay `unclassified`
rather than being sorted into a flattering bucket. Now floored.

**Item B is done, and derived** (`--rank`, also in `just flywheel`): the 12
unchecked logics are banded by *distance to an external checker*, not by
opinion. Band 1 — `QF_IDL`, `QF_RDL`, `SAT` — already build a refutation
artifact; `propositional_interpolant` constructs a DRAT proof, checks it with
`check_drat`, and returns `Option<BoolExpr>`, dropping the artifact on the floor.

Ranking exposed a defect in the metric itself: `tier` is per *row*, and three
logics (`QF_AUFBV`, `QF_IDL`, `QF_RDL`) are known only through a compound row,
so a quarter of the gap was uniform-by-assumption. Measured, `QF_IDL / QF_RDL`
genuinely differ — QF_RDL renders a 47 KB Lean theory reconstruction that
official Lean 4.30.0 accepts (two mutations rejected), QF_IDL renders only an
attestation. The table is deliberately **not** edited to claim QF_RDL as
external: `check-lean-gate.sh` compiles a one-module-per-family slice that
contains no QF_RDL module, and moving this metric by rewriting the prose it
reads is the failure this strand exists to prevent.

**Done same day:** QF_RDL is handed to official Lean by `lean_crosscheck`
(`family=qf_rdl_difference`, `representative=theory-reconstruction`, axiom
footprint = ordered field + the query's hypotheses, no `sorryAx`), theory-family
ratchet 33 → 34. Only after that was the table edited — gate first, transcribe
second, because `tier` reads prose and the reverse order would move the metric
by writing a sentence. 11 → **12 of 23 logics**, floor raised to 37.

**`SAT` closed too.** It was the same shape QF_RDL was, and the ADR worry
dissolved on inspection: every other interpolating area already ships a
`*_certified` sibling (QF_BV, QF_UF, QF_LRA, QF_LIA, QF_UFLRA, QF_UFLIA), all of
one shape, so propositional was the seventh case of an accepted pattern.
`verify_interpolant` had already built and checked both DRAT proofs and returned
a bool; `propositional_interpolant_certified` returns them. drat-trim accepts
both, including on a PHP(3,2) partition needing real resolution.

**Next.** Band 1 holds only `QF_IDL`. Chasing it turned up something larger: a
conjunctive integer system whose *rational* relaxation is already infeasible
(`x > 5 ∧ x < 3`, `x - y ≤ 1 ∧ y - x ≤ -3`) has an ordinary Farkas refutation,
yet every such query routes to `ArithDpll` and renders a structural attestation
— an `axiom P` / `axiom ¬P` shim carrying none of the reasoning. The proof
existed; only a `Real`-shaped destination for it did.

`instantiate_at_int_model` supplies the destination. `generalize_over_ordered_ring`
already abstracts a Farkas refutation over the 22 ordered-ring laws (axiom-free),
and `build_int_model_of_arith` already exhibits ℤ as a model of all 22 with empty
witness footprints; nothing had ever instantiated at it. Measured, `x+y+z ≤ 1 ∧
1 ≤ x,y,z` becomes a kernel-checked theorem over `Int` with **an empty axiom
footprint**.

Not yet wired into dispatch, and deliberately no capability row until it is —
the same gate-first discipline QF_RDL followed. That wiring is the next slice. Then items A (generate the table) and C (explicit
"decided, not certified" status), which are the real fix: this checker is a
heuristic over prose and says so.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `07de6526` | Mathematics strand's primary metric derived and gated: 36 of 101 capabilities name an external artifact checker, across 11 of 23 logics, against a documented 4 of 26. Control: disabling the external tier drops it to 0 and the floor fires. |
| 2026-08-17 | `a8a862133` | Denominator counts LOGICS not `area` strings: a compound like `QF_UFLIA/UFLRA` spans two, and its abbreviated second element named a phantom `UFLRA`. The 12 logics with no external check are now an explicit queue. |
| 2026-08-17 | `549a1ecc7` | Item B answered by derivation: the gap is banded by distance to an external checker, and the ranking found QF_RDL already renders a Lean theory module official Lean accepts — a "gap" logic blocked only on gate wiring. Controls: 6 new tests, incl. one proving a solved logic never appears in the queue. |
| 2026-08-17 | `69026936d` | A control no gate RUNS cannot fail, so it is not a control: 63 of 137 control modules were executed by nothing, and running the 51 needing no cargo found 264 tests — 258 passing and gated for free, 6 erroring, four of them import failures against renamed scripts. Ratcheted; the gate caught its own controls being unwired. |
| 2026-08-17 | `19f739a57` | 44 orphaned controls adopted (257 tests, ~31s) and the baseline ratcheted 63 → 17. Fixing the scanner to join line continuations found 2 more already-wired — it had counted 3 of 44 and would have called them orphans. Corrected an overstatement: 5 of the 7 unadopted need `pytest` (absent here), 1 has an order dependency, and exactly 1 has genuinely rotted (`producer drift: Cargo.lock`). |
| 2026-08-17 | `60a7b4712` | QF_RDL closed end to end: `lean_crosscheck` now hands official Lean a QF_RDL theory module every run (33 → 34 theory families), and only then did the table gain a QF_RDL-specific row — 11 → 12 of 23 logics externally checked. Controls: two mutations of the module are rejected by Lean; the attestation class is proven still reachable. |
| 2026-08-17 | `bfc16da51` | The reachability gate contradicted itself and was wrong in my favour: `check-adopted-controls.sh` documents its exclusions as "pytest-style", so those COMMENT lines contained a runner word and vouched for the two modules the comment says are NOT run. Comments are mentions now; baseline corrected 17 → 19. |
| 2026-08-17 | `pending` | `SAT` closed: `propositional_interpolant_certified` returns the two DRAT refutations `verify_interpolant` already built and threw away; drat-trim accepts both, on PHP(3,2) as well as the trivial case. 12 → **13 of 23 logics**, floor 38, band 1 down to `QF_IDL` alone. One control was written, found vacuous (both proofs are the single step `0`), and replaced with one that discriminates. |
| 2026-08-17 | `pending` | Item A's minimum landed: `check-capability-routes.py` requires every function the table names to exist (42 routes, 0 missing — a ratchet, not a repair). The naive version's two false positives (`(vocabulary)` is prose, `(nia_square)` is a `mod`) are pinned as controls. |
| 2026-08-17 | `pending` | Item C: `Capability.checked_by` states who checks each artifact (+ a **Checked by** column in the matrix), replacing the prose regex. Reading all 15 unclassified rows showed the bucket was a regex gap, not a real category — 14 were self-checks phrased "re-checked"/"VERIFY-BEFORE-RETURN". Heuristic kept only as an asymmetric cross-check (claiming external with no checker named fails). Headline unmoved at 38 / 13 of 23; unclassified 15 → 0. |
| 2026-08-17 | `pending` | `instantiate_at_int_model`: a Farkas refutation, generalized over the ordered ring, instantiated at ℤ — `∀ (x0 x1 x2 : Int), … → False`, kernel-checked, **axiom footprint empty**. The machinery for both halves existed; nothing had joined them. Not yet dispatched, so no capability row. Controls: the statement is asserted to mention `Int`, conclude `False`, and keep 3 variables + 4 hypotheses, since an empty footprint on a vacuous statement proves nothing. |
| 2026-08-17 | `pending` | The motivating query closed as a measurement: `x > 5 ∧ x < 3` — the `(set-logic QF_LIA)` instance that renders a structural attestation today — has an axiom-free integer refutation, `∀ (x0 : Int), 5-x<0 → x-3<0 → False`. The reasoning is available; only the dispatch that reaches for it is missing. |
