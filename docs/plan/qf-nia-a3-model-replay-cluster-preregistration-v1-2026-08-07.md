# QF_NIA A3 model-replay cluster preregistration v1 — 2026-08-07

## Scope and hypothesis

This preregisters the first implementation cluster selected from the complete
v2 causal census. It does not authorize a cap increase or acceptance of a model
that fails original-term replay.

The shared mechanism is narrower than “NIA is hard”: `nia-linearize` constructs
a Boolean-structured integer-linear relaxation, the arithmetic DPLL reports a
theory-consistent SAT candidate, and `finish_sat` rejects that reconstructed
candidate because at least one relaxed assertion does not evaluate to `true`.
The current diagnostic erases which assertion failed and whether the value was
`false`, non-Boolean, or unevaluable. The first increment must expose that
bounded evidence before changing search or reconstruction.

Baseline code is topic commit
`882ec89da2d9daf491d4d301933f0c6302234dd5`. Population authority is retained
census SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`.

## Exact cluster

The target predicate is exact over that immutable census: `route =
nia-linearize`, `reason = incomplete`, `kind = incomplete`, and detail exactly
`arith DPLL candidate failed full model replay`. It selects these 13 rows and no
others:

| Role | Reference | Exact row |
|---|---|---|
| near-miss | UNSAT | `20170427-VeryMax/ITS/From_AProVE_2014__SortCount.jar-obl-10__terminationS_2_0.smt2` |
| target | SAT | `20170427-VeryMax/ITS/From_AProVE_2014__juHashMapCreate.jar-obl-10__p4943_safety_0.smt2` |
| target | SAT | `20170427-VeryMax/ITS/From_AProVE_2014__juHashMapCreateContainsValue.jar-obl-11__p32598_safety_0.smt2` |
| target | SAT | `20170427-VeryMax/ITS/From_AProVE_2014__juHashMapCreateIsEmpty.jar-obl-10__p1784_safety_0.smt2` |
| near-miss | UNSAT | `20170427-VeryMax/ITS/From_T2__fun1b.t2__terminationS_11_0.smt2` |
| target | SAT | `20170427-VeryMax/ITS/From_T2__s1.t2__p20015_safety_0.smt2` |
| target | SAT | `20170427-VeryMax/SAT14/1051.smt2` |
| target | SAT | `20170427-VeryMax/SAT14/1280.smt2` |
| target | SAT | `20170427-VeryMax/SAT14/571.smt2` |
| near-miss | UNSAT | `20210219-Dartagnan/ReachSafety-Loops/geo1-u_valuebound2-O0.smt2` |
| near-miss | UNSAT | `20210219-Dartagnan/ReachSafety-Loops/ps2-ll_unwindbound50-O0.smt2` |
| near-miss | UNSAT | `AProVE/aproveSMT4687047739446499948.smt2` |
| near-miss | UNSAT | `AProVE/aproveSMT5048239408100334127.smt2` |

The seven SAT rows are the only score targets in this cluster. The six UNSAT
rows may become decided only through an independently sound refutation; they
must never become SAT merely because reconstruction is made more permissive.

## Controls and acceptance

1. **Mechanism SAT control:**
   `nia_linearize::tests::narrow_domain_product_system_stays_satisfiable` must
   remain SAT and replay against the original product assertion.
2. **Rejected-candidate control:**
   `dpll_lia::tests::false_full_replay_candidate_is_unknown_not_backend_error`
   must remain `Unknown`, never SAT or a backend error.
3. **Opaque-evaluation control:**
   `dpll_lia::tests::opaque_uf_model_replay_is_unknown_not_error` must retain
   its typed reconstruction decline; diagnostics must distinguish evaluation
   failure from an evaluated-false assertion.
4. **Process-survival control:** the census row containing the 16,525-argument
   `distinct` must remain `Unknown(ResourceLimit)` under 8 GiB and must not
   enter route dispatch.
5. **No-loss set:** all 34 rows whose entry in sidecar SHA-256
   `392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`
   has `axeyum ∈ {sat, unsat}`. This selector binds 30 SAT and four UNSAT rows;
   the fresh 200-row retention run must decide every one with the same verdict.

Every returned SAT model must replay all original assertions. Reference labels
select targets and controls; they are not fed into the solver and cannot rescue
a failed replay.

## Ordered experiment

1. Add deterministic bounded replay diagnostics at the DPLL reconstruction
   boundary: first failing assertion ordinal and `TermId`, evaluated outcome,
   and counts of bound/unbound original symbols. Do not print full models or
   source terms and do not change the verdict.
2. Re-run all 13 rows with `AXEYUM_NIA_DEBUG=1`, 24,000 ms per query, and the
   same 8 GiB process ceiling. Record a complete diagnostic matrix.
3. Select a more specific shared defect only if the matrix supports it. Add a
   minimal in-repository regression that reproduces the defect plus the three
   controls above before changing reconstruction or search.
4. Implement the repair at the model-construction/theory interface that owns
   the defect. A fixture-specific exception, reference-conditioned behavior,
   replay bypass, general cap increase, or host-dependent budget change is
   forbidden.
5. Run the exact 13-case A/B, then the fresh 200-row QF_NIA list. Retain only a
   monotone result with all 34 prior decisions, zero disagreements, and replayed
   original-term models for every SAT answer.

## Stop conditions

Stop without solver-policy credit if diagnostics do not identify a shared
mechanism, any reference-UNSAT row becomes SAT, any prior decision is lost, a
SAT model fails replay, the 8 GiB process ceiling fires, or the repair requires
raising a general cap. A diagnostic-only improvement may still be retained as
route observability if it is deterministic, bounded, tested, and does not alter
verdicts.

## Diagnostic disposition

The diagnostic-first increment completed at `4ff9a82c6`; see the
[`v1 diagnostic result`](qf-nia-a3-model-reconstruction-diagnostic-v1-result-2026-08-07.md).
Six rows reproduced an evaluated-false assertion with all symbols bound, and
each also violated a selected arithmetic literal. The owner was
`theory_model`, which collapsed reconstruction `Unknown`/`Unsat` to an empty
model and caused default-value replay to erase the actual decline. The repair
preserves the typed outcome and changes no verdict. It does not satisfy this
cluster's breadth exit; concrete probe-model reuse is the next separately
preregistered experiment.
