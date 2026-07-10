# Support matrix (4-column)

Generated from `axeyum_solver::support_matrix::SUPPORT_MATRIX` — do not edit by hand.
Regenerate after changing the source of truth and commit the result; a golden test
(`tests/support_matrix.rs`) fails if this file drifts from the code.

Four **independent** axes per SMT-LIB fragment, so "the parser accepts it" is never conflated with "the solver decides it" or "the result carries a proof". The companion [capability matrix](capability-matrix.md) gives the *assurance* of a result; this one gives the per-stage *status*.

## Legend

**parser-accepts** (does `axeyum-smtlib` parse it?):
- **accepted** — parsed and acted on.
- **accepted-but-ignored** — parsed but a deliberate no-op in the single-result `solve_smtlib` facade (e.g. `get-model`, `get-unsat-core`, `get-proof`, `echo`, `exit`); some commands also have explicit helper APIs.
- **accepted (bounded)** — parsed only over a bounded/restricted shape (bounded strings; arrays without nested components; constant-operand-only ops; non-parametric datatypes).
- **rejected** — deliberately refused (full `reset`, parametric datatypes, the unbounded `String`/`Seq` sort).

**IR-semantics** (does `axeyum-ir` model its semantics?):
- **modeled** — first-class IR sort(s)/op(s) with ground-evaluator semantics.
- **partial** — a subset of operations / only a bounded shape.
- **lowered (no IR sort)** — no native sort; semantics via bit-vector/Boolean lowering (strings, floating-point values).
- **absent** — not modeled.

**solver-decides** (definite `sat`/`unsat` for the core queries?):
- **decides** — returns both `sat` and `unsat` for the core fragment.
- **unsat decided; sat→unknown** — `unsat` is decided but a satisfying model is not built, so `sat` degrades to a sound `unknown` (the `str.len` BV+LIA gap). First-class — never a wrong answer.
- **sound, incomplete (unknown-safe)** — may return `unknown` in general (nonlinear arithmetic, quantifiers outside finite/guarded domains, optimization).
- **unsupported** — not decided.

**proof-supports** (does an `unsat` carry a checkable proof?):
- **checked** — self-contained certificate re-checkable with no access to the producing solver (DRAT recheck, Farkas verify, a re-derived congruence closure, end-to-end faithfulness miter).
- **partial-trust** — a certificate exists modulo a trusted reduction layer (clausal DRAT after a trusted elimination/bit-blast) or only for covered sub-cases.
- **none** — no proof artifact (`sat` model replay / conflict core only).

## Matrix

| Fragment | parser-accepts | IR-semantics | solver-decides | proof-supports |
|---|---|---|---|---|
| QF_BV (scalar bit-vectors) | accepted | modeled | decides | checked |
| QF_ABV (arrays) | accepted (bounded) | modeled | decides | partial-trust |
| QF_UF (EUF / congruence) | accepted | modeled | decides | checked |
| QF_LIA (general linear integer) | accepted | modeled | decides | partial-trust |
| QF_LIA · integer infeasibility (Diophantine + interval) | accepted | modeled | decides | checked |
| QF_LRA (linear real) | accepted | modeled | decides | checked |
| QF_NIA (nonlinear integer) | accepted | modeled | sound, incomplete (unknown-safe) | none |
| QF_NRA (general nonlinear real) | accepted | modeled | sound, incomplete (unknown-safe) | none |
| QF_NRA · cylindrical decomposition (coupled, mixed/non-strict, any dimension) | accepted | modeled | decides | none |
| QF_NRA · degree-2 SOS / globally-(non)negative quadratic forms | accepted | modeled | decides | checked |
| QF_NRA · single-variable real-algebraic | accepted | modeled | decides | none |
| QF_UFLIA / QF_UFLRA (UF + arithmetic) | accepted | modeled | decides | partial-trust |
| QF_FP (floating-point) | accepted | lowered (no IR sort) | decides | partial-trust |
| quantifiers (∃/∀, finite-domain + instantiation) | accepted | modeled | sound, incomplete (unknown-safe) | partial-trust |
| datatypes (algebraic) | accepted (bounded) | modeled | decides | partial-trust |
| strings (bounded) | accepted (bounded) | lowered (no IR sort) | unsat decided; sat→unknown | none |
| optimization (OMT: box/lex/Pareto, MaxSAT, MILP) | accepted | modeled | sound, incomplete (unknown-safe) | none |
| incremental (push/pop, reset-assertions) | accepted | modeled | decides | none |

## Notes (per row)

- **QF_BV (scalar bit-vectors)** — full scalar op set parsed and modeled; bit-blast to SAT decides both directions; unsat carries a DRAT proof + an end-to-end faithfulness miter (Alethe/Lean too). ADR-0006/0011/0012
- **QF_ABV (arrays)** — Canonical arrays admit Bool/BitVec index and element components; eager read-over-write + Ackermann elimination remains the fallback. Unsat DRAT is modulo the trusted (replay-validatable) elimination. ADR-0010/0079
- **QF_UF (EUF / congruence)** — declare-fun + congruence closure on a backtrackable e-graph decides; unsat carries a congruence explanation re-derived by an independent union-find checker (Alethe + Lean too). ADR-0013/0032
- **QF_LIA (general linear integer)** — Int sort + div/mod/abs eliminated exactly; Diophantine refutation + branch-and-bound simplex + Gomory cuts decide (degrade to unknown on node budget); general-case unsat DRAT is bounded (refutes at the chosen bit-blast width). Checked-proof sub-fragments are listed separately. ADR-0014/0020/0021
- **QF_LIA · integer infeasibility (Diophantine + interval)** — integer-systems infeasibility (equality systems, e.g. 2x=1; and the single-variable interval c≤k·x≤d) carries an independent integer-Farkas self-check (Evidence::UnsatDiophantine) AND a kernel-checked Lean proof accepted by the real `lean` binary (discreteness via the ℤ prelude). ADR-0042/0043. General integer-cut (Gomory) proof reconstruction is future.
- **QF_LRA (linear real)** — exact-rational simplex is complete for QF_LRA; unsat carries a Farkas certificate with a from-scratch independent verifier (Alethe la_generic + Lean too). ADR-0015
- **QF_NIA (nonlinear integer)** — general NIA is sound-incomplete (linear abstraction + bounded bit-blast with no-overflow MULTIPLIER GUARDS so small-witness nonlinear sat decides — replay-checked over exact integer semantics; genuine nonlinear-integer unsat is undecidable for bounded blasting ⇒ sound unknown); the single-variable integer polynomial decider (nia_square) is exact (e.g. x*x=2 → unsat). Differentially validated DISAGREE=0 vs Z3. No proof artifact, and proof export is fail-closed (Inconclusive) when overflow guards restrict the blast. ADR-0024
- **QF_NRA (general nonlinear real)** — the FALLBACK for the hard coupled/high-degree tail the CAD declines (linear abstraction + replay + McCormick spatial branch-and-bound; relaxation-unsat sound, sat replay-checked, unknown otherwise). No proof artifact for this general fallback. ADR-0024. (The complete CAD decision side and the proof-carrying sub-fragments are listed separately below.)
- **QF_NRA · cylindrical decomposition (coupled, mixed/non-strict, any dimension)** — complete CAD decision side: coupled-equality resultant grid (irrational coordinates) + strict and non-strict cylindrical decomposition over open cells AND critical 0-cells, ANY dimension, with RATIONAL or ALGEBRAIC coordinates (algebraic criticals lifted via Res(min-poly, p) + exact RealAlgebraic field arithmetic). Every sat replay-checked; every unsat exhaustive-or-decline (decline propagates, never a gap). Differentially VALIDATED DISAGREE=0 vs Z3 (the NRA + NIA fuzzes found+fixed three real wrong-unsats in shared isolation/sampling/lift code). No proof artifact yet (per-cell Positivstellensatz reconstruction is the open arc). ADR-0044/0045/0046
- **QF_NRA · degree-2 SOS / globally-(non)negative quadratic forms** — exact decision via a PSD/sum-of-squares certificate (multivariate AM-GM, (x±y)²<0, …). Self-checking LDLᵀ certificate (Evidence::UnsatSos), AND a kernel-checked Lean proof for both strict directions up to 3-variable AM-GM, accepted by the real `lean` binary. ADR-0039/0040/0041
- **QF_NRA · single-variable real-algebraic** — exact single-variable polynomial decision with irrational (real-algebraic) witnesses (x*x=2 → sat √2, replay-checked by exact sign test); coupled 2-var via resultant. No proof artifact yet (sat witnesses are not Lean-reconstructed). ADR-0038
- **QF_UFLIA / QF_UFLRA (UF + arithmetic)** — eager Ackermann congruence → arithmetic; complete for the conjunctive fragment's UNSAT, and a satisfiable query now yields a REPLAY-CHECKED sat model — the arithmetic model is projected back to a full-Value-keyed function interpretation and replayed against the original assertions (decline to sound unknown on any replay doubt). Alethe proof covers the conjunctive UNSAT sub-cases modulo trusted Ackermann. ADR-0013/0015
- **QF_FP (floating-point)** — FP sorts/ops parsed (some conversions constant-only); FP values are BitVec (no IR sort), lowered to circuits differentially validated vs native/apfloat; unsat DRAT is modulo the trusted FP circuit. ADR-0023/0026/0028
- **quantifiers (∃/∀, finite-domain + instantiation)** — complete over finite (Bool/BV) domains, guarded-finite Int expansion, and single-variable real Fourier-Motzkin; otherwise sound refutation by e-matching/MBQI instantiation (ground unsat transfers; sat/no-progress is unknown). Checkable Alethe/Lean for the refutation slices. ADR-0016/0032
- **datatypes (algebraic)** — non-parametric declare-datatype(s) parsed (parametric rejected); structural acyclicity/injectivity + elimination/native expansion decide; unsat DRAT modulo trusted datatype folding (Alethe/Lean too). ADR-0022
- **strings (bounded)** — no String IR sort — declare-const lowered to a bounded packed BV (len ≤ 16); ops parsed within the bound; sat decided through the BV path but str.len unsat may be unknown (BV+LIA gap). Model replay only, no unsat proof. ADR-0025/0029
- **optimization (OMT: box/lex/Pareto, MaxSAT, MILP)** — maximize/minimize parsed and acted on; each optimum is certified only by an internal confirmed-unsat domination query (no exported artifact) and degrades to a sound OptOutcome::Unknown when a probe is undecided. ADR-0027
- **incremental (push/pop, reset-assertions)** — push/pop and reset-assertions parsed (full `reset` is rejected); warm QF_BV/Bool with assumption-core pruning + all-SAT decides; supported BV-indexed Bool/BV array-symbol reads, scalar UFs, direct array equality, and bounded store/constant/ITE structural reads retain scalar owners in the persistent engine. Exact transitive ROW summaries stay dormant until candidate violation, then persist in CNF with replay projection. Remaining array/UF theory defers; no DRAT/Alethe across push/pop. ADR-0009/0030/0086/0087
