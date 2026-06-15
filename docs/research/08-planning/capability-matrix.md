# Capability matrix

Generated from `axeyum_solver::capabilities::CAPABILITIES` — do not edit by hand.
Regenerate after changing the ledger and commit the result; a golden test
(`tests/capabilities.rs`) fails if this file drifts from the source of truth.

Assurance levels: **checked** (independent certificate — Farkas/DRAT/replayed model), **validated** (differential vs an oracle, no per-query certificate), **sound, incomplete** (`unknown`-safe), **experimental** (lower assurance or bounded/horizon surface).

| Area | Capability | Assurance | Evidence | Ref |
|---|---|---|---|---|
| QF_BV | bit-vectors → AIG → SAT (full scalar operator set) | validated | model replay vs ground evaluator; differential vs Z3 | ADR-0006/0007 |
| QF_BV | UNSAT with a DRAT proof (proof-producing CDCL + in-tree checker) | checked | DRAT proof checked by check_drat (RUP+RAT) | ADR-0011/0012 |
| QF_BV | arbitrary width up to 2^16 (wide bit-vectors) | validated | WideUint vs u128/i128; model replay | ADR-0006 |
| QF_ABV | arrays via eager read-over-write + Ackermann elimination | validated | reduction to QF_BV; model replay; UNSAT exportable as a re-checkable DRAT certificate (clausal layer, modulo trusted elimination) | ADR-0010 |
| QF_UF | uninterpreted functions via Ackermann reduction | validated | reduction; model replay; UNSAT exportable as a re-checkable DRAT certificate (clausal layer, modulo trusted reduction) | ADR-0013 |
| QF_LRA | linear real arithmetic (exact-rational simplex) | checked | Farkas certificate for UNSAT; exact rational model | ADR-0015 |
| QF_LIA | linear integer arithmetic (bit-blast + branch-and-bound simplex) | validated | model replay; bounded bit-blast / simplex; bounded UNSAT exportable as a re-checkable DRAT certificate (at the chosen width) | ADR-0014/0020/0021 |
| QF_NRA/NIA | nonlinear via linear abstraction + sign/zero lemmas + McCormick B&B | sound, incomplete | model replay (SAT); relaxation-unsat (UNSAT); unknown otherwise | ADR-0024 |
| QF_FP | float add/sub/mul/div/fma/sqrt — F16/F32/F64/F128 + small formats | validated | circuit differential vs native f32/f64 and rustc_apfloat; model replay | ADR-0023/0026/0028 |
| QF_FP | float rem/roundToIntegral/to_fp/conversions/classification | validated | differential vs trusted fold / native; unvalidated formats refused | ADR-0023/0026 |
| datatypes | algebraic datatypes (constructor axioms; elimination + native) | validated | model replay; first-class sort; folded-away UNSAT exportable as a re-checkable DRAT certificate | ADR-0022 |
| quantifiers | finite-domain expansion + E-matching instantiation | sound, incomplete | complete over finite domains; instantiation otherwise (unknown-safe) | ADR-0016 |
| QF_S (strings) | bounded-length strings + regex (BV-lowered) — API only, not SMT-LIB-wired | experimental | model replay through BV path; length bound explicit (≤16) | ADR-0025/0029 |
| optimization | MaxSAT / OMT / MILP (branch-and-bound over the arithmetic cores) | experimental | optimum certified by the underlying decision procedure per step | ADR-0027 |
| incremental | warm push/pop/assume QF_BV; assumption-core path pruning; all-SAT reachable-state enumeration (symbolic execution / reachability) | validated | model replay; SAT final-conflict core (a sound inconsistent subset) | ADR-0009 |
| incremental | symbolic memory: select/store via check_with_memory (eager elimination; warm lazy arrays = ADR-0030 future work) | validated | eager array elimination (ADR-0010) + model replay; warm path refuses arrays | ADR-0010/0030 |
