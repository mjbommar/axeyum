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
| QF_S (strings) | bounded strings + regex (BV-lowered); SMT-LIB front end wired for declare/literal/=/distinct + str.prefixof/suffixof/contains + str.at (const idx) + str.++ (const fold) + str.len (sat; unsat may be unknown — BV+LIA gap), rest via API | experimental | model replay through BV path; canonical-padding equality; length bound explicit | ADR-0025/0029 |
| optimization | MaxSAT / OMT / MILP (branch-and-bound over the arithmetic cores) | experimental | optimum certified by the underlying decision procedure per step | ADR-0027 |
| incremental | warm push/pop/assume QF_BV; assumption-core path pruning; all-SAT reachable-state enumeration (symbolic execution / reachability) | validated | model replay; SAT final-conflict core (a sound inconsistent subset) | ADR-0009 |
| incremental | symbolic memory: select/store via check_with_memory (eager elimination; warm lazy arrays = ADR-0030 future work) | validated | eager array elimination (ADR-0010) + model replay; warm path refuses arrays | ADR-0010/0030 |
| symbolic execution | DFS path explorer (SymbolicExecutor): assume / branch fork query / enter+backtrack / concrete test-input model / distinct test-suite enumeration (all-SAT) / optimize objective over the path condition (min/max, unsigned/signed BV + LIA) | validated | models replay-checked vs path condition; optimum certified by the underlying procedure; three-valued PathStatus keeps unknown from wrongly pruning a live path | ADR-0009/0027 |
| reachability | bounded model checking over a symbolic transition system (bounded_model_check; warm BV/Bool, plus bounded_model_check_with_memory for array/symbolic-memory state via eager elimination) | validated | Reachable = replay-checked counterexample trace (incl. select/store); UnreachableWithinBound is bounded only (interpolation = future work); unknown-safe | ADR-0009/0010 |
| reachability | unbounded safety proving by k-induction (prove_safety_k_induction) | sound, incomplete | Safe = base case (BMC) + inductive-step UNSAT (unbounded); Reachable = replay-checked counterexample; non-inductive properties return Inconclusive, never a wrong Safe | ADR-0009 |
| reachability | certified k-induction (certify_safety_k_induction): Safe carries DRAT certificates for both obligations | checked | base-case + inductive-step UNSAT each exported as a drat-trim-checkable DIMACS+DRAT pair (clausal layer, modulo trusted term→CNF reduction) | ADR-0011/0012 |
