//! Word-level string / sequence theory for Axeyum — the Phase-B core
//! (ADR-0053).
//!
//! This crate implements the cvc5 CAV-2014 normal-form / arrangement procedure
//! over first-class `Sort::Seq` terms (ADR-0051). It depends **only** on
//! [`axeyum_ir`] — input is `Seq`-sorted [`TermId`](axeyum_ir::TermId)s over a
//! shared [`TermArena`](axeyum_ir::TermArena); output is denotation-preserving
//! rewrites (this slice) and, in later slices, verdicts + replay-checked witness
//! assignments. No solver-crate dependency, no C/C++, `forbid(unsafe_code)`,
//! WASM-clean.
//!
//! ## What is here (slice T-B.1): the normalization invariant
//!
//! [`normal_form::normalize`] is a confluent, terminating, **denotation-preserving**
//! rewrite applied before any word-level reasoning. It makes equal strings
//! syntactically comparable and is the precondition for flat/normal-form
//! computation. Its four rule families are:
//!
//! 1. **flatten** nested `str.++` trees into a canonical **right-associated**
//!    spine;
//! 2. **drop** `seq.empty` (ε) components of a concatenation;
//! 3. **fuse** a maximal run of adjacent *constant* components into a single
//!    canonical constant block (see the module docs for why this is a
//!    right-associated `seq.unit` block, not an atomic literal, in this IR);
//! 4. **push `str.len`** through concatenation and constants:
//!    `len(x ++ y) → len(x) + len(y)`, `len(const) → Int`, `len(seq.unit e) → 1`,
//!    `len(seq.empty) → 0`.
//!
//! Every rule is property-tested against the ground evaluator: on random
//! `Seq`-sorted terms and random assignments the rewritten term evaluates
//! identically to the original. The rewrite is **idempotent**
//! (`normalize(normalize(t))` interns to the same [`TermId`](axeyum_ir::TermId)
//! as `normalize(t)`).
//!
//! [`normal_form::concat_components`] exposes the flattened, ε-dropped,
//! constant-fused component view that the later flat/normal-form slices consume.
//!
//! ## What is here (slice T-B.2): flat forms, normal forms, explanations
//!
//! [`classes`] builds a deterministic union-find over a caller-supplied slice of
//! asserted `Seq`-sorted equalities (each positionally indexed as its *premise
//! ID*) and computes, bottom-up over an acyclic class-containment ordering, the
//! CAV-2014 (Liang–Reynolds–Tinelli) **normal form** of every equivalence
//! class — a vector of sub-class representatives that concatenates to the same
//! sequence as every member. Every derived fact carries a **sufficient premise
//! set** ([`BTreeSet<usize>`](std::collections::BTreeSet), cvc5's `d_expDep`).
//!
//! T-B.2 is soundness-first: a **containment cycle** (a loop for the later
//! `F-Loop` device) yields [`classes::Declined::Cycle`], and members that
//! disagree beyond exact-vector reconciliation yield
//! [`classes::Declined::Unreconciled`] — the T-B.3 inference and T-B.4
//! arrangement rules that would reconcile those cases are not part of this
//! slice, so it declines rather than guess. Congruence over `str.++` is the
//! e-graph's responsibility, not this union-find's.
//!
//! ## What is here (slice T-B.3): cycle detection + normal-form inference
//!
//! [`infer()`] runs a deterministic, budget-guarded fixpoint over the T-B.2
//! substrate that turns some of its declines into progress. It emits
//! [`Inference`]s — each a derived [`Fact`] (a theory consequence of its cited
//! premises) or a [`Conflict`] (a jointly-unsatisfiable premise set) — via four
//! rules:
//!
//! * **cycle ε-inference** ([`infer::Rule::CycleEpsilon`]): on a class-containment
//!   cycle (`x ≈ y ++ x`, or a mutual `x ≈ y ++ a`, `a ≈ z ++ x`) every
//!   off-cycle component is forced to ε (CAV-2014), which breaks the loop T-B.2
//!   [`Declined::Cycle`] refused to unfold;
//! * **`INFER_UNIFY`** ([`infer::Rule::InferUnify`]): two components of
//!   **structurally** provable equal length at an aligned position must be equal
//!   (LIA length entailment is out of scope — it arrives with the Phase-A
//!   `LenAbs` link);
//! * **`INFER_ENDPOINT_EQ` / `INFER_ENDPOINT_EMP`**
//!   ([`infer::Rule::InferEndpointEq`] / [`infer::Rule::InferEndpointEmp`]): tail
//!   handling when one member's vector is a component-wise-equal prefix of
//!   another's.
//!
//! `F-Split` / `Len-Split` arrangement branching (T-B.4) and `F-Loop` / regex
//! (T-B.5) are **not** part of this slice: where they would be required the pass
//! declines (stops the alignment) rather than guess. Every published premise set
//! cites **original** premise indices only, even for facts derived from earlier
//! derived facts.
//!
//! ## What is here (slice T-B.7): word-level `unsat` behind a re-checked derivation
//!
//! [`refute_word_equations`] is the first route to word-level `unsat`, and it only
//! ever fires behind an **independent re-check**. It runs the T-B.3 fixpoint (the
//! untrusted search) and, on a reported [`Conflict`], returns `unsat` only when
//! [`check_conflict`] re-derives that conflict from its cited premises alone —
//! sharing no reasoning code with [`infer()`], trusting the record only as a hint,
//! and declining anything it cannot re-derive from first principles (loops,
//! parity/length arguments, inference-dependent conflicts). This mirrors how the
//! pure-Rust SAT path waited for DRAT: a wrong `unsat` is impossible because every
//! `unsat` carries a re-checkable derivation.

#![forbid(unsafe_code)]
#![allow(clippy::missing_errors_doc)] // documented per-item where a `Result` is returned

pub mod arrange;
pub mod check_derivation;
pub mod classes;
pub mod infer;
pub mod normal_form;
pub mod refute;
pub mod regex;

pub use arrange::{SearchBudget, SearchOutcome, UnknownReason, solve_word_equations};
pub use check_derivation::{
    check_conflict, check_congruence_equality, check_cycle_constant_conflict, check_equality,
    check_fact,
};
pub use classes::{Classes, Declined, FlatForm, NormalForm, NormalForms, Unreconciled};
pub use infer::{Conflict, ConflictReason, Fact, Inference, Inferences, Rule, infer};
pub use normal_form::{concat_components, normalize};
pub use refute::{RefuteOutcome, refute_word_equations};
