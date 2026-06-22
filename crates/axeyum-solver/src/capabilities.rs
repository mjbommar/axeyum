//! The capability ledger: a single, machine-checked source of truth for **what
//! the stack decides, at what assurance level, backed by what evidence**.
//!
//! The project's identity is "untrusted fast search, trusted small checking", so
//! *whether* a result is trustworthy matters as much as *whether* it is produced.
//! Historically that trust metadata lived in prose (the support-matrix tables and
//! per-module doc comments) and drifted out of sync with the code. This module
//! makes it data: [`CAPABILITIES`] is the source of truth, and the rendered
//! [`capability_matrix_markdown`] is golden-tested against the committed
//! `docs/research/08-planning/capability-matrix.md`, so docs cannot silently go
//! stale (the test fails instead).
//!
//! The same data is what *should* drive `Unsupported` messages, rustdoc, and
//! benchmark-artifact provenance over time — but the first slice is the ledger
//! plus the un-drift-able doc. Entries are ordered deliberately; iteration is in
//! source order (no hash-map nondeterminism — determinism is a public promise).

use core::fmt;
use core::fmt::Write as _;

/// How much to trust a `sat`/`unsat`/`unknown` from a given capability.
///
/// This is the assurance axis the review (recommendation #9) asks for: it keeps
/// "implemented" from being mistaken for "trusted core".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assurance {
    /// Decision procedure with an independently *checkable* certificate for the
    /// hard direction (e.g. a Farkas certificate, a DRAT proof, or a replayed
    /// model) — the closest to the "trusted small checking" north star.
    Checked,
    /// Sound and (for its fragment) complete, and differentially **validated**
    /// against an external oracle or native semantics, but without a
    /// self-contained certificate emitted per query.
    Validated,
    /// Sound but **incomplete**: may return `unknown` (first-class, never wrong).
    SoundIncomplete,
    /// Lower-assurance / horizon feature: sound in intent but not yet validated
    /// to the bar above, or behind a bound/experimental surface.
    Experimental,
}

impl Assurance {
    /// A short stable label used in the rendered matrix.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Assurance::Checked => "checked",
            Assurance::Validated => "validated",
            Assurance::SoundIncomplete => "sound, incomplete",
            Assurance::Experimental => "experimental",
        }
    }
}

impl fmt::Display for Assurance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// One capability the stack exposes: a theory/operation slice, its assurance,
/// the evidence backing a result, and the deciding ADR.
#[derive(Debug, Clone, Copy)]
pub struct Capability {
    /// The logic fragment / theory area (e.g. `"QF_BV"`, `"QF_FP"`).
    pub area: &'static str,
    /// The specific capability within the area.
    pub feature: &'static str,
    /// How much to trust its results.
    pub assurance: Assurance,
    /// What backs a result (the checkable artifact or validation basis).
    pub evidence: &'static str,
    /// The architecture-decision record that introduced/governs it.
    pub reference: &'static str,
}

/// The ledger. Ordered by area, then by feature, for a stable rendered matrix.
///
/// Keep this honest: an entry asserts the assurance is actually backed by the
/// stated evidence (tests/ADR). Downgrade rather than overstate.
pub const CAPABILITIES: &[Capability] = &[
    Capability {
        area: "QF_BV",
        feature: "bit-vectors → AIG → SAT (full scalar operator set)",
        assurance: Assurance::Validated,
        evidence: "model replay vs ground evaluator; differential vs Z3",
        reference: "ADR-0006/0007",
    },
    Capability {
        area: "QF_BV",
        feature: "UNSAT with a DRAT proof (proof-producing CDCL + in-tree checker)",
        assurance: Assurance::Checked,
        evidence: "DRAT proof checked by check_drat (RUP+RAT); UnsatProof::recheck re-validates \
                   from text alone",
        reference: "ADR-0011/0012",
    },
    Capability {
        area: "QF_BV",
        feature: "end-to-end certified UNSAT (certify_qf_bv_unsat_end_to_end): bit-blasting \
                  certified faithful vs an independent reference + CNF-UNSAT DRAT",
        assurance: Assurance::Checked,
        evidence: "faithfulness miter (exhaustive, DRAT) closes the term→CNF gap modulo an \
                   independent reference bit-blaster; EndToEndUnsatOutcome::recheck re-validates both",
        reference: "ADR-0011/0012",
    },
    Capability {
        area: "QF_BV",
        feature: "Craig interpolation (qf_bv_interpolant): joint bit-blast, propositional \
                  interpolant over the resolution proof, lifted to extract-predicates on shared terms",
        assurance: Assurance::Validated,
        evidence: "re-verified before return — A ∧ ¬I and I ∧ B each decided Unsat by the \
                   independent QF_BV decider (check_auto) + shared-symbol vocabulary; lift declines \
                   to None on any non-shared-term / interior-gate var (partial, never unverified)",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_BV",
        feature: "arbitrary width up to 2^16 (wide bit-vectors); bv2nat exact \
                  in the i128 reference range, wider → graceful unknown",
        assurance: Assurance::Validated,
        evidence: "WideUint vs u128/i128; model replay (an Int-crossing bv2nat \
                   beyond i128 is reported, not wrapped)",
        reference: "ADR-0006",
    },
    Capability {
        area: "QF_ABV",
        feature: "arrays via eager read-over-write + Ackermann elimination",
        assurance: Assurance::Validated,
        evidence: "reduction to QF_BV; model replay; UNSAT exportable as a re-checkable \
                   DRAT certificate (clausal layer, modulo trusted elimination)",
        reference: "ADR-0010",
    },
    Capability {
        area: "QF_UF",
        feature: "uninterpreted functions: lazy congruence closure on a backtrackable \
                  e-graph (check_qf_uf, the check_auto fast path) with an eager Ackermann \
                  bit-blast fallback",
        assurance: Assurance::Checked,
        evidence: "UNSAT carries a congruence explanation re-derived by an independent \
                   union-find + congruence checker (check_congruence); SAT model built from \
                   the e-graph classes and replayed against the original; both routes \
                   differentially + randomly validated against the Ackermann path",
        reference: "ADR-0013/0032",
    },
    Capability {
        area: "QF_UF",
        feature: "Craig interpolation (qf_uf_interpolant): ground interpolant summarized from the \
                  congruence-closure explanation, lowering non-shared congruence boundaries to \
                  argument equalities",
        assurance: Assurance::Validated,
        evidence: "re-verified before return by three independent checks (A ∧ ¬I unsat, I ∧ B \
                   unsat via check_qf_uf, shared vocabulary); partial generator (single \
                   disequality conflict, monochrome congruence) — declines outside scope, never \
                   an unverified interpolant",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LRA",
        feature: "linear real arithmetic (exact-rational simplex)",
        assurance: Assurance::Checked,
        evidence: "Farkas certificate for UNSAT; exact rational model",
        reference: "ADR-0015",
    },
    Capability {
        area: "QF_LRA",
        feature: "Craig interpolation (lra_interpolant): interpolant read off the Farkas \
                  certificate of an unsat A ∧ B",
        assurance: Assurance::Checked,
        evidence: "interpolant = the A-side Farkas combination; re-verified before return by three \
                   independent checks (A ∧ ¬I unsat, I ∧ B unsat, shared vocabulary); declines on \
                   any failure (never an unverified interpolant)",
        reference: "ADR-0047",
    },
    Capability {
        area: "SAT (propositional)",
        feature: "Craig interpolation (axeyum_cnf::propositional_interpolant): McMillan fold over \
                  the elaborated LRAT resolution proof of an unsat A ∧ B",
        assurance: Assurance::Checked,
        evidence: "interpolant re-verified before return — A ∧ ¬I and I ∧ B each Tseitin-encoded \
                   and discharged unsat by the proof-producing core + check_drat, plus shared-\
                   vocabulary containment; declines (None) on any failure",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LIA",
        feature: "linear integer arithmetic (bit-blast + branch-and-bound simplex)",
        assurance: Assurance::Validated,
        evidence: "model replay; bounded bit-blast / simplex; bounded UNSAT exportable as a \
                   re-checkable DRAT certificate (at the chosen width)",
        reference: "ADR-0014/0020/0021",
    },
    Capability {
        area: "QF_UFLIA/UFLRA",
        feature: "uninterpreted functions over Int/Real, by EUF + linear-arithmetic \
                  combination (eager Ackermann elimination → the arithmetic dispatcher)",
        assurance: Assurance::SoundIncomplete,
        evidence: "complete for the conjunctive fragment's UNSAT — eager congruence \
                   constraints + LIA/LRA decide f(a)≠f(b)∧a≤b∧b≤a, f(x+0)≠f(x), and nested \
                   f(g(a))≠f(g(b))∧a=b; SAT yields a REPLAY-CHECKED model — the arithmetic \
                   model is projected back to a full-Value-keyed function interpretation and \
                   replayed against the original assertions (decline to sound Unknown on any \
                   replay/projection doubt); never a wrong sat/unsat",
        reference: "ADR-0013/0015 (P1.6)",
    },
    Capability {
        area: "QF_UFLIA/UFLRA",
        feature: "Craig interpolation (uflra_interpolant): Ackermannize A∪B (shared abstraction), \
                  conjunctive LRA interpolant on the function-free relaxation, fresh vars translated \
                  back to shared UF terms",
        assurance: Assurance::Validated,
        evidence: "re-verified before return — A ∧ ¬I and I ∧ B each Unsat via check_with_uf_arithmetic \
                   + shared symbol/function vocabulary; declines on a congruence-needed (disjunctive) \
                   refutation or any re-check failure (never an unverified interpolant)",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_NRA",
        feature: "nonlinear real: a complete cylindrical-decomposition decision side \
                  (single-variable real-algebraic + degree-2 SOS/PSD + coupled-equality \
                  resultant grid + strict and non-strict CAD, ANY dimension, rational OR \
                  algebraic coordinates) over a linear-abstraction/McCormick fallback; \
                  sound-incomplete only on the hard coupled/high-degree tail",
        assurance: Assurance::SoundIncomplete,
        evidence: "irrational witnesses as Value::RealAlgebraic (x*x=2 → Sat √2); every \
                   SAT replay-checked (sign_at / exact field-arithmetic eval), every CAD \
                   UNSAT exhaustive-or-decline; differentially VALIDATED DISAGREE=0 vs Z3 \
                   over the NRA fuzz (which found+fixed real wrong-unsats); degree-2 SOS \
                   UNSAT carries a kernel-checked Lean proof, general CAD UNSAT no proof yet",
        reference: "ADR-0024/0038/0039/0040/0044/0045/0046",
    },
    Capability {
        area: "QF_NIA",
        feature: "nonlinear integer: linear abstraction + bounded bit-blast with \
                  no-overflow multiplier guards + the single-variable integer-polynomial \
                  decider (nia_square)",
        assurance: Assurance::SoundIncomplete,
        evidence: "small-witness SAT decides (the no-overflow guard finds faithful, \
                   non-wrapping products; every SAT replay-checked over exact integer \
                   semantics); x*x=2 → unsat; genuine nonlinear-integer UNSAT is \
                   undecidable for bounded blasting ⇒ sound Unknown (never wrong unsat); \
                   differentially VALIDATED DISAGREE=0 vs Z3 over the NIA fuzz; proof \
                   export is fail-closed (Inconclusive) when overflow guards restrict the \
                   blast",
        reference: "ADR-0024 + the no-overflow multiplier guard / fail-closed proof export",
    },
    Capability {
        area: "QF_FP",
        feature: "float add/sub/mul/div/fma/sqrt — F16/F32/F64/F128 + small formats",
        assurance: Assurance::Validated,
        evidence: "circuit differential vs native f32/f64 and rustc_apfloat; model replay",
        reference: "ADR-0023/0026/0028",
    },
    Capability {
        area: "QF_FP",
        feature: "float rem/roundToIntegral/to_fp/conversions/classification",
        assurance: Assurance::Validated,
        evidence: "differential vs trusted fold / native; unvalidated formats refused",
        reference: "ADR-0023/0026",
    },
    Capability {
        area: "datatypes",
        feature: "algebraic datatypes (constructor axioms; elimination + native)",
        assurance: Assurance::Validated,
        evidence: "model replay; first-class sort; folded-away UNSAT exportable as a \
                   re-checkable DRAT certificate",
        reference: "ADR-0022",
    },
    Capability {
        area: "quantifiers",
        feature: "finite-domain expansion + congruence-aware e-matching on the e-graph keystone \
                  (single/multi-variable, multi-pattern set-cover triggers, nested triggers) \
                  + the instantiation fixpoint loop + model-based instantiation (MBQI)",
        assurance: Assurance::SoundIncomplete,
        evidence: "complete over finite domains; otherwise sound refutation by instantiation \
                   (every instance is entailed, so a ground UNSAT transfers; SAT/no-progress is \
                   unknown-safe). E-matching is modulo the ground congruence (keystone EGraph::ematch)",
        reference: "ADR-0016/0032",
    },
    Capability {
        area: "QF_S (strings)",
        feature: "bounded strings + regex (BV-lowered); SMT-LIB front end wired for \
                  declare/literal/=/distinct + str.prefixof/suffixof/contains + str.at (const idx) \
                  + str.++ (const fold) + str.len (sat; unsat may be unknown — BV+LIA gap), \
                  str.to_code/from_code + substr/indexof/replace/replace_all/lex-compare/\
                  take/drop/to_int/from_int/is_digit + regex membership via API",
        assurance: Assurance::Experimental,
        evidence: "model replay through BV path; canonical-padding equality; length bound explicit",
        reference: "ADR-0025/0029",
    },
    Capability {
        area: "optimization",
        feature: "OMT — all three z3 modes (box, lexicographic, Pareto) over LIA + BV; \
                  weighted MaxSAT with a witnessing model; MILP (branch-and-bound over the \
                  arithmetic cores)",
        assurance: Assurance::Experimental,
        evidence: "each optimum/Pareto point certified by the underlying decision procedure \
                   per step (a confirmed-unsat domination query); deterministic point/push caps",
        reference: "ADR-0027",
    },
    Capability {
        area: "incremental",
        feature: "warm push/pop/assume QF_BV; assumption-core path pruning; all-SAT \
                  reachable-state enumeration (symbolic execution / reachability)",
        assurance: Assurance::Validated,
        evidence: "model replay; SAT final-conflict core (a sound inconsistent subset)",
        reference: "ADR-0009",
    },
    Capability {
        area: "incremental",
        feature: "symbolic memory: select/store via check_with_memory (eager elimination; \
                  warm lazy arrays = ADR-0030 future work)",
        assurance: Assurance::Validated,
        evidence: "eager array elimination (ADR-0010) + model replay; warm path refuses arrays",
        reference: "ADR-0010/0030",
    },
    Capability {
        area: "symbolic execution",
        feature: "DFS path explorer (SymbolicExecutor): assume / branch fork query / \
                  enter+backtrack / concrete test-input model / distinct test-suite enumeration \
                  (all-SAT) / optimize objective over the path condition (min/max, unsigned/signed \
                  BV + LIA)",
        assurance: Assurance::Validated,
        evidence: "models replay-checked vs path condition; optimum certified by the underlying \
                   procedure; three-valued PathStatus keeps unknown from wrongly pruning a live path",
        reference: "ADR-0009/0027",
    },
    Capability {
        area: "reachability",
        feature: "bounded model checking over a symbolic transition system \
                  (bounded_model_check; warm BV/Bool, plus bounded_model_check_with_memory \
                  for array/symbolic-memory state via eager elimination)",
        assurance: Assurance::Validated,
        evidence: "Reachable = replay-checked counterexample trace (incl. select/store); \
                   UnreachableWithinBound is bounded only (interpolation = future work); unknown-safe",
        reference: "ADR-0009/0010",
    },
    Capability {
        area: "reachability",
        feature: "unbounded safety proving by k-induction (prove_safety_k_induction)",
        assurance: Assurance::SoundIncomplete,
        evidence: "Safe = base case (BMC) + inductive-step UNSAT (unbounded); Reachable = \
                   replay-checked counterexample; non-inductive properties return Inconclusive, \
                   never a wrong Safe",
        reference: "ADR-0009",
    },
    Capability {
        area: "reachability",
        feature: "certified k-induction (certify_safety_k_induction): Safe carries DRAT \
                  certificates for both obligations",
        assurance: Assurance::Checked,
        evidence: "base-case + inductive-step UNSAT each exported as a drat-trim-checkable \
                   DIMACS+DRAT pair (clausal layer, modulo trusted term→CNF reduction)",
        reference: "ADR-0011/0012",
    },
    Capability {
        area: "reachability",
        feature: "CHC/PDR inductive-invariant DISCOVERY (prove_safety_pdr): single-predicate IC3/PDR \
                  over the transition system — proves safe properties that are not k-inductive by \
                  discovering the invariant",
        assurance: Assurance::Checked,
        evidence: "the IC3 search is UNTRUSTED — a Safe verdict is returned only when the discovered \
                   invariant passes 3 independent check_auto-unsat checks (initiation, consecution, \
                   safety); Reachable only when BMC-confirmed; prove_safety_pdr_certified bundles the \
                   3 DRAT-recheckable proofs; all caps → Unknown",
        reference: "ADR-0048",
    },
];

/// Renders [`CAPABILITIES`] as the canonical capability-matrix markdown table.
///
/// Golden-tested against `docs/research/08-planning/capability-matrix.md`; that
/// file is regenerated from here, never hand-edited.
#[must_use]
pub fn capability_matrix_markdown() -> String {
    let mut out = String::new();
    out.push_str("# Capability matrix\n\n");
    out.push_str(
        "Generated from `axeyum_solver::capabilities::CAPABILITIES` — do not edit by hand.\n\
         Regenerate after changing the ledger and commit the result; a golden test\n\
         (`tests/capabilities.rs`) fails if this file drifts from the source of truth.\n\n",
    );
    out.push_str(
        "Assurance levels: **checked** (independent certificate — Farkas/DRAT/replayed \
                  model), **validated** (differential vs an oracle, no per-query certificate), \
                  **sound, incomplete** (`unknown`-safe), **experimental** (lower assurance or \
                  bounded/horizon surface).\n\n",
    );
    out.push_str("| Area | Capability | Assurance | Evidence | Ref |\n");
    out.push_str("|---|---|---|---|---|\n");
    for c in CAPABILITIES {
        // `write!` to a String is infallible; the result is intentionally ignored.
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            c.area,
            c.feature,
            c.assurance.label(),
            c.evidence,
            c.reference,
        );
    }
    out
}
