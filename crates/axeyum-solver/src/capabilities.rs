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
        feature: "CERTIFIED pure-Gaussian XOR UNSAT (CDCL(XOR) fallback, ADR-0035): when the \
                  recovered XOR system is inconsistent by Gaussian elimination ALONE (level 0, no \
                  branching), the conflict subset S (summing to 0 = 1) is refuted by a per-query DRAT \
                  certificate over CNF(S). BOUNDARY: the INTERLEAVED CDCL(XOR) UNSAT (branching needed) \
                  stays search-only TRUSTED (the XorGaussian ledger hole) — this row covers ONLY the \
                  pure-Gauss-level-0 sub-case",
        assurance: Assurance::Checked,
        evidence: "xor_gauss_drat_refutation builds CNF(S) + a DRAT proof from the conflict subset \
                   (Gf2System::unsat_reason_subset provenance); validated end-to-end by the independent \
                   check_drat and re-attached as Evidence::Unsat(Some(_)), re-checkable from text via \
                   Evidence::check / UnsatProof::recheck. Declines (keeps the trusted behavior, no false \
                   cert) on the interleaved case or any non-validating proof",
        reference: "ADR-0035",
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
        feature: "UNSAT with an ALETHE proof, Carcara-checked (prove_qf_bv_unsat_alethe + \
                  prove_qf_bv_unsat_alethe_ext_compare): per-operator bitblast steps using Carcara's \
                  native bitblast rule set (bvnot/and/or/xor/xnor, add/neg/mul, ult/slt, comp, =, \
                  extract/concat/sign_extend), bvsub via the poly-simp bridge, and the extended \
                  comparisons bvule/ugt/uge/sle/sgt/sge normalized in-emitter to bvult/bvslt before \
                  emission — the on-ramp to Lean evidence",
        assurance: Assurance::Checked,
        evidence: "every emitted proof is self-validated by the in-tree check_alethe AND independently \
                   accepted (valid && !holey) by the external Rust Carcara checker in carcara_crosscheck \
                   (60 cases incl. the 6 new extended-comparison drivers, proven NOT skipped) — an emitter \
                   bug surfaces as a Carcara rejection, never an unsound accept. Declines (no proof) on \
                   shifts / div-rem (no Carcara bitblast rule) → the in-house miter cert covers those",
        reference: "ADR-0011/0012",
    },
    Capability {
        area: "QF_BV",
        feature: "kernel-certified CONSTANT-shift lowering identity (reconstruct_const_shift_lowering): \
                  the previously-trusted lowering (bvshl/bvlshr/bvashr a k) = concat/extract/sign_extend \
                  for a constant k now carries a Lean-kernel-checked proof — Carcara has NO rule for it \
                  (shift→concat is non-polynomial; no bitblast_shl), so the Lean kernel is the external \
                  checker. Constant-shift QF_BV thus reconstructs end-to-end with the lowering step \
                  certified, not trusted",
        assurance: Assurance::Checked,
        evidence: "per-bit reflexive proof ⋀_i (bv_bit(shift,i) ↔ bv_bit(rhs,i)) — both sides route \
                   through the SAME bv_bit model so each conjunct is Iff.refl IFF the lowering is correct; \
                   kernel infer + def_eq gate, axiom audit shows NO sorryAx; a WRONG slice is KernelRejected \
                   (tamper test has teeth). Constant-only: variable shifts (no literal k) out of fragment; \
                   division stays trusted/out-of-scope (term blowup past width ~2, not a missing rule)",
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
        feature: "CERTIFIED single-predicate Craig interpolation (qf_bv_interpolant_certified): the \
                  same verified QF_BV interpolant I, plus two externally-checkable bit-blast certificates",
        assurance: Assurance::Checked,
        evidence: "when the lifted interpolant I is a single top-level predicate (=/bvult/bvslt over \
                   bit-blastable operands; the ¬I slot peels one not), A ∧ ¬I and I ∧ B stay in the \
                   Carcara-checked flat-predicate fragment ⇒ emits a self-validated Alethe \
                   bitblast_*/resolution refutation for each (Craig conditions 1 and 2) via \
                   prove_qf_bv_unsat_alethe, each independently accepted by Carcara (valid && !holey); \
                   returns the certificate ONLY when both refutations emit and self-check, else \
                   declines to the Validated qf_bv_interpolant path. BOUNDARY: single-predicate only — \
                   the common compound (and/or/not-tree of extract-predicates) interpolant is outside \
                   the emitter's fragment and stays Validated",
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
                   DRAT certificate (clausal layer, modulo trusted elimination). The Ackermann-over-select \
                   read-CONSISTENCY stratum is Carcara-checked (select as a plain UF); direct equal-array \
                   same-index read conflicts emit literal SMT-LIB select with eq_reflexive/eq_congruent/\
                   symm/resolution and check in-tree, in Carcara (including tamper rejection), and in the \
                   real Lean kernel with no array-elimination trust step; and the \
                   read-over-write-SAME collapse select(store(a,i,v),i)=v now has a Carcara-checked \
                   derivation (prove_qf_abv_row_same_alethe_carcara: eq_simplify/cong/ite_simplify/trans/\
                   resolution, with a tamper-rejection test), and the read-over-write-DIFF collapse \
                   select(store(a,i,e),j)=select(a,j) for distinct CONSTANT indices is likewise Carcara-checked \
                   (prove_qf_abv_row_diff_alethe_carcara: evaluate/cong/ite_simplify/trans/resolution, with a \
                   tamper-rejection test) — both shrinking the trusted surface to just the \
                   read-over-write rewrite INSTANCE (asserted as a premise; the array axiom is not yet \
                   certified)",
        reference: "ADR-0010/0075",
    },
    Capability {
        area: "QF_ABV",
        feature: "LAZY arrays (check_qf_abv_lazy / lazy-ROW / lazy extensionality): on-demand CEGAR — \
                  select-congruence + read-over-write axioms added only when a candidate model violates \
                  them, AND array (dis)equality by EXTENSIONALITY (diff-skolem witness a≠b ⇒ \
                  select(a,k)≠select(b,k) + on-demand select-congruence for a=b), woven into one CEGAR \
                  loop. Strictly additive over the eager path: reached only after eager + lazy-ROW refuse \
                  (e.g. true extensionality over a wide index that bounded Ackermann declines)",
        assurance: Assurance::Validated,
        evidence: "the abstraction is a relaxation (its UNSAT transfers) and every added lemma (ROW, \
                   select-congruence, extensionality congruence, diff-witness) is a sound consequence of \
                   read-over-write / array extensionality; every SAT projects a full array model (finite \
                   map + diff-skolem witnesses + else values) and REPLAYS against the original assertions \
                   incl. the (dis)equalities — a failed replay → Unknown, never a wrong SAT. Differential \
                   vs the eager check_with_array_elimination (300 LCG cases, 0 disagreements, every lazy \
                   sat replayed); caps (rounds/sites/256 diff-skolems/deadline) → Unknown. The eager path \
                   stays the always-correct fallback",
        reference: "ADR-0010",
    },
    Capability {
        area: "QF_ABV / QF_AUFBV",
        feature: "canonical online CDCL(T) arrays: replay-guided base-select congruence, \
                  candidate-guided lazy read-over-write, and bounded array equality/disequality \
                  observations with one diff witness per equality atom; equality flags retain their \
                  original array equality on the backtrackable e-graph, and candidate-true symbol \
                  classes share one deterministic majority-default model; direct base reads are \
                  grouped by final e-class and candidate-violated cross-parent congruence is guarded \
                  by the merge explanation; reads through store terms join the same parent scheduler \
                  while lazy read-over-write reserves bounded local atoms and inserts violated ROW \
                  clauses permanently inside the same search; candidate-violated UF, parent-select, \
                  and bounded array-equality interfaces append aligned equality atoms over \
                  pre-observed e-graph terms to that retained search; scalar UF applications in \
                  indices/elements share the same exact BV + e-graph bus; finite-scalar \
                  array-valued UF results retain semantic application parents on the e-graph and \
                  project fresh result arrays by final parent class before function tables; direct, \
                  supported structural, and nested array-valued-application finite-array parameters \
                  can key retained array-valued UF parents using relation-flag guarded key \
                  congruence, structural owner realization, replay-safe rewritten structural keys, \
                  and full-value key projection; array-ITE \
                  equality decomposes exactly before search, and bounded store/ITE/constant class \
                  equations realize total leaf-array models without changing observed reads; array index \
                  and element components may each be Bool or BitVec, with mixed shapes projected \
                  through GenericArrayValue",
        assurance: Assurance::Validated,
        evidence: "every partial round is a relaxation, so UNSAT transfers; SAT requires \
                   array-first/function-second projection and original-query replay. 816 solver-lib \
                   tests plus 2,784 array comparisons are clean: 768 established BV-array \
                   comparisons, 384 Bool/mixed analytic/front-door/Z3 comparisons, and 384 \
                   structural-store eager/front-door/Z3 comparisons, plus 384 dynamic-ROW \
                   and 384 dynamic-interface eager/front-door/Z3 comparisons, plus 288 array-result \
                   and 192 structural-class analytic/front-door/Z3 comparisons; the established BV belt includes \
                   456 equality-bearing cases, and the structural belt adds same/congruent/unrelated \
                   parents, branch/transitive paths, and UF indices. Dynamic ROW gates cover \
                   hit/miss, nested sites, replayed branch changes, UF indices, shadowing, and the \
                   exact shared cap. Dynamic-interface gates cover strict and nested UF, base/store \
                   select congruence, guarded parent branches, array equality with ROW, mixed \
                   array-to-UF fixpoints, and replayable alternatives while retaining one canonical \
                   search. Separate 80-parent gates avoid direct-symbol and congruent-store \
                   preparation products. The \
                   public Bool-component rows issue5925 and issue4240 move unknown→unsat/sat; \
                   DISAGREE=0 and all SAT models replay. The focused warm array-UF parent suite also \
                   covers direct, structural, and nested array-valued-application finite-array \
                   parameters, relation-flag guarded key congruence, full-value key projection, \
                   and replayed nested-key equality conflicts. ADR-0078's low-load 1 s aggregate baseline \
                   remains QF_ABV 187/193 and QF_AUFBV 49/53 pending a comparable remeasure; online \
                   probes use cloned arenas so fallback inputs remain pristine",
        reference: "ADR-0071/0072/0073/0074/0077/0078/0079/0080/0081/0082/0084/0085/0086/0087/0088/0089/0090/0091/0092/0093/0094",
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
                   differentially + randomly validated against the Ackermann path. The online \
                   DPLL(T) loop is now a full CDCL(T) spine — theory propagation + 1-UIP conflict \
                   learning with non-chronological backjump (congruence-explain reasons threaded on \
                   the trail); verdict-invariant, 0 differential disagreements, 800 learned theory-lemma \
                   clauses re-validated congruence-UNSAT and shorter than the full core",
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
        area: "QF_UF",
        feature: "CERTIFIED conjunctive Craig interpolation (qf_uf_interpolant_certified): the same \
                  verified EUF interpolant I, plus two externally-checkable congruence certificates",
        assurance: Assurance::Checked,
        evidence: "I is a conjunction of equalities over shared terms (the diseq-in-B case; the \
                   diseq-in-A negated-I case peels ¬I back to a bare equality), so A ∧ ¬I and I ∧ B \
                   are each single-disequality congruence conflicts ⇒ EUF-refutable; emits a \
                   self-validated Alethe eq_congruent/eq_transitive/resolution refutation for each \
                   (Craig conditions 1 and 2) via prove_qf_uf_unsat_alethe, each independently \
                   accepted by Carcara (valid && !holey) AND by the Lean kernel via \
                   prove_unsat_to_lean_module (infer + def_eq False, no sorryAx); returns the \
                   certificate ONLY when both refutations emit and self-check, else declines to the \
                   Validated qf_uf_interpolant path. BOUNDARY: conjunctive-only — the degenerate \
                   ⊤/⊥ interpolant and non-congruence shapes stay Validated",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LRA",
        feature: "linear real arithmetic (exact-rational simplex)",
        assurance: Assurance::Checked,
        evidence: "Farkas certificate for UNSAT; exact rational model. UNSAT also reconstructs to a \
                   kernel-checked Lean proof (reconstruct_lra_proof) — conjunctive Farkas AND now \
                   2-leaf BOOLEAN-STRUCTURED (disjunctive) refutations: a clause (L₁ ∨ L₂) whose leaves \
                   are each Farkas-unsat, closed by a kernel Or.rec case-split over the per-leaf Farkas \
                   (no new prelude axiom; audit shows no sorryAx). Strict/multi-clause disjunctions decline",
        reference: "ADR-0015",
    },
    Capability {
        area: "QF_LRA",
        feature: "ONLINE incremental LRA theory solver (LraTheory: assert/push/pop + Farkas conflict \
                  cores) + a DPLL(T) driver (check_qf_lra_online) — the warm theory engine for online \
                  combination, first slice of the architecture-maturity keystone",
        assurance: Assurance::Validated,
        evidence: "incremental Fourier–Motzkin with backtrackable trail; soundness by DIFFERENTIAL \
                   validation vs the trusted offline check_with_lra — 4000 random conjunctions \
                   (sat+unsat) + 27.7k push/pop checkpoints, 0 disagreements, every sat model replayed, \
                   conflict cores re-verified unsat (same discipline as the online EUF path). \
                   Propagation under-approximated (deferred); non-LRA atoms decline gracefully",
        reference: "ADR-0015",
    },
    Capability {
        area: "QF_LRA",
        feature: "Craig interpolation (lra_interpolant): interpolant read off the Farkas \
                  certificate of an unsat A ∧ B",
        assurance: Assurance::Validated,
        evidence: "interpolant = the A-side Farkas combination; VERIFY-BEFORE-RETURN — re-decided by \
                   three independent checks (A ∧ ¬I unsat, I ∧ B unsat, shared vocabulary), declining \
                   on any non-Unsat/doubt; no per-query certificate is emitted (so Validated, not \
                   Checked), but the interpolant is independently re-checkable by re-running the checks",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LRA",
        feature: "CERTIFIED conjunctive Craig interpolation (lra_interpolant_certified): the same \
                  verified interpolant I, plus two externally-checkable Farkas certificates",
        assurance: Assurance::Checked,
        evidence: "I is a single linear inequality, so A ∧ ¬I and I ∧ B are each CONJUNCTIONS of \
                   linear-real atoms (¬I is one inequality) ⇒ Farkas-refutable; emits a self-validated \
                   Alethe la_generic refutation for each (Craig conditions 1 and 2), each independently \
                   accepted by Carcara (valid && !holey) AND by the Lean kernel via \
                   prove_unsat_to_lean_module (infer + def_eq False, no sorryAx); returns the certificate \
                   ONLY when both refutations emit and self-check, else declines to the Validated \
                   lra_interpolant path. BOUNDARY: conjunctive-only — disjunctive/Boolean-I \
                   (lra_interpolant_cnf) and non-LRA stay Validated",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LRA",
        feature: "DISJUNCTIVE Craig interpolation (lra_interpolant_cnf): interpolating-SMT over the \
                  DPLL(T) refutation — propositional-resolution interpolation with Farkas theory-lemma \
                  leaves, mixed lemmas purified by a shared synthetic atom",
        assurance: Assurance::Validated,
        evidence: "lifts interpolation beyond the conjunctive case to CNF/Boolean-structured QF_LRA \
                   (the shape IMC/PDR fixpoints generate); VERIFY-BEFORE-RETURN — A ∧ ¬I and I ∧ B each \
                   check_auto-Unsat + shared vocabulary (the vocab check rejects any non-shared \
                   synthetic atom); the abstraction/purification/lifting are untrusted; declines on \
                   sat/non-pure-real/unverified",
        reference: "ADR-0047",
    },
    Capability {
        area: "SAT (propositional)",
        feature: "Craig interpolation (axeyum_cnf::propositional_interpolant): McMillan fold over \
                  the elaborated LRAT resolution proof of an unsat A ∧ B",
        assurance: Assurance::Validated,
        evidence: "VERIFY-BEFORE-RETURN — A ∧ ¬I and I ∧ B each Tseitin-encoded and discharged unsat \
                   by the proof-producing core + the independent check_drat checker, plus shared-\
                   vocabulary containment; declines (None) on any failure. No per-query certificate \
                   is returned (Validated); the DRAT-checked verify is the strongest interpolation \
                   basis and is re-runnable by the consumer",
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
        area: "QF_LIA",
        feature: "kernel-checked LEAN proof for integer UNSAT shapes (int_reconstruct, integer prelude): \
                  Diophantine gcd-infeasible equality systems; single-variable integer-interval cuts \
                  c ≤ k_lo·x ∧ k_hi·x ≤ d — INCLUDING the different-multiplier case (k_lo ≠ k_hi, e.g. \
                  3x ≥ 2 ∧ 2x ≤ 1) that is LP-feasible but integer-infeasible, via no_int_between; and \
                  equality-and-bound k·x = b ∧ (c ≤ x | x ≤ c) (e.g. 2x=4 ∧ x≥3) where the equality pins x \
                  outside the bound — a real-Farkas close (scale-by-k + substitute), reconstructed over \
                  the IntPrelude",
        assurance: Assurance::Checked,
        evidence: "reconstructed to a Lean term the in-tree Lean-grade KERNEL accepts (infer + def_eq \
                   False); axiom audit shows only IntPrelude axioms + the verbatim hypotheses, NO sorryAx; \
                   a reconstructor bug surfaces as KernelRejected, never an unsound accept. Carcara does \
                   NOT implement integer lia_generic (warns + holey), so the Lean kernel is the external \
                   checker here. Feasible-decline tests confirm no fabrication",
        reference: "ADR-0042/0043",
    },
    Capability {
        area: "QF_LIA",
        feature: "ONLINE incremental LIA theory solver (LiaTheory + check_qf_lia_online): backtrackable \
                  assert/push/pop + deletion-minimized conflict cores, integer-complete (strict \
                  tightening, branch-and-bound, cuts) — the warm integer theory engine",
        assurance: Assurance::Validated,
        evidence: "re-decided-incremental over the trusted offline check_with_lia_simplex; DIFFERENTIAL \
                   validation — 400 random conjunctions (sat+unsat) + 3.7k push/pop steps, 0 disagreements, \
                   every sat model replayed with INTEGER values; strict-tightening (0<x<1 ⇒ UNSAT) handled. \
                   Propagation deferred; non-LIA atoms decline gracefully",
        reference: "ADR-0014/0015",
    },
    Capability {
        area: "QF_LIA",
        feature: "ONLINE LIA is a real CDCL(T) spine (mirrors the LRA path): THEORY PROPAGATION (each \
                  unassigned order atom probed by the cheap LP-RELAXATION — real-infeasible of asserted ∧ \
                  ¬atom ⇒ atom entailed over ℤ since ℤ-solutions ⊆ ℝ-solutions — strictly cheaper than a \
                  per-atom integer solve), AND 1-UIP CONFLICT LEARNING with non-chronological backjump \
                  (per-var levels/reasons, analyze_conflict resolves to the first-UIP asserting clause, \
                  theory pop once per decision crossed)",
        assurance: Assurance::Validated,
        evidence: "DECIDER change, verdict-INVARIANT: differential vs the offline integer decider over \
                   400 decided LCG instances + 3.7k push/pop/assert steps, 0 disagreements, every sat \
                   model replayed with integer values; a probe integer-offline-CONFIRMED all 1650 fired \
                   propagations entailed (0 unsound), and 84 learned 1-UIP theory-lemma clauses each \
                   ENTAILED (¬clause ∧ level-0 facts integer-UNSAT) and shorter than the full core. \
                   LP-feasible probe inconclusive ⇒ skip; overflow/equality/out-of-fragment skip. uflia \
                   combination (reuses LiaTheory) unchanged",
        reference: "ADR-0014/0015",
    },
    Capability {
        area: "QF_LRA",
        feature: "ONLINE LRA is a real CDCL(T) spine: THEORY PROPAGATION (the DPLL(T) loop interleaves \
                  unit + theory propagation to a joint fixpoint — each unassigned order atom probed by a \
                  Fourier–Motzkin negation-probe, propagated with an ASSERTED-only Farkas-core reason), \
                  AND 1-UIP CONFLICT LEARNING with non-chronological backjump (per-var levels/reasons, \
                  the discarded TheoryProp.reason now threaded onto the trail; analyze_conflict resolves \
                  to the first-UIP asserting clause — shorter than the full core — and backjumps, popping \
                  the theory once per decision crossed to keep the push/pop lockstep)",
        assurance: Assurance::Validated,
        evidence: "DECIDER change, verdict-INVARIANT (propagation prunes, 1-UIP learning only shortens \
                   clauses + reorders search): differential vs offline check_with_lra over 4000 decided \
                   LCG instances + 27.7k push/pop checks, 0 disagreements, every sat model replayed; a \
                   probe offline-CONFIRMED all 2367 fired propagations entailed (0 unsound), and 585 \
                   learned 1-UIP theory-lemma clauses are each ENTAILED (¬clause ∧ level-0 facts \
                   check_with_lra-UNSAT) and shorter than the full core. Unknown/overflow/equality skip. \
                   lia_online/euf 1-UIP mirrors are follow-up; uflra/uflia BoolSearch unchanged",
        reference: "ADR-0014/0015",
    },
    Capability {
        area: "QF_LIA",
        feature: "Craig interpolation (lia_interpolant): interpolate the rational relaxation \
                  (Int→Real, Farkas), clear denominators to integer coefficients",
        assurance: Assurance::Validated,
        evidence: "VERIFY-BEFORE-RETURN over the integers — A ∧ ¬I and I ∧ B each Unsat via \
                   check_with_lia_simplex + shared vocabulary; the relaxation/Farkas/denominator-\
                   clearing are untrusted. Declines on a cuts-needed unsat (rational relaxation sat), \
                   overflow, or non-conjunctive-QF_LIA. No per-query certificate emitted",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LIA",
        feature: "CERTIFIED conjunctive Craig interpolation (lia_interpolant_certified): the same \
                  verified interpolant I, plus two KERNEL-CHECKED integer certificates",
        assurance: Assurance::Checked,
        evidence: "I is a single integer linear inequality, so A ∧ ¬I and I ∧ B are each integer \
                   CONJUNCTIONS (¬I built as the bare DUAL comparison so the integer fragment \
                   classifier reads it); reconstructs EACH to a kernel-checked Lean module via \
                   prove_unsat_to_lean_module (infer + def_eq False, no sorryAx) — Carcara has NO \
                   lia_generic rule (warns + holey), so the Lean kernel is the external checker. \
                   Returns the certificate ONLY when BOTH conjunctions reconstruct through a COVERED \
                   integer-prelude fragment (Diophantine gcd-infeasible / single-variable interval cut), \
                   else declines to the Validated lia_interpolant path. BOUNDARY: covered-shapes-only — \
                   an interpolant whose A ∧ ¬I or I ∧ B needs an UNCOVERED integer refutation (a general \
                   cut, or a multivariate rational-relaxation refutation the integer reconstructor \
                   declines) stays Validated; equality interpolants (no single-comparison dual) and \
                   disjunctive/Boolean-I (lia_interpolant_cnf) stay Validated too",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_LIA",
        feature: "DISJUNCTIVE Craig interpolation (lia_interpolant_cnf): the integer mirror of \
                  lra_interpolant_cnf — lifts integer interpolation to assertions with arbitrary Boolean \
                  structure (∧/∨/¬/ite/= over linear-int atoms). Relax Int→Real (shared surrogates), reuse \
                  the full lra_interpolant_cnf McMillan interpolating-SMT machinery, translate the real \
                  interpolant back to integer atoms (per-atom denominator clearing). Closes the \
                  imc_lia disjunctive-interpolant gap; wired into Solver::interpolant after lia_interpolant",
        assurance: Assurance::Validated,
        evidence: "VERIFY-BEFORE-RETURN over ℤ — A ∧ ¬I and I ∧ B each Unsat via the DISJUNCTIVE integer \
                   decider check_with_lia_dpll + shared vocabulary; relaxation/McMillan/translation are \
                   untrusted. Declines (Ok(None)) on a cuts-needed leaf (relaxation sat ⇒ lra_interpolant_cnf \
                   declines), real-analogue-less constructs (div/mod/abs/coercions/BV), overflow, or any \
                   re-check failure — never an unverified interpolant. Soundness fuzz: 27 Some / 373 None, \
                   0 unsound",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_UFLRA",
        feature: "ONLINE Nelson–Oppen combination (check_qf_uflra_online): the online EufTheory + the \
                  online LraTheory combined by model-based equality sharing (interface-equality \
                  exchange + DFS interface split) — the warm alternative to eager Ackermann. Now \
                  decides FULL Boolean-structured QF_UFLRA via a real CDCL(T) over the combination: \
                  Dpll<CombinedIncremental> drives one warm EUF+LRA theory with backtrackable \
                  assert/push/pop, joint unit+theory propagation, and 1-UIP conflict learning + \
                  non-chronological backjump over Boolean + theory + INTERFACE-EQUALITY literals (the \
                  Nelson–Oppen undetermined interface split is now ordinary SAT branching on registered \
                  eq/lt/gt vars, not a private DFS — the enumerative BoolSearch is retired to a fallback). \
                  Now the DEFAULT check_auto route for mixed UF+real-arith queries (tried before eager \
                  Ackermann, which stays the byte-unchanged fallback on online Unknown)",
        assurance: Assurance::Validated,
        evidence: "soundness by DIFFERENTIAL validation vs the trusted offline check_with_uf_arithmetic \
                   — random UFLRA conjunctions AND random and/or/not/ite Boolean trees over UFLRA atoms, \
                   0 disagreements, every sat model REPLAYED against the originals (the conjunctive fuzz \
                   caught + fixed 2 real soundness bugs; the Boolean fuzz jointly decided 123 = 41 sat / \
                   82 unsat). A per-model Unknown forces a whole-query Unknown (no wrong unsat). Caps \
                   (models/atoms/clauses/split-depth/timeout) → graceful Unknown; non-UFLRA → Unknown. \
                   The shared-CDCL(T)-spine keystone (gap-analysis centerpiece) is COMPLETE for UFLRA — \
                   built slice by slice each verdict-invariant under the differential: warm CombinedTheory \
                   oracle (cache-by-layout, parallel-run verdict-IDENTICAL to the cold Nelson–Oppen core), \
                   combined theory propagation (EUF + LRA + interface entailments, all fired propagations \
                   offline-confirmed entailed, 0 unsound), a generic Dpll<T: TheorySolver> (no-behavior- \
                   change refactor, 1-UIP counters byte-identical), the CombinedIncremental TheorySolver \
                   surface (interface vars registered as SAT decision atoms), and the Dpll-over- \
                   CombinedIncremental wiring (learned theory lemmas re-validated entailed). The \
                   check_auto dispatch wiring is itself guarded by an in-tree differential \
                   vs the eager route (300-query mixed UF+arith LCG corpus: 240 co-decided, 0 \
                   disagreements, 0 LOGICAL decision-regressions, sat replay, +16 value-add decisions \
                   where eager returns Unknown; the online probe runs on an arena CLONE with a bounded \
                   sub-budget so the eager fallback is never starved)",
        reference: "ADR-0013/0015",
    },
    Capability {
        area: "QF_UFLIA",
        feature: "ONLINE Nelson–Oppen combination (check_qf_uflia_online): online EufTheory + online \
                  LiaTheory by model-based equality sharing — the integer analogue, handling LIA \
                  non-convexity via model-based DFS interface splitting (interface candidates include \
                  UF-argument constants, so integer tightening fires). Now decides FULL \
                  Boolean-structured QF_UFLIA via a real CDCL(T) over the combination (the integer mirror \
                  of QF_UFLRA): Dpll<CombinedIncrementalLia> drives one warm EUF+LiaTheory with \
                  backtrackable assert/push/pop, joint unit+theory propagation, and 1-UIP learning + \
                  non-chronological backjump over Boolean + theory + INTERFACE-EQUALITY literals (the \
                  ≥1-EUF-endpoint interface split is now SAT branching on registered int eq/lt/gt vars, \
                  not a private DFS — the enumerative BoolSearch is retired to a fallback). Now the \
                  DEFAULT check_auto route for mixed UF+int-arith queries (online-first, eager Ackermann \
                  the byte-unchanged fallback on online Unknown)",
        assurance: Assurance::Validated,
        evidence: "differential vs the trusted offline check_with_uf_arithmetic — random UFLIA \
                   conjunctions AND random and/or/not/ite Boolean trees over UFLIA atoms (600-instance \
                   fuzz, non-zero sat + unsat coverage), 0 disagreements, every sat model REPLAYED with \
                   integer values; the combined model covers EUF-only symbols and an uncertifiable / \
                   per-model leaf yields Unknown (no wrong unsat). Caps (models/atoms/clauses/split-depth/\
                   timeout) → graceful Unknown; non-UFLIA → Unknown. 1-UIP learning / theory propagation \
                   deferred",
        reference: "ADR-0013/0014",
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
        area: "QF_UFLRA",
        feature: "CERTIFIED conjunctive Craig interpolation (uflra_interpolant_certified): the same \
                  verified interpolant I, plus two externally-checkable la_generic refutations treating \
                  every uninterpreted-function application as an opaque real",
        assurance: Assurance::Checked,
        evidence: "the certifiable I is always congruence-free (the conjunctive construction declines \
                   whenever the refutation needs functional consistency), so A ∧ ¬I and I ∧ B are each \
                   conjunctions of linear-real comparisons over OPAQUE applications — single-la_generic \
                   refutable; emits a self-validated Alethe la_generic refutation for each (¬I as the dual \
                   comparison) via prove_uflra_unsat_alethe (abstract apps → fresh reals, refute pure-LRA, \
                   substitute apps back), each independently accepted by Carcara (valid && !holey) on the \
                   inlined .smt2; returns the certificate ONLY when both refutations emit and self-check, \
                   else declines to the Validated uflra_interpolant path. BOUNDARY: conjunctive, \
                   congruence-free only; the Lean reconstruction path does not yet cover opaque-application \
                   LRA, so the external check is Carcara",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_UFLIA/UFLRA",
        feature: "Craig interpolation (uflia_interpolant): the integer analogue — Ackermannize A∪B, \
                  lia_interpolant on the function-free integer relaxation, fresh vars translated back \
                  to shared UF terms",
        assurance: Assurance::Validated,
        evidence: "re-verified before return — A ∧ ¬I and I ∧ B each Unsat via check_with_uf_arithmetic \
                   + shared symbol/function vocabulary; declines on a congruence-needed or cuts-needed \
                   (rational-relaxation-sat) refutation, or any re-check failure",
        reference: "ADR-0047",
    },
    Capability {
        area: "QF_UFLIA",
        feature: "CERTIFIED conjunctive Craig interpolation (uflia_interpolant_certified): the same \
                  verified interpolant I, plus two kernel-checked integer Lean certificates treating \
                  every uninterpreted-function application as an opaque integer",
        assurance: Assurance::Checked,
        evidence: "the certifiable I is always congruence-free (the conjunctive construction declines \
                   whenever the refutation needs functional consistency), so A ∧ ¬I and I ∧ B are each \
                   integer conjunctions over OPAQUE applications; each maximal non-arithmetic subterm \
                   (f c) is treated as a fresh opaque integer (AtomVar::Opaque — sound: an (f c) is some \
                   integer, so the free-variable system only generalizes), reconstructed directly through \
                   the integer-prelude reconstructors (reconstruct_diophantine/int_inequality_to_lean_module) \
                   which gate infer + def_eq False before rendering; ¬I as the bare dual comparison; returns \
                   the certificate ONLY when both conjunctions reconstruct through a covered integer fragment \
                   (Diophantine / IntInequality) with no sorryAx, else declines to the Validated \
                   uflia_interpolant path. BOUNDARY: conjunctive, congruence-free, covered integer shapes \
                   only; Carcara has no integer lia_generic rule, so the external checker is the Lean kernel",
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
        area: "datatypes",
        feature: "Carcara-checked is-tester COLLAPSE certificate \
                  (prove_qf_dt_unsat_alethe_via_simplification, is-tester arm): each \
                  is_C(K(args)) redex is abstracted to a truth-bit w; the test-fold \
                  (= (is_C (K args)) true/false), K==C iff true, is taken as a TRUSTED \
                  premise; the collapse to the bit-blast residual is closed by \
                  eq_transitive / cong+equiv1 + resolution",
        assurance: Assurance::Checked,
        evidence: "every STRUCTURAL step of the collapse is accepted (valid && !holey) by \
                   the external Carcara checker (datatype_tester_cert) — reserved \
                   !dttest/!dtcon heads are uninterpreted, the test-fold is an asserted \
                   premise; a tampered eq_transitive is REJECTED. Honest boundary: the \
                   is-tester FOLD stays a trusted premise (only its USE is certified); the \
                   field-unification axioms (distinctness/injectivity/acyclicity) stay \
                   trusted; the axiom-free Lean/kernel route is the row below (Carcara stays \
                   premise-based)",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "axiom-free Lean-kernel is-tester FOLD reconstruction \
                  (reconstruct_qf_dt_tester_to_lean_module, route A): a pure is_C(K(x)) \
                  contradiction (¬is_C(C x) TRUE fold, or is_C(K x) FALSE fold for K!=C) is \
                  reconstructed to a kernel-checked False where the datatype is modeled as a \
                  multi-constructor kernel inductive and is_C is its recursor eliminating into a \
                  computational Bool, so is_C(C x)=true / is_C(K x)=false is ι-reduction \
                  (Eq.refl Bool / a Bool.true!=Bool.false discriminator), NOT an assumed fold",
        assurance: Assurance::Checked,
        evidence: "the in-tree axeyum-lean-kernel infers the term to False (require_infers_false), \
                   and — when a real lean binary is present — the rendered module type-checks and \
                   `#print axioms` reports NO sorryAx and NO datatype-fold axiom (only the input \
                   tester assertion + carrier atoms), the family and Bool rendered as real Lean \
                   `inductive`s so Lean regenerates the recursor with ι (lean_crosscheck \
                   tester_fold_checks_in_real_lean). Honest boundary: is-tester fold this slice; \
                   constructor DISTINCTNESS is the axiom-free Lean row below; injectivity Lean \
                   route is deferred (needs noConfusion beyond ι); the Carcara premise-based route \
                   is unchanged",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "axiom-free Lean-kernel constructor DISTINCTNESS reconstruction \
                  (reconstruct_qf_dt_distinct_to_lean_module): an asserted equality C(x)=D(y) \
                  between DISTINCT constructors C!=D of the same datatype is reconstructed to a \
                  kernel-checked False by COMPOSING the is-tester ι-fold with a congruence \
                  transport — is_D(C x) ι-reduces to false, is_D(D y) to true; congrArg is_D h \
                  (an Eq.rec) lands at Eq Bool (is_D(C x)) (is_D(D y)) = (false=true); the \
                  existing Bool.true!=Bool.false discriminator (Bool.rec ι) closes it to False. \
                  NO noConfusion, NO assumed distinctness axiom",
        assurance: Assurance::Checked,
        evidence: "the in-tree axeyum-lean-kernel infers the term to False (require_infers_false), \
                   and — when a real lean binary is present — the rendered module type-checks and \
                   `#print axioms` reports NO sorryAx and NO datatype-distinctness axiom (only the \
                   input equality + carrier atoms), the family and Bool rendered as real Lean \
                   `inductive`s so Lean regenerates the recursor with ι (lean_crosscheck \
                   distinct_constructors_check_in_real_lean). A SAME-constructor equality \
                   C(x)=C(y) is DECLINED (no wrong False — that is injectivity's job). Honest \
                   boundary: distinctness this slice; constructor INJECTIVITY is the axiom-free \
                   Lean row below; the Carcara premise-based distinctness route is unchanged",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "axiom-free Lean-kernel constructor INJECTIVITY reconstruction \
                  (reconstruct_qf_dt_injective_to_lean_module): a same-constructor equality \
                  C(x)=C(y) plus a conflicting field disequality ¬(x_i=y_i) is reconstructed to a \
                  kernel-checked False through the SELECTOR route (the field-projection analogue \
                  of distinctness's is-tester discriminator) — the i-th field selector over the \
                  family (datatype_family_selector) gives sel_i(C x) ι-reduces to x_i and \
                  sel_i(C y) to y_i; congrArg sel_i h (an Eq.rec) lands at \
                  Eq α (sel_i(C x)) (sel_i(C y)) = (x_i=y_i); applying the input field \
                  disequality ¬(x_i=y_i) to it closes to False. NO noConfusion, NO assumed \
                  injectivity axiom",
        assurance: Assurance::Checked,
        evidence: "the in-tree axeyum-lean-kernel infers the term to False (require_infers_false), \
                   and — when a real lean binary is present — the rendered module type-checks and \
                   `#print axioms` reports NO sorryAx, NO noConfusion and NO datatype-injectivity \
                   axiom (only the input equality, the field disequality + carrier atoms), the \
                   family and Bool rendered as real Lean `inductive`s so Lean regenerates the \
                   recursor with ι (lean_crosscheck injective_field_mismatch_check_in_real_lean). A \
                   DISTINCT-constructor equality C(x)=D(y) is left to distinctness, and a \
                   same-constructor equality with NO conflicting field is DECLINED (no wrong \
                   False). Honest boundary: injectivity is one of the four axiom-free Lean \
                   field-axiom routes (is-tester + distinctness + injectivity + acyclicity, the \
                   row below); the Carcara premise-based injectivity route is unchanged",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "axiom-free Lean-kernel datatype ACYCLICITY reconstruction \
                  (reconstruct_qf_dt_acyclic_to_lean_module): a single-level containment cycle \
                  x = C(.. x ..) over a recursive datatype is reconstructed to a kernel-checked \
                  False by a SIZE argument — NO well-founded recursion, NO assumed acyclicity \
                  axiom. The datatype is modeled as a recursive kernel inductive \
                  (add_recursive_datatype_family, the tail field is the inductive's own sort); a \
                  size measure size:D->Nat (recursive_datatype_size) gives size(C .. x ..) ι-reduces \
                  to Nat.succ(size x); congrArg size hx (an Eq.rec) lands Eq Nat (size x) \
                  (Nat.succ (size x)); and n != Nat.succ n — proven BY INDUCTION on Nat (a \
                  Nat.zero != Nat.succ discriminator + Nat.succ injectivity via a predecessor \
                  selector, all Nat.rec into Prop) — closes it to False",
        assurance: Assurance::Checked,
        evidence: "the in-tree axeyum-lean-kernel infers the term to False (require_infers_false), \
                   and — when a real lean binary is present — the rendered module type-checks and \
                   `#print axioms` reports NO sorryAx and NO acyclicity axiom (only the input cycle \
                   equality + carrier atoms), the recursive datatype family, Nat and Bool rendered \
                   as real Lean `inductive`s so Lean regenerates the recursors with ι \
                   (lean_crosscheck acyclicity_cycle_check_in_real_lean, both orientations). A \
                   finite (non-cyclic) list x = C(h, nil) is DECLINED (no wrong False). Honest \
                   boundary: acyclicity COMPLETES the QF_DT field-axiom Lean chain (is-tester + \
                   distinctness + injectivity + acyclicity all axiom-free Lean); single-level \
                   cycles this slice (multi-step cycles x=C(..y..), y=C(..x..) deferred)",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "Carcara-checked constructor DISTINCTNESS certificate \
                  (prove_qf_dt_distinct_alethe_carcara): an asserted (= (C x..) (D y..)) with \
                  distinct C!=D is refuted by COMPOSING the certified is-tester collapse with \
                  congruence — cong lifts the equality under is_C, the two is-tester folds give \
                  is_C(C x..)=#b1 and is_C(D y..)=#b0, and eq_transitive forces #b1=#b0 (evaluate \
                  + equiv1 + false + resolution close to the empty clause)",
        assurance: Assurance::Checked,
        evidence: "every STRUCTURAL step (cong/eq_transitive/resolution/evaluate/equiv1/false) is \
                   accepted (valid && !holey) by the external Carcara checker \
                   (datatype_distinct_cert) — reserved !dttest/!dtcon heads are uninterpreted, the \
                   constructor equality and the two is-tester folds are asserted premises; a \
                   tampered eq_transitive chain is REJECTED. Honest boundary: the constructor \
                   equality and the is-tester folds stay TRUSTED premises (only the distinctness \
                   reasoning that distinct C!=D forces #b1=#b0 is certified); injectivity and \
                   acyclicity stay trusted/deferred; nullary constructors are out of scope; the \
                   Lean/kernel reconstruction route is deferred (Carcara-only)",
        reference: "ADR-0022",
    },
    Capability {
        area: "datatypes",
        feature: "Carcara-checked constructor INJECTIVITY certificate \
                  (prove_qf_dt_injective_alethe_carcara): an asserted (= (C x..) (C y..)) with the \
                  SAME C plus a conflicting field disequality (not (= x_i y_i)) is refuted by \
                  COMPOSING the certified select-over-construct fold with congruence — cong lifts \
                  the equality under sel_i, the two select folds give sel_i(C x..)=x_i and \
                  sel_i(C y..)=y_i, and eq_transitive forces (= x_i y_i) (resolution against the \
                  disequality closes to the empty clause)",
        assurance: Assurance::Checked,
        evidence: "every STRUCTURAL step (cong/eq_transitive/resolution) is accepted (valid && \
                   !holey) by the external Carcara checker (datatype_injective_cert) — reserved \
                   !dtsel/!dtcon heads are uninterpreted, the constructor equality, the field \
                   disequality and the two select folds are asserted premises; a tampered eq_transitive \
                   chain / wrong-field projection is REJECTED. Honest boundary: the constructor \
                   equality, the field disequality and the select folds stay TRUSTED premises (only \
                   the injectivity reasoning that same-C equality forces (= x_i y_i) is certified); \
                   distinct-constructor equalities are declined (distinctness's job); acyclicity stays \
                   trusted/deferred (needs induction); nullary constructors are out of scope; the \
                   Lean/kernel reconstruction route is deferred (Carcara-only)",
        reference: "ADR-0022",
    },
    Capability {
        area: "quantifiers",
        feature: "finite-domain expansion + congruence-aware e-matching on the e-graph keystone \
                  (single/multi-variable, multi-pattern set-cover triggers, nested triggers) \
                  + the instantiation fixpoint loop + model-based instantiation (MBQI), now with \
                  MBP-DRIVEN instantiation: when scalar point-probing finds no falsifying value, the \
                  universal's negation (¬φ as an LRA/LIA conjunction) is projected via mbp_lra/mbp_lia \
                  from a witness sub-solve to synthesize a SYMBOLIC instantiation point (e.g. a witness \
                  symbolic in another variable, or a non-unit-coefficient witness the ±1 probe misses)",
        assurance: Assurance::SoundIncomplete,
        evidence: "complete over finite domains; otherwise sound refutation by instantiation \
                   (every instance body[x:=t] is entailed by ∀x.body for ANY ground t, so a ground UNSAT \
                   transfers; MBP/the sub-solve only CHOOSE a useful t — a bad choice adds a redundant-but-\
                   true instance, never an unsound one; SAT/no-progress is unknown-safe). E-matching is \
                   modulo the ground congruence (keystone EGraph::ematch)",
        reference: "ADR-0016/0032",
    },
    Capability {
        area: "quantifiers",
        feature: "justified lazy equality-clause scheduling over e-matched instances",
        assurance: Assurance::SoundIncomplete,
        evidence: "disjunctions of equality/disequality literals are evaluated against direct \
                   ground unit facts, recorded disequalities, and congruence closure. Any-true \
                   instances are suppressed; all-false and one-undetermined complete source \
                   instances are scheduled before unresolved/non-clausal fallback. No detached \
                   literal is asserted: the QF solver still receives only a genuine full universal \
                   instance, preserving evidence replay. A 256-match target schedules one instance \
                   and improves median optimized batch-plus-QF time 40.4%; the 54-row quantified-BV \
                   division is decision-identical to baseline. ADR-0117 adds source-bound checked \
                   detached units and ADR-0118 composes them across generated premises; direct \
                   online-SAT justifications remain open",
        reference: "ADR-0110",
    },
    Capability {
        area: "quantifiers",
        feature: "source-bound checked detached equality-clause propagation",
        assurance: Assurance::Checked,
        evidence: "a public arena-bound certificate carries the untouched universal, ordered \
                   binding tuple, exact complete source instance, detached equality/disequality \
                   literal, and every false sibling with sorted original-ground reasons. A fresh \
                   checker reconstructs the instance, verifies the unique unit shape, and replays \
                   each sibling from only its named equality/disequality facts. Search explanations \
                   are untrusted; generated-premise reasons without checked provenance decline to \
                   the complete source instance. \
                   On 128 matches with six false siblings, detached units reduce reachable DAG \
                   nodes 4,230 to 2,438 and tree nodes 10,121 to 4,745; optimized median QF time \
                   improves 8.250 to 3.226 ms and checked end-to-end time 11.301 to 9.886 ms. \
                   Non-equality theory literals, proof serialization, and direct online SAT \
                   insertion remain open",
        reference: "ADR-0117",
    },
    Capability {
        area: "quantifiers",
        feature: "bounded recursive provenance for generated quantifier ground premises",
        assurance: Assurance::Checked,
        evidence: "public exact-instance and recursive ground-derivation artifacts retain one \
                   derivation with every admitted generated equality/disequality. A fresh checker \
                   reconstructs every source substitution, requires an exact sorted table for all \
                   non-source named reasons, recursively checks prior detached implications, and \
                   replays each false sibling plus the complete unit clause. Missing, duplicate, \
                   unused, reordered, wrong-variant/conclusion, nested tampering, depth over 16, \
                   and node-budget exhaustion reject to complete-instance fallback. A six-stage \
                   target preserves UNSAT while reducing reachable query DAG nodes 54 to 17 and \
                   tree nodes 117 to 33. Direct online SAT insertion, non-equality antecedents, and \
                   serialized proof forms remain open",
        reference: "ADR-0118",
    },
    Capability {
        area: "quantifiers",
        feature: "checked equality clauses in a retained CDCL(T) quantifier session",
        assurance: Assurance::Checked,
        evidence: "the original ground Boolean/equality skeleton is encoded once. Before every \
                   generated batch, CDCL(T) and EUF backtrack to level zero while preserving \
                   permanent and learned clauses, activities, and phases. Exact-instance or \
                   recursively propagated ground derivations are independently rechecked before \
                   complete equality clauses or detached units enter the live database; new atoms \
                   are appended in root scope with matching SAT/theory indexes. Online SAT only \
                   resumes matching, and online UNSAT becomes a product verdict only after the \
                   ordinary QF solver refutes the exact admitted ground set. Unsupported, tampered, \
                   mismapped, or over-budget sessions fall back. A six-stage target cuts QF rebuilds \
                   from 7 to 2 and improves optimized median end-to-end time from 0.560 to 0.351 ms \
                   (1.60x), with public quantified-BV/LIA decisions unchanged. Non-equality \
                   antecedents, online proof serialization, and SAT-trail-driven matching remain open",
        reference: "ADR-0119",
    },
    Capability {
        area: "quantifiers",
        feature: "scoped SAT-candidate equality guidance for nested e-matching",
        assurance: Assurance::Checked,
        evidence: "when ordinary source matching reaches a fixpoint, true equality atoms from the \
                   retained SAT candidate are merged only inside one matching-e-graph scope. Existing \
                   exact declaration/argument paths queue affected top applications and a reverse \
                   pattern-to-quantifier index joins only impacted quantifiers. Concrete binding \
                   tuples are materialized before pop; candidate equalities never enter explanation \
                   maps, detached-literal reasons, evidence, or another branch. Only complete exact \
                   source instances leave the scope, are independently rechecked, and enter ADR-0119's \
                   retained clause gate; product UNSAT still requires ordinary QF replay. A nested-\
                   trigger target moves Unknown to UNSAT and improves optimized median time from 0.573 \
                   to 0.148 ms (3.87x). A 64-pattern target scans 1 pattern/application, agrees with \
                   full matching, and improves median 5.478 to 4.329 ms (1.27x). Equality/work caps \
                   decline safely. High-frequency assignment callbacks, non-equality antecedents, and \
                   online proof serialization remain open",
        reference: "ADR-0120",
    },
    Capability {
        area: "quantifiers",
        feature: "shared incremental e-matching session with interned trigger patterns and batched \
                  graph indexes",
        assurance: Assurance::SoundIncomplete,
        evidence: "one quantified refutation attempt infers and translates every trigger once, \
                   interns structurally identical patterns, incrementally registers only appended \
                   ground assertions/equalities in one retained e-graph, and executes all unique \
                   patterns against one round-local class/application index. Public one-shot witness \
                   APIs remain complete, and only genuine full source instances reach the QF replay \
                   gate. A 32-quantifier/256-term target returns the identical 8,192 tuples and \
                   improves median optimized matching 17.477 to 0.974 ms (17.9x); the 54-row \
                   quantified-BV division is decision-identical. Bytecode, inverted parent paths, \
                   relevance/generation filters, and direct on-merge delta propagation remain open",
        reference: "ADR-0111",
    },
    Capability {
        area: "quantifiers",
        feature: "revision-checked persistent e-match indexes and root-symbol candidate queues",
        assurance: Assurance::SoundIncomplete,
        evidence: "add-only e-graph growth extends retained class/application indexes from the new \
                   node suffix and dirties only patterns whose root declaration gained an \
                   application. Real merges and scope rollback revision-invalidate root-keyed \
                   indexes; quantifier sessions conservatively rematch every pattern after a merge. \
                   Fresh/indexed matching is exact across growth, nested congruence, and rollback. \
                   A 64-root/4,096-term target returns identical complete tuples while executing 1 \
                   instead of 64 patterns and improves optimized median second-round matching from \
                   2.555 to 0.311 ms (8.2x). Public quantified-BV/LIA decisions and replay are \
                   unchanged. ADR-0113 adds selective on-merge inverted paths; exact path-shape and \
                   relevance/generation filters remain open",
        reference: "ADR-0112",
    },
    Capability {
        area: "quantifiers",
        feature: "merge-incremental e-match indexes and inverted-parent trigger queues",
        assurance: Assurance::SoundIncomplete,
        evidence: "every real e-class union, including congruence cascades, enters a deterministic \
                   journal consumed by retained matching indexes without a graph rebuild. Raw \
                   applications remain operator-indexed and are canonicalized only for selected \
                   roots. Quantifier sessions walk transitive e-class parent links from changed \
                   equality endpoints and rematch only reached trigger declarations; cached and \
                   multi-pattern substitutions join through current roots. Matching preserves \
                   distinct substitutions from explicitly equal applications with unequal \
                   arguments. Direct, nested, repeated-variable, ground-subpattern, add-plus-merge, \
                   recursive-cycle, rollback, and full-rematch parity gates pass. A 64-root/4,096-\
                   term complete-round target executes 1 instead of 64 patterns and improves \
                   optimized median merge-round time from 2.231 to 0.151 ms (14.8x). Public \
                   quantified-BV/LIA decisions and replay are unchanged. ADR-0114 adds exact \
                   declaration/argument path tries; class-label and relevance/generation filters \
                   remain open",
        reference: "ADR-0113",
    },
    Capability {
        area: "quantifiers",
        feature: "compiled shared e-match parent-path tries",
        assurance: Assurance::SoundIncomplete,
        evidence: "every interned pattern occurrence contributes its outward (parent declaration, \
                   argument index) path to one deterministic flat trie with shared prefixes and \
                   deduplicated terminals. Merge lookup pairs e-class roots with trie states and \
                   follows only compatible parent arguments, remaining cycle-safe while selecting \
                   exact path terminals. Add-node root queues and current-root cached joins remain \
                   unchanged. Direct/nested/repeated/ground/add-plus-merge/equal-application parity, \
                   divergent declarations and argument positions, duplicate paths, multiple starts, \
                   cycles, and declaration/full-rematch comparisons pass. A 64-pattern/4,096-term \
                   target with one shared trigger root executes 1 rather than 64 patterns and \
                   improves optimized median complete-round time from 12.777 to 0.386 ms (33.1x). \
                   Public quantified-BV/LIA decisions and replay are unchanged. ADR-0115 adds \
                   exact class-label and nullary ground-argument filters; relevance and generation \
                   filters remain open",
        reference: "ADR-0114",
    },
    Capability {
        area: "quantifiers",
        feature: "exact e-class label and nullary ground-argument path filters",
        assurance: Assurance::SoundIncomplete,
        evidence: "e-class roots retain backtrackable sorted declaration sets. Path terminals \
                   require the changed start class to contain a non-variable occurrence's top \
                   declaration, while transitions may require a candidate parent's direct nullary \
                   ground sibling class to contain that constant declaration. Compound ground \
                   siblings remain deliberately unfiltered. Unfiltered, class-only, ground-only, \
                   and combined modes return identical complete tuples. On 64 same-shape patterns \
                   over 4,096 applications, the filters reduce reached terminals from 64 to 8, 8, \
                   and 1 respectively; optimized medians are 13.453, 2.314, 1.991, and 0.404 ms, \
                   making the combined route 33.3x faster than unfiltered lookup. Public \
                   quantified-BV/LIA decisions, replay, and evidence APIs are unchanged. Relevance \
                   and generation-cost scheduling remain open; ADR-0116 adds exact top-application \
                   delta queues",
        reference: "ADR-0115",
    },
    Capability {
        area: "quantifiers",
        feature: "generation-delta top-application e-match queues",
        assurance: Assurance::SoundIncomplete,
        evidence: "initial matching scans complete root-declaration application sets, then \
                   retained sessions append matches only from newly created or filtered \
                   merge-reached top applications. Candidate-restricted matching uses the same \
                   recursive class matcher; prior substitutions remain valid under monotonic \
                   unions and joins canonicalize current roots. Every bridge term is active-source \
                   relevant by construction, so a separate relevance bit would currently filter \
                   nothing. On one affected pattern over 4,096 outer applications, full and delta \
                   routes return identical tuples while scanning 4,096 and 1 top applications; \
                   optimized medians improve from 0.370 to 0.122 ms (3.03x). Public quantified-BV/\
                   LIA decisions, replay, and evidence APIs are unchanged. Generation-cost \
                   scheduling remains separate",
        reference: "ADR-0116",
    },
    Capability {
        area: "quantifiers",
        feature: "evaluator-replayed scalar counterexamples for closed quantifier-free universals",
        assurance: Assurance::Checked,
        evidence: "untrusted search replaces the universal binders with fresh constants and solves \
                   the negated body, but the certificate carries only original binder IDs and typed \
                   values. The independent checker rejects open/nested/UF/non-scalar forms and \
                   evaluates the untouched original body, accepting only Bool(false). This upgrades \
                   ARI176e1 and issue5279-nqe from bare UNSAT; ADR-0102 additionally reconstructs \
                   both by genuine dependent-product elimination over the Int/Bool preludes and \
                   kernel-checked integer normalization, with no theorem-specific refuter axiom. \
                   ADR-0139 applies the same checked certificate boundary to closed Bool/BV \
                   universals: exact typed constructor values instantiate the untouched theorem, \
                   and an explicit evaluated-AIG proof refutes its body. `qbv-simp` raises the \
                   exact public quantified-BV audit to 49/54 dominant and Lean UNSAT 13/18. \
                   The quantified-LIA audit is checked/certified 11/11, Lean-checked 7/7 UNSAT, and \
                   has eleven dominant candidates with empty trust ledgers and DISAGREE=0. Open \
                   formulas, general QE, function counterexamples, and broader Lean reconstruction \
                   remain open",
        reference: "ADR-0100/0102/0139",
    },
    Capability {
        area: "quantifiers",
        feature: "checked finite equality partitions for closed nested Bool/Int quantifiers",
        assurance: Assurance::Checked,
        evidence: "each Int binder is admitted only when every occurrence is a direct equality \
                   against an explicit constant; those constants plus one deterministic other value \
                   are a complete behavioral quotient. Search expands in a clone, while the checker \
                   independently recursively evaluates the untouched original formula under a hard \
                   representative-case cap. ADR-0106 reconstructs the one-literal-per-Int-binder \
                   subclass with genuine Bool/Int quantifiers, Bool.rec, and explicit integer \
                   equality decidability; finite evaluation guides proof search but is not admitted. \
                   This certifies and Lean-checks cbqi-sdlx-fixpoint-3-dd. The current quantified-LIA \
                   audit is 11/12 decided, checked/certified 11/11, Lean-checked 7/7 UNSAT, with \
                   eleven dominant candidates, DISAGREE=0, and zero trust holes. Multi-constant \
                   partitions, affine uses, free symbols, and all three large mixed-binder ITE rows \
                   remain outside this equality-partition route; ADR-0107 separately decides the \
                   two SAT rows",
        reference: "ADR-0101/0106",
    },
    Capability {
        area: "quantifiers",
        feature: "checked targeted Presburger CEGQI UNSAT: exact Euclidean-residue and \
                  positive-slope piecewise affine-growth universals",
        assurance: Assurance::Checked,
        evidence: "search only proposes genuine universal instances and requires an ordinary QF \
                   refutation; separate original-IR checkers re-match the complete theorem and \
                   compare typed certificates without calling search or the broad solver. \
                   Euclidean div/mod witnesses certify clock-3/clock-10; two consecutive \
                   div-derived affine-growth witnesses certify repair-const-nterm. ADR-0104 adds \
                   one explicit standard Euclidean-decomposition theorem to the trusted Int prelude, \
                   then eliminates its existential witnesses to reconstruct both clock rows without \
                   div/mod proof operations or query-specific axioms. The quantified-LIA audit is \
                   checked/certified 11/11, Lean-checked 7/7 UNSAT, and has eleven dominant candidates \
                   with DISAGREE=0 and no trust holes. ADR-0105 reconstructs the full checked \
                   affine-growth class constructively through guarded exact ite semantics, two \
                   consecutive instances, and positive-slope monotonicity, adding no new axiom. \
                   Broad arithmetic CEGQI remains",
        reference: "ADR-0095/0097/0104/0105",
    },
    Capability {
        area: "quantifiers",
        feature: "checked nested-XOR integer universal refutation by hierarchical instantiation",
        assurance: Assurance::Checked,
        evidence: "untrusted search instantiates two outer pivots, uses the resulting false XOR \
                   operand to expose one positive nested universal, and proposes one off-pivot \
                   ground instance; the QF solver must refute it. A separate original-IR checker \
                   re-matches the exact two-outer/one-inner Int theorem with distinct constant \
                   selector branches. This certifies issue4433-nqe; the current quantified-LIA \
                   audit is 12/12 decided and checked/certified 12/12, with DISAGREE=0 and no \
                   incomplete rows. \
                   ADR-0103 rechecks that certificate and reconstructs the complete signed/swapped \
                   class through three genuine universal applications, kernel-checked Iff/XOR \
                   reasoning, and integer normalization. With ADR-0104's separate residue route, the \
                   current audit is Lean-checked 8/8 UNSAT with twelve dominant candidates. General \
                   polarity-aware nested QE/QSAT remains open",
        reference: "ADR-0099/0103",
    },
    Capability {
        area: "quantifiers",
        feature: "checked affine and reflexive scalar Skolem SAT witnesses: deterministic typed \
                  certificates in Model, with canonical original-assertion replay for prenex \
                  `forall* exists`, exact BV identities, and one positive-`or` guarded unit-gap schema",
        assurance: Assurance::Checked,
        evidence: "witness search is untrusted; certificates own an arena-stable affine recipe over \
                   validated original-arena atoms. `check_model` independently re-matches binder \
                   IDs/sorts and witness vocabulary, materializes only in a private clone, and accepts \
                   Boolean affine/reflexive tautologies (ADR-0096), the exact guarded unit-gap theorem \
                   (ADR-0098), or one same-width BV universal variable with coefficient one and zero \
                   offset (ADR-0121). BV replay recognizes only reflexive `bvsle`/`bvule` (plus equality); \
                   modular affine recipes and composite witnesses decline. `issue4328-nqe` moves the \
                   public quantified-BV slice to 30 SAT / 9 UNSAT / 4 unknown / 11 unsupported, with \
                   zero errors, disagreement, or replay failures. Its evidence is independently checked, \
                   has no trust holes, and is a dominant candidate. Piecewise/general Skolem functions \
                   remain open",
        reference: "ADR-0096/0098/0121",
    },
    Capability {
        area: "quantifiers",
        feature: "checked vacuous BV equality-guard models below direct Bool/BV alternation",
        assurance: Assurance::Checked,
        evidence: "untrusted search proposes an exact-width witness for one outer BV existential. \
                   A separate original-IR checker requires a direct nonempty unique Bool/BV quantifier \
                   prefix, a root implication, and an antecedent equating that exact outer binder to \
                   one same-width constant; SAT is credited only when the witness differs from the \
                   constant. The consequent remains opaque because the false antecedent proves the \
                   implication for every nested assignment. `issue5365-nqe` moves the public \
                   quantified-BV slice to 31 SAT / 9 UNSAT / 3 unknown / 11 unsupported with 40/40 \
                   decisions evidence-certified and checked, no trust holes on the target, and zero \
                   disagreement, error, or replay failure. General free-BV models and QE/QSAT remain open",
        reference: "ADR-0122",
    },
    Capability {
        area: "quantifiers",
        feature: "checked free-Boolean models for positive universal Bool/Int assertions and \
                  Boolean-discharged opaque BV closures",
        assurance: Assurance::Checked,
        evidence: "untrusted search erases quantifiers to propose a complete free-Boolean model. \
                   The independent checker retains untouched original assertions, exhaustively \
                   handles bound Booleans or drops only positive universal binders, substitutes the \
                   carried original-symbol values, exactly lifts integer ite, and requires a \
                   source-bound LIA-DPLL refutation of the negated closure. Arithmetic cores are \
                   rechecked exactly; large propositional closures carry source-matched DIMACS/DRAT. \
                   Concrete counterexamples generalize only search blocking cubes and cannot grant \
                   SAT. This replay-checks 015-psyco-pp and psyco-196, moving quantified LIA to \
                   11/12 with checked/certified and dominant 11/11, DISAGREE=0, and no trust holes. \
                   ADR-0123 additionally admits Bool/Int/BV syntax but keeps every non-reflexive BV \
                   predicate opaque; only a decisive carried Boolean branch can prove the original \
                   closure true, and unresolved BV closures decline before the LIA fallback. This \
                   recovers `model_6_1_bv`, moving quantified BV to 32 SAT / 9 UNSAT / 2 unknown / \
                   11 unsupported with 41/41 checked/certified decisions and zero disagreement, \
                   error, or replay failure. Negative quantifier contexts, relevant free BV values, \
                   functions, and general QSAT remain outside the route",
        reference: "ADR-0107/0123",
    },
    Capability {
        area: "quantifiers",
        feature: "checked complete free-BV models for affine-LSB universals and directly negated \
                  universal witnesses",
        assurance: Assurance::Checked,
        evidence: "untrusted search enumerates all low-bit assignments for at most eight free BV \
                   symbols and uses the QF_BV solver only to propose complete witnesses. A separate \
                   original-IR checker requires exact sorted free-symbol coverage, unique direct \
                   Bool/BV prefixes, 128-binder/4,096-node/256-depth caps, and no functions or \
                   non-Bool/BV terms. Positive universals are proved by exact affine GF(2) LSB \
                   interpretation; directly negated universals replay complete typed binder values \
                   through the ground evaluator. `smtcomp-qbv-053118` moves unsupported to replayed \
                   SAT. The public quantified-BV slice is 33 SAT / 17 UNSAT / 0 unknown / 4 \
                   unsupported with 50/50 evidence-certified/rechecked decisions, 41 dominant \
                   candidates, zero disagreement/error/replay failure, and an empty target trust \
                   ledger. Nonlinear low-bit products, nested alternation, functions, arrays, \
                   arithmetic, broad BV model construction, and Lean SAT reconstruction remain open",
        reference: "ADR-0130",
    },
    Capability {
        area: "quantifiers",
        feature: "checked complete free-BV models for directly negated signed-interval existential \
                  implications",
        assurance: Assurance::Checked,
        evidence: "untrusted search asks QF_BV only for a complete free-symbol candidate satisfying \
                   extracted sufficient ground obligations. A separate original-IR checker requires \
                   one directly negated existential implication, exactly one binder-dependent \
                   antecedent conjunct, exact signed lower/upper bounds, and exactly one signed cap \
                   leaf. It evaluator-replays every other antecedent leaf to true and the untouched \
                   division-bearing conclusion to false, rejects empty intervals, and proves signed \
                   lower <= upper <= cap with arbitrary-width two's-complement comparison. \
                   `intersection-example-onelane` moves unsupported to replayed SAT. The public \
                   quantified-BV slice is 34 SAT / 17 UNSAT / 0 unknown / 3 unsupported with 51/51 \
                   evidence-certified/rechecked decisions, 42 dominant candidates, zero \
                   disagreement/error/replay failure, and an empty target trust ledger. Arbitrary \
                   binder arithmetic, implication shapes, alternation, functions/arrays, broad BV \
                   model construction, and Lean SAT reconstruction remain open",
        reference: "ADR-0131",
    },
    Capability {
        area: "quantifiers",
        feature: "checked complete free-BV models for directly negated zero-product existential \
                  implications",
        assurance: Assurance::Checked,
        evidence: "untrusted search asks QF_BV only for a complete free-symbol candidate satisfying \
                   extracted ground obligations. A separate original-IR checker requires one direct \
                   negated existential implication, exactly one binder-dependent antecedent \
                   conjunct, and an inner implication whose conclusion is signed nonnegativity of \
                   a binary product. One direct binder-free signed-division factor must \
                   evaluator-replay to exact zero, the other factor must contain the unique binder, \
                   and the comparison bound must be a same-width literal zero. The nonlinear factor \
                   and inner premise are never interpreted; every other antecedent leaf and the \
                   untouched false conclusion replay under the complete model. `gn-wrong-091018` \
                   moves unsupported to replayed SAT. The public quantified-BV slice is 35 SAT / 17 \
                   UNSAT / 0 unknown / 2 unsupported with 52/52 evidence-certified/rechecked \
                   decisions, 43 dominant candidates, zero disagreement/error/replay failure, and \
                   an empty target trust ledger. General nonlinear reasoning, arbitrary zero \
                   expressions/comparisons, alternation, functions/arrays, broad BV model \
                   construction, and Lean SAT reconstruction remain open",
        reference: "ADR-0132",
    },
    Capability {
        area: "quantifiers",
        feature: "checked residual-QF_BV positive-universal models with complete free-Booleans",
        assurance: Assurance::Checked,
        evidence: "bounded CEGIS may add concrete source instances from QF_BV counterexamples, \
                   but they remain search-only. A separate checker admits only positive Bool/BV \
                   universals with unique binders disjoint from free symbols, no applications or \
                   free BVs, and exact sorted \
                   coverage of every free Boolean under 128-binder/4,096-node/256-depth caps. It \
                   substitutes the complete free-Boolean model into a clone of the untouched \
                   source, opens the universals, negates the exact residual, and rechecks its \
                   source-bound DRAT/LRAT proof. `psyco-001-bv` moves unsupported to replayed SAT. \
                   The public quantified-BV slice is 36 SAT / 17 UNSAT / 0 unknown / 1 unsupported \
                   with 53/53 evidence-certified/rechecked decisions, 44 dominant candidates, zero \
                   disagreement/error/replay failure, and an empty target trust ledger. Negative \
                   quantifiers, existentials, functions/arrays, free BVs, mixed arithmetic, general \
                   QSAT, and Lean SAT reconstruction remain open",
        reference: "ADR-0133",
    },
    Capability {
        area: "quantifiers",
        feature: "checked query-scoped QF_BV positive-universal instance sets",
        assurance: Assurance::Checked,
        evidence: "bounded CEGIS may select complete positive-universal Bool/BV source instances, \
                   but candidate models, quantifier erasure, and instance selection remain \
                   search-only. A separate checker binds the exact ordered query, re-admits every \
                   quantified assertion under ADR-0133's source contract, validates 1 through 256 \
                   unique complete typed binding tuples, rebuilds each source instance, and \
                   rechecks DRAT/LRAT for exactly the ground QF_BV weakening plus those instances. \
                   Any heuristic candidate block disables certification. `psyco-107-bv` moves \
                   unsupported to certified UNSAT. The public quantified-BV slice is 36 SAT / 18 \
                   UNSAT / 0 unknown / 0 unsupported with 54/54 evidence-certified/rechecked \
                   decisions, 45 dominant candidates, zero disagreement/error/replay failure, and \
                   an empty target trust ledger. General QSAT, negative quantifier contexts, \
                   existentials, functions/arrays, free BVs in quantified assertions, mixed \
                   arithmetic, wasm proof export, and broader Lean reconstruction remain open",
        reference: "ADR-0134",
    },
    Capability {
        area: "quantifiers",
        feature: "kernel-checked query-scoped Bool/BV source instances",
        assurance: Assurance::Checked,
        evidence: "ADR-0134's admitted top-level conjunction shape reconstructs with untouched \
                   source axioms, typed Bool/BV universal binders, exact constructor-witness \
                   applications, independently checked source assumptions, structurally shared \
                   AIG lowering, and a compact named-gate Alethe refutation. Classical \
                   double-negation normalization is explicit and kernel-checked. A two-instance \
                   theorem passes the in-tree kernel and is registered in the external-Lean \
                   representative (the current host has no `lean` binary). ADR-0137's DAG-linear \
                   dependency walk and bounded closed serializer chunks let the release-only \
                   `psyco-107-bv` stress gate finish in 102--107 seconds below a 3 GiB process limit, \
                   raising public Lean coverage to 9/18. Negative contexts, existentials, functions/arrays, free BVs in \
                   quantified assertions, mixed arithmetic, general QSAT, and Lean SAT \
                   reconstruction remain open",
        reference: "ADR-0135/0137",
    },
    Capability {
        area: "quantifiers",
        feature: "source-bound counterexamples for closed Bool/BV `forall+ exists+` alternation",
        assurance: Assurance::Checked,
        evidence: "untrusted search solves an outer-only implication antecedent and deterministic \
                   one-binder perturbations. A certificate is admitted only when the independent \
                   checker validates one closed unique Bool/BV `forall+ exists+` prefix, substitutes \
                   every carried outer value into the exact source matrix, deterministically freshens \
                   the existential binders, regenerates the residual QF_BV CNF, and rechecks its \
                   source-bound DRAT/LRAT proof. ADR-0125 scales only the total-binder cap from 128 to \
                   1,024 while retaining the 4,096-node matrix cap. `small-pipeline-fixpoint-3` and \
                   `bug802` move unknown to certified UNSAT in medians 63.692 and 19.804 ms. The public \
                   quantified-BV slice is 32 SAT / 11 UNSAT / 0 unknown / 11 unsupported with 43/43 \
                   checked/certified decisions, zero disagreement, error, or replay failure, and empty \
                   target trust ledgers. The direct-Z3 alternation matrices cover 80 cases, including \
                   16 controls whose 160 outer binders exceed ADR-0124's original cap. The QF_BV \
                   term-to-CNF reduction keeps its established explicit trust boundary; general QSAT, \
                   open formulas, functions, arrays, arithmetic, and Lean reconstruction remain open",
        reference: "ADR-0124/0125",
    },
    Capability {
        area: "quantifiers",
        feature: "evaluator-replayed witnesses for closed Bool/BV negated existentials",
        assurance: Assurance::Checked,
        evidence: "untrusted search freshens one exact top-level `not (exists+ body)` and solves \
                   the positive QF body. A separate checker admits at most 128 unique Bool/BV \
                   binders and a 4,096-node closed quantifier-free Bool/BV body, validates complete \
                   binding IDs/order/sorts, and evaluates the untouched original body directly; only \
                   `Bool(true)` certifies that the negated assertion is false. `NUM878`, `ari-syqi`, \
                   and `ari118-bv-2occ-x` move unsupported to certified UNSAT in median 3/0/3 ms. \
                   The public quantified-BV slice is 32 SAT / 14 UNSAT / 0 unknown / 8 unsupported \
                   with 46/46 checked/certified decisions, zero disagreement, error, or replay failure, \
                   and empty target trust ledgers. The complete direct-Z3 suite covers 1,400 cases and \
                   controls. Open bodies, functions, arrays, arithmetic binders, nested quantifiers, \
                   and broader QSAT remain open. ADR-0138 rechecks the certificate and constructs \
                   genuine typed `Exists.intro` witnesses against the untouched negated source \
                   axiom. Small bodies carry logical gate proofs; large bodies use shared \
                   computational Bool definitions and local AIG lets, all reduced by the kernel. \
                   The three-row release gate completes in 12.43 seconds under 4 GiB, raising the \
                   exact public audit to 48/54 dominant and Lean UNSAT 12/18",
        reference: "ADR-0126/0138",
    },
    Capability {
        area: "quantifiers",
        feature: "source-bound conjunctive Bool/BV universal instances",
        assurance: Assurance::Checked,
        evidence: "untrusted search tries defaults and deterministic same-sort source constants \
                   for one unique universal reached only through top-level conjunction nodes. The \
                   checker validates the source path, unique prefix, complete typed bindings, exact \
                   substitution, 128-binder/4,096-node caps, and the DRAT/LRAT proof regenerated for \
                   the entire weakened QF_BV source assertion. `cond-var-elim-binary` moves unsupported \
                   to checked UNSAT in median 0.364 ms. The public quantified-BV slice is 32 SAT / \
                   15 UNSAT / 0 unknown / 7 unsupported with 47/47 checked/certified decisions, zero \
                   disagreement, error, or replay failure, and an empty target trust ledger. The \
                   complete direct-Z3 suite covers 1,464 cases and controls. Non-conjunctive contexts, \
                   multiple selected universals, nested quantifiers, functions, arrays, arithmetic, \
                   general QSAT, and Lean reconstruction remain open",
        reference: "ADR-0127",
    },
    Capability {
        area: "quantifiers",
        feature: "evaluator-replayed universal counterexamples below vacuous Bool/BV existentials",
        assurance: Assurance::Checked,
        evidence: "untrusted search freshens only the universal binders and solves the negated QF_BV \
                   body. A separate original-IR checker requires an exact nonempty `exists+ forall+` \
                   prefix with at most 128 unique Bool/BV binders and 4,096 source DAG nodes, proves \
                   the existential binders absent by admitting no body symbols except the universal \
                   binders, validates complete typed universal bindings, and evaluates the untouched \
                   body directly to false. `issue2031-bv-var-elim` moves unsupported to checked UNSAT \
                   in median 0.129 ms. The public quantified-BV slice is 32 SAT / 16 UNSAT / 0 unknown / \
                   6 unsupported with 48/48 checked/certified decisions, zero disagreement, error, or \
                   replay failure, and an empty target trust ledger. The cumulative direct-Z3 suite \
                   covers 1,592 cases and controls. Nonvacuous/open bodies, reversed or broader \
                   alternation, functions, arrays, arithmetic binders, general QSAT, and Lean \
                   reconstruction remain open",
        reference: "ADR-0128",
    },
    Capability {
        area: "quantifiers",
        feature: "source-bound paired Bool/BV existential witness transfer",
        assurance: Assurance::Checked,
        evidence: "untrusted search alpha-aligns one positive existential tuple with one negated \
                   existential tuple under exact shared ground premises. A separate checker validates \
                   both source paths, equal typed prefixes, 128-total-binder/4,096-source-node caps, \
                   and every target-body conjunct. Non-identical conjuncts require either a regenerated \
                   source-subset QF_BV DRAT/LRAT implication proof or the exact signed-add lemma \
                   `x<=s b && x+s<=s k => x+w<=s k`, with `0<=w<=s` and `b<=MAX_SIGNED-s` rechecked \
                   to exclude modular overflow. `nested9_true-unreach-call` moves unsupported to checked \
                   UNSAT in median 0.075 ms. The public quantified-BV slice is 32 SAT / 17 UNSAT / \
                   0 unknown / 5 unsupported with 49/49 checked/certified decisions, zero disagreement, \
                   error, or replay failure, and an empty target trust ledger. The cumulative direct-Z3 \
                   suite covers 1,720 cases and controls. Different premises, non-conjunctive polarity, \
                   unequal prefixes, nested quantifiers, functions, arrays, arithmetic, general QSAT, \
                   and Lean reconstruction remain open",
        reference: "ADR-0129",
    },
    Capability {
        area: "quantifiers",
        feature: "checked finite counterexample covers for positive universal Bool/Int UNSAT",
        assurance: Assurance::Checked,
        evidence: "untrusted search weakens positive universals to a ground Boolean skeleton, then \
                   generalizes concrete falsifying bound models to sufficient free-Boolean cubes. \
                   The independent checker regenerates every exact source instance from the original \
                   assertion and binder values, source-bound-refutes cube plus instance through \
                   LIA-DPLL/DRAT, and separately refutes the weakened skeleton plus every cube block. \
                   Certificates are bounded to 256 cases, 128 binders per case, 64 free Booleans, and \
                   one shared deadline; malformed, duplicate, incomplete, or tampered covers decline. \
                   The first Lean slice flattens original conjunctions, retains one genuine positive \
                   universal, applies each carried witness tuple, and closes a bounded excluded-middle \
                   tree with signed Boolean and normalized integer proofs. This decides 006-cbqi-ite \
                   and moves quantified LIA to 12/12 decided, certified, rechecked, and dominant, with \
                   Lean 8/8 UNSAT, DISAGREE=0, and no trust holes. ADR-0109 renders computational Bool \
                   as a real Lean inductive and deterministically hoists only repeated closed proof-DAG \
                   nodes; the target module shrinks from 151,845,067 to 2,682,977 bytes and reconstruction \
                   from 17.74 to 10.75 seconds without changing verdict or trust. Open-context sharing, \
                   general projection, alternation, functions, and multiple independent universal \
                   conjuncts remain open",
        reference: "ADR-0108/0109",
    },
    Capability {
        area: "quantifiers",
        feature: "model-based projection for LRA (mbp_lra): model-guided existential elimination of \
                  one real variable (Loos–Weispfenning) — the QE primitive Spacer/PDR uses for \
                  predecessor generalization",
        assurance: Assurance::Validated,
        evidence: "the LW selection is untrusted — VERIFY-BEFORE-RETURN: every projection F' is \
                   re-checked (M ⊨ F', variable absent, and F' ⇒ ∃x.F by per-literal check_with_lra \
                   UNSAT against the exact Fourier–Motzkin projection); declines (None) on any doubt \
                   (disjunctive-disequality case, overflow, non-LRA). No per-query certificate emitted",
        reference: "ADR-0048 (P2.6)",
    },
    Capability {
        area: "quantifiers",
        feature: "model-based projection for LIA (mbp_lia): the integer mirror of mbp_lra — model-guided \
                  existential elimination of one integer variable (Cooper/Omega), the QE primitive \
                  integer PDR / quantifier instantiation needs. Unit-coefficient slice exact (x-free \
                  passthrough, ±1 equality substitution, interval resolvents with exact strict→non-strict \
                  integer tightening + cross-feasibility); non-unit Cooper-divisibility cases declined",
        assurance: Assurance::Validated,
        evidence: "the selection is untrusted — VERIFY-BEFORE-RETURN: every projection F' is re-checked \
                   (M ⊨ F', variable absent, and F' ⇒ ∃x∈ℤ.F by per-literal check_with_lia_dpll UNSAT \
                   against an independent exact integer Omega projection); declines (None) on the \
                   divisibility boundary (|c|>1, no IR modulo the deciders interpret), disjunctive \
                   disequality, overflow, or non-LIA — a soundness fuzz over 400 LCG cases projected 29 / \
                   declined 285 with ZERO unsound. No per-query certificate emitted",
        reference: "ADR-0048 (P2.6)",
    },
    Capability {
        area: "QF_S (strings)",
        feature: "bounded strings + regex (BV-lowered); SMT-LIB front end wired for \
                  declare/literal/=/distinct + str.prefixof/suffixof/contains + str.at (const idx) \
                  + str.++ (const fold) + str.len (ADR-0052 linear marker decides; broader \
                  coupled word/length shapes may be unknown), \
                  str.to_code/from_code + substr/indexof/replace/replace_all/lex-compare/\
                  take/drop/to_int/from_int/is_digit + regex membership via API",
        assurance: Assurance::Experimental,
        evidence: "model replay through BV path; canonical-padding equality; length bound explicit; \
                   certified non-arena UNSAT routes follow ADR-0061",
        reference: "ADR-0025/0029/0052/0061",
    },
    Capability {
        area: "optimization",
        feature: "OMT — all three z3 modes (box, lexicographic, Pareto) over LIA + BV; \
                  weighted MaxSAT with a witnessing model; MILP (branch-and-bound over the \
                  arithmetic cores)",
        assurance: Assurance::Experimental,
        evidence: "each optimum/Pareto point certified by the underlying decision procedure \
                   per step (a confirmed-unsat domination query); deterministic point/push caps; \
                   out-of-fragment objectives degrade to Unknown instead of hard solver errors",
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
        feature: "symbolic memory and UF fallback: select/store and Op::Apply via \
                  check_with_memory plus check_assuming_with_memory one-shot branch queries \
                  (full dispatcher; syntactic same-index ROW hits, literal-distinct store \
                  misses, constant-array reads, and reducible array-valued ite reads can stay \
                  warm; reducible symbolic-address conditional ROW over store chains can also \
                  stay warm with original-term replay/core reporting; observed reads over \
                  supported store, constant-array, and array-ITE parents now retain private \
                  scalar owners plus one exact transitive scalar summary as dormant metadata; \
                  only candidate-false summaries become permanent CNF roots, reusing SAT state \
                  across checks while projecting only direct leaf owners; select reads over \
                  BV-indexed Bool/BV array symbols, including wide/BV256 index or element values, \
                  abstract to retained warm scalar variables with scoped select-congruence lemmas \
                  and replay-projected array models; scalar Bool/BV \
                  uninterpreted-function applications, including wide/BV256 argument or result values, \
                  abstract to retained warm variables with scoped congruence lemmas and \
                  replay-projected function interpretations; reads over scalar-keyed array-valued \
                  UF applications retain private array owners, enforce conditional argument/index \
                  congruence, and project full-value function results before replay; positive \
                  equality merges direct/application projection owners before function construction, \
                  while top-level disequality over supported structural parents uses one exact \
                  private diff index and two retained reads; top-level positive structural equality \
                  over supported store/constant/array-ITE parents uses cached private constructor \
                  owners, bounded equality observations, class-aware fixed-point realization, owner \
                  filtering, and replay; supported array equality atoms nested under scalar Boolean \
                  structure become private relation flags with guarded true-branch read equality, \
                  guarded false-branch diff witnesses, candidate-true-only owner merging/structural \
                  realization, filtering, and replay; direct, supported structural, and nested \
                  array-valued-application finite-array parameters key retained array-valued UF \
                  parents with scalar dependency retention, structural owner realization, \
                  replay-safe rewritten structural keys, relation-flag guarded congruence, \
                  filtering, and replay)",
        assurance: Assurance::Validated,
        evidence: "full dispatcher model replay; same-index/literal-distinct/const-array/array-ite/\
                   symbolic-ROW/select-congruence/scalar-UF/array-result-UF/array-relation/structural-equality/\
                   relation-flag/array-parameter assertion and branch warm replay; 816 solver units, 77 symbolic-execution tests, \
                   three 192-case warm/check_auto/Z3 matrices, the 64-seed structural-equality matrix, and the \
                   focused relation-flag and array-UF-parent suites pass, including nested \
                   array-valued application-key replay; the EVM scoreboard remains DISAGREE=0 and depth-32 \
                   warm improves from 30.933 to 11.257 ms, though direct ITE folding remains faster at \
                   0.405 ms; warm path refuses \
                   remaining deferred array/UF theories, including nested/extended array components",
        reference: "ADR-0010/0030/0086/0087/0088/0089/0090/0091/0092/0093/0094",
    },
    Capability {
        area: "symbolic execution",
        feature: "DFS path explorer (SymbolicExecutor): assume / branch fork query / \
                  enter+backtrack / generic CFG exploration harness with model-witnessed targets / \
                  checked CFG exploration with concrete witness replay hook / \
                  concrete test-input model / SymbolicMemory load/store helper plus automatic \
                  warm/memory assume/branch/model routing for array/UF path conditions and default \
                  CFG exploration / distinct test-suite enumeration (all-SAT) / \
                  optimize objective over the path condition (min/max, unsigned/signed BV + LIA)",
        assurance: Assurance::Validated,
        evidence: "models replay-checked vs path condition; CFG targets are returned only with \
                   replay-checked models and optionally bucketed by caller-supplied concrete replay; \
                   memory load helpers, scalar UF calls, and CFG queries stay warm when their reads \
                   reduce or scalar applications abstract, and route through the full dispatcher when \
                   unreduced; optimum certified by the underlying \
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
        feature: "unbounded safety proving by k-induction (prove_safety_k_induction; \
                  plus prove_safety_k_induction_with_memory for array/symbolic-memory \
                  state via eager elimination)",
        assurance: Assurance::SoundIncomplete,
        evidence: "Safe = base case (BMC, incl. memory BMC for select/store systems) + \
                   inductive-step UNSAT (unbounded); Reachable = replay-checked \
                   counterexample; non-inductive properties return Inconclusive, never a \
                   wrong Safe; focused BMC gates cover an inductive array property and a \
                   reachable symbolic-memory counterexample",
        reference: "ADR-0009/0010",
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
    Capability {
        area: "reachability",
        feature: "interpolation-based model checking (prove_safety_imc): McMillan IMC over QF_BV — \
                  proves unbounded safety by growing an interpolant-derived reachable over-approximation \
                  to a fixpoint (the first real consumer of the interpolation engine)",
        assurance: Assurance::Validated,
        evidence: "the interpolation fixpoint is UNTRUSTED — Safe only when the discovered invariant \
                   passes 3 check_auto-unsat checks (initiation, consecution, safety); Reachable only \
                   when BMC-confirmed; qf_bv_interpolant None / too-coarse over-approximation deepen k; \
                   all caps → Unknown",
        reference: "ADR-0048",
    },
    Capability {
        area: "reachability",
        feature: "CHC / Horn front-end (solve_horn): the standard SMT-LIB constrained-Horn input \
                  (HornClause/HornSystem, predicates = Bool-result functions) — solves single-predicate, \
                  ACYCLIC multi-predicate, AND MUTUALLY-RECURSIVE (cyclic) linear systems. SCC \
                  condensation (deterministic Tarjan over declaration order); a non-trivial SCC of \
                  sort-compatible members is merged into one self-recursive predicate over a \
                  control-tagged disjoint-union state, solved by the model-checking engines, then \
                  projected back per member; self-recursion + predecessor-invariant substitution as before. \
                  Also STRATIFIED-NONLINEAR bodies (≥2 atoms): every already-solved lower-stratum body \
                  atom is folded (its invariant conjoined into the constraint), reducing to the linear \
                  shape when ≤1 same-SCC recursive atom remains",
        assurance: Assurance::Validated,
        evidence: "the dependency analysis / SCC / tag-merge / projection are UNTRUSTED — a Sat (SAFE) is \
                   returned only when the full multi-predicate interpretation makes EVERY clause valid \
                   (per-clause check_auto-Unsat of body∧constraint∧¬head over the ORIGINAL clauses); \
                   Unsat via the engine's replay-checked counterexample / a reachable query. (A reduction \
                   soundness bug — variable leakage into the invariant — was caught by this gate + \
                   soundness-negative tests and fixed; mutual recursion adds a soundness-negative test \
                   that a member-conflating projection can never yield a wrong Unsat; verify_horn_model \
                   conjoins EVERY body atom, audited for the nonlinear extension.) SCCs over caps \
                   (16 members / 32 state width), sort-incompatible members, GENUINE nonlinear recursion \
                   (≥2 same-SCC atoms after folding), or >8-atom bodies → Unknown",
        reference: "ADR-0048",
    },
    Capability {
        area: "reachability",
        feature: "Spacer-style IC3/PDR over LRA (prove_safety_pdr_lra): inductive-invariant discovery \
                  for infinite-state real-valued transition systems — mbp_lra predecessor cubes, \
                  relative-inductive blocking, literal-drop generalization, fixpoint",
        assurance: Assurance::Validated,
        evidence: "the IC3 search + mbp_lra projection are UNTRUSTED — Safe only when the discovered \
                   invariant passes 3 check_auto-unsat checks (init/consecution/safety); Reachable only \
                   when an inline LRA k-unrolling is check_auto-Sat; closes Safe incl. MULTI-VARIABLE \
                   systems (twin counters x=y); all caps → Unknown",
        reference: "ADR-0048",
    },
    Capability {
        area: "reachability",
        feature: "Spacer-style IC3/PDR over LIA (prove_safety_pdr_lia): the integer mirror of \
                  prove_safety_pdr_lra — inductive-invariant discovery for infinite-state integer-valued \
                  transition systems, mbp_lia predecessor cubes, relative-inductive blocking, literal-drop \
                  generalization, fixpoint; an unprojectable (divisibility-boundary) predecessor routes to \
                  the trusted k-unrolling instead of fabricating a cube",
        assurance: Assurance::Validated,
        evidence: "the IC3 search + mbp_lia projection are UNTRUSTED — Safe only when the discovered \
                   invariant passes 3 check_auto-unsat checks over ℤ (init/consecution/safety); Reachable \
                   only when an integer k-unrolling is check_auto-Sat (trace replayed = init + each trans + \
                   bad); integer-specific safety (e.g. odd target unreachable by +2 steps) decided by the \
                   integer decider in the loop; soundness-negative test that an actually-reachable system \
                   can never return a wrong Safe; all caps / mbp_lia decline → Unknown",
        reference: "ADR-0048",
    },
    Capability {
        area: "reachability",
        feature: "interpolation-based model checking over LIA (prove_safety_imc_lia): the integer mirror \
                  of prove_safety_imc_lra — McMillan IMC for infinite-state integer-valued transition \
                  systems, the reachability over-approximation grown by interpolating the UNSAT \
                  k-unrolling — tries the DISJUNCTIVE lia_interpolant_cnf first (Boolean-structured \
                  invariants), falling back to the conjunctive lia_interpolant; reuses pdr_lia's integer \
                  TransitionSystem. Closes a disjunctive fixpoint (e.g. reachable set {0,10}, invariant \
                  x≤0 ∨ x≥10) the conjunctive-only path declined; deepens/declines when both interpolants \
                  decline (cuts-needed leaf)",
        assurance: Assurance::Validated,
        evidence: "untrusted interpolation/fixpoint search — Safe only when the over-approximation R passes \
                   3 check_auto-unsat checks over ℤ (initiation/consecution/safety), independently \
                   re-checked test-side; Reachable only when the concrete integer k-unrolling is \
                   check_auto-Sat (trace replayed); lia_interpolant is verify-before-return and its \
                   declines (cuts-needed / non-conjunctive / overflow) become a sound Unknown, never an \
                   error; soundness-negative test that an actually-unsafe system never returns Safe",
        reference: "ADR-0047/0048",
    },
    Capability {
        area: "reachability",
        feature: "interpolation-based model checking over LRA (prove_safety_imc_lra): IMC for \
                  infinite-state real-valued transition systems via the disjunctive lra_interpolant_cnf + \
                  an inline LRA k-unrolling",
        assurance: Assurance::Validated,
        evidence: "same untrusted-fixpoint / 3-check Safe gate + check_auto-Sat Reachable as QF_BV IMC. \
                   PARTIAL coverage: closes a fixpoint only when the first (conjunctive) interpolation \
                   step suffices (init already an inductive over-approximation); a disjunctive frontier \
                   deepens then declines to Unknown (conjunctive Farkas only — disjunctive interpolation \
                   is future work). Never a wrong Safe/Reachable",
        reference: "ADR-0048",
    },
    Capability {
        area: "synthesis",
        feature: "abduction (abduct / get-abduct): find H over the shared vocabulary with axioms ∧ H \
                  sat and axioms ∧ H ⊨ conjecture — the checker turned generator. Grammar reuses \
                  syntactic atoms AND synthesizes new shared-term equalities + arithmetic comparisons \
                  (to shared terms / problem constants), a SyGuS-lite step",
        assurance: Assurance::Validated,
        evidence: "the candidate enumeration (shared-vocab atoms, ≤2-literal conjunctions) is \
                   untrusted — every returned H is re-checked: consistency (check_auto Sat), \
                   sufficiency (axioms ∧ H ∧ ¬conjecture check_auto Unsat), and shared vocabulary; \
                   Unknown rejects, over-eager None on budget exhaustion / out-of-grammar (never \
                   a wrong abduct)",
        reference: "ADR-0049",
    },
    Capability {
        area: "diagnostics",
        feature: "route-trace / decline telemetry (Solver::check_auto_explained → (CheckResult, \
                  RouteTrace)): a fragment probe + an ordered trail of every dispatch route tried, each \
                  Decided or Declined with a reason (Unsupported / NotApplicable / Budget / Incomplete / \
                  VerifierRejected, reusing UnknownKind) — the gap-analysis 'minimal strategy/probe' \
                  layer and the named prerequisite for the lazy-CDCL(T) dispatch push",
        assurance: Assurance::Validated,
        evidence: "PURELY ADDITIVE — one dispatch path, a recorder threaded through check_auto_with_recorder \
                   that never participates in a branch condition, so the verdict is invariant by \
                   construction; guarded by a 400-query LCG differential (check_auto_explained.0 == \
                   check_auto EXACTLY, 0 mismatches) + a determinism check (byte-identical trace across \
                   runs). No decider verdict logic touched",
        reference: "ADR-0050",
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
