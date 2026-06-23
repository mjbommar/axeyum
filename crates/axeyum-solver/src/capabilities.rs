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
                  decides FULL Boolean-structured QF_UFLRA via an enumerative DPLL(T): Tseitin \
                  skeleton over the theory atoms, propositional-model enumeration with theory-conflict \
                  blocking clauses, the conjunctive MBTC reused verbatim as the per-model theory oracle. \
                  Now the DEFAULT check_auto route for mixed UF+real-arith queries (tried before eager \
                  Ackermann, which stays the byte-unchanged fallback on online Unknown)",
        assurance: Assurance::Validated,
        evidence: "soundness by DIFFERENTIAL validation vs the trusted offline check_with_uf_arithmetic \
                   — random UFLRA conjunctions AND random and/or/not/ite Boolean trees over UFLRA atoms, \
                   0 disagreements, every sat model REPLAYED against the originals (the conjunctive fuzz \
                   caught + fixed 2 real soundness bugs; the Boolean fuzz jointly decided 123 = 41 sat / \
                   82 unsat). A per-model Unknown forces a whole-query Unknown (no wrong unsat). Caps \
                   (models/atoms/clauses/split-depth/timeout) → graceful Unknown; non-UFLRA → Unknown. \
                   Enumerative DPLL(T) with blocking-clause pruning (1-UIP learning / theory propagation \
                   deferred). The check_auto dispatch wiring is itself guarded by an in-tree differential \
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
                  Boolean-structured QF_UFLIA via the same enumerative DPLL(T) as QF_UFLRA (Tseitin \
                  skeleton over the theory atoms, propositional-model enumeration with theory-conflict \
                  blocking clauses, the conjunctive MBTC reused as the per-model theory oracle). Now the \
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
