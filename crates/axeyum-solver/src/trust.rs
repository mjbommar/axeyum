//! The reduction **trust ledger** (P3.0): every reduction the stack relies on is
//! a named, countable [`TrustId`] with a pedantic level, mirroring cvc5's
//! `TrustId`. This turns the implicit "checked **modulo trusted reduction**"
//! caveat into an auditable list — the precondition for shrinking the trusted
//! base to zero (Track 3 in `docs/plan/track-3-proof-lean/`).
//!
//! A reduction is **certified** when every evidence route that records it has an
//! independent per-query checker that re-derives it, **partially certified** when
//! some routes do and some do not, and a **trust hole** when none do. That status
//! is not typed per id: it is folded from [`EVIDENCE_ROUTES`], one row per
//! (reduction, does-the-checker-re-derive-it) route, by [`TrustId::coverage`]
//! (P0.5). `tests/trust_ledger_derivation.rs` rebuilds the same fold from the
//! `(TrustId::…, <certified>)` pairs the producing code actually writes and fails
//! on disagreement, so a reduction cannot be graded by memory and cannot be added
//! without saying what produces and checks it.
//!
//! A produced [`crate::EvidenceReport`] records the
//! [`TrustStep`]s a given result depended on (with whether *this run* certified
//! each), so a consumer can see exactly what it is trusting.
//!
//! [`ALL_TRUST_IDS`] is the canonical iteration order (source order, never
//! hash-map order — determinism is a public promise). The rendered
//! [`trust_ledger_markdown`] is golden-tested against
//! `docs/research/08-planning/trust-ledger.md`, so the doc cannot drift.

use core::fmt;
use core::fmt::Write as _;

/// A reduction the stack relies on, mirroring cvc5's `TrustId`. `Copy` + `Ord`
/// so dependency sets are `BTreeSet`s with deterministic iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustId {
    /// Term → AIG bit-blasting (`axeyum-bv`).
    BitBlast,
    /// AIG → CNF Tseitin encoding (`axeyum-cnf`).
    Tseitin,
    /// CNF UNSAT from the CDCL core (DRAT-checked).
    SatRefutation,
    /// CNF UNSAT from the CDCL(T) core **modulo N enumerated theory lemmas**
    /// (ADR-1704).
    ///
    /// The Boolean half is exactly as checked as [`SatRefutation`]: the same
    /// DRAT/LRAT stream through the same unchanged `check_drat`/`check_lrat`.
    /// What is different is the formula it refutes — the CNF *extended by the
    /// theory lemmas as input clauses* — so the statement established is
    /// strictly weaker, and each lemma is an obligation the theory owes.
    ///
    /// This id exists rather than reusing [`SatRefutation`] because that id's
    /// meaning is a refutation of the CNF. One id cannot carry both without the
    /// ledger becoming unreadable at the only place it is load-bearing, and
    /// ADR-1704 section 5 states the prohibition as an outcome:
    /// `theory_lemmas > 0` and [`SatRefutation`] must never co-occur.
    /// [`theory_refutation_trust_step`] is where that is enforced.
    ///
    /// `is_certified` is `false` and stays `false` until the per-lemma
    /// discharge is wired for every theory that can produce one. The number to
    /// watch is not this bit but the artifact's own
    /// `theory_lemmas_unchecked`, which no producer can move.
    ///
    /// [`SatRefutation`]: TrustId::SatRefutation
    SatRefutationModuloTheory,
    /// Arrays → BV by read-over-write + Ackermann (ADR-0010). The
    /// **eager-elimination** UNSAT sub-case (`check_with_array_elimination`: every
    /// `select` over an array variable replaced by a fresh var after read-over-write,
    /// the full pairwise select-congruence set asserted up front, the resulting
    /// `QF_BV` refuted) now has an independent per-query re-checker —
    /// [`crate::ArrayElimUnsatCertificate::recheck`] re-runs the deterministic
    /// [`eliminate_arrays`](axeyum_rewrite::eliminate_arrays) on the original
    /// assertions, structurally re-derives the select-congruence set (witnessing
    /// each appended constraint is a valid array-read consequence — read-over-write
    /// is an equivalence, select-congruence is valid — so the eliminated formula is
    /// a sound relaxation), re-bit-blasts it to confirm the stored CNF, and re-runs
    /// `check_drat`. This composes the Ackermann congruence witness ([`Ackermann`]):
    /// array elim's second step IS an Ackermann congruence over a per-array read
    /// function. `is_certified` stays `false` because the *general* array reasoning
    /// (the lazy/CEGAR `sat` path, lazy extensionality, the array-combined
    /// `QF_AUFBV` route, and array `sat` models) carries no such certificate — see
    /// [`TrustId::is_certified`].
    ///
    /// [`Ackermann`]: TrustId::Ackermann
    ArrayElim,
    /// Uninterpreted-function applications → fresh vars + functional consistency (ADR-0013).
    /// The **eager-elimination** UNSAT sub-case (`check_with_function_elimination`:
    /// every distinct application replaced by a fresh var, the full pairwise
    /// congruence set asserted up front, the resulting `QF_BV` refuted) now has an
    /// independent per-query re-checker —
    /// [`crate::AckermannUnsatCertificate::recheck`] re-runs the deterministic
    /// elimination on the original assertions, structurally re-derives the
    /// congruence set (witnessing each appended constraint is a valid UF
    /// consequence, so the eliminated formula is a sound relaxation), re-bit-blasts
    /// it to confirm the stored CNF, and re-runs `check_drat`. `is_certified` stays
    /// `false` because the *general* Ackermann (lazy/CEGAR `sat`, the
    /// array-combined `QF_AUFBV` route, and arithmetic-sorted function `sat` models)
    /// carries no such certificate — see [`TrustId::is_certified`].
    Ackermann,
    /// Bounded integers → `BitVec` at a chosen width (ADR-0014). The
    /// **proven-box bounded** sub-case (`decide_bounded_int_blast`: every free Int
    /// variable confined to a finite, exactly-encodable box) now has an
    /// independent per-query re-checker —
    /// [`crate::BoundedIntBlastCertificate::recheck`] re-derives the box + covering
    /// width from the original assertions and re-runs `check_drat` over the
    /// bit-blasted CNF. `is_certified` stays `false` because the *general*
    /// int-blast (the sat-only width ladder, and unbounded queries) carries no such
    /// certificate — see [`TrustId::is_certified`].
    IntBlast,
    /// Datatype `select`/`is`/eq folded over constructors → BV (ADR-0022).
    DatatypeElim,
    /// Floating-point operators → BV circuits (ADR-0023). The
    /// **small IEEE-style-format** sub-case now carries an independent
    /// **exhaustive faithfulness witness**: for `FP8_E5M2` (8 bits, IEEE ∞/NaN
    /// conventions) the per-operator FP→BV circuits are checked over **every** input
    /// bit pattern against `rustc_apfloat`'s native `Float8E5M2` reference
    /// (`crates/axeyum-fp/tests/fpa2bv_faithfulness.rs`): all 256 unary / 65 536
    /// binary inputs of `fp.add`/`fp.sub`/`fp.mul`/`fp.neg`/`fp.abs`/`fp.eq`/
    /// `fp.lt`/`fp.leq`/`fp.min`/`fp.max` agree, modulo the SMT-LIB-*unspecified*
    /// opposite-sign-zero `fp.min`/`fp.max` sign (both `±0` are accepted, matching
    /// the `af6c8bf` fix) and NaN-payload tolerance. This is **stronger** than the
    /// re-derivation certificates ([`ArrayElim`]/[`Ackermann`]/[`IntBlast`]): those
    /// re-blast the same circuit and re-check its CNF, which proves *determinism*
    /// but not *faithfulness* — a stably-wrong circuit (exactly the `af6c8bf` ±0
    /// wrong-`unsat`) survives re-derivation. An exhaustive independent oracle does
    /// not, and the witness has demonstrated teeth (it rejects a swapped-selection
    /// `fp.min`/`fp.max` mutation). `is_certified` stays `false` because the
    /// **large** formats (`F32`/`F64`/`F128` — not exhaustively enumerable, only
    /// sampled differentially) and the **non-IEEE** small formats (`FP8_E4M3`,
    /// `FP4_E2M1` — no Axeyum arithmetic circuit and a deviating reference) carry no
    /// such per-query certificate — see [`TrustId::is_certified`].
    ///
    /// [`ArrayElim`]: TrustId::ArrayElim
    /// [`Ackermann`]: TrustId::Ackermann
    /// [`IntBlast`]: TrustId::IntBlast
    Fpa2Bv,
    /// Reduction-free exhaustive evaluation over the finite symbol domain.
    TermLevelEnum,
    /// Exact-rational Farkas refutation for `QF_LRA` (ADR-0015).
    Farkas,
    /// Lazy-SMT skeleton + Farkas-certified theory lemmas (ADR-0021).
    LraDpll,
    /// CDCL(XOR) UNSAT via Gaussian reasoning (ADR-0035). The
    /// pure-Gaussian-level-0 sub-case (the recovered XOR system is inconsistent by
    /// Gaussian elimination alone, no branching) now carries a `check_drat`-checked
    /// per-query certificate; the interleaved CDCL(XOR) sub-case (branching needed)
    /// remains search-only and trusted. `is_certified` stays `false` because not
    /// *every* XOR UNSAT is certified — see [`TrustId::is_certified`].
    XorGaussian,
    /// Degree-2 sum-of-squares / PSD certificate for NRA (ADR-0039).
    Sos,
    /// Integer-systems infeasibility (integer Farkas / Diophantine) (ADR-0042).
    Diophantine,
}

/// Every [`TrustId`] in canonical (stable) order — the iteration source of truth.
pub const ALL_TRUST_IDS: &[TrustId] = &[
    TrustId::BitBlast,
    TrustId::Tseitin,
    TrustId::SatRefutation,
    TrustId::SatRefutationModuloTheory,
    TrustId::ArrayElim,
    TrustId::Ackermann,
    TrustId::IntBlast,
    TrustId::DatatypeElim,
    TrustId::Fpa2Bv,
    TrustId::TermLevelEnum,
    TrustId::Farkas,
    TrustId::LraDpll,
    TrustId::XorGaussian,
    TrustId::Sos,
    TrustId::Diophantine,
];

/// A sentinel [`EvidenceRoute::checker`]: this route attaches **no** checkable
/// artifact at all (a bare `Evidence::Unsat(None)`, a search-only refutation, an
/// undischarged theory lemma). A route whose checker is [`NO_CHECKER`] can never
/// carry `certifies: true` — there is nothing to re-derive the step with — and
/// `tests/trust_ledger_derivation.rs` enforces exactly that.
pub const NO_CHECKER: &str = "(none)";

/// How much of a reduction's **recorded** use the in-tree checkers re-derive.
///
/// This is the ledger status, and since P0.5 it is *computed* from
/// [`EVIDENCE_ROUTES`] rather than typed per id. The three real values are
/// distinctions the producing code already makes and a boolean cannot hold: a
/// DRAT-checked SAT refutation and an undischarged theory lemma are not the same
/// kind of thing, yet both used to render as one word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CertifiedCoverage {
    /// **certified** — every route that records this reduction re-derives it, so
    /// no result relying on it is trusted-uncertified. This is the conservative
    /// bit [`TrustId::is_certified`] returns.
    Full,
    /// **partially certified** — at least one route re-derives the reduction and
    /// at least one does not. The per-run [`TrustStep::certified`] flag, not the
    /// ledger, says which happened for a *given* result.
    Partial,
    /// **trust hole** — no route that records this reduction re-derives it. What
    /// Track 3 P3.5 drives to zero.
    Uncertified,
    /// **no evidence route declared** — a [`TrustId`] with no entry in
    /// [`EVIDENCE_ROUTES`]. Never a valid state: it means a reduction was added
    /// to the enum without saying what produces and checks it. The ledger renders
    /// it loudly rather than defaulting it to either honest value.
    Unrouted,
}

impl CertifiedCoverage {
    /// The word the rendered ledger prints in its `Status` column.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            CertifiedCoverage::Full => "certified",
            CertifiedCoverage::Partial => "partially certified",
            CertifiedCoverage::Uncertified => "trust hole",
            CertifiedCoverage::Unrouted => "UNROUTED (no evidence route declared)",
        }
    }
}

/// One **evidence route** through a reduction: a producing site, the artifact it
/// attaches, the in-tree checker that consumes that artifact, and — the
/// load-bearing field — whether that checker re-derives *this* reduction.
///
/// `certifies` is not "the result was checked". A DRAT proof of the bit-blasted
/// CNF *is* checked, and re-derives Tseitin and the SAT refutation, and says
/// **nothing** about whether the term → AIG bit-blasting was faithful. That is
/// why `drat_qf_bv_evidence` records `(TrustId::BitBlast, false)` beside
/// `(TrustId::SatRefutation, true)`, and why this table carries a row per route
/// rather than a bit per reduction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EvidenceRoute {
    /// The reduction this route goes through.
    pub id: TrustId,
    /// The producing function, as an in-tree symbol name.
    pub producer: &'static str,
    /// The artifact this route attaches to its result.
    pub evidence: &'static str,
    /// The in-tree checker that consumes that artifact, or [`NO_CHECKER`].
    pub checker: &'static str,
    /// Whether `checker` re-derives **this** reduction on this route.
    pub certifies: bool,
}

/// Every evidence route that records a [`TrustStep`], one row per
/// (reduction, does-the-checker-re-derive-it) pair.
///
/// This is the ledger's source of truth: [`TrustId::coverage`] folds this table
/// and [`TrustId::is_certified`] reads that fold. The table is a *declaration*,
/// so on its own it would be one more hand-written list — what makes it a
/// derivation is `tests/trust_ledger_derivation.rs`, which rebuilds the same fold
/// from the `(TrustId::…, <certified>)` pairs the producing code actually writes,
/// fails on any disagreement, and fails when a `producer` or `checker` names a
/// symbol that is not in the tree.
///
/// Routes that certify a sub-case but record **no** [`TrustStep`] are
/// deliberately absent: `ArrayElimUnsatCertificate::recheck`,
/// `AckermannUnsatCertificate::recheck` and the datatype compositions each
/// re-derive their reduction, but they run outside `produce_evidence`, so a
/// consumer reading `crate::EvidenceReport::trusted_steps` never sees them. A
/// certificate the ledger cannot observe must not raise the ledger.
pub const EVIDENCE_ROUTES: &[EvidenceRoute] = &[
    EvidenceRoute {
        id: TrustId::BitBlast,
        producer: "prove_qf_bv_unsat_alethe",
        evidence: "Evidence::UnsatAletheProof",
        checker: "check_alethe",
        // The Alethe proof carries a `bitblast_<op>` step per lowered operator
        // and `check_alethe` structurally re-derives each one, so bit-blasting
        // itself is checked on this route. NOT the miter: `bitblast_miter.rs`
        // has no caller inside `axeyum-solver`.
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::BitBlast,
        producer: "drat_qf_bv_evidence",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "UnsatProof",
        // A DRAT refutation of the CNF is silent about whether the CNF encodes
        // the term. This is the route the default QF_BV front door takes.
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::Tseitin,
        producer: "prove_qf_bv_unsat_alethe",
        evidence: "Evidence::UnsatAletheProof",
        checker: "check_alethe",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::Tseitin,
        producer: "pure_gauss_xor_unsat_certificate_for_query",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "check_drat",
        // The pure-Gauss certificate refutes the conflict subset `CNF(S)`; the
        // encoding that produced those clauses is not re-derived.
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::SatRefutation,
        producer: "drat_qf_bv_evidence",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "UnsatProof",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::SatRefutation,
        producer: "drat_qf_bv_evidence",
        evidence: "Evidence::Unsat(None)",
        checker: NO_CHECKER,
        // Proof production is a second search. When the deadline is already spent
        // or the search / checking stage runs out, the verdict stands and the
        // certificate does not exist — a result relying on the SAT refutation
        // with nothing to re-derive it.
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::SatRefutationModuloTheory,
        producer: "theory_refutation_trust_step",
        evidence: "TheoryRefutation with theory_lemma_count() > 0",
        checker: NO_CHECKER,
        // ADR-1704: the Boolean half is DRAT-checked, but the lemmas it assumed
        // are undischarged obligations, so nothing re-derives the step itself.
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::ArrayElim,
        producer: "reduction_unsat_certificate",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "export_qf_aufbv_unsat_proof_within",
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::Ackermann,
        producer: "reduction_unsat_certificate",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "export_qf_aufbv_unsat_proof_within",
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::IntBlast,
        producer: "certify_bounded_int_blast",
        evidence: "Evidence::UnsatBoundedIntBlast",
        checker: "BoundedIntBlastCertificate",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::IntBlast,
        producer: "prove_lia_unsat_alethe",
        evidence: "Evidence::UnsatArithAletheProof",
        checker: "check_alethe_lra",
        // The LIA refutation is re-derived; the `bv2nat` range abstraction that
        // produced it is the trusted int/BV-width bridge.
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::DatatypeElim,
        producer: "reduction_unsat_certificate",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "export_datatype_unsat_proof",
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::Fpa2Bv,
        producer: "with_fpa2bv_step",
        evidence: "unsat evidence over an FP query whose operators are all faithful by construction",
        checker: "fpa2bv_simple_op_certified",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::Fpa2Bv,
        producer: "with_fpa2bv_step",
        evidence: "unsat evidence over a rounding-bearing or large-format FP query",
        checker: NO_CHECKER,
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::TermLevelEnum,
        producer: "certify_qf_bv_by_enumeration",
        evidence: "Evidence::UnsatTermLevel",
        checker: "certify_qf_bv_by_enumeration",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::Farkas,
        producer: "lra_farkas_certificate",
        evidence: "Evidence::UnsatFarkas",
        checker: "FarkasCertificate",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::LraDpll,
        producer: "certify_lra_dpll_unsat",
        evidence: "Evidence::UnsatLraDpll",
        checker: "LraDpllRefutation",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::XorGaussian,
        producer: "pure_gauss_xor_unsat_certificate_for_query",
        evidence: "Evidence::Unsat(Some(UnsatProof))",
        checker: "check_drat",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::XorGaussian,
        producer: "produce_qf_bv_evidence",
        evidence: "Evidence::Unsat(None)",
        checker: NO_CHECKER,
        // The interleaved CDCL(XOR) sub-case: branching was needed, so there is
        // no RUP-checkable proof (ADR-0035).
        certifies: false,
    },
    EvidenceRoute {
        id: TrustId::Sos,
        producer: "reconstruct_sos_to_lean_module",
        evidence: "Evidence::UnsatSos",
        checker: "SosCertificate",
        certifies: true,
    },
    EvidenceRoute {
        id: TrustId::Diophantine,
        producer: "reconstruct_diophantine_to_lean_module",
        evidence: "Evidence::UnsatDiophantine",
        checker: "check_diophantine_certificate",
        certifies: true,
    },
];

impl TrustId {
    /// Stable label used in the rendered ledger and provenance.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            TrustId::BitBlast => "bit-blast",
            TrustId::Tseitin => "tseitin",
            TrustId::SatRefutation => "sat-refutation",
            TrustId::SatRefutationModuloTheory => "sat-refutation-modulo-theory",
            TrustId::ArrayElim => "array-elim",
            TrustId::Ackermann => "ackermann",
            TrustId::IntBlast => "int-blast",
            TrustId::DatatypeElim => "datatype-elim",
            TrustId::Fpa2Bv => "fpa2bv",
            TrustId::TermLevelEnum => "term-level-enum",
            TrustId::Farkas => "farkas",
            TrustId::LraDpll => "lra-dpll",
            TrustId::XorGaussian => "xor-gaussian",
            TrustId::Sos => "sos",
            TrustId::Diophantine => "diophantine",
        }
    }

    /// One-line meaning.
    #[must_use]
    pub const fn meaning(self) -> &'static str {
        match self {
            TrustId::BitBlast => "term \u{2192} AIG bit-blasting",
            TrustId::Tseitin => "AIG \u{2192} CNF Tseitin encoding",
            TrustId::SatRefutation => "CNF UNSAT from the CDCL core",
            TrustId::SatRefutationModuloTheory => {
                "CNF UNSAT from the CDCL(T) core modulo N enumerated theory lemmas"
            }
            TrustId::ArrayElim => "arrays \u{2192} BV (read-over-write + Ackermann)",
            TrustId::Ackermann => {
                "uninterpreted functions \u{2192} fresh vars + functional consistency"
            }
            TrustId::IntBlast => "bounded integers \u{2192} BV at a chosen width",
            TrustId::DatatypeElim => "datatypes folded over constructors \u{2192} BV",
            TrustId::Fpa2Bv => "floating-point operators \u{2192} BV circuits",
            TrustId::TermLevelEnum => "reduction-free exhaustive evaluation over the finite domain",
            TrustId::Farkas => "exact-rational Farkas refutation (QF_LRA)",
            TrustId::LraDpll => "lazy-SMT skeleton + Farkas-certified theory lemmas",
            TrustId::XorGaussian => {
                "CDCL(XOR) search-only UNSAT (in-search Gaussian reasoning, no DRAT)"
            }
            TrustId::Sos => "degree-2 sum-of-squares / PSD nonnegativity certificate (NRA)",
            TrustId::Diophantine => "integer-systems infeasibility (integer Farkas / Diophantine)",
        }
    }

    /// cvc5-style grade: 0 = hard fail (unsound if wrong, no recovery) … 10 = minor.
    #[must_use]
    pub const fn pedantic_level(self) -> u8 {
        match self {
            TrustId::TermLevelEnum | TrustId::Farkas | TrustId::Sos | TrustId::Diophantine => 10,
            TrustId::Tseitin | TrustId::SatRefutation | TrustId::LraDpll => 9,
            TrustId::BitBlast => 8,
            TrustId::Fpa2Bv => 5,
            // `SatRefutationModuloTheory` belongs here and not at 9: its
            // Boolean half is machine-checked and every assumption is
            // enumerated in the artifact, so a reviewer can see and later
            // discharge exactly what is trusted -- the same posture as the
            // eager-elimination reductions beside it, and not the search-only
            // opacity of `XorGaussian` below. But an undischarged lemma is
            // still a wrong `unsat` with no recovery if the theory is wrong.
            TrustId::SatRefutationModuloTheory
            | TrustId::ArrayElim
            | TrustId::Ackermann
            | TrustId::DatatypeElim => 4,
            // Search-only XOR UNSAT has no per-query certificate and a wrong
            // refutation is unsound with no recovery, so it grades low (ADR-0035).
            TrustId::IntBlast | TrustId::XorGaussian => 3,
        }
    }

    /// The ledger status of this reduction, **folded from [`EVIDENCE_ROUTES`]**
    /// rather than typed per id (P0.5): [`CertifiedCoverage::Full`] when every
    /// declared route re-derives the step, [`CertifiedCoverage::Partial`] when
    /// some do and some do not, [`CertifiedCoverage::Uncertified`] when none do,
    /// and [`CertifiedCoverage::Unrouted`] when the id has no declared route at
    /// all — a state `tests/trust_ledger_derivation.rs` rejects.
    #[must_use]
    pub const fn coverage(self) -> CertifiedCoverage {
        let mut index = 0;
        let mut found = false;
        let mut any_certifies = false;
        let mut all_certify = true;
        while index < EVIDENCE_ROUTES.len() {
            let route = EVIDENCE_ROUTES[index];
            if route.id as u8 == self as u8 {
                found = true;
                if route.certifies {
                    any_certifies = true;
                } else {
                    all_certify = false;
                }
            }
            index += 1;
        }
        if !found {
            return CertifiedCoverage::Unrouted;
        }
        if all_certify {
            CertifiedCoverage::Full
        } else if any_certifies {
            CertifiedCoverage::Partial
        } else {
            CertifiedCoverage::Uncertified
        }
    }

    /// Whether *every* result depending on this reduction has an independent
    /// per-query checker today. Derived: `coverage() == CertifiedCoverage::Full`.
    ///
    /// This is the **conservative** ledger status: a reduction returns `true` only
    /// when no result that relies on it is trusted-uncertified — which is what the
    /// prose has always claimed, and what the hand-written `match` this replaced
    /// did not do. Three ids read `true` under a *different*, looser rule ("a
    /// certifying route exists somewhere"): [`BitBlast`], [`Tseitin`] and
    /// [`SatRefutation`]. All three are recorded `certified: false` on live
    /// routes — the default DRAT front door attaches a *checked* DRAT proof while
    /// leaving the bit-blasting trusted, and a proof-production timeout returns a
    /// bare `Evidence::Unsat(None)` that relies on the SAT refutation with nothing
    /// to re-check it — so under the conservative rule they are
    /// [`CertifiedCoverage::Partial`], not certified.
    ///
    /// Because "partial" is not the same claim as "no certificate exists", the
    /// rendered ledger prints three statuses; a reader of `partially certified`
    /// still sees that DRAT and Alethe are real. [`XorGaussian`]
    /// stays `false` even though its **pure-Gaussian-level-0** sub-case now carries
    /// a `check_drat` certificate (a freshly re-checkable `Evidence::Unsat(Some(_))`
    /// over `CNF(S)`), because the **interleaved CDCL(XOR)** sub-case (branching
    /// needed) is still search-only with no per-query certificate. The per-run
    /// [`TrustStep::certified`] flag reports which sub-case a *given* `unsat`
    /// actually took: `true` for the certified pure-Gauss refutation, `false` for
    /// the trusted interleaved one. A reviewer must therefore read
    /// [`TrustStep::certified`], not this ledger bit, to know whether a *particular*
    /// XOR `unsat` was certified — and must not read `XorGaussian` as
    /// "interleaved XOR-UNSAT is certified" (it is not).
    ///
    /// [`IntBlast`] is analogous: its **proven-box bounded** sub-case now carries a
    /// re-checkable [`crate::BoundedIntBlastCertificate`] (box + covering width
    /// re-derived from the originals, plus `check_drat`), but the general int-blast
    /// (the sat-only width ladder / unbounded queries) has no per-query
    /// certificate, so this bit stays `false`.
    ///
    /// [`Ackermann`] is likewise analogous: its **eager-elimination** UNSAT
    /// sub-case now carries a re-checkable [`crate::AckermannUnsatCertificate`] (the
    /// elimination + full congruence set re-derived from the originals, the CNF
    /// re-blasted, plus `check_drat`), but the lazy/CEGAR `sat` path, the
    /// array-combined `QF_AUFBV` route, and arithmetic-sorted function `sat` models
    /// have no per-query certificate, so this bit stays `false`.
    ///
    /// [`ArrayElim`] is likewise analogous: its **eager-elimination** UNSAT sub-case
    /// now carries a re-checkable [`crate::ArrayElimUnsatCertificate`] (the
    /// read-over-write + full select-congruence set re-derived from the originals,
    /// the CNF re-blasted, plus `check_drat`), composing the Ackermann congruence
    /// witness, but the lazy/CEGAR `sat` path, lazy extensionality, the
    /// array-combined `QF_AUFBV` route, and array `sat` models have no per-query
    /// certificate, so this bit stays `false`.
    ///
    /// [`Fpa2Bv`] is analogous in spirit but witnessed *forward* rather than by
    /// re-derivation, and now carries **two** distinct sub-case witnesses (both of
    /// which the per-run [`TrustStep::certified`] flag reports, while this global bit
    /// stays `false`):
    ///
    /// 1. A **small IEEE-style-format** sub-case (`FP8_E5M2`) with an **exhaustive
    ///    faithfulness** check — every input bit pattern of the per-operator circuit
    ///    agrees with the independent `rustc_apfloat` reference
    ///    (`crates/axeyum-fp/tests/fpa2bv_faithfulness.rs`), a stronger guarantee than
    ///    re-blasting the same circuit.
    /// 2. A **by-construction-faithful-operator** sub-case (tasks #69/#70/#70a): a
    ///    `Fpa2Bv` `unsat` query whose FP operators are **all** faithful by
    ///    construction (at the guarded `≤128`-bit widths) is certified at any such
    ///    width. Two tiers qualify: (i) **exact bit ops** — `fp.neg`/`fp.abs`, the
    ///    five category predicates
    ///    `fp.isNaN`/`fp.isInfinite`/`fp.isZero`/`fp.isNormal`/`fp.isSubnormal`, and
    ///    the sign predicates `fp.isNegative`/`fp.isPositive` (`sign ∧ ¬NaN`) —
    ///    faithful by inspection at any width; and (ii) **proven-faithful comparison /
    ///    selection circuits** `fp.eq`/`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq` and
    ///    `fp.min`/`fp.max` — faithful by a width-independent monotone-`order_key`
    ///    argument, exhaustively witnessed at `FP8_E5M2` + an F16 edge witness (the
    ///    `fp.min`/`fp.max` unspecified ±0 sign bit is minted in the internal symbol
    ///    namespace since #72, so it stays genuinely free and the reduction
    ///    over-approximates the FP allowed-result set — `BV-unsat ⟹ FP-unsat` holds). (FP formats are guarded to `≤128` bits so
    ///    the circuits' `u128` sign masks never overflow — else a wider format would
    ///    corrupt the circuit and its certificate.) The parser records the FP op-set
    ///    on `FpUsage`; `produce_evidence_smtlib` gates the step on that allow-list
    ///    (over-approximation: a free FP var lowers to a fresh BV over all patterns,
    ///    so `BV-unsat ⟹ FP-unsat` when every lowered op is faithful).
    ///
    /// This bit stays `false` because it is not *every* `Fpa2Bv` query: the large
    /// formats (`F32`/`F64`/`F128`, only sampled) and any query using a
    /// rounding-bearing op (`fp.add`, `fp.mul`, `to_fp`, …) have no per-query
    /// certificate — those need the by-construction rounding-circuit proof (a funded
    /// arc, task #70).
    ///
    /// [`XorGaussian`]: TrustId::XorGaussian
    /// [`IntBlast`]: TrustId::IntBlast
    /// [`Ackermann`]: TrustId::Ackermann
    /// [`ArrayElim`]: TrustId::ArrayElim
    /// [`Fpa2Bv`]: TrustId::Fpa2Bv
    #[must_use]
    pub const fn is_certified(self) -> bool {
        matches!(self.coverage(), CertifiedCoverage::Full)
    }

    /// The governing architecture-decision record.
    #[must_use]
    pub const fn reference(self) -> &'static str {
        match self {
            TrustId::BitBlast | TrustId::Tseitin => "ADR-0006",
            TrustId::SatRefutation => "ADR-0012",
            TrustId::SatRefutationModuloTheory => "ADR-1704",
            TrustId::ArrayElim => "ADR-0010",
            TrustId::Ackermann => "ADR-0013",
            TrustId::IntBlast => "ADR-0014",
            TrustId::DatatypeElim => "ADR-0022",
            TrustId::Fpa2Bv => "ADR-0023",
            TrustId::TermLevelEnum => "ADR-0005",
            TrustId::Farkas => "ADR-0015",
            TrustId::LraDpll => "ADR-0021",
            TrustId::XorGaussian => "ADR-0035",
            TrustId::Sos => "ADR-0039",
            TrustId::Diophantine => "ADR-0042",
        }
    }
}

impl fmt::Display for TrustId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// A trust step a particular result depended on: the reduction and whether the
/// run that produced this result actually carried an independent certificate for
/// it. Bit-blast is `certified: true` on the QF_BV **Alethe** route, where
/// `check_alethe` re-derives every `bitblast_<op>` step, and `false` on the plain
/// DRAT export route, whose proof re-derives the CNF refutation and says nothing
/// about the lowering. That split is exactly what makes
/// [`TrustId::coverage`] report [`CertifiedCoverage::Partial`] for
/// [`TrustId::BitBlast`] — it is not an exception to the ledger, it is the input
/// the ledger is folded from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TrustStep {
    /// The reduction.
    pub id: TrustId,
    /// Whether *this run* carried an independent certificate for the step.
    pub certified: bool,
}

/// Renders [`ALL_TRUST_IDS`] as the canonical trust-ledger markdown table.
///
/// Golden-tested against `docs/research/08-planning/trust-ledger.md`; that file is
/// regenerated from here, never hand-edited.
#[must_use]
pub fn trust_ledger_markdown() -> String {
    let mut out = String::new();
    out.push_str("# Reduction trust ledger\n\n");
    out.push_str(
        "Generated from `axeyum_solver::trust::ALL_TRUST_IDS` — do not edit by hand.\n\
         Regenerate after changing the enum and commit the result; a golden test\n\
         (`tests/trust_ledger.rs`) fails if this file drifts from the source of truth.\n\n",
    );
    out.push_str(
        "Pedantic levels mirror cvc5's `TrustId` grading: 0 = hard fail \u{2026} 10 = minor.\n\
         The status is **folded from `trust::EVIDENCE_ROUTES`**, one row per \
         (reduction, does-the-checker-re-derive-it) route: **certified** = every \
         route that records the step re-derives it; **partially certified** = some \
         routes do and some do not (read the per-result `TrustStep::certified`, not \
         this column, for a given `unsat`); **trust hole** = no route re-derives it \
         (the base Track 3 P3.5 drives to zero).\n\n",
    );
    let count = |want: CertifiedCoverage| {
        ALL_TRUST_IDS
            .iter()
            .filter(|id| id.coverage() == want)
            .count()
    };
    let full = count(CertifiedCoverage::Full);
    let partial = count(CertifiedCoverage::Partial);
    let holes = count(CertifiedCoverage::Uncertified);
    let unrouted = count(CertifiedCoverage::Unrouted);
    let _ = writeln!(
        out,
        "Trusted base: **{holes}** reduction(s) are trust holes and **{partial}** are \
         only partially certified; **{full}** are fully certified.\n"
    );
    if unrouted > 0 {
        let _ = writeln!(
            out,
            "\u{26a0} **{unrouted}** reduction(s) declare NO evidence route \
             (`trust::EVIDENCE_ROUTES`). The ledger cannot grade them.\n"
        );
    }
    out.push_str("| Reduction | Meaning | Pedantic | Status | Ref |\n");
    out.push_str("|---|---|---|---|---|\n");
    for &id in ALL_TRUST_IDS {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            id.label(),
            id.meaning(),
            id.pedantic_level(),
            id.coverage().label(),
            id.reference(),
        );
    }
    out
}

/// The trust step a CDCL(T) refutation grades at, **read off the artifact**
/// (ADR-1704 section 3).
///
/// This is the one place the ADR's prohibition 2 is decided, so it is written
/// as a function rather than left to each caller: a refutation that assumed
/// nothing grades at [`TrustId::SatRefutation`] and is certified when the
/// checker verified it; a refutation that assumed anything grades at
/// [`TrustId::SatRefutationModuloTheory`] and is **never** certified, because
/// no per-lemma discharge is wired yet. `theory_lemma_count` is itself a
/// subtraction on the artifact (`|extended| - |cnf|`), so nothing a producer
/// writes can move this.
///
/// ```
/// use axeyum_cnf::{CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, TheoryRefutation};
/// use axeyum_solver::trust::{TrustId, theory_refutation_trust_step};
///
/// let mut cnf = CnfFormula::new(1);
/// let x = CnfLit::positive(CnfVar::new(0).unwrap());
/// cnf.add_clause(CnfClause::new(vec![x])).unwrap();
/// cnf.add_clause(CnfClause::new(vec![x.negated()])).unwrap();
/// let artifact =
///     TheoryRefutation::from_cnf_and_lemmas(cnf, Vec::new(), vec![DratStep::Add(Vec::new())]);
/// let step = theory_refutation_trust_step(&artifact);
/// assert_eq!(step.id, TrustId::SatRefutation);
/// assert!(step.certified);
/// ```
#[must_use]
pub fn theory_refutation_trust_step(refutation: &axeyum_cnf::TheoryRefutation) -> TrustStep {
    use axeyum_cnf::TheoryRefutationCheck;

    let check = refutation.check();
    if refutation.theory_lemma_count() == 0 {
        return TrustStep {
            id: TrustId::SatRefutation,
            certified: matches!(check, TheoryRefutationCheck::Verified),
        };
    }
    TrustStep {
        id: TrustId::SatRefutationModuloTheory,
        // Never `true`: `CheckedModuloLemmas` is the *undischarged* grade, and
        // a `Failed` artifact is certified by nothing at all.
        certified: false,
    }
}

#[cfg(test)]
mod tests {
    use super::{ALL_TRUST_IDS, TrustId, theory_refutation_trust_step};
    use axeyum_cnf::{CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, TheoryRefutation};

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().copied().map(lit).collect()))
                .unwrap();
        }
        f
    }

    /// ADR-1704 section 5, prohibition 2, as an executable assertion: a
    /// refutation that assumed a theory lemma is never graded at the pure
    /// propositional id, whatever the checker said about its Boolean half.
    #[test]
    fn a_refutation_modulo_a_lemma_never_grades_at_sat_refutation() {
        // (x1) & (x2) & (x3), refuted only by the difference-logic lemma.
        let cnf = formula(3, &[&[1], &[2], &[3]]);
        let artifact = TheoryRefutation::from_cnf_and_lemmas(
            cnf,
            vec![vec![lit(-1), lit(-2), lit(-3)]],
            vec![DratStep::Add(Vec::new())],
        );
        assert_eq!(artifact.theory_lemma_count(), 1);
        let step = theory_refutation_trust_step(&artifact);
        assert_eq!(step.id, TrustId::SatRefutationModuloTheory);
        assert_ne!(step.id, TrustId::SatRefutation);
        assert!(
            !step.certified,
            "an undischarged lemma is never a certified step"
        );
    }

    /// The control, so the test above is not just "this function always
    /// returns the modulo id": the same route over a lemma-free artifact does
    /// grade at `SatRefutation`, certified.
    #[test]
    fn a_lemma_free_refutation_grades_at_sat_refutation_certified() {
        let cnf = formula(1, &[&[1], &[-1]]);
        let artifact =
            TheoryRefutation::from_cnf_and_lemmas(cnf, Vec::new(), vec![DratStep::Add(Vec::new())]);
        let step = theory_refutation_trust_step(&artifact);
        assert_eq!(step.id, TrustId::SatRefutation);
        assert!(step.certified);
    }

    /// A lemma-free artifact whose Boolean stream does NOT check is graded at
    /// `SatRefutation` **uncertified** rather than silently certified -- the
    /// `certified` flag reports this run, not the id's ledger status.
    #[test]
    fn a_lemma_free_artifact_that_fails_its_check_is_not_certified() {
        let cnf = formula(2, &[&[1], &[-1, 2]]);
        let artifact = TheoryRefutation::from_cnf_and_lemmas(
            cnf,
            Vec::new(),
            vec![DratStep::Add(vec![lit(2)])],
        );
        let step = theory_refutation_trust_step(&artifact);
        assert_eq!(step.id, TrustId::SatRefutation);
        assert!(!step.certified);
    }

    /// The new id is in the canonical iteration order exactly once, so the
    /// rendered ledger cannot omit or duplicate it.
    #[test]
    fn the_modulo_theory_id_is_listed_once() {
        assert_eq!(
            ALL_TRUST_IDS
                .iter()
                .filter(|id| **id == TrustId::SatRefutationModuloTheory)
                .count(),
            1
        );
    }
}
