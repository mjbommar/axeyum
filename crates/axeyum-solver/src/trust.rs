//! The reduction **trust ledger** (P3.0): every reduction the stack relies on is
//! a named, countable [`TrustId`] with a pedantic level, mirroring cvc5's
//! `TrustId`. This turns the implicit "checked **modulo trusted reduction**"
//! caveat into an auditable list — the precondition for shrinking the trusted
//! base to zero (Track 3 in `docs/plan/track-3-proof-lean/`).
//!
//! A reduction is **certified** when an independent per-query checker re-derives
//! it (bit-blast via the exhaustive miter; Tseitin/SAT via DRAT; Farkas /
//! lazy-SMT / term-level enumeration by their verifiers) and a **trust hole**
//! when it is a sound (equi)satisfiability transform with no per-query
//! certificate yet. A produced [`crate::EvidenceReport`] records the
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
    /// Floating-point operators → BV circuits (ADR-0023).
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

impl TrustId {
    /// Stable label used in the rendered ledger and provenance.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            TrustId::BitBlast => "bit-blast",
            TrustId::Tseitin => "tseitin",
            TrustId::SatRefutation => "sat-refutation",
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
            TrustId::ArrayElim | TrustId::Ackermann | TrustId::DatatypeElim => 4,
            // Search-only XOR UNSAT has no per-query certificate and a wrong
            // refutation is unsound with no recovery, so it grades low (ADR-0035).
            TrustId::IntBlast | TrustId::XorGaussian => 3,
        }
    }

    /// Whether *every* result depending on this reduction has an independent
    /// per-query checker today (the bit-blast miter; DRAT for Tseitin/SAT;
    /// Farkas/lazy-SMT/enumeration verifiers). Trust holes return `false` — these
    /// are what Track 3 P3.5 drives to zero.
    ///
    /// This is the **conservative** ledger status: a reduction returns `true` only
    /// when no result that relies on it is trusted-uncertified. [`XorGaussian`]
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
    /// [`XorGaussian`]: TrustId::XorGaussian
    /// [`IntBlast`]: TrustId::IntBlast
    /// [`Ackermann`]: TrustId::Ackermann
    /// [`ArrayElim`]: TrustId::ArrayElim
    #[must_use]
    pub const fn is_certified(self) -> bool {
        match self {
            TrustId::BitBlast
            | TrustId::Tseitin
            | TrustId::SatRefutation
            | TrustId::TermLevelEnum
            | TrustId::Farkas
            | TrustId::LraDpll
            | TrustId::Sos
            | TrustId::Diophantine => true,
            TrustId::ArrayElim
            | TrustId::Ackermann
            | TrustId::IntBlast
            | TrustId::DatatypeElim
            | TrustId::Fpa2Bv
            | TrustId::XorGaussian => false,
        }
    }

    /// The governing architecture-decision record.
    #[must_use]
    pub const fn reference(self) -> &'static str {
        match self {
            TrustId::BitBlast | TrustId::Tseitin => "ADR-0006",
            TrustId::SatRefutation => "ADR-0012",
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
/// it (e.g. bit-blast is `certified: true` only on the end-to-end miter route,
/// `false` on the plain DRAT export route — even though a miter route *exists*,
/// per [`TrustId::is_certified`]).
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
         **certified** = an independent per-query checker re-derives the step \
         (bit-blast miter / DRAT / Farkas / enumeration); **trust hole** = a sound \
         reduction with no per-query certificate yet (the base Track 3 P3.5 drives to \
         zero).\n\n",
    );
    let holes = ALL_TRUST_IDS.iter().filter(|t| !t.is_certified()).count();
    let _ = writeln!(
        out,
        "Trusted base: **{holes}** reduction(s) remain trust holes.\n"
    );
    out.push_str("| Reduction | Meaning | Pedantic | Status | Ref |\n");
    out.push_str("|---|---|---|---|---|\n");
    for &id in ALL_TRUST_IDS {
        let status = if id.is_certified() {
            "certified"
        } else {
            "trust hole"
        };
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            id.label(),
            id.meaning(),
            id.pedantic_level(),
            status,
            id.reference(),
        );
    }
    out
}
