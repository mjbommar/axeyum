//! The **support matrix**: a four-column, machine-checked report of what the
//! stack does with each SMT-LIB fragment, split into *four independent axes* so
//! "the parser accepts it" is never silently conflated with "the solver decides
//! it" or "the result carries a proof".
//!
//! The [`capabilities`](crate::capabilities) ledger answers *how much to trust a
//! result* (one assurance level per capability). This module answers a different,
//! orthogonal question the README prose used to bury: **per fragment, what is the
//! status on each of four pipeline stages?**
//!
//! 1. **parser-accepts** — does `axeyum-smtlib` parse it? (and is it acted on,
//!    accepted-but-ignored, bounded, or rejected)
//! 2. **IR-semantics** — does `axeyum-ir` model its semantics (sorts/ops/evaluator)?
//! 3. **solver-decides** — does the solver return a definite `sat`/`unsat` for the
//!    fragment's core queries, or degrade to `unknown`?
//! 4. **proof-supports** — does an `unsat` carry an independently checkable proof?
//!
//! The crucial honesty wins are the *non-binary* statuses: "accepted-but-ignored"
//! is a first-class parser status (the `reset` family, `get-model` and friends),
//! and "unsat-supported, sat→unknown" is a first-class solver status (the
//! arithmetic-sorted UF case, where `unsat` is decided but a satisfying model is
//! not built, so `sat` degrades to a sound `unknown`).
//!
//! [`SUPPORT_MATRIX`] is the source of truth; [`support_matrix_markdown`] renders
//! it, and a golden test (`tests/support_matrix.rs`) fails if the committed
//! `docs/research/08-planning/support-matrix.md` drifts from this code.
//! Iteration is in source order (no hash-map nondeterminism — determinism is a
//! public promise). Each cell is derived from a real code path; the most
//! load-bearing solver/proof cells are additionally exercised by probes in the
//! golden test (see that file's `probe_*` tests).

use core::fmt::Write as _;

/// **parser-accepts** axis: what the SMT-LIB front end (`axeyum-smtlib`) does
/// with the construct.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParserStatus {
    /// Parsed and acted on (builds IR / mutates script state).
    Accepted,
    /// Parsed (and arity-checked) but a deliberate no-op in the single-result
    /// `solve_smtlib` facade — e.g. `get-model`, `get-unsat-core`, `get-proof`,
    /// `echo`, `exit`. Some commands also have explicit helper APIs.
    AcceptedIgnored,
    /// Parsed but only over a bounded/restricted shape (e.g. bounded strings,
    /// arrays without nested components, constant-operand-only ops).
    AcceptedBounded,
    /// Deliberately refused with `Unsupported` (e.g. full `reset`, parametric
    /// datatypes, the unbounded `String`/`Seq` sort).
    Rejected,
}

impl ParserStatus {
    /// Short stable label for the rendered matrix.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            ParserStatus::Accepted => "accepted",
            ParserStatus::AcceptedIgnored => "accepted-but-ignored",
            ParserStatus::AcceptedBounded => "accepted (bounded)",
            ParserStatus::Rejected => "rejected",
        }
    }
}

/// **IR-semantics** axis: whether `axeyum-ir` models the construct's semantics
/// (a sort/op the typed IR and ground evaluator understand).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrStatus {
    /// First-class IR sort(s)/op(s) with ground-evaluator semantics.
    Modeled,
    /// Partially modeled (a subset of operations, or modeled only for a bounded shape).
    Partial,
    /// No native IR sort — semantics carried by lowering to bit-vectors/Booleans
    /// (e.g. strings, floating-point values are `BitVec`).
    Lowered,
    /// Not modeled in the IR.
    Absent,
}

impl IrStatus {
    /// Short stable label for the rendered matrix.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            IrStatus::Modeled => "modeled",
            IrStatus::Partial => "partial",
            IrStatus::Lowered => "lowered (no IR sort)",
            IrStatus::Absent => "absent",
        }
    }
}

/// **solver-decides** axis: whether the solver returns a definite `sat`/`unsat`
/// for the fragment's core queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverStatus {
    /// Returns both `sat` and `unsat` definitively for the core fragment.
    Decides,
    /// `unsat` is decided but a satisfying model is not built, so `sat` degrades
    /// to a sound `unknown` (the arithmetic-sorted UF case; the string-length
    /// BV+LIA gap). First-class — never a wrong answer, just an honest `unknown`.
    UnsatSatUnknown,
    /// Sound but incomplete: may return `unknown` in general (nonlinear
    /// arithmetic, quantifiers outside finite/guarded domains, optimization).
    SoundIncomplete,
    /// The solver does not decide this fragment.
    Unsupported,
}

impl SolverStatus {
    /// Short stable label for the rendered matrix.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            SolverStatus::Decides => "decides",
            SolverStatus::UnsatSatUnknown => "unsat decided; sat→unknown",
            SolverStatus::SoundIncomplete => "sound, incomplete (unknown-safe)",
            SolverStatus::Unsupported => "unsupported",
        }
    }
}

/// **proof-supports** axis: whether an `unsat` carries an independently checkable
/// artifact (DRAT, Farkas, Alethe/Carcara, Lean reconstruction, or a re-derived
/// congruence explanation).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofStatus {
    /// `unsat` carries a self-contained certificate re-checkable with no access to
    /// the producing solver (DRAT recheck, Farkas verify, a re-derived congruence
    /// closure, or an end-to-end faithfulness miter).
    Checked,
    /// A certificate exists but only modulo a trusted reduction layer (DRAT at the
    /// clausal layer after a trusted elimination/bit-blast) or only for covered
    /// sub-cases.
    PartialTrust,
    /// No proof artifact — `unsat` is trust-the-solver, or only a `sat` model
    /// replay / conflict core exists.
    NoProof,
}

impl ProofStatus {
    /// Short stable label for the rendered matrix.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            ProofStatus::Checked => "checked",
            ProofStatus::PartialTrust => "partial-trust",
            ProofStatus::NoProof => "none",
        }
    }
}

/// One fragment/feature row of the support matrix: the four independent statuses
/// plus a short, code-grounded note on *why* each cell is what it is.
#[derive(Debug, Clone, Copy)]
pub struct SupportRow {
    /// The logic fragment / feature (the row key).
    pub fragment: &'static str,
    /// parser-accepts status.
    pub parser: ParserStatus,
    /// IR-semantics status.
    pub ir: IrStatus,
    /// solver-decides status.
    pub solver: SolverStatus,
    /// proof-supports status.
    pub proof: ProofStatus,
    /// A short note grounding the cells in the real code paths / caveats.
    pub note: &'static str,
}

/// The support matrix. Ordered deliberately (theories, then features); iteration
/// is in source order for a stable rendered table.
///
/// Keep this honest: a cell asserts the *actual* behavior of the code path named
/// in `note`. Mark conservatively (`partial`/`unknown`/`partial-trust`) rather
/// than overstate — an honest matrix is the whole point.
pub const SUPPORT_MATRIX: &[SupportRow] = &[
    SupportRow {
        fragment: "QF_BV (scalar bit-vectors)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::Checked,
        note: "full scalar op set parsed and modeled; bit-blast to SAT decides both \
               directions; unsat carries a DRAT proof + an end-to-end faithfulness \
               miter (Alethe/Lean too). ADR-0006/0011/0012",
    },
    SupportRow {
        fragment: "QF_ABV (arrays)",
        parser: ParserStatus::AcceptedBounded,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::PartialTrust,
        note: "Canonical arrays admit Bool/BitVec index and element components; eager \
               read-over-write + Ackermann elimination remains the fallback. Unsat DRAT \
               is modulo the trusted (replay-validatable) elimination. ADR-0010/0079",
    },
    SupportRow {
        fragment: "QF_UF (EUF / congruence)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::Checked,
        note: "declare-fun + congruence closure on a backtrackable e-graph decides; \
               unsat carries a congruence explanation re-derived by an independent \
               union-find checker (Alethe + Lean too). ADR-0013/0032",
    },
    SupportRow {
        fragment: "QF_LIA (general linear integer)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::PartialTrust,
        note: "Int sort + div/mod/abs eliminated exactly; Diophantine refutation + \
               branch-and-bound simplex + Gomory cuts decide (degrade to unknown on \
               node budget); general-case unsat DRAT is bounded (refutes at the chosen \
               bit-blast width). Checked-proof sub-fragments are listed separately. \
               ADR-0014/0020/0021",
    },
    SupportRow {
        fragment: "QF_LIA · integer infeasibility (Diophantine + interval)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::Checked,
        note: "integer-systems infeasibility (equality systems, e.g. 2x=1; and the \
               single-variable interval c≤k·x≤d) carries an independent integer-Farkas \
               self-check (Evidence::UnsatDiophantine) AND a kernel-checked Lean proof \
               accepted by the real `lean` binary (discreteness via the ℤ prelude). \
               ADR-0042/0043. General integer-cut (Gomory) proof reconstruction is future.",
    },
    SupportRow {
        fragment: "QF_LRA (linear real)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::Checked,
        note: "exact-rational simplex is complete for QF_LRA; unsat carries a Farkas \
               certificate with a from-scratch independent verifier (Alethe la_generic \
               + Lean too). ADR-0015",
    },
    SupportRow {
        fragment: "QF_NIA (nonlinear integer)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::SoundIncomplete,
        proof: ProofStatus::NoProof,
        note: "general NIA is sound-incomplete (linear abstraction + bounded bit-blast \
               with no-overflow MULTIPLIER GUARDS so small-witness nonlinear sat decides \
               — replay-checked over exact integer semantics; genuine nonlinear-integer \
               unsat is undecidable for bounded blasting ⇒ sound unknown); the \
               single-variable integer polynomial decider (nia_square) is exact (e.g. \
               x*x=2 → unsat). Differentially validated DISAGREE=0 vs Z3. No proof \
               artifact, and proof export is fail-closed (Inconclusive) when overflow \
               guards restrict the blast. ADR-0024",
    },
    SupportRow {
        fragment: "QF_NRA (general nonlinear real)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::SoundIncomplete,
        proof: ProofStatus::NoProof,
        note: "the FALLBACK for the hard coupled/high-degree tail the CAD declines \
               (linear abstraction + replay + McCormick spatial branch-and-bound; \
               relaxation-unsat sound, sat replay-checked, unknown otherwise). No proof \
               artifact for this general fallback. ADR-0024. (The complete CAD decision \
               side and the proof-carrying sub-fragments are listed separately below.)",
    },
    SupportRow {
        fragment: "QF_NRA · cylindrical decomposition (coupled, mixed/non-strict, any dimension)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::NoProof,
        note: "complete CAD decision side: coupled-equality resultant grid (irrational \
               coordinates) + strict and non-strict cylindrical decomposition over open \
               cells AND critical 0-cells, ANY dimension, with RATIONAL or ALGEBRAIC \
               coordinates (algebraic criticals lifted via Res(min-poly, p) + exact \
               RealAlgebraic field arithmetic). Every sat replay-checked; every unsat \
               exhaustive-or-decline (decline propagates, never a gap). Differentially \
               VALIDATED DISAGREE=0 vs Z3 (the NRA + NIA fuzzes found+fixed three real \
               wrong-unsats in shared isolation/sampling/lift code). No proof artifact \
               yet (per-cell Positivstellensatz reconstruction is the open arc). \
               ADR-0044/0045/0046",
    },
    SupportRow {
        fragment: "QF_NRA · degree-2 SOS / globally-(non)negative quadratic forms",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::Checked,
        note: "exact decision via a PSD/sum-of-squares certificate (multivariate AM-GM, \
               (x±y)²<0, …). Self-checking LDLᵀ certificate (Evidence::UnsatSos), AND a \
               kernel-checked Lean proof for both strict directions up to 3-variable \
               AM-GM, accepted by the real `lean` binary. ADR-0039/0040/0041",
    },
    SupportRow {
        fragment: "QF_NRA · single-variable real-algebraic",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::NoProof,
        note: "exact single-variable polynomial decision with irrational (real-algebraic) \
               witnesses (x*x=2 → sat √2, replay-checked by exact sign test); coupled \
               2-var via resultant. No proof artifact yet (sat witnesses are not \
               Lean-reconstructed). ADR-0038",
    },
    SupportRow {
        fragment: "QF_UFLIA / QF_UFLRA (UF + arithmetic)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::PartialTrust,
        note: "eager Ackermann congruence → arithmetic; complete for the conjunctive \
               fragment's UNSAT, and a satisfiable query now yields a REPLAY-CHECKED \
               sat model — the arithmetic model is projected back to a full-Value-keyed \
               function interpretation and replayed against the original assertions \
               (decline to sound unknown on any replay doubt). Alethe proof covers the \
               conjunctive UNSAT sub-cases modulo trusted Ackermann. ADR-0013/0015",
    },
    SupportRow {
        fragment: "QF_FP (floating-point)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Lowered,
        solver: SolverStatus::Decides,
        proof: ProofStatus::PartialTrust,
        note: "FP sorts/ops parsed (some conversions constant-only); FP values are \
               BitVec (no IR sort), lowered to circuits differentially validated vs \
               native/apfloat; unsat DRAT is modulo the trusted FP circuit. \
               ADR-0023/0026/0028",
    },
    SupportRow {
        fragment: "quantifiers (∃/∀, finite-domain + instantiation)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::SoundIncomplete,
        proof: ProofStatus::PartialTrust,
        note: "complete over finite (Bool/BV) domains, guarded-finite Int expansion, \
               and single-variable real Fourier-Motzkin; otherwise sound refutation by \
               e-matching/MBQI/targeted CEGQI. Equality/disequality clause instances are lazily \
               three-valued from justified ground units and congruence: true instances are \
               suppressed, conflicts retain complete source instances, and source-ground unit-like \
               clauses may propagate one detached literal only after a public checker reconstructs \
               the exact instance and replays every false sibling from named facts. Generated \
               equality/disequality premises retain bounded recursive derivations from exact \
               instances or prior checked propagations. Checked equality clauses are inserted into \
               one retained CDCL(T)+EUF session at level zero; learned clauses, activities, and \
               phases survive rounds, while every online refutation still requires ordinary QF \
               replay and unsupported/tampered/resource-limited sessions fall back \
               (ADR-0110/0117/0118/0119). At a source-matching fixpoint, true equalities from a \
               complete SAT candidate may enable nested triggers only inside one rollback matching \
               scope. Exact path queues materialize complete source instances before pop; candidate \
               equalities never become reasons or evidence (ADR-0120). Unresolved/non-clausal \
               instances retain the legacy \
               fallback. The \
               refutation loop compiles/interns triggers once and incrementally extends one shared \
               ground e-graph. Revision-checked indexes extend from add-only node suffixes and \
               root-symbol queues rematch only affected patterns. Real unions update indexes from \
               a deterministic merge journal. Compiled shared declaration/argument parent-path \
               tries select merge-affected pattern terminals. Backtrackable exact root declaration \
               sets filter nested occurrence labels and direct nullary ground siblings before \
               rematching. Retained match caches then append only from newly added or filtered \
               merge-reached top applications; cached joins use current e-class roots \
               (ADR-0111/0112/0113/0114/0115/0116). Checked \
               original-IR UNSAT slices include \
               Euclidean residue and positive-slope affine growth; restricted infinite-domain SAT \
               carries arena-stable affine Skolem recipes checked by separate prenex affine/reflexive \
               and guarded unit-gap original-assertion checkers. The BV subclass accepts only one exact \
               same-width universal identity recipe and reflexive signed/unsigned non-strict order \
               (ADR-0121). A separate outer-BV witness certificate proves one exact equality guard \
               false below a direct nonempty Bool/BV quantifier prefix, making the root implication \
               vacuous without inspecting its consequent (ADR-0122). An exact nested-XOR integer \
               universal carries a separate hierarchical-instantiation certificate. Closed \
               quantifier-free scalar universals can carry concrete binder values replayed directly \
               against the original body; an exact top-level negated existential over a bounded \
               closed Bool/BV body can likewise carry complete values that make the untouched \
               positive body evaluate true (ADR-0126). Closed nested Bool/Int formulas whose binders occur only \
               in equality-to-constant predicates use a checked exact finite quotient. Free-Boolean \
               models of positive Bool/Int universals are checked by source-bound LIA-DPLL plus \
               scalable DRAT closure; Bool/Int/BV closures may instead be discharged structurally \
               only when carried Booleans make every opaque BV predicate irrelevant, with unresolved \
               BV formulas barred from the LIA fallback (ADR-0123). A closed Bool/BV `forall+ exists+` \
               implication with an outer-only antecedent may carry concrete outer values plus a \
               source-regenerated residual QF_BV DRAT proof; existential freshening and proof binding \
               are independently replayed. Large hardware tuples admit at most 1,024 total binders \
               while retaining the 4,096-node matrix cap (ADR-0124/0125). A unique positive universal \
               conjunct may carry a source-bound Bool/BV instance when the whole weakened assertion \
               has a rechecked QF_BV proof (ADR-0127). A nonempty leading existential block may be \
               erased only when a separate checker proves every existential binder absent from the \
               closed Bool/BV universal body and directly evaluates a complete universal assignment \
               to false under 128-binder/4,096-source-node caps (ADR-0128). Positive universal UNSAT with only free Booleans can carry a \
               checked finite counterexample cover: every concrete source instance excludes one \
               sufficient cube and the independently refuted weakened skeleton proves coverage. The \
               one-universal-conjunct slice reconstructs those covers through genuine quantifier \
               applications and bounded kernel case analysis; repeated closed proof-DAG nodes export \
               once through binder-safe Lean definitions. General free-BV models, piecewise/general Skolem functions, \
               non-equality online antecedents, direct online proof serialization, high-frequency \
               assignment callbacks, negative quantifier contexts, broader alternation/functions, \
               general nested QE/QSAT, and broad proof reconstruction remain incomplete. \
               ADR-0016/0032/0095/0096/0097/0098/0099/0100/0101/0107/0108/0109/0110/0111/0112/0113/0114/0115/0116/0117/0118/0119/0120/0121/0122/0123/0124/0125/0126/0127/0128",
    },
    SupportRow {
        fragment: "datatypes (algebraic)",
        parser: ParserStatus::AcceptedBounded,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::PartialTrust,
        note: "non-parametric declare-datatype(s) parsed (parametric rejected); \
               structural acyclicity/injectivity + elimination/native expansion \
               decide; unsat DRAT modulo trusted datatype folding (Alethe/Lean too). \
               ADR-0022",
    },
    SupportRow {
        fragment: "strings (bounded)",
        parser: ParserStatus::AcceptedBounded,
        ir: IrStatus::Lowered,
        solver: SolverStatus::UnsatSatUnknown,
        proof: ProofStatus::NoProof,
        note: "no String IR sort — declare-const lowered to a bounded packed BV \
               (len ≤ 16); ops parsed within the bound; sat decided through the BV \
               path but str.len unsat may be unknown (BV+LIA gap). Model replay only, \
               no unsat proof. ADR-0025/0029",
    },
    SupportRow {
        fragment: "optimization (OMT: box/lex/Pareto, MaxSAT, MILP)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::SoundIncomplete,
        proof: ProofStatus::NoProof,
        note: "maximize/minimize parsed and acted on; each optimum is certified only \
               by an internal confirmed-unsat domination query (no exported artifact) \
               and degrades to a sound OptOutcome::Unknown when a probe is undecided. \
               ADR-0027",
    },
    SupportRow {
        fragment: "incremental (push/pop, reset-assertions)",
        parser: ParserStatus::Accepted,
        ir: IrStatus::Modeled,
        solver: SolverStatus::Decides,
        proof: ProofStatus::NoProof,
        note: "push/pop and reset-assertions parsed (full `reset` is rejected); warm \
               QF_BV/Bool with assumption-core pruning + all-SAT decides; supported \
               BV-indexed Bool/BV array reads, scalar UFs, bounded structural reads, \
               scalar-keyed array-valued UF parents, projection-owned equality, exact \
               top-level structural diff witnesses, positive structural equality, Boolean \
               relation flags, and direct/supported-structural/nested-application \
               array-valued UF parameters retain private owners in the persistent engine. \
               Exact transitive ROW summaries stay dormant until candidate violation; \
               array-result reads/relations/keys use conditional congruence, array-first/\
               function-second projection, structural owner realization, and replay. \
               Nested/extended arrays and DRAT/Alethe across push/pop remain deferred. \
               ADR-0009/0030/0086/0087/0088/0089/0090/0091/0092/0093/0094",
    },
];

/// Renders [`SUPPORT_MATRIX`] as the canonical support-matrix markdown document.
///
/// Golden-tested against `docs/research/08-planning/support-matrix.md`; that file
/// is regenerated from here, never hand-edited.
#[must_use]
pub fn support_matrix_markdown() -> String {
    let mut out = String::new();
    out.push_str("# Support matrix (4-column)\n\n");
    out.push_str(
        "Generated from `axeyum_solver::support_matrix::SUPPORT_MATRIX` — do not edit by hand.\n\
         Regenerate after changing the source of truth and commit the result; a golden test\n\
         (`tests/support_matrix.rs`) fails if this file drifts from the code.\n\n",
    );
    out.push_str(
        "Four **independent** axes per SMT-LIB fragment, so \"the parser accepts it\" is never \
         conflated with \"the solver decides it\" or \"the result carries a proof\". The \
         companion [capability matrix](capability-matrix.md) gives the *assurance* of a \
         result; this one gives the per-stage *status*.\n\n",
    );

    out.push_str("## Legend\n\n");
    out.push_str(
        "**parser-accepts** (does `axeyum-smtlib` parse it?):\n\
         - **accepted** — parsed and acted on.\n\
         - **accepted-but-ignored** — parsed but a deliberate no-op in the single-result \
           `solve_smtlib` facade (e.g. `get-model`, `get-unsat-core`, `get-proof`, \
           `echo`, `exit`); some commands also have explicit helper APIs.\n\
         - **accepted (bounded)** — parsed only over a bounded/restricted shape (bounded \
           strings; arrays without nested components; constant-operand-only ops; \
           non-parametric datatypes).\n\
         - **rejected** — deliberately refused (full `reset`, parametric datatypes, the \
           unbounded `String`/`Seq` sort).\n\n",
    );
    out.push_str(
        "**IR-semantics** (does `axeyum-ir` model its semantics?):\n\
         - **modeled** — first-class IR sort(s)/op(s) with ground-evaluator semantics.\n\
         - **partial** — a subset of operations / only a bounded shape.\n\
         - **lowered (no IR sort)** — no native sort; semantics via bit-vector/Boolean lowering \
           (strings, floating-point values).\n\
         - **absent** — not modeled.\n\n",
    );
    out.push_str(
        "**solver-decides** (definite `sat`/`unsat` for the core queries?):\n\
         - **decides** — returns both `sat` and `unsat` for the core fragment.\n\
         - **unsat decided; sat→unknown** — `unsat` is decided but a satisfying model is not \
           built, so `sat` degrades to a sound `unknown` (the `str.len` BV+LIA gap). \
           First-class — never a wrong answer.\n\
         - **sound, incomplete (unknown-safe)** — may return `unknown` in general (nonlinear \
           arithmetic, quantifiers outside finite/guarded domains, optimization).\n\
         - **unsupported** — not decided.\n\n",
    );
    out.push_str(
        "**proof-supports** (does an `unsat` carry a checkable proof?):\n\
         - **checked** — self-contained certificate re-checkable with no access to the producing \
           solver (DRAT recheck, Farkas verify, a re-derived congruence closure, end-to-end \
           faithfulness miter).\n\
         - **partial-trust** — a certificate exists modulo a trusted reduction layer (clausal \
           DRAT after a trusted elimination/bit-blast) or only for covered sub-cases.\n\
         - **none** — no proof artifact (`sat` model replay / conflict core only).\n\n",
    );

    out.push_str("## Matrix\n\n");
    out.push_str(
        "| Fragment | parser-accepts | IR-semantics | solver-decides | proof-supports |\n",
    );
    out.push_str("|---|---|---|---|---|\n");
    for r in SUPPORT_MATRIX {
        // `write!` to a String is infallible; the result is intentionally ignored.
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            r.fragment,
            r.parser.label(),
            r.ir.label(),
            r.solver.label(),
            r.proof.label(),
        );
    }

    out.push_str("\n## Notes (per row)\n\n");
    for r in SUPPORT_MATRIX {
        let _ = writeln!(out, "- **{}** — {}", r.fragment, r.note);
    }

    out
}
