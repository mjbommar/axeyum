//! The certificate for a **clause-loop** refutation, and its checker
//! (ADR-2131, lane `NRA-CLAUSE-LOOP`).
//!
//! # What this closes
//!
//! [`crate::nra_clause_loop`] shipped its `sat` half and **withheld** its
//! `unsat`, and its module docs named exactly three things that half would rest
//! on and had no checker for:
//!
//! 1. the Tseitin abstraction being equisatisfiable with the original query,
//! 2. every blocking clause being implied over the reals,
//! 3. the SAT core's refutation of the resulting clause set.
//!
//! This module is the checker for all three, and the route emits `unsat` only
//! when it accepts. Each is discharged by a different kind of evidence, and the
//! split matters because the three are not equally hard:
//!
//! * **(2) is the theory obligation** and it is discharged by the evidence that
//!   already exists: every blocking clause carries the
//!   [`CellRefutation`](crate::nra_cell_cert::CellRefutation) whose covering
//!   closed it, and [`check_cell_refutation`] — ADR-2126's exact checker — is
//!   run on it here, independently of the producer having run it.
//! * **(3) is the propositional obligation** and it is discharged by a DRAT
//!   refutation from [`axeyum_cnf::solve_with_drat_proof`], checked by
//!   [`axeyum_cnf::check_drat`]. Note which solver produces it: the clause loop
//!   searches with [`axeyum_cnf::IncrementalSat`], and the proof comes from a
//!   **second, independent solve** by the proof-producing core. A bug in the
//!   incremental solver's refutation cannot reach the verdict, because its
//!   refutation is not what is checked.
//! * **(1) is the abstraction obligation**, and it is the one with no
//!   off-the-shelf checker. It is discharged structurally: see below.
//!
//! # How the abstraction is checked without re-running the encoder
//!
//! The naive move is to re-encode the query in the checker and compare. That is
//! not a check, it is the producer run twice. What this checker does instead:
//!
//! **The certificate does not carry the clause list at all.** It carries the
//! *gate table* — one [`GateDef`] per Tseitin gate variable, naming its
//! connective and its input literals — and the checker derives the clauses
//! itself. So a producer cannot smuggle in a clause; there is nowhere to put
//! one. The three things the checker then establishes:
//!
//! * **Freshness.** Every gate variable is defined exactly once and is distinct
//!   from every atom variable. This is what makes the gate definitions a
//!   *conservative extension*: a fresh variable constrained only by `g ↔ φ`
//!   cannot turn a satisfiable formula unsatisfiable. It is the whole soundness
//!   argument for obligation (1) and it is three lines to check.
//! * **Faithfulness.** [`check_encodes`] walks the ORIGINAL assertion terms
//!   against the gate table, confirming that the literal claimed for each
//!   assertion really does denote that term: a `not` flips polarity, an `and` /
//!   `or` / `=>` / `xor` node must be a gate of the matching kind whose inputs
//!   recursively denote the arguments, and a leaf must be a polynomial
//!   comparison equal to the certificate's atom for that variable. This walk
//!   reads the terms and the table; it never builds a clause.
//! * **Rooting.** The unit clauses are exactly the literals for the assertions,
//!   one per assertion, none missing and none extra.
//!
//! What is *shared* with the producer is [`gate_clauses`], the function mapping
//! one gate definition to its clauses — deliberately, because a second
//! hand-written copy would drift. It is pinned by
//! `gate_clauses_are_exactly_the_connective` , which enumerates every assignment
//! over the gate and its inputs and requires the clause set to be satisfied by
//! exactly the rows where `g ↔ op(inputs)`. An exhaustive semantic test on the
//! shared function is stronger evidence than a duplicate implementation.
//!
//! # Why the cited atoms, and why that is checked
//!
//! A blocking clause is over the atoms the covering CITED, not over the whole
//! Boolean assignment. That is sound — a covering in which every cell is closed
//! by one of the cited atoms proves the cited atoms alone jointly unsatisfiable,
//! and a finer arrangement does not weaken a refutation — but "the producer only
//! cited these" is a claim. So [`check_clause_refutation`] walks the whole
//! covering tree and **rejects** a lemma whose tree names an atom outside the
//! clause ([`ClauseCheckFailure::LemmaCellOutsideClause`]). The certificate
//! therefore carries every distinction its producer made.
//!
//! # What a rejection costs
//!
//! Nothing but the verdict. A refutation the checker refuses is DROPPED — the
//! route records [`crate::nra_real_root::CadDecline::ClauseLoopCertificateRejected`]
//! and the query falls through to the rest of the ladder. There is no weakened
//! answer and no partial credit.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, check_drat};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::nra_cell_cert::{
    CellCheckFailure, CellCheckStats, CellReason, CertAtom, check_cell_refutation,
};
use crate::nra_cell_cert::{CellCovering, CellRefutation};
use crate::nra_real_root::cert_atom_of;

/// The Boolean connective a Tseitin gate defines.
///
/// `=>` is absent on purpose: the encoder writes `a => b` as an `Or` gate over
/// `[¬a, b]`, so there is no third clause shape and no third truth table. The
/// checker knows that and matches the TERM's `=>` against an `Or` gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateKind {
    /// `g ↔ ⋀ inputs`
    And,
    /// `g ↔ ⋁ inputs`
    Or,
    /// `g ↔ (inputs[0] ⊕ inputs[1])`, exactly two inputs.
    Xor,
}

impl GateKind {
    /// A stable, matchable key.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
        }
    }
}

/// One Tseitin gate: a fresh variable and the connective it abbreviates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateDef {
    var: CnfVar,
    kind: GateKind,
    inputs: Vec<CnfLit>,
}

impl GateDef {
    /// Build a gate definition.
    #[must_use]
    pub fn new(var: CnfVar, kind: GateKind, inputs: Vec<CnfLit>) -> Self {
        Self { var, kind, inputs }
    }

    /// The defined variable.
    #[must_use]
    pub const fn var(&self) -> CnfVar {
        self.var
    }

    /// The connective.
    #[must_use]
    pub const fn kind(&self) -> GateKind {
        self.kind
    }

    /// The input literals, in the order the term's arguments appear.
    #[must_use]
    pub fn inputs(&self) -> &[CnfLit] {
        &self.inputs
    }
}

/// One learned clause with the covering that justifies it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoryLemma {
    clause: CnfClause,
    polarity: Vec<bool>,
    cited: Vec<usize>,
    refutation: CellRefutation,
}

impl TheoryLemma {
    /// Assemble a lemma.
    ///
    /// `polarity` is the Boolean model the theory was asked about — one entry
    /// per certificate atom — and `cited` the atom indices the covering used.
    #[must_use]
    pub fn new(
        clause: CnfClause,
        polarity: Vec<bool>,
        cited: Vec<usize>,
        refutation: CellRefutation,
    ) -> Self {
        Self {
            clause,
            polarity,
            cited,
            refutation,
        }
    }

    /// The learned clause.
    #[must_use]
    pub const fn clause(&self) -> &CnfClause {
        &self.clause
    }

    /// The covering that refutes the cited atoms.
    #[must_use]
    pub const fn refutation(&self) -> &CellRefutation {
        &self.refutation
    }
}

/// A complete, checkable refutation of a Boolean combination of sign atoms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClauseRefutation {
    atoms: Vec<CertAtom>,
    gates: Vec<GateDef>,
    roots: Vec<CnfLit>,
    lemmas: Vec<TheoryLemma>,
    drat: Vec<DratStep>,
}

impl ClauseRefutation {
    /// Assemble a refutation.
    #[must_use]
    pub fn new(
        atoms: Vec<CertAtom>,
        gates: Vec<GateDef>,
        roots: Vec<CnfLit>,
        lemmas: Vec<TheoryLemma>,
        drat: Vec<DratStep>,
    ) -> Self {
        Self {
            atoms,
            gates,
            roots,
            lemmas,
            drat,
        }
    }

    /// The distinct polynomial comparisons; atom `i` is propositional variable `i`.
    #[must_use]
    pub fn atoms(&self) -> &[CertAtom] {
        &self.atoms
    }

    /// The Tseitin gate table.
    #[must_use]
    pub fn gates(&self) -> &[GateDef] {
        &self.gates
    }

    /// One literal per original assertion.
    #[must_use]
    pub fn roots(&self) -> &[CnfLit] {
        &self.roots
    }

    /// The theory lemmas, each with its covering.
    #[must_use]
    pub fn lemmas(&self) -> &[TheoryLemma] {
        &self.lemmas
    }

    /// The DRAT refutation of the derived clause set.
    #[must_use]
    pub fn drat(&self) -> &[DratStep] {
        &self.drat
    }

    /// Replace the DRAT proof, keeping everything else.
    ///
    /// The proof is produced AFTER the rest of the certificate exists, because
    /// the formula it refutes is derived from the rest.
    pub fn set_drat(&mut self, drat: Vec<DratStep>) {
        self.drat = drat;
    }
}

/// What [`check_clause_refutation`] counted while accepting.
///
/// Counts, not a boolean: "accepted" having examined no lemma, no gate and no
/// cell is the vacuous pass a boolean cannot distinguish, and a fuzz that
/// asserts a nonzero `lemmas` is asserting the checker did work.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ClauseCheckStats {
    /// Certificate atoms.
    pub atoms: usize,
    /// Gate definitions whose freshness and faithfulness were checked.
    pub gates: usize,
    /// Assertion terms walked against the gate table.
    pub roots: usize,
    /// Term/literal pairs the faithfulness walk verified.
    pub encode_steps: usize,
    /// Theory lemmas whose covering the cell checker accepted.
    pub lemmas: usize,
    /// Cells the cell checker examined, summed over every lemma.
    pub lemma_cells: usize,
    /// Exact root-freeness tests the cell checker ran, summed over every lemma.
    pub lemma_exact_tests: usize,
    /// Clauses the checker DERIVED (gate definitions + roots + lemmas).
    pub derived_clauses: usize,
    /// DRAT steps the propositional checker verified.
    pub drat_steps: usize,
}

/// Why a clause refutation was rejected.
///
/// Every variant names ONE check, so a test can assert which guard fired rather
/// than only that something did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClauseCheckFailure {
    /// No atoms, no assertions, or no lemmas.
    Empty,
    /// A gate variable is also an atom variable, so its definition clauses are
    /// not a conservative extension.
    GateShadowsAtom {
        /// The offending variable index.
        var: usize,
    },
    /// A gate variable is defined more than once.
    GateRedefined {
        /// The offending variable index.
        var: usize,
    },
    /// A gate's input count does not match its connective.
    GateArity {
        /// The offending variable index.
        var: usize,
        /// The connective it claims, as [`GateKind::name`] spells it. Carried
        /// because "wrong arity" without the connective does not say what the
        /// right arity would have been.
        kind: &'static str,
        /// How many inputs it carries.
        inputs: usize,
    },
    /// The root literal count does not match the assertion count.
    RootArity {
        /// Assertions in the query.
        expected: usize,
        /// Root literals in the certificate.
        found: usize,
    },
    /// The literal claimed for an assertion does not denote that term.
    EncodingMismatch {
        /// Which assertion.
        assertion_index: usize,
    },
    /// The faithfulness walk exceeded its step budget.
    EncodingBudget,
    /// A lemma's polarity vector is not one entry per certificate atom.
    LemmaPolarityArity {
        /// Which lemma.
        lemma: usize,
        /// Entries it carries.
        found: usize,
    },
    /// A lemma's covering was built over atoms that are not the certificate's
    /// atoms under the lemma's own polarity.
    LemmaAtomMismatch {
        /// Which lemma.
        lemma: usize,
        /// Which atom index.
        atom_index: usize,
    },
    /// A lemma's clause is not the negation of its cited assignment.
    LemmaClauseMismatch {
        /// Which lemma.
        lemma: usize,
    },
    /// A lemma's covering closes a cell with an atom its clause does not cite,
    /// so the clause claims more than the covering proves.
    LemmaCellOutsideClause {
        /// Which lemma.
        lemma: usize,
        /// The atom index the covering used.
        atom_index: usize,
    },
    /// The cell checker refused a lemma's covering.
    LemmaCellRejected {
        /// Which lemma.
        lemma: usize,
        /// The cell checker's own reason.
        failure: CellCheckFailure,
    },
    /// The derived clause set could not be formed (a literal outside the
    /// declared variable range).
    FormulaMalformed,
    /// The DRAT proof does not refute the derived clause set.
    DratRejected,
}

impl ClauseCheckFailure {
    /// A stable, matchable key. **Exhaustive, so a new guard does not compile
    /// until it is named here** (ADR-2060's method).
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Empty => "empty",
            Self::GateShadowsAtom { .. } => "gate-shadows-atom",
            Self::GateRedefined { .. } => "gate-redefined",
            Self::GateArity { .. } => "gate-arity",
            Self::RootArity { .. } => "root-arity",
            Self::EncodingMismatch { .. } => "encoding-mismatch",
            Self::EncodingBudget => "encoding-budget",
            Self::LemmaPolarityArity { .. } => "lemma-polarity-arity",
            Self::LemmaAtomMismatch { .. } => "lemma-atom-mismatch",
            Self::LemmaClauseMismatch { .. } => "lemma-clause-mismatch",
            Self::LemmaCellOutsideClause { .. } => "lemma-cell-outside-clause",
            Self::LemmaCellRejected { .. } => "lemma-cell-rejected",
            Self::FormulaMalformed => "formula-malformed",
            Self::DratRejected => "drat-rejected",
        }
    }
}

/// Damage a certificate in ONE named way, for the adversarial fixtures.
///
/// # Why this exists rather than a hand-built certificate
///
/// A fixture that assembles a certificate from scratch tests the checker
/// against a shape the PRODUCER never emits, which is the easy half. What has to
/// be shown is that a certificate the producer really built, for a query the
/// route really refutes, stops being accepted when one part of it is damaged --
/// and that each part has its OWN guard. So the fixture takes a live
/// certificate, applies exactly one mutation, and requires a NAMED rejection.
///
/// # Ordering, which is the whole point
///
/// The DRAT proof is attached BEFORE the mutation. Mutating first and proving
/// afterwards would produce a valid proof of the damaged clause set, and the
/// checker would be right to accept it -- the fixture would pass while checking
/// nothing. Proof first, damage second, is what makes the guard the subject.
///
/// Returns `false` when the certificate has no such feature to damage (for
/// instance no gate, on a query with no Boolean structure). A fixture must
/// assert on that return value: a mutation that silently did nothing turns the
/// test into a measurement of the mutator.
#[must_use]
pub fn apply_mutation(cert: &mut ClauseRefutation, mutation: &str) -> bool {
    match mutation {
        // The control. Nothing is damaged and the checker must ACCEPT -- without
        // it, every rejection below is consistent with a checker that refuses
        // everything.
        "none" => true,

        // The certificate-drop fixture the brief names: damage a learned
        // clause's CELL so the covering closes a cell with an atom the clause
        // does not cite. The clause set is untouched, so the DRAT proof still
        // checks and only the cited-atom guard can catch it.
        "lemma-cell" => {
            let Some(lemma) = cert.lemmas.first_mut() else {
                return false;
            };
            let cited: Vec<usize> = lemma.cited.clone();
            if cited.is_empty() || cert.atoms.len() < 2 {
                return false;
            }
            // Point one Atom cell at an atom index outside the cited set.
            let Some(outsider) = (0..cert.atoms.len()).find(|i| !cited.contains(i)) else {
                return false;
            };
            retarget_first_atom_cell(&mut lemma.refutation, outsider)
        }

        // Drop a literal from a learned clause. The clause is then STRONGER than
        // its covering justifies, which is the direction that costs soundness.
        "lemma-clause" => {
            let Some(lemma) = cert.lemmas.iter_mut().find(|l| l.clause.lits().len() > 1) else {
                return false;
            };
            let mut lits = lemma.clause.lits().to_vec();
            lits.pop();
            lemma.clause = CnfClause::new(lits);
            true
        }

        // Truncate the propositional proof. The clause set is intact and the
        // lemmas are intact; only the refutation of the abstraction is gone.
        "drat" => {
            if cert.drat.is_empty() {
                return false;
            }
            cert.drat.pop();
            true
        }

        // Change a gate's connective. The gate table then no longer describes
        // the assertions, and the faithfulness walk is the only thing that can
        // see it -- the derived clauses are perfectly well-formed for the WRONG
        // connective.
        "gate-kind" => {
            let Some(def) = cert.gates.iter_mut().find(|d| d.inputs.len() == 2) else {
                return false;
            };
            def.kind = match def.kind {
                GateKind::And => GateKind::Or,
                GateKind::Or | GateKind::Xor => GateKind::And,
            };
            true
        }

        // Drop an assertion's root literal, so the certificate refutes a
        // SUBSET of the query. Every remaining clause is still implied, so only
        // the arity guard can see it.
        "root" => {
            if cert.roots.len() < 2 {
                return false;
            }
            cert.roots.pop();
            true
        }

        // Let a gate variable collide with an atom variable, breaking the
        // conservative-extension argument that the whole abstraction rests on.
        "gate-shadow" => {
            if cert.atoms.is_empty() {
                return false;
            }
            let Some(def) = cert.gates.first_mut() else {
                return false;
            };
            let Ok(v) = CnfVar::new(0) else {
                return false;
            };
            def.var = v;
            true
        }

        _ => false,
    }
}

/// Point the first `Atom` cell of a covering tree at `atom_index`.
fn retarget_first_atom_cell(refutation: &mut CellRefutation, atom_index: usize) -> bool {
    fn walk(cov: &mut CellCovering, atom_index: usize) -> bool {
        for cell in cov.cells_mut() {
            match cell {
                CellReason::Atom { atom_index: a } => {
                    *a = atom_index;
                    return true;
                }
                CellReason::Deeper { sub, .. } => {
                    if walk(sub, atom_index) {
                        return true;
                    }
                }
                CellReason::Undecided => {}
            }
        }
        false
    }
    walk(refutation.root_mut(), atom_index)
}

/// The most term/literal pairs the faithfulness walk will verify.
///
/// A refusal by declaration, like every other bound on this route. The walk is
/// over a DAG with memoisation so it is linear in the term count, but a bound
/// that is checked is worth more than an argument that it cannot be reached.
const MAX_ENCODE_STEPS: usize = 1 << 16;

/// The clauses one gate definition contributes.
///
/// Shared with the producer, and pinned by an exhaustive truth-table test rather
/// than by a second hand-written copy: see the module docs.
#[must_use]
pub fn gate_clauses(def: &GateDef) -> Vec<CnfClause> {
    let g = CnfLit::positive(def.var());
    let inputs = def.inputs();
    let mut out = Vec::new();
    match def.kind() {
        GateKind::And => {
            let mut back = Vec::with_capacity(inputs.len() + 1);
            back.push(g);
            for &k in inputs {
                out.push(CnfClause::new(vec![g.negated(), k]));
                back.push(k.negated());
            }
            out.push(CnfClause::new(back));
        }
        GateKind::Or => {
            let mut fwd = Vec::with_capacity(inputs.len() + 1);
            fwd.push(g.negated());
            for &k in inputs {
                out.push(CnfClause::new(vec![g, k.negated()]));
                fwd.push(k);
            }
            out.push(CnfClause::new(fwd));
        }
        GateKind::Xor => {
            // Two inputs by construction; `GateArity` rejects anything else
            // before this runs.
            if inputs.len() == 2 {
                let (a, b) = (inputs[0], inputs[1]);
                out.push(CnfClause::new(vec![g.negated(), a, b]));
                out.push(CnfClause::new(vec![g.negated(), a.negated(), b.negated()]));
                out.push(CnfClause::new(vec![g, a.negated(), b]));
                out.push(CnfClause::new(vec![g, a, b.negated()]));
            }
        }
    }
    out
}

/// The clause set a certificate stands for: gate definitions, assertion units,
/// and theory lemmas, in that order.
///
/// Derived, never carried. The producer builds the formula it proves with this
/// function and the checker rebuilds it with the same one, so "the proof refutes
/// the certificate" is not a claim about two lists agreeing.
fn derive_formula(cert: &ClauseRefutation) -> Option<CnfFormula> {
    let mut max_var = 0usize;
    let note = |l: CnfLit, max: &mut usize| *max = (*max).max(l.var().index());
    for g in cert.gates() {
        max_var = max_var.max(g.var().index());
        for &i in g.inputs() {
            note(i, &mut max_var);
        }
    }
    for &r in cert.roots() {
        note(r, &mut max_var);
    }
    for l in cert.lemmas() {
        for &lit in l.clause().lits() {
            note(lit, &mut max_var);
        }
    }
    max_var = max_var.max(cert.atoms().len().saturating_sub(1));

    let mut f = CnfFormula::new(max_var + 1);
    for g in cert.gates() {
        for c in gate_clauses(g) {
            f.add_clause(c).ok()?;
        }
    }
    for &r in cert.roots() {
        f.add_clause(CnfClause::new(vec![r])).ok()?;
    }
    for l in cert.lemmas() {
        f.add_clause(l.clause().clone()).ok()?;
    }
    Some(f)
}

/// The clause set a certificate stands for, for the producer.
///
/// The producer needs the same formula the checker will rebuild, so it calls
/// this rather than assembling one of its own.
pub(crate) fn formula_of(cert: &ClauseRefutation) -> Option<CnfFormula> {
    derive_formula(cert)
}

/// Check a clause-loop refutation against the ORIGINAL query.
///
/// Accepts only when all three obligations in the module docs are discharged.
/// The returned [`ClauseCheckStats`] say what was examined.
///
/// # Errors
///
/// Returns the one check that failed. A rejection is a refusal to certify, not
/// a claim that the query is satisfiable.
pub fn check_clause_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    cert: &ClauseRefutation,
) -> Result<ClauseCheckStats, ClauseCheckFailure> {
    if cert.atoms().is_empty() || assertions.is_empty() || cert.lemmas().is_empty() {
        return Err(ClauseCheckFailure::Empty);
    }
    let mut stats = ClauseCheckStats {
        atoms: cert.atoms().len(),
        ..ClauseCheckStats::default()
    };

    // --- Check 1: the gate table is a CONSERVATIVE EXTENSION. ---
    // Every gate variable defined once, and never an atom variable. This is the
    // entire soundness argument for the abstraction obligation, so it runs first
    // and nothing below is meaningful without it.
    let mut gates: BTreeMap<usize, &GateDef> = BTreeMap::new();
    for def in cert.gates() {
        let v = def.var().index();
        if v < cert.atoms().len() {
            return Err(ClauseCheckFailure::GateShadowsAtom { var: v });
        }
        let arity_ok = match def.kind() {
            GateKind::And | GateKind::Or => def.inputs().len() >= 2,
            GateKind::Xor => def.inputs().len() == 2,
        };
        if !arity_ok {
            return Err(ClauseCheckFailure::GateArity {
                var: v,
                kind: def.kind().name(),
                inputs: def.inputs().len(),
            });
        }
        if gates.insert(v, def).is_some() {
            return Err(ClauseCheckFailure::GateRedefined { var: v });
        }
        stats.gates += 1;
    }

    // --- Check 2: the roots are one literal per assertion. ---
    if cert.roots().len() != assertions.len() {
        return Err(ClauseCheckFailure::RootArity {
            expected: assertions.len(),
            found: cert.roots().len(),
        });
    }

    // --- Check 3: FAITHFULNESS. Each root literal denotes its assertion. ---
    let mut seen: BTreeSet<(TermId, CnfLit)> = BTreeSet::new();
    for (j, (&term, &lit)) in assertions.iter().zip(cert.roots().iter()).enumerate() {
        match check_encodes(arena, term, lit, cert, &gates, &mut seen, &mut stats) {
            Ok(()) => stats.roots += 1,
            Err(ClauseCheckFailure::EncodingBudget) => {
                return Err(ClauseCheckFailure::EncodingBudget);
            }
            Err(_) => {
                return Err(ClauseCheckFailure::EncodingMismatch { assertion_index: j });
            }
        }
    }

    // --- Check 4: every lemma is a THEORY lemma, justified by its covering. ---
    for (li, lemma) in cert.lemmas().iter().enumerate() {
        check_lemma(li, lemma, cert, &mut stats)?;
        stats.lemmas += 1;
    }

    // --- Check 5: the derived clause set is propositionally REFUTED. ---
    let formula = derive_formula(cert).ok_or(ClauseCheckFailure::FormulaMalformed)?;
    stats.derived_clauses = formula.clauses().len();
    stats.drat_steps = cert.drat.len();
    match check_drat(&formula, cert.drat()) {
        Ok(true) => Ok(stats),
        _ => Err(ClauseCheckFailure::DratRejected),
    }
}

/// One lemma: its polarity, its atoms, its clause, its covering.
fn check_lemma(
    li: usize,
    lemma: &TheoryLemma,
    cert: &ClauseRefutation,
    stats: &mut ClauseCheckStats,
) -> Result<(), ClauseCheckFailure> {
    if lemma.polarity.len() != cert.atoms().len() {
        return Err(ClauseCheckFailure::LemmaPolarityArity {
            lemma: li,
            found: lemma.polarity.len(),
        });
    }

    // The covering must have been built over exactly the certificate's atoms
    // under this lemma's polarity. Anything else and the covering refutes a
    // DIFFERENT conjunction than the clause names.
    let refuted = lemma.refutation().atoms();
    if refuted.len() != cert.atoms().len() {
        return Err(ClauseCheckFailure::LemmaAtomMismatch {
            lemma: li,
            atom_index: refuted.len().min(cert.atoms().len()),
        });
    }
    for (i, (want, got)) in cert.atoms().iter().zip(refuted.iter()).enumerate() {
        let expected = if lemma.polarity[i] {
            want.clone()
        } else {
            CertAtom::new(want.cmp().negate(), want.poly().clone())
        };
        if expected != *got {
            return Err(ClauseCheckFailure::LemmaAtomMismatch {
                lemma: li,
                atom_index: i,
            });
        }
    }

    // The clause must be EXACTLY the negation of the cited assignment: one
    // literal per cited atom, the opposite of the polarity the theory was asked
    // about, and nothing else.
    let mut cited: BTreeSet<usize> = BTreeSet::new();
    for &i in &lemma.cited {
        if i >= cert.atoms().len() {
            return Err(ClauseCheckFailure::LemmaClauseMismatch { lemma: li });
        }
        cited.insert(i);
    }
    let mut want: BTreeSet<CnfLit> = BTreeSet::new();
    for &i in &cited {
        let Ok(v) = CnfVar::new(i) else {
            return Err(ClauseCheckFailure::LemmaClauseMismatch { lemma: li });
        };
        let pos = CnfLit::positive(v);
        want.insert(if lemma.polarity[i] {
            pos.negated()
        } else {
            pos
        });
    }
    let have: BTreeSet<CnfLit> = lemma.clause().lits().iter().copied().collect();
    if have != want || have.len() != lemma.clause().lits().len() {
        return Err(ClauseCheckFailure::LemmaClauseMismatch { lemma: li });
    }

    // Every cell the covering closes must be closed by an atom the CLAUSE
    // names. Without this the clause could be shorter than what the covering
    // actually proves -- which is exactly the direction that would be unsound.
    let mut outside: Option<usize> = None;
    walk_cited(lemma.refutation().root(), &cited, &mut outside);
    if let Some(atom_index) = outside {
        return Err(ClauseCheckFailure::LemmaCellOutsideClause {
            lemma: li,
            atom_index,
        });
    }

    // And the covering itself, by ADR-2126's exact checker -- run HERE, not
    // trusted from the producer having run it.
    match check_cell_refutation(lemma.refutation()) {
        Ok(cs) => {
            accumulate(stats, cs);
            Ok(())
        }
        Err(failure) => Err(ClauseCheckFailure::LemmaCellRejected { lemma: li, failure }),
    }
}

fn accumulate(stats: &mut ClauseCheckStats, cs: CellCheckStats) {
    stats.lemma_cells += cs.cells;
    stats.lemma_exact_tests += cs.delineability_exact_tests;
}

/// Record the first atom index a covering names that the clause does not cite.
fn walk_cited(cov: &CellCovering, cited: &BTreeSet<usize>, out: &mut Option<usize>) {
    for cell in cov.cells() {
        match cell {
            CellReason::Atom { atom_index } => {
                if !cited.contains(atom_index) && out.is_none() {
                    *out = Some(*atom_index);
                }
            }
            CellReason::Deeper { sub, .. } => walk_cited(sub, cited, out),
            // `check_cell_refutation` rejects these outright; nothing to cite.
            CellReason::Undecided => {}
        }
    }
}

/// Confirm that `lit` denotes `term` under the certificate's gate table.
///
/// A walk over the term DAG and the table. It builds nothing and asserts
/// nothing about clauses; the clause set is derived separately from the same
/// table once this walk has established that the table describes the query.
#[allow(
    clippy::too_many_arguments,
    reason = "one recursive walk carrying the term arena, the table it checks \
              against, its memo, and its counters -- bundling them into a struct \
              would hide which of them the recursion actually threads"
)]
fn check_encodes(
    arena: &TermArena,
    term: TermId,
    lit: CnfLit,
    cert: &ClauseRefutation,
    gates: &BTreeMap<usize, &GateDef>,
    seen: &mut BTreeSet<(TermId, CnfLit)>,
    stats: &mut ClauseCheckStats,
) -> Result<(), ClauseCheckFailure> {
    if !seen.insert((term, lit)) {
        return Ok(());
    }
    stats.encode_steps += 1;
    if stats.encode_steps > MAX_ENCODE_STEPS {
        return Err(ClauseCheckFailure::EncodingBudget);
    }

    let mismatch = || ClauseCheckFailure::EncodingMismatch { assertion_index: 0 };

    if let TermNode::App { op, args } = arena.node(term) {
        let op = *op;
        let args: Vec<TermId> = args.to_vec();
        match op {
            Op::BoolNot if args.len() == 1 => {
                return check_encodes(arena, args[0], lit.negated(), cert, gates, seen, stats);
            }
            // A one-argument `and`/`or` is the identity in the encoder: no gate
            // is allocated, the child's literal IS the node's literal. The
            // checker has to allow that or it would demand a gate that does not
            // exist.
            Op::BoolAnd | Op::BoolOr if args.len() == 1 => {
                return check_encodes(arena, args[0], lit, cert, gates, seen, stats);
            }
            Op::BoolAnd | Op::BoolOr if args.len() >= 2 => {
                let want = if matches!(op, Op::BoolAnd) {
                    GateKind::And
                } else {
                    GateKind::Or
                };
                let def = gate_for(lit, gates, want, args.len()).ok_or_else(mismatch)?;
                for (k, &a) in args.iter().enumerate() {
                    check_encodes(arena, a, def.inputs[k], cert, gates, seen, stats)?;
                }
                return Ok(());
            }
            Op::BoolImplies if args.len() == 2 => {
                // `a => b` is an `Or` gate over `[¬a, b]`.
                let def = gate_for(lit, gates, GateKind::Or, 2).ok_or_else(mismatch)?;
                check_encodes(
                    arena,
                    args[0],
                    def.inputs[0].negated(),
                    cert,
                    gates,
                    seen,
                    stats,
                )?;
                check_encodes(arena, args[1], def.inputs[1], cert, gates, seen, stats)?;
                return Ok(());
            }
            Op::BoolXor if args.len() == 2 => {
                let def = gate_for(lit, gates, GateKind::Xor, 2).ok_or_else(mismatch)?;
                check_encodes(arena, args[0], def.inputs[0], cert, gates, seen, stats)?;
                check_encodes(arena, args[1], def.inputs[1], cert, gates, seen, stats)?;
                return Ok(());
            }
            _ => {}
        }
    }

    // A leaf. It must be a polynomial comparison, and the literal must be the
    // POSITIVE literal of the atom variable carrying exactly that comparison.
    if lit.is_negated() {
        return Err(mismatch());
    }
    let idx = lit.var().index();
    let Some(want) = cert.atoms().get(idx) else {
        return Err(mismatch());
    };
    match cert_atom_of(arena, term) {
        Some(got) if got == *want => Ok(()),
        _ => Err(mismatch()),
    }
}

/// The gate `lit` names, when `lit` is a positive literal of a gate variable of
/// the wanted kind and arity.
fn gate_for<'a>(
    lit: CnfLit,
    gates: &BTreeMap<usize, &'a GateDef>,
    want: GateKind,
    arity: usize,
) -> Option<&'a GateDef> {
    if lit.is_negated() {
        return None;
    }
    let def = *gates.get(&lit.var().index())?;
    if def.kind != want || def.inputs.len() != arity {
        return None;
    }
    Some(def)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).expect("var")
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }

    /// Evaluate a clause under an assignment over variables `0..n`.
    fn clause_holds(c: &CnfClause, asg: &[bool]) -> bool {
        c.lits()
            .iter()
            .any(|l| asg[l.var().index()] != l.is_negated())
    }

    /// The exhaustive semantic pin on the ONE function the producer and the
    /// checker share.
    ///
    /// For every gate kind and arity, over EVERY assignment to the gate variable
    /// and its inputs: the clause set must be satisfied exactly on the rows where
    /// `g ↔ op(inputs)`. Both directions are asserted — a clause set that is too
    /// weak lets a wrong row through, and one that is too strong rejects a right
    /// row and would make a satisfiable formula unsatisfiable, which is the
    /// direction that costs soundness.
    #[test]
    fn gate_clauses_are_exactly_the_connective() {
        // Gate variable is index 0; inputs are 1..=arity, all positive.
        for (kind, arities) in [
            (GateKind::And, vec![2usize, 3, 4]),
            (GateKind::Or, vec![2, 3, 4]),
            (GateKind::Xor, vec![2]),
        ] {
            for arity in arities {
                let def = GateDef::new(v(0), kind, (1..=arity).map(p).collect());
                let cs = gate_clauses(&def);
                assert!(!cs.is_empty(), "{} arity {arity}: no clauses", kind.name());
                let n = arity + 1;
                let mut rows = 0usize;
                for bits in 0..(1u32 << n) {
                    let asg: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
                    let g = asg[0];
                    let ins = &asg[1..];
                    let truth = match kind {
                        GateKind::And => ins.iter().all(|b| *b),
                        GateKind::Or => ins.iter().any(|b| *b),
                        GateKind::Xor => ins[0] != ins[1],
                    };
                    let all = cs.iter().all(|c| clause_holds(c, &asg));
                    assert_eq!(
                        all,
                        g == truth,
                        "{} arity {arity} row {asg:?}: clauses say {all}, g<->op says {}",
                        kind.name(),
                        g == truth
                    );
                    if all {
                        rows += 1;
                    }
                }
                // A non-vacuous control: the definition admits exactly 2^arity
                // rows (one per input assignment), so a clause set that admitted
                // everything or nothing could not have passed the loop above by
                // accident.
                assert_eq!(
                    rows,
                    1usize << arity,
                    "{} arity {arity}: wrong number of admitted rows",
                    kind.name()
                );
            }
        }
    }

    /// An `Xor` gate with the wrong arity contributes NO clauses, so the arity
    /// guard in [`check_clause_refutation`] is the only thing standing between a
    /// malformed table and an unconstrained variable. This pins that the guard
    /// is load-bearing rather than decorative.
    #[test]
    fn a_wrong_arity_xor_gate_yields_no_clauses() {
        let def = GateDef::new(v(0), GateKind::Xor, vec![p(1), p(2), p(3)]);
        assert!(gate_clauses(&def).is_empty());
    }

    /// The certificate the producer really emits, read back field by field.
    ///
    /// Not a round-trip of the checker's verdict -- that is what the fixtures
    /// assert. This asserts the SHAPE, because "the checker accepted" is
    /// compatible with a certificate that carries nothing: no gate, no lemma, a
    /// covering with no cells. Every accessor is read, and every count is
    /// required to be nonzero or to match the query.
    #[test]
    fn a_live_certificate_carries_the_whole_abstraction() {
        // Two branches, both individually infeasible, so the loop must learn at
        // least two lemmas and the query has real Boolean structure.
        let script = "(declare-fun x () Real)\n(declare-fun y () Real)\n\
                      (assert (or (and (> x 1) (< x 0)) (and (< x (- 1)) (> x 0))))\n\
                      (assert (= y 0))\n(check-sat)\n";
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        crate::nra_real_root::reset_cad_decline();
        let cert = crate::nra_clause_loop::certificate_for_testing(
            &parsed.arena,
            &parsed.assertions,
            None,
        )
        .expect("the loop must refute this query");

        // One root per assertion, no more and no fewer. The checker enforces
        // this too; asserting it here says the PRODUCER gets it right rather
        // than that the checker would have caught it.
        assert_eq!(
            cert.roots().len(),
            parsed.assertions.len(),
            "one root literal per assertion"
        );
        assert!(!cert.atoms().is_empty(), "no atoms in the certificate");

        // The gate table must describe the `or`/`and` structure, and every gate
        // variable must be fresh -- above every atom variable.
        assert!(
            !cert.gates().is_empty(),
            "no gates for a query with an `or`"
        );
        let kinds: Vec<&str> = cert.gates().iter().map(|g| g.kind().name()).collect();
        assert!(
            kinds.contains(&"or") && kinds.contains(&"and"),
            "the gate table does not describe the query's connectives: {kinds:?}"
        );
        for g in cert.gates() {
            assert!(
                g.var().index() >= cert.atoms().len(),
                "gate variable {} shadows an atom variable",
                g.var().index()
            );
            assert!(
                g.inputs().len() >= 2,
                "a gate with fewer than two inputs was emitted"
            );
        }

        // Every lemma carries a covering, and the covering is over the same
        // atoms the certificate declares.
        assert!(
            cert.lemmas().len() >= 2,
            "both branches must have been refuted: {}",
            cert.lemmas().len()
        );
        for lemma in cert.lemmas() {
            assert!(
                !lemma.clause().lits().is_empty() || cert.lemmas().len() == 1,
                "an empty clause can only be the ONLY lemma"
            );
            assert_eq!(
                lemma.refutation().atoms().len(),
                cert.atoms().len(),
                "a covering built over a different atom set"
            );
            assert!(
                !lemma.refutation().order().is_empty(),
                "a covering with no variable order"
            );
        }

        // And the proof half.
        assert!(!cert.drat().is_empty(), "no DRAT proof attached");

        // The checker accepts the article, which is the control that makes every
        // rejection fixture meaningful.
        let stats = check_clause_refutation(&parsed.arena, &parsed.assertions, &cert)
            .expect("the checker must accept the certificate the producer built");
        assert!(stats.lemmas >= 2 && stats.gates > 0 && stats.drat_steps > 0);
    }
}
