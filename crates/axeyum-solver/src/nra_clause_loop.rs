//! CDCL(T) over polynomial sign atoms: the **clause loop** for `QF_NRA`
//! (ADR-2126, lane `NRA-CELL-EXACT`).
//!
//! # Why this exists, with the number
//!
//! [`crate::nra_single_cell`] takes a **conjunction** of polynomial comparisons
//! and nothing else. ADR-2121 measured what that costs on the population
//! ADR-2110 named: of its 24 in-bounds `QF_NRA` files, **12 decline
//! `non-conjunctive`** — half the slice — and ADR-2126's re-bucketing of the
//! same 24 confirms the count unchanged. The shape is always the same:
//! `meti-tarski` writes one assertion as a single `let`-bound `and` tree with an
//! `or` a few levels inside, so a column computed at the top of the term says
//! nothing about it, and the route refuses the whole file for one disjunction.
//!
//! This is the loop that removes that refusal. It is the same shape z3 runs
//! (`nlsat_solver.cpp:1848` `search()` is CDCL over sign atoms; a conflict goes
//! to `resolve` at `:2639`, whose `resolve_lazy_justification` (`:2454`) calls
//! the single-cell explainer at `:2469` and adds the result as a learned clause
//! at `:2766`/`:2792`) and the same shape cvc5 runs (coverings inside theory
//! combination: `coverings_solver.cpp:134` emits the covering conflict as a
//! lemma, built by `cdcac.cpp:555` `getUnsatCoverImpl`).
//!
//! **Where this route differs from both is the EVIDENCE.** z3's nlsat produces
//! no proof object for its lemmas at all -- `nlsat_tactic.cpp:144` is a literal
//! `fail_if_proof_generation("nlsat", g)`, and the only validation available is
//! an optional debug-mode re-solve of the negated lemma
//! (`nlsat_solver.cpp:1160`). cvc5's coverings do produce a proof tree, but the
//! arithmetic content of every covering step is a `ProofRule::TRUST` step tagged
//! `TrustId::ARITH_NL_COVERING_DIRECT` / `_RECURSIVE`
//! (`coverings/proof_generator.cpp:106`, `:139`) and its rule checker is a stub
//! returning `Node::null()` (`coverings/proof_checker.cpp:33`). ADR-2131's
//! certificate is CHECKED, not trusted -- see [`crate::nra_clause_cert`].
//!
//! # The loop
//!
//! 1. **Abstract.** Walk the assertions' Boolean structure, Tseitin-encode it
//!    over the propositional variables `1..=atoms.len()` (one per distinct
//!    polynomial comparison) plus fresh gate variables. Anything that is not a
//!    Boolean connective over polynomial comparisons is a typed decline —
//!    [`CadDecline::ClauseLoopShape`].
//! 2. **Ask the SAT core** ([`axeyum_cnf::IncrementalSat`], this repository's own
//!    CDCL, not a new loop) for a Boolean model.
//! 3. **Ask the theory.** Turn that model into a conjunction — atom `i` true
//!    gives the atom, false gives its negation, which for a sign atom is just
//!    the opposite comparison — and hand it to
//!    [`crate::nra_single_cell::decide_atoms`].
//! 4. A `Sat` sample is **replayed against the original assertions** by the
//!    ground evaluator. A `Refuted` covering yields a **blocking clause** over
//!    the atoms the covering actually cited, and the loop continues. A theory
//!    decline ends the loop with the theory's own recorded cause.
//! 5. The SAT core reporting `unsat` means the abstraction is refuted.
//!
//! # Soundness, and why the two halves are justified differently
//!
//! **A `sat` from this loop rests on nothing in the Boolean layer.** The final
//! step is the same one `decide_single_cell` performs: bind the sample and
//! evaluate every ORIGINAL assertion through [`axeyum_ir::eval`], requiring
//! `Bool(true)` from each. If the Tseitin encoding were wrong, if a blocking
//! clause were too strong, if the SAT core returned a model of the wrong
//! formula -- a replayed model is still a model, and a wrong one fails the
//! replay and declines.
//!
//! **An `unsat` from this loop is a different claim, and it now carries a
//! CERTIFICATE** (ADR-2131). ADR-2126 withheld it and named exactly what it
//! would rest on -- (a) the Tseitin encoding being equisatisfiable, (b) every
//! blocking clause being implied over the reals, (c) the SAT core's refutation.
//! [`crate::nra_clause_cert`] is the checker for all three, and
//! [`certify_unsat`] emits `unsat` only when it accepts:
//!
//! * **(b)** is discharged by the per-conflict
//!   [`crate::nra_cell_cert::CellRefutation`] this loop now KEEPS for every
//!   blocking clause, re-checked here by `check_cell_refutation`;
//! * **(c)** by a DRAT refutation from [`axeyum_cnf::solve_with_drat_proof`] --
//!   produced by a SECOND, independent solve, so the incremental solver that
//!   found the refutation is not also the evidence for it -- checked by
//!   `check_drat`;
//! * **(a)** by the gate table: the certificate carries the Tseitin GATE
//!   DEFINITIONS rather than the clauses, and the checker derives the clauses
//!   itself, after confirming the gate variables are fresh and that the table
//!   really describes the original assertions.
//!
//! A refused certificate is [`CadDecline::ClauseLoopCertificateRejected`]: the
//! verdict is dropped and the query falls through to the rest of the ladder.
//!
//! One asymmetry is worth stating plainly, because it is why the two halves have
//! different obligations: a blocking clause can only make the loop **miss** a
//! satisfying assignment, never invent one. So on the `sat` side an unsound
//! blocking clause costs completeness and cannot cost soundness -- while on the
//! `unsat` side it would cost soundness, which is exactly why every one of them
//! is now carried and re-checked rather than argued about.
//!
//! # Bounded by declaration
//!
//! [`MAX_CLAUSE_ATOMS`] distinct atoms and [`MAX_CLAUSE_LOOP_ROUNDS`] theory
//! calls. Both are refusals, not failures: past either the loop declines with
//! its own cause and decides nothing.

use std::collections::BTreeMap;
use std::time::Instant;

use axeyum_cnf::{
    CnfClause, CnfLit, CnfVar, IncrementalSat, ProofSolveOutcome, SatResult,
    solve_with_drat_proof_within,
};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::backend::CheckResult;
use crate::nra_cell_cert::{CellCovering, CellReason, CellRefutation, CertAtom};
use crate::nra_clause_cert::{
    ClauseCheckStats, ClauseRefutation, GateDef, GateKind, TheoryLemma, apply_mutation,
    check_clause_refutation, formula_of, gate_clauses,
};
use crate::nra_real_root::{CadDecline, cert_atom_of, record_cad_decline, record_clause_decline};
use crate::nra_single_cell::{AtomOutcome, decide_atoms, replay_rational_model};

/// The most distinct polynomial comparisons this loop will abstract.
///
/// A refusal by declaration. The theory call per Boolean model is the expensive
/// part and the number of models is exponential in the atom count, so the cap
/// bounds the whole loop rather than any one step.
pub(crate) const MAX_CLAUSE_ATOMS: usize = 48;

/// The most theory calls one decision may make.
///
/// The blocking clauses this loop learns are the atoms a covering CITED, which
/// is a real unsat core and usually much shorter than the assignment — but
/// nothing guarantees it, so the round cap is what bounds the search rather than
/// an argument about how fast it converges.
pub(crate) const MAX_CLAUSE_LOOP_ROUNDS: usize = 256;

/// Decide a Boolean combination of polynomial real comparisons by CDCL over the
/// sign atoms with single-cell CAD as the theory.
///
/// Returns `Some(Sat)` with a model replayed against `assertions`, or `None` to
/// decline — with the cause recorded through
/// [`crate::nra_real_root::record_cad_decline`]. It never returns `Unsat`: see
/// the module docs for what would have to exist first.
///
/// The caller owns the `AXEYUM_NRA_CAD` gate; this function reads no
/// environment.
pub(crate) fn decide_clause_loop(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<CheckResult> {
    LAST_CLAUSE_CHECK.with(|slot| slot.set(None));
    let skeleton = Skeleton::build(arena, assertions)?;
    if skeleton.atoms.len() > MAX_CLAUSE_ATOMS {
        record_cad_decline(CadDecline::ClauseLoopShape);
        record_clause_decline(CadDecline::ClauseLoopShape);
        return None;
    }

    let mut sat = IncrementalSat::new();
    sat.reserve(skeleton.next_var).ok()?;
    for clause in &skeleton.clauses {
        sat.add_clause(clause.clone()).ok()?;
    }

    // Every blocking clause the loop learns, with the covering that justifies
    // it. This is the theory half of the certificate and it is collected as the
    // loop runs, not reconstructed afterwards: a covering that was discarded
    // cannot be recovered, and a certificate assembled from a second run would
    // be a certificate about a second run (ADR-2131).
    let mut lemmas: Vec<TheoryLemma> = Vec::new();

    for _round in 0..MAX_CLAUSE_LOOP_ROUNDS {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            record_cad_decline(CadDecline::Deadline);
            record_clause_decline(CadDecline::Deadline);
            return None;
        }
        let model = match sat.solve(None) {
            Ok(SatResult::Sat(assignment)) => assignment,
            Ok(SatResult::Unsat(_)) => {
                // The abstraction is refuted. ADR-2131: that becomes this
                // route's `unsat` only if the certificate for it is BUILT and
                // ACCEPTED. The incremental solver's own refutation is not the
                // evidence -- an independent proof-producing solve is.
                return certify_unsat(arena, assertions, &skeleton, lemmas, deadline);
            }
            Ok(SatResult::Unknown(_)) | Err(_) => {
                record_cad_decline(CadDecline::ClauseLoopBudget);
                record_clause_decline(CadDecline::ClauseLoopBudget);
                return None;
            }
        };
        let values = model.values();

        // The theory query: atom `i` true is the atom, false is its negation.
        // For a sign atom the negation is just the opposite comparison, so the
        // theory never sees a Boolean structure at all.
        let mut conj: Vec<CertAtom> = Vec::with_capacity(skeleton.atoms.len());
        let mut polarity: Vec<bool> = Vec::with_capacity(skeleton.atoms.len());
        for (i, atom) in skeleton.atoms.iter().enumerate() {
            // A REFUSAL, not a default. `sat.reserve` covers every atom variable,
            // so a short model means the core returned an assignment over a
            // different formula than the one it was given -- and defaulting to
            // `false` there would hand the theory a conjunction the Boolean model
            // never asked for, silently. A tool that omits rather than refuses
            // turns its output into a measurement of the part it understood.
            let Some(asserted) = values.get(i).copied() else {
                record_cad_decline(CadDecline::ClauseLoopBudget);
                record_clause_decline(CadDecline::ClauseLoopBudget);
                return None;
            };
            polarity.push(asserted);
            conj.push(if asserted {
                atom.clone()
            } else {
                CertAtom::new(atom.cmp().negate(), atom.poly().clone())
            });
        }

        match decide_atoms(&conj, deadline)? {
            AtomOutcome::Sat(sample) => {
                // Replayed against the ORIGINAL assertions, not against `conj`.
                // Every claim the Boolean layer made is discharged here.
                let model = replay_rational_model(arena, assertions, &sample)?;
                return Some(CheckResult::Sat(model));
            }
            AtomOutcome::Refuted(refutation) => {
                let (clause, cited) = blocking_clause(&refutation, &polarity)?;
                if clause.lits().is_empty() {
                    // Nothing left to block: the theory refuted the atoms under
                    // this polarity with an EMPTY core. The empty clause goes
                    // into the certificate like any other lemma and the DRAT
                    // proof closes on it immediately.
                    lemmas.push(TheoryLemma::new(clause, polarity, cited, refutation));
                    return certify_unsat(arena, assertions, &skeleton, lemmas, deadline);
                }
                sat.add_clause(clause.clone()).ok()?;
                lemmas.push(TheoryLemma::new(clause, polarity, cited, refutation));
            }
        }
    }
    record_cad_decline(CadDecline::ClauseLoopBudget);
    record_clause_decline(CadDecline::ClauseLoopBudget);
    None
}

/// Turn a refuted abstraction into a CHECKED `unsat`, or into a typed decline.
///
/// Three things happen here and their order is the argument:
///
/// 1. The certificate is assembled from the gate table, the assertion roots and
///    the lemmas the loop collected.
/// 2. The clause set is derived from it and handed to the PROOF-PRODUCING core
///    ([`solve_with_drat_proof_within`]) -- a second, independent solve. The
///    incremental solver found the refutation; it does not also get to be the
///    evidence for it.
/// 3. [`check_clause_refutation`] must accept. It re-runs the cell checker on
///    every lemma, re-walks the assertions against the gate table, and checks
///    the DRAT proof.
///
/// Any of the three failing is a DECLINE. The verdict is dropped, never
/// weakened, and the query falls through to the rest of the ladder.
fn certify_unsat(
    arena: &TermArena,
    assertions: &[TermId],
    skeleton: &Skeleton,
    lemmas: Vec<TheoryLemma>,
    deadline: Option<Instant>,
) -> Option<CheckResult> {
    let cert = prove_certificate(skeleton, lemmas, deadline)?;
    match check_clause_refutation(arena, assertions, &cert) {
        Ok(stats) => {
            LAST_CLAUSE_CHECK.with(|slot| slot.set(Some(stats)));
            Some(CheckResult::Unsat)
        }
        Err(_failure) => {
            record_cad_decline(CadDecline::ClauseLoopCertificateRejected);
            record_clause_decline(CadDecline::ClauseLoopCertificateRejected);
            None
        }
    }
}

/// Assemble the certificate and attach its DRAT proof, or decline.
///
/// Split out of [`certify_unsat`] so the adversarial fixtures can obtain a LIVE
/// certificate -- one the producer really built for a query the route really
/// refutes -- damage exactly one part of it, and require a named rejection. A
/// fixture that assembled its own certificate would be testing the checker
/// against a shape the producer never emits.
fn prove_certificate(
    skeleton: &Skeleton,
    lemmas: Vec<TheoryLemma>,
    deadline: Option<Instant>,
) -> Option<ClauseRefutation> {
    let mut cert = ClauseRefutation::new(
        skeleton.atoms.clone(),
        skeleton.gates.clone(),
        skeleton.roots.clone(),
        lemmas,
        Vec::new(),
    );
    let Some(formula) = formula_of(&cert) else {
        record_cad_decline(CadDecline::ClauseLoopCertificateRejected);
        record_clause_decline(CadDecline::ClauseLoopCertificateRejected);
        return None;
    };
    match solve_with_drat_proof_within(&formula, deadline) {
        ProofSolveOutcome::Unsat(proof) => cert.set_drat(proof),
        // The proof core found a MODEL of the clause set the incremental solver
        // called unsat. That is a disagreement between two solvers, and the
        // honest response is to decide nothing -- not to believe either.
        ProofSolveOutcome::Sat(_) => {
            record_cad_decline(CadDecline::ClauseLoopCertificateRejected);
            record_clause_decline(CadDecline::ClauseLoopCertificateRejected);
            return None;
        }
        ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => {
            record_cad_decline(CadDecline::ClauseLoopBudget);
            record_clause_decline(CadDecline::ClauseLoopBudget);
            return None;
        }
    }
    Some(cert)
}

/// Run the loop and hand back the PROVED certificate instead of a verdict.
///
/// For the adversarial fixtures only; nothing in dispatch calls it. It runs the
/// same loop `decide_clause_loop` runs and stops one step short of the checker,
/// so a fixture damages the real article.
pub(crate) fn certificate_for_testing(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<ClauseRefutation> {
    let skeleton = Skeleton::build(arena, assertions)?;
    if skeleton.atoms.len() > MAX_CLAUSE_ATOMS {
        return None;
    }
    let mut sat = IncrementalSat::new();
    sat.reserve(skeleton.next_var).ok()?;
    for clause in &skeleton.clauses {
        sat.add_clause(clause.clone()).ok()?;
    }
    let mut lemmas: Vec<TheoryLemma> = Vec::new();
    for _round in 0..MAX_CLAUSE_LOOP_ROUNDS {
        let model = match sat.solve(None) {
            Ok(SatResult::Sat(assignment)) => assignment,
            Ok(SatResult::Unsat(_)) => {
                return prove_certificate(&skeleton, lemmas, deadline);
            }
            Ok(SatResult::Unknown(_)) | Err(_) => return None,
        };
        let values = model.values();
        let mut conj: Vec<CertAtom> = Vec::with_capacity(skeleton.atoms.len());
        let mut polarity: Vec<bool> = Vec::with_capacity(skeleton.atoms.len());
        for (i, atom) in skeleton.atoms.iter().enumerate() {
            let asserted = values.get(i).copied()?;
            polarity.push(asserted);
            conj.push(if asserted {
                atom.clone()
            } else {
                CertAtom::new(atom.cmp().negate(), atom.poly().clone())
            });
        }
        match decide_atoms(&conj, deadline)? {
            // A satisfiable query has no certificate to damage. That is a real
            // answer for a fixture to assert on, not a failure.
            AtomOutcome::Sat(_) => return None,
            AtomOutcome::Refuted(refutation) => {
                let (clause, cited) = blocking_clause(&refutation, &polarity)?;
                let empty = clause.lits().is_empty();
                if !empty {
                    sat.add_clause(clause.clone()).ok()?;
                }
                lemmas.push(TheoryLemma::new(clause, polarity, cited, refutation));
                if empty {
                    return prove_certificate(&skeleton, lemmas, deadline);
                }
            }
        }
    }
    None
}

/// Check a live certificate after exactly one named mutation.
///
/// The fixture surface. Returns `None` when the query produced no certificate
/// (so a fixture can tell "nothing to damage" from "the checker accepted"), and
/// otherwise `Ok(stats)` or `Err(failure-name)`.
pub(crate) fn certificate_probe_for_testing(
    arena: &TermArena,
    assertions: &[TermId],
    mutation: &str,
) -> Option<Result<ClauseCheckStats, String>> {
    let mut cert = certificate_for_testing(arena, assertions, None)?;
    if !apply_mutation(&mut cert, mutation) {
        // A mutation that silently did nothing would turn the fixture into a
        // measurement of the mutator. Say so instead.
        return Some(Err(format!("mutation-not-applicable:{mutation}")));
    }
    Some(check_clause_refutation(arena, assertions, &cert).map_err(|f| f.name().to_string()))
}

thread_local! {
    /// What the clause-loop checker EXAMINED on the last `unsat` this route
    /// emitted, or `None` if the last decision produced none.
    ///
    /// Same reason `nra_single_cell` keeps one: a fuzz that counts `unsat`
    /// verdicts cannot tell an accepted certificate from a checker that stopped
    /// looking, and this is what lets it assert the second.
    static LAST_CLAUSE_CHECK: core::cell::Cell<Option<ClauseCheckStats>> =
        const { core::cell::Cell::new(None) };
}

/// The stats from the last accepted clause-loop certificate.
pub(crate) fn last_clause_check() -> Option<ClauseCheckStats> {
    LAST_CLAUSE_CHECK.with(core::cell::Cell::get)
}

/// The clause that forbids the assignment a covering refuted.
///
/// Over the atoms the covering **cited** rather than over the whole assignment.
/// A covering proves "at every point, one of the cited atoms is violated", which
/// is a statement about the cited atoms alone, so their conjunction is
/// unsatisfiable and blocking just those is sound. The arrangement being finer
/// than those atoms require does not weaken that: a refutation over a finer
/// arrangement still refutes.
///
/// Falls back to the whole assignment if the covering cites nothing, which
/// cannot happen for an accepted covering (every leaf cell is closed by an atom)
/// but is the conservative direction if it ever does.
fn blocking_clause(
    refutation: &CellRefutation,
    polarity: &[bool],
) -> Option<(CnfClause, Vec<usize>)> {
    let mut cited: Vec<usize> = Vec::new();
    collect_cited(refutation.root(), &mut cited);
    cited.sort_unstable();
    cited.dedup();
    if cited.is_empty() {
        cited = (0..polarity.len()).collect();
    }
    let mut lits: Vec<CnfLit> = Vec::with_capacity(cited.len());
    for &i in &cited {
        let asserted = *polarity.get(i)?;
        let var = CnfVar::new(i).ok()?;
        lits.push(if asserted {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        });
    }
    Some((CnfClause::new(lits), cited))
}

/// Every atom index a covering tree names as the reason for a cell.
fn collect_cited(cov: &CellCovering, out: &mut Vec<usize>) {
    for cell in cov.cells() {
        match cell {
            CellReason::Atom { atom_index } => out.push(*atom_index),
            CellReason::Deeper { sub, .. } => collect_cited(sub, out),
            CellReason::Undecided => {}
        }
    }
}

// ---------------------------------------------------------------------------
// The Boolean abstraction
// ---------------------------------------------------------------------------

/// The Tseitin encoding of the query's Boolean structure over sign atoms.
struct Skeleton {
    /// Distinct polynomial comparisons. Atom `i` is propositional variable `i`.
    atoms: Vec<CertAtom>,
    /// The CNF, including the unit clauses asserting each assertion.
    clauses: Vec<CnfClause>,
    /// One Tseitin gate definition per gate variable, in allocation order.
    ///
    /// The CERTIFICATE carries this and not [`Self::clauses`]: the checker
    /// derives the clauses from the table itself, so there is nowhere for a
    /// producer to put a clause the table does not justify (ADR-2131).
    gates: Vec<GateDef>,
    /// The literal asserted for each original assertion, in order.
    roots: Vec<CnfLit>,
    /// One past the highest variable index used.
    next_var: usize,
}

impl Skeleton {
    fn build(arena: &TermArena, assertions: &[TermId]) -> Option<Self> {
        if assertions.is_empty() {
            record_cad_decline(CadDecline::ClauseLoopShape);
            record_clause_decline(CadDecline::ClauseLoopShape);
            return None;
        }
        let mut b = Builder {
            atoms: Vec::new(),
            clauses: Vec::new(),
            gates: Vec::new(),
            next_var: 0,
            memo: BTreeMap::new(),
        };
        // Reserve variables `0..atoms.len()` for atoms by encoding first and
        // renumbering never: atoms take the next index the first time they are
        // seen, gates take indices after the last atom. Two passes would be
        // cleaner but would walk the term twice; instead gates are allocated
        // from a HIGH base that no atom can reach, which is what the cap buys.
        b.next_var = MAX_CLAUSE_ATOMS;
        let mut roots: Vec<CnfLit> = Vec::with_capacity(assertions.len());
        for &a in assertions {
            let lit = b.encode(arena, a)?;
            b.clauses.push(CnfClause::new(vec![lit]));
            roots.push(lit);
        }
        if b.atoms.is_empty() {
            record_cad_decline(CadDecline::ClauseLoopShape);
            record_clause_decline(CadDecline::ClauseLoopShape);
            return None;
        }
        Some(Self {
            atoms: b.atoms,
            clauses: b.clauses,
            gates: b.gates,
            roots,
            next_var: b.next_var,
        })
    }
}

struct Builder {
    atoms: Vec<CertAtom>,
    clauses: Vec<CnfClause>,
    gates: Vec<GateDef>,
    next_var: usize,
    memo: BTreeMap<TermId, CnfLit>,
}

impl Builder {
    fn fresh(&mut self) -> Option<CnfVar> {
        let v = CnfVar::new(self.next_var).ok()?;
        self.next_var = self.next_var.checked_add(1)?;
        Some(v)
    }

    fn atom_lit(&mut self, atom: CertAtom) -> Option<CnfLit> {
        let idx = if let Some(i) = self.atoms.iter().position(|a| *a == atom) {
            i
        } else {
            if self.atoms.len() >= MAX_CLAUSE_ATOMS {
                record_cad_decline(CadDecline::ClauseLoopShape);
                record_clause_decline(CadDecline::ClauseLoopShape);
                return None;
            }
            self.atoms.push(atom);
            self.atoms.len() - 1
        };
        Some(CnfLit::positive(CnfVar::new(idx).ok()?))
    }

    /// A literal equivalent to `term`, adding its defining clauses.
    ///
    /// Full (both-polarity) Tseitin definitions, not polarity-optimised: the
    /// loop reads back a model of these variables and a one-sided definition
    /// leaves a gate variable free to take a value its inputs do not justify.
    fn encode(&mut self, arena: &TermArena, term: TermId) -> Option<CnfLit> {
        if let Some(l) = self.memo.get(&term) {
            return Some(*l);
        }
        let lit = self.encode_uncached(arena, term)?;
        self.memo.insert(term, lit);
        Some(lit)
    }

    fn encode_uncached(&mut self, arena: &TermArena, term: TermId) -> Option<CnfLit> {
        if let TermNode::App { op, args } = arena.node(term) {
            let op = *op;
            let args: Vec<TermId> = args.to_vec();
            match op {
                Op::BoolNot if args.len() == 1 => {
                    return Some(self.encode(arena, args[0])?.negated());
                }
                Op::BoolAnd if !args.is_empty() => {
                    let kids = self.encode_all(arena, &args)?;
                    return self.gate_and(&kids);
                }
                Op::BoolOr if !args.is_empty() => {
                    let kids = self.encode_all(arena, &args)?;
                    return self.gate_or(&kids);
                }
                Op::BoolImplies if args.len() == 2 => {
                    let a = self.encode(arena, args[0])?.negated();
                    let b = self.encode(arena, args[1])?;
                    return self.gate_or(&[a, b]);
                }
                Op::BoolXor if args.len() == 2 => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    return self.gate_xor(a, b);
                }
                _ => {}
            }
        }
        // A leaf: it has to be a polynomial comparison, or this query is not a
        // shape the loop abstracts. A Boolean VARIABLE lands here too, and
        // declining on it is deliberate -- it would be a propositional variable
        // with no theory meaning, and this slice does not claim to handle one.
        if let Some(atom) = cert_atom_of(arena, term) {
            self.atom_lit(atom)
        } else {
            record_cad_decline(CadDecline::ClauseLoopShape);
            record_clause_decline(CadDecline::ClauseLoopShape);
            None
        }
    }

    fn encode_all(&mut self, arena: &TermArena, args: &[TermId]) -> Option<Vec<CnfLit>> {
        let mut out = Vec::with_capacity(args.len());
        for &a in args {
            out.push(self.encode(arena, a)?);
        }
        Some(out)
    }

    /// Emit a gate and the clauses its definition contributes.
    ///
    /// The clauses come from [`gate_clauses`] -- the SAME function the checker
    /// derives them with -- so the certificate's gate table and the formula the
    /// loop actually searched cannot describe different things (ADR-2131).
    fn emit_gate(&mut self, kind: GateKind, inputs: Vec<CnfLit>) -> Option<CnfLit> {
        let var = self.fresh()?;
        let def = GateDef::new(var, kind, inputs);
        self.clauses.extend(gate_clauses(&def));
        self.gates.push(def);
        Some(CnfLit::positive(var))
    }

    fn gate_and(&mut self, kids: &[CnfLit]) -> Option<CnfLit> {
        if kids.len() == 1 {
            return Some(kids[0]);
        }
        self.emit_gate(GateKind::And, kids.to_vec())
    }

    fn gate_or(&mut self, kids: &[CnfLit]) -> Option<CnfLit> {
        if kids.len() == 1 {
            return Some(kids[0]);
        }
        self.emit_gate(GateKind::Or, kids.to_vec())
    }

    fn gate_xor(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        self.emit_gate(GateKind::Xor, vec![a, b])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nra_real_root::{cad_decline, reset_cad_decline};

    const DECL2: &str = "(declare-fun x () Real)\n(declare-fun y () Real)\n";

    fn decide(script: &str) -> (Option<CheckResult>, &'static str) {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        reset_cad_decline();
        let out = decide_clause_loop(&parsed.arena, &parsed.assertions, None);
        (out, cad_decline().name())
    }

    fn is_sat(r: Option<&CheckResult>) -> bool {
        matches!(r, Some(CheckResult::Sat(_)))
    }

    /// The shape the whole lever exists for: a disjunction inside one assertion.
    ///
    /// `decide_single_cell` refuses this file outright. Twelve of ADR-2121's 24
    /// in-bounds files are exactly this.
    #[test]
    fn a_disjunction_the_conjunctive_route_refuses_is_solved_here() {
        let script = format!(
            "{DECL2}(assert (and (> (* x x) 4) (or (> y 10) (< y (- 10)))))\n(check-sat)\n"
        );
        // The conjunctive route refuses it.
        let parsed = axeyum_smtlib::parse_script(&script).expect("parse");
        reset_cad_decline();
        let conj = crate::nra_single_cell::decide_single_cell(
            &parsed.arena,
            &parsed.assertions,
            None,
            true,
        );
        assert!(conj.is_none(), "the control is that the OLD route refuses");
        assert_eq!(cad_decline().name(), "non-conjunctive");

        // The clause loop solves it, and the model is replayed.
        let (r, cause) = decide(&script);
        assert!(is_sat(r.as_ref()), "expected sat, got {r:?} ({cause})");
    }

    /// A satisfiable Boolean combination the loop must NOT refute.
    ///
    /// Only one branch of the disjunction is satisfiable, so a loop that
    /// blocked too much -- or blocked the wrong polarity -- would run out of
    /// Boolean models and decline instead of answering.
    #[test]
    fn a_satisfiable_combination_is_not_refuted() {
        let script = format!(
            "{DECL2}\
             (assert (or (and (> x 0) (< x 0)) (and (> x 1) (< x 2))))\n\
             (assert (= y 0))\n(check-sat)\n"
        );
        let (r, cause) = decide(&script);
        assert!(
            is_sat(r.as_ref()),
            "the loop must find the second branch: {r:?} ({cause})"
        );
    }

    /// An unsatisfiable combination whose refutation needs cells from **two
    /// different branches** of the disjunction, answered with a CHECKED
    /// certificate (ADR-2131).
    ///
    /// Neither branch is refutable without looking at it: `x > 1 ∧ x < 0` dies
    /// on its own atoms and so does `x < -1 ∧ x > 0`, and the loop must refute
    /// BOTH before the abstraction closes.
    ///
    /// Under ADR-2126 this asserted the CAUSE, because the verdict was withheld.
    /// It now asserts the verdict AND that the checker examined something, which
    /// is strictly more: an acceptance with zero lemmas and zero cells is the
    /// vacuous pass a bare `Unsat` cannot distinguish.
    #[test]
    fn an_unsatisfiable_combination_needing_two_branches_is_certified() {
        let script = format!(
            "{DECL2}\
             (assert (or (and (> x 1) (< x 0)) (and (< x (- 1)) (> x 0))))\n\
             (assert (= y 0))\n(check-sat)\n"
        );
        let (r, cause) = decide(&script);
        assert!(
            matches!(r, Some(CheckResult::Unsat)),
            "expected a certified unsat, got {r:?} ({cause})"
        );
        let stats = last_clause_check().expect("an accepted certificate");
        assert!(
            stats.lemmas >= 2,
            "the refutation must need BOTH branches: {stats:?}"
        );
        assert!(
            stats.lemma_cells > 0 && stats.drat_steps > 0,
            "the checker must have examined cells AND a proof: {stats:?}"
        );
        assert!(
            stats.roots > 0 && stats.gates > 0,
            "the abstraction walk must have examined the gate table: {stats:?}"
        );
    }

    /// A satisfiable Boolean combination in which the two branches SHARE a
    /// variable and only one branch is infeasible.
    ///
    /// The extension ADR-2131 required over
    /// [`a_satisfiable_combination_is_not_refuted`]: there the branches are
    /// independent, so a loop that confused which atoms a covering cited could
    /// still stumble onto the right answer. Here `x` appears in BOTH branches
    /// and `y` couples them, so a blocking clause naming the wrong atom blocks
    /// the LIVE branch and the loop refutes a satisfiable query.
    ///
    /// The assertion is `not Unsat` rather than `Sat`, deliberately: a decline
    /// is a permitted answer on this route and a WRONG ANSWER is not.
    #[test]
    fn a_shared_variable_with_one_dead_branch_is_never_refuted() {
        let script = format!(
            "{DECL2}\
             (assert (or (and (> x 1) (< x 0)) (and (> x 1) (< x 5))))\n\
             (assert (and (> y x) (< y 6)))\n(check-sat)\n"
        );
        let (r, cause) = decide(&script);
        assert!(
            !matches!(r, Some(CheckResult::Unsat)),
            "a satisfiable query must never be refuted: {r:?} ({cause})"
        );
    }

    /// A shape the loop does not abstract is a typed refusal, not a wrong answer.
    #[test]
    fn a_non_polynomial_leaf_is_refused_by_declaration() {
        let script = "(declare-fun b () Bool)\n(declare-fun x () Real)\n\
                      (assert (or b (> x 0)))\n(check-sat)\n";
        let (r, cause) = decide(script);
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "clause-loop-shape");
    }

    /// A plain conjunction still works: the loop is a generalisation, not a
    /// replacement that loses the old shape.
    #[test]
    fn a_plain_conjunction_still_decides() {
        let script =
            format!("{DECL2}(assert (> x 2))\n(assert (< y 1))\n(assert (> y 0))\n(check-sat)\n");
        let (r, cause) = decide(&script);
        assert!(is_sat(r.as_ref()), "expected sat, got {r:?} ({cause})");
    }

    /// The loop is deterministic: same query, same verdict, every time.
    /// Determinism is a public API promise and the loop makes no random choice.
    #[test]
    fn the_loop_is_deterministic_across_repeated_runs() {
        let script = format!(
            "{DECL2}(assert (and (> (* x x) 4) (or (> y 10) (< y (- 10)))))\n(check-sat)\n"
        );
        let first = decide(&script);
        for _ in 0..4 {
            let again = decide(&script);
            assert_eq!(
                is_sat(first.0.as_ref()),
                is_sat(again.0.as_ref()),
                "the loop changed its verdict between runs"
            );
            assert_eq!(first.1, again.1, "the loop changed its cause between runs");
        }
    }

    /// The degenerate-argument class CLAUDE.md's hard rule requires.
    ///
    /// This route never divides, but "never touches a partial operator" is a
    /// claim and not a fact until it is shown. Both fixtures are SATISFIABLE, so
    /// a route that folded `(/ x 0)` to a convention and refuted would fail here.
    #[test]
    fn the_clause_loop_never_refutes_a_division_by_constant_zero() {
        for script in [
            format!("{DECL2}(assert (or (> (/ x 0) 1) (> y 0)))\n(assert (> y 5))\n(check-sat)\n"),
            format!("{DECL2}(assert (or (> (/ x y) 1) (> x 3)))\n(assert (> x 4))\n(check-sat)\n"),
        ] {
            let (r, cause) = decide(&script);
            assert!(
                !matches!(r, Some(CheckResult::Unsat)),
                "a satisfiable query must never be refuted: {r:?} ({cause})"
            );
        }
    }
}
