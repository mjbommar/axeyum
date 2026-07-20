//! Disjunctive (CNF) Craig interpolation for `QF_LRA` — the interpolating-SMT
//! construction that lifts interpolation beyond the conjunctive
//! [`lra_interpolant`](crate::lra_interpolant) to assertions with arbitrary
//! Boolean structure over linear-real atoms (Track 3, the disjunctive companion
//! of the Farkas interpolator).
//!
//! [`lra_interpolant_cnf`] takes two slices of `QF_LRA` assertions `A` and `B`
//! (each interpreted as the **conjunction** of its members, but the members may
//! themselves be `∧`/`∨`/`¬`/`ite`/`=` Boolean combinations of linear-real
//! order atoms) whose conjunction `A ∧ B` is unsatisfiable, and returns a
//! verified Craig interpolant `I` (a Boolean [`TermId`] over the shared real
//! symbols) such that `A ⇒ I`, `I ∧ B ⇒ ⊥`, and every real symbol of `I` is
//! shared by `A` and `B`. It returns `Ok(None)` whenever `A ∧ B` is
//! satisfiable, the input is outside the supported fragment, the construction
//! cannot complete, or any re-check fails. It **never** returns an unverified
//! interpolant.
//!
//! # Method (`McMillan` interpolating SMT for LRA)
//!
//! 1. **Boolean abstraction.** Each distinct linear-real order atom of `A`/`B`
//!    is mapped to a Boolean variable ([`CnfVar`]). The Boolean structure of
//!    each assertion is Tseitin-encoded into a CNF formula over those atom
//!    variables (plus side-private auxiliary variables), giving `A_cnf` and
//!    `B_cnf`. A leaf that is not a recognised real order atom (or `Eq` over
//!    reals, which expands to `(a ≤ b) ∧ (a ≥ b)`) declines.
//! 2. **Theory lemmas.** `A ∧ B` is decided by the certified lazy-SMT LRA
//!    procedure [`certify_lra_dpll_unsat`], which returns the theory lemmas it
//!    learned — each an LRA-valid clause `¬a₁ ∨ … ∨ ¬aₙ` (its core conjunction
//!    is Farkas-refutable). Each lemma is mapped to a clause over the atom
//!    variables.
//! 3. **Colour and place.** An atom is `A`-coloured / `B`-coloured / shared by
//!    which side it occurs on. A theory lemma over only-`A` (or shared) atoms is
//!    added to `A_cnf`; over only-`B` (or shared) atoms, to `B_cnf`. A **mixed**
//!    lemma — one carrying both an `A`-only and a `B`-only atom — is *purified*
//!    by a fresh shared Farkas atom `P`: the conjunctive
//!    [`lra_interpolant`](crate::lra_interpolant) interpolates the lemma's
//!    `A`-side core against its `B`-side, yielding a real partial interpolant
//!    `P` with `A-core ⇒ P` and `P ∧ B-core ⇒ ⊥`. The `A`-valid clause
//!    `(¬a₁ ∨ … ∨ P)` joins `A_cnf` and the `B`-valid clause `(¬P ∨ ¬b₁ ∨ …)`
//!    joins `B_cnf`; resolving on `P` recovers the lemma. If the partial
//!    interpolant cannot be produced/verified, the construction declines
//!    (`Ok(None)`).
//! 4. **Propositional interpolation.** [`propositional_interpolant`] on
//!    `(A_cnf, B_cnf)` yields a [`BoolExpr`] over the shared atom variables.
//! 5. **Lift.** Each shared atom variable lifts to its LRA-atom [`TermId`];
//!    `And`/`Or`/`Not`/`Top`/`Bot` lift to the arena Boolean builders.
//!
//! # Trust
//!
//! The abstraction, the lazy-SMT lemma harvest, the propositional fold, and the
//! lifting are **entirely untrusted**. Soundness comes only from
//! [`verify_interpolant`], which re-checks all three Craig conditions on the
//! **original** assertions with the disjunctive decider [`check_auto`] before
//! any interpolant is returned. Any decision that is not `unsat`, any
//! shared-vocabulary violation, or any construction failure yields `Ok(None)`.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{BoolExpr, CnfClause, CnfFormula, CnfLit, CnfVar, propositional_interpolant};
use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::dpll_t::{LraDpllOutcome, certify_lra_dpll_unsat};

/// Produces a verified disjunctive (CNF) `QF_LRA` Craig interpolant for the
/// unsatisfiable conjunction `A ∧ B`, where `a_assertions` is `A` and
/// `b_assertions` is `B`. Unlike [`crate::lra_interpolant`], the assertions may
/// carry arbitrary Boolean structure (`∧`/`∨`/`¬`/`ite`/`=`) over linear-real
/// order atoms.
///
/// Returns `Ok(Some(I))` with a fully re-checked interpolant term `I`, or
/// `Ok(None)` when `A ∧ B` is satisfiable, the input is outside the supported
/// fragment, the construction cannot complete (e.g. a mixed theory lemma's
/// Farkas partial interpolant cannot be produced, or a leaf is not a real order
/// atom), or the candidate fails any of its three independent post-checks. It
/// **never** returns an unverified interpolant.
///
/// # Errors
///
/// Propagates [`SolverError`] from the underlying certified lazy-SMT decision or
/// the verification [`check_auto`] calls (e.g. a `sat`-replay or self-check
/// soundness alarm). Ordinary unsupported input declines with `Ok(None)`.
pub fn lra_interpolant_cnf(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    // 1. Decide A ∧ B with the certified lazy-SMT LRA procedure and harvest the
    //    learned theory lemmas. Anything but a certified `unsat` (sat, unknown,
    //    or non-pure-real content the procedure rejects) is a sound decline.
    let mut combined: Vec<TermId> = Vec::with_capacity(a_assertions.len() + b_assertions.len());
    combined.extend_from_slice(a_assertions);
    combined.extend_from_slice(b_assertions);
    let config = SolverConfig::default();
    let lemmas = match certify_lra_dpll_unsat(arena, &combined, &config) {
        Ok(LraDpllOutcome::Unsat(refutation)) => refutation.lemmas,
        Ok(LraDpllOutcome::Sat(_) | LraDpllOutcome::Unknown(_))
        | Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(other) => return Err(other),
    };

    // 2. Boolean abstraction: assign each distinct real order atom a CnfVar, and
    //    Tseitin-encode each assertion's Boolean structure into A_cnf / B_cnf
    //    over a shared variable space. Atom variables come first (so the same
    //    atom is the same global variable across A and B); each side then grows
    //    with its own private auxiliary variables.
    let mut abstractor = Abstractor::default();
    // Pre-register the atoms appearing in A and in B so the side classification
    // (`A`-only / `B`-only / shared) is determined before encoding.
    if abstractor
        .register_atoms(arena, a_assertions, Side::A)
        .is_none()
    {
        return Ok(None);
    }
    if abstractor
        .register_atoms(arena, b_assertions, Side::B)
        .is_none()
    {
        return Ok(None);
    }

    let atom_count = abstractor.atoms.len();
    if atom_count == 0 {
        // No real atoms at all: nothing for this construction to interpolate.
        return Ok(None);
    }

    // Build the two CNF formulas over **disjoint** auxiliary-variable ranges:
    // atom variables `[0, atom_count)` are shared; A's Tseitin auxiliaries start
    // at `atom_count`; B's start above A's range. Disjoint ranges keep the
    // propositional colouring clean — an A-auxiliary index must never coincide
    // with a B-auxiliary index. Synthetic Farkas atoms (added below) come above
    // both ranges, also shared.
    let Some(mut a_cnf) = abstractor.encode_assertions(arena, a_assertions, atom_count) else {
        return Ok(None);
    };
    let b_base = a_cnf.variable_count();
    let Some(mut b_cnf) = abstractor.encode_assertions(arena, b_assertions, b_base) else {
        return Ok(None);
    };
    // The synthetic-atom allocator starts above both aux ranges.
    abstractor.next_synthetic = b_cnf.variable_count().max(a_cnf.variable_count());

    // 3. Place each theory lemma onto the correctly-coloured side (purifying
    //    mixed lemmas with a Farkas partial interpolant). A decline propagates.
    if !place_lemmas(arena, &mut abstractor, &mut a_cnf, &mut b_cnf, &lemmas)? {
        return Ok(None);
    }

    // 4. Propositional Craig interpolation over the shared atom-variable space.
    //    The two formulas must share `variable_count`; equalise by growing the
    //    smaller (the extra variables are unused private auxiliaries).
    equalise_variable_count(&mut a_cnf, &mut b_cnf);
    let Some(bool_interp) = propositional_interpolant(&a_cnf, &b_cnf) else {
        return Ok(None);
    };

    // 5. Lift the BoolExpr (over shared atom variables) back to a real-term
    //    interpolant. Only atom variables may appear; an auxiliary variable in
    //    the propositional interpolant has no LRA-atom and declines.
    let Some(interpolant) = abstractor.lift(arena, &bool_interp) else {
        return Ok(None);
    };

    // 6. VERIFY-BEFORE-RETURN on the ORIGINAL disjunctive assertions. Decline on
    //    any non-`unsat` / vocabulary failure — the sole soundness anchor.
    if verify_interpolant(arena, a_assertions, b_assertions, interpolant)? {
        Ok(Some(interpolant))
    } else {
        Ok(None)
    }
}

/// Re-checks the three Craig conditions for `interpolant` against the
/// **original** disjunctive `QF_LRA` partitions with the auto decider
/// [`check_auto`] (which handles Boolean structure over real atoms):
///
/// 1. `A ∧ ¬I` is `unsat` (i.e. `A ⇒ I`),
/// 2. `I ∧ B` is `unsat` (i.e. `I ∧ B ⇒ ⊥`),
/// 3. every real symbol of `I` occurs in both `A` and `B`.
///
/// Returns `Ok(true)` only when all three hold; a vocabulary failure or builder
/// error yields `Ok(false)`. This is the sole soundness anchor: the
/// abstraction, lemma harvest, propositional fold, and lifting are all
/// untrusted.
///
/// # Errors
///
/// Propagates a [`SolverError`] from the `QF_LRA` decider (a soundness alarm),
/// never an ordinary decline.
fn verify_interpolant(
    arena: &mut TermArena,
    a_assertions: &[TermId],
    b_assertions: &[TermId],
    interpolant: TermId,
) -> Result<bool, SolverError> {
    // (3) Vocabulary: every symbol of I occurs in both A and B.
    let a_symbols = symbols_of(arena, a_assertions);
    let b_symbols = symbols_of(arena, b_assertions);
    for symbol in symbols_of(arena, &[interpolant]) {
        if !a_symbols.contains(&symbol) || !b_symbols.contains(&symbol) {
            return Ok(false);
        }
    }

    let config = SolverConfig::default();

    // (1) A ∧ ¬I unsat.
    let Ok(not_i) = arena.not(interpolant) else {
        return Ok(false);
    };
    let mut a_check: Vec<TermId> = a_assertions.to_vec();
    a_check.push(not_i);
    if !matches!(check_auto(arena, &a_check, &config)?, CheckResult::Unsat) {
        return Ok(false);
    }

    // (2) I ∧ B unsat.
    let mut b_check: Vec<TermId> = Vec::with_capacity(b_assertions.len() + 1);
    b_check.push(interpolant);
    b_check.extend_from_slice(b_assertions);
    if !matches!(check_auto(arena, &b_check, &config)?, CheckResult::Unsat) {
        return Ok(false);
    }

    Ok(true)
}

/// Which partition an atom belongs to (for the propositional colouring).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    A,
    B,
}

/// One literal of a theory lemma's infeasible core: the atom variable, its
/// polarity in the core (`positive` ⇒ the bare atom, else its negation), and the
/// real literal term used for the Farkas sub-interpolation.
#[derive(Clone, Copy)]
struct LemmaLit {
    var: CnfVar,
    positive: bool,
    term: TermId,
}

impl LemmaLit {
    /// The literal this contributes to the lemma **clause** (the negation of the
    /// core): a core literal `l` contributes `¬l`.
    fn clause_lit(&self) -> CnfLit {
        if self.positive {
            CnfLit::positive(self.var).negated()
        } else {
            CnfLit::positive(self.var)
        }
    }
}

/// Places every theory lemma onto its correctly-coloured CNF side.
///
/// A **single-sided** lemma (every atom A-only, every atom B-only, or all
/// shared) is added directly as its clause (the negation of the infeasible
/// core). A **mixed** lemma is purified via [`add_purified_lemma`]. Returns
/// `Ok(true)` when all lemmas were placed, `Ok(false)` to decline (an
/// unregistered atom, a failed purification, or a clause-add error).
fn place_lemmas(
    arena: &mut TermArena,
    abstractor: &mut Abstractor,
    a_cnf: &mut CnfFormula,
    b_cnf: &mut CnfFormula,
    lemmas: &[Vec<crate::dpll_t::LemmaLiteral>],
) -> Result<bool, SolverError> {
    for lemma in lemmas {
        // Split the lemma's core literals by colour. `LemmaLit` keeps the atom
        // var, the polarity (`positive` ⇒ the core literal is the bare atom), and
        // the real literal term for the Farkas sub-interpolation.
        let mut a_side: Vec<LemmaLit> = Vec::new();
        let mut b_side: Vec<LemmaLit> = Vec::new();
        let mut a_present = false;
        let mut b_partition_present = false;
        for literal in lemma {
            let Some((var, positive)) = abstractor.atom_literal(arena, literal.literal) else {
                // A lemma literal whose atom we did not register: decline rather
                // than drop a clause the refutation depends on.
                return Ok(false);
            };
            let item = LemmaLit {
                var,
                positive,
                term: literal.literal,
            };
            match abstractor.side_of(var) {
                Some(Side::A) => {
                    a_present = true;
                    a_side.push(item);
                }
                Some(Side::B) => {
                    b_partition_present = true;
                    b_side.push(item);
                }
                // A shared atom is consistent on either colouring; assign it to
                // the A side of the Farkas partition (a fixed, deterministic
                // convention) so the partial interpolant stays over shared vars.
                None => a_side.push(item),
            }
        }

        if a_present && b_partition_present {
            // Mixed lemma → purify via a Farkas partial interpolant.
            if !add_purified_lemma(arena, abstractor, a_cnf, b_cnf, &a_side, &b_side)? {
                return Ok(false);
            }
            continue;
        }

        // Single-sided: place the clause (the negation of the infeasible core).
        let clause = CnfClause::new(
            a_side
                .iter()
                .chain(&b_side)
                .map(LemmaLit::clause_lit)
                .collect(),
        );
        let target: &mut CnfFormula = if b_partition_present {
            &mut *b_cnf
        } else {
            &mut *a_cnf
        };
        if target.add_clause(clause).is_err() {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Purifies a **mixed** theory lemma into two single-coloured clauses joined by
/// a fresh shared Farkas atom `P`, returning `Ok(true)` on success.
///
/// The lemma's core is `(∧ a-lits) ∧ (∧ b-lits)`, Farkas-infeasible. A Farkas
/// interpolant `P` of the partition `(a-lits, b-lits)` satisfies `(∧ a-lits) ⇒ P`
/// and `P ∧ (∧ b-lits) ⇒ ⊥`, over shared vocabulary. Hence:
///
/// - the **A**-valid clause `(¬a₁ ∨ … ∨ P)` is added to `a_cnf`;
/// - the **B**-valid clause `(¬P ∨ ¬b₁ ∨ …)` is added to `b_cnf`.
///
/// Resolving the two on `P` recovers the original lemma, so soundness of the
/// abstraction is preserved (and the final re-check is the real anchor). `P`'s
/// fresh shared [`CnfVar`] and its lifted atom term are registered with the
/// abstractor. Returns `Ok(false)` when the Farkas interpolation of the core
/// cannot be produced or any clause add fails (the caller then declines).
fn add_purified_lemma(
    arena: &mut TermArena,
    abstractor: &mut Abstractor,
    a_cnf: &mut CnfFormula,
    b_cnf: &mut CnfFormula,
    a_side: &[LemmaLit],
    b_side: &[LemmaLit],
) -> Result<bool, SolverError> {
    // The Farkas partition is over the **core** literals (the bare atom or its
    // negation), not the clause literals.
    let a_lits: Vec<TermId> = a_side.iter().map(|l| l.term).collect();
    let b_lits: Vec<TermId> = b_side.iter().map(|l| l.term).collect();

    // A Farkas interpolant of the infeasible core. A non-`Unsupported` decline
    // (e.g. the core needs a richer partition) means we cannot purify → decline.
    let p_term = match crate::lra_interpolant(arena, &a_lits, &b_lits) {
        Ok(Some(term)) => term,
        Ok(None) | Err(SolverError::Unsupported(_)) => return Ok(false),
        Err(other) => return Err(other),
    };

    // Register `P` as a fresh **shared** synthetic atom; it lifts to `p_term`.
    let p_var = abstractor.register_synthetic_shared(p_term);
    // Both formulas must range over `p_var` (it occurs in both, so it is shared).
    grow_to(a_cnf, p_var.index() + 1);
    grow_to(b_cnf, p_var.index() + 1);

    // A-clause: (¬a₁ ∨ … ∨ P).  Core literal `aᵢ` ⇒ clause literal `¬aᵢ`.
    let mut a_clause: Vec<CnfLit> = a_side.iter().map(LemmaLit::clause_lit).collect();
    a_clause.push(CnfLit::positive(p_var));
    if a_cnf.add_clause(CnfClause::new(a_clause)).is_err() {
        return Ok(false);
    }

    // B-clause: (¬P ∨ ¬b₁ ∨ …).
    let mut b_clause: Vec<CnfLit> = b_side.iter().map(LemmaLit::clause_lit).collect();
    b_clause.push(CnfLit::positive(p_var).negated());
    if b_cnf.add_clause(CnfClause::new(b_clause)).is_err() {
        return Ok(false);
    }

    Ok(true)
}

/// One abstracted real order atom: the base comparison term and the [`CnfVar`]
/// standing for it.
struct AtomBinding {
    /// The base order-atom term (`RealLt`/`RealLe`/`RealGt`/`RealGe`).
    term: TermId,
    /// The propositional variable abstracting it.
    var: CnfVar,
}

/// The Boolean-abstraction state: a deterministic order-atom ↔ [`CnfVar`]
/// bijection plus per-atom side flags. Mirrors the `dpll_t::Abstractor` atom
/// recognition (including the `Eq`-over-reals split into `≤` ∧ `≥`), so the
/// atoms it abstracts line up with the lemmas [`certify_lra_dpll_unsat`]
/// produces.
#[derive(Default)]
struct Abstractor {
    /// Base order-atom term → its dense atom index.
    index_of: BTreeMap<TermId, usize>,
    /// Atom bindings in dense-index order.
    atoms: Vec<AtomBinding>,
    /// `in_a[i]` / `in_b[i]`: whether atom `i` occurs in `A` / `B`.
    in_a: Vec<bool>,
    in_b: Vec<bool>,
    /// Fresh **shared** synthetic Farkas atoms `P`: their [`CnfVar`] → lifted
    /// real-atom term. These occupy variable indices above both formulas' aux
    /// ranges.
    synthetic: BTreeMap<CnfVar, TermId>,
    /// The next free variable index for a synthetic shared atom (set once both
    /// CNF formulas are built, above their auxiliary ranges).
    next_synthetic: usize,
}

impl Abstractor {
    /// Registers (without encoding) every order atom occurring in `assertions`,
    /// marking each with `side`. Returns `None` on an unsupported leaf so the
    /// caller declines. Equality over reals is split into its two order atoms,
    /// matching the lazy-SMT abstraction.
    fn register_atoms(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        side: Side,
    ) -> Option<()> {
        for &assertion in assertions {
            self.walk_register(arena, assertion, side)?;
        }
        Some(())
    }

    fn walk_register(&mut self, arena: &mut TermArena, term: TermId, side: Side) -> Option<()> {
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(_) => Some(()),
            TermNode::Symbol(_) if arena.sort_of(term) == Sort::Bool => Some(()),
            TermNode::App { op, args } => match op {
                Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies => {
                    for &arg in &args {
                        self.walk_register(arena, arg, side)?;
                    }
                    Some(())
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    for &arg in &args {
                        self.walk_register(arena, arg, side)?;
                    }
                    Some(())
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    for &arg in &args {
                        self.walk_register(arena, arg, side)?;
                    }
                    Some(())
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    self.register_atom(term, side);
                    Some(())
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    let le = arena.real_le(args[0], args[1]).ok()?;
                    let ge = arena.real_ge(args[0], args[1]).ok()?;
                    self.register_atom(le, side);
                    self.register_atom(ge, side);
                    Some(())
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Records `term` as an atom, allocating a fresh [`CnfVar`] on first sight,
    /// and marks its `side`.
    fn register_atom(&mut self, term: TermId, side: Side) {
        let index = if let Some(&index) = self.index_of.get(&term) {
            index
        } else {
            let index = self.atoms.len();
            // The atom index is the CnfVar index; both grow together.
            let var = CnfVar::new(index).expect("atom index fits in a CnfVar");
            self.index_of.insert(term, index);
            self.atoms.push(AtomBinding { term, var });
            self.in_a.push(false);
            self.in_b.push(false);
            index
        };
        match side {
            Side::A => self.in_a[index] = true,
            Side::B => self.in_b[index] = true,
        }
    }

    /// The exclusive side of an atom variable, or `None` when it is shared (in
    /// both `A` and `B`). Used to colour theory lemmas.
    fn side_of(&self, var: CnfVar) -> Option<Side> {
        let i = var.index();
        let in_a = self.in_a.get(i).copied().unwrap_or(false);
        let in_b = self.in_b.get(i).copied().unwrap_or(false);
        match (in_a, in_b) {
            (true, false) => Some(Side::A),
            (false, true) => Some(Side::B),
            // Shared, or (defensively) an unknown variable.
            _ => None,
        }
    }

    /// Encodes the Boolean structure of `assertions` (their conjunction) into a
    /// CNF formula whose variable space starts at `base_count`: the shared atom
    /// variables occupy `[0, atom_count)`, indices `[atom_count, base_count)` are
    /// phantom placeholders (the other side's auxiliary range, kept disjoint),
    /// and the Tseitin encoder allocates fresh auxiliaries from `base_count`
    /// upward. Returns `None` on an unsupported leaf.
    fn encode_assertions(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        base_count: usize,
    ) -> Option<CnfFormula> {
        let mut formula = CnfFormula::new(base_count);
        for &assertion in assertions {
            let expr = self.encode(arena, assertion)?;
            // Assert the assertion's encoding as a unit (the conjunction holds).
            let lit = expr.tseitin(&mut formula);
            formula.add_clause(CnfClause::new(vec![lit])).ok()?;
        }
        Some(formula)
    }

    /// Allocates a fresh **shared** synthetic Farkas atom variable for `p_term`,
    /// at the next index above both formulas' auxiliary ranges. The variable is
    /// shared (it appears in both the A-clause and B-clause of a purified lemma),
    /// so it may legitimately occur in the final interpolant and lifts to
    /// `p_term`.
    fn register_synthetic_shared(&mut self, p_term: TermId) -> CnfVar {
        let var = CnfVar::new(self.next_synthetic).expect("synthetic index fits in a CnfVar");
        self.next_synthetic += 1;
        self.synthetic.insert(var, p_term);
        var
    }

    /// Builds the [`BoolExpr`] skeleton of `term` over atom variables. Returns
    /// `None` on an unsupported leaf.
    #[allow(clippy::only_used_in_recursion)]
    fn encode(&mut self, arena: &mut TermArena, term: TermId) -> Option<BoolExpr> {
        let node = arena.node(term).clone();
        match node {
            TermNode::BoolConst(value) => Some(if value { BoolExpr::Top } else { BoolExpr::Bot }),
            TermNode::App { op, args } => match op {
                Op::BoolNot => Some(self.encode(arena, args[0])?.not()),
                Op::BoolAnd => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    Some(a.and(b))
                }
                Op::BoolOr => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    Some(a.or(b))
                }
                Op::BoolXor => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    // a xor b = (a ∧ ¬b) ∨ (¬a ∧ b).
                    Some(a.clone().and(b.clone().not()).or(a.not().and(b)))
                }
                Op::BoolImplies => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    Some(a.not().or(b))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
                    let a = self.encode(arena, args[0])?;
                    let b = self.encode(arena, args[1])?;
                    // a iff b = (a ∧ b) ∨ (¬a ∧ ¬b).
                    Some(a.clone().and(b.clone()).or(a.not().and(b.not())))
                }
                Op::Ite if arena.sort_of(term) == Sort::Bool => {
                    let c = self.encode(arena, args[0])?;
                    let t = self.encode(arena, args[1])?;
                    let e = self.encode(arena, args[2])?;
                    // ite(c, t, e) = (c ∧ t) ∨ (¬c ∧ e).
                    Some(c.clone().and(t).or(c.not().and(e)))
                }
                Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe => {
                    let var = *self.index_of.get(&term)?;
                    Some(BoolExpr::Var(CnfVar::new(var).ok()?))
                }
                Op::Eq if arena.sort_of(args[0]) == Sort::Real => {
                    let le = arena.real_le(args[0], args[1]).ok()?;
                    let ge = arena.real_ge(args[0], args[1]).ok()?;
                    let le_var = *self.index_of.get(&le)?;
                    let ge_var = *self.index_of.get(&ge)?;
                    Some(
                        BoolExpr::Var(CnfVar::new(le_var).ok()?)
                            .and(BoolExpr::Var(CnfVar::new(ge_var).ok()?)),
                    )
                }
                _ => None,
            },
            // A free Boolean symbol (not over the shared real vocabulary) or a
            // non-Boolean constant at a Boolean position: this construction does
            // not abstract it, so decline.
            _ => None,
        }
    }

    /// Matches `literal` (a theory-lemma literal, an atom or its `BoolNot`) to
    /// `(atom_var, positive)`, where `positive` is the literal's polarity.
    /// Returns `None` if its base atom was not registered.
    fn atom_literal(&self, arena: &TermArena, literal: TermId) -> Option<(CnfVar, bool)> {
        let (base, positive) = match arena.node(literal) {
            TermNode::App {
                op: Op::BoolNot,
                args,
            } => (args[0], false),
            _ => (literal, true),
        };
        let index = *self.index_of.get(&base)?;
        let var = self.atoms.get(index)?.var;
        Some((var, positive))
    }

    /// Lifts a propositional interpolant [`BoolExpr`] (over shared atom
    /// variables) back to a real-term [`TermId`]: an atom variable becomes its
    /// LRA-atom term, a synthetic Farkas variable becomes its partial-interpolant
    /// term; `And`/`Or`/`Not`/`Top`/`Bot` become arena builders. Returns `None`
    /// if a variable is neither a registered atom nor a synthetic atom (an
    /// auxiliary leaked in) or a builder fails.
    fn lift(&self, arena: &mut TermArena, expr: &BoolExpr) -> Option<TermId> {
        match expr {
            BoolExpr::Top => Some(arena.bool_const(true)),
            BoolExpr::Bot => Some(arena.bool_const(false)),
            BoolExpr::Var(var) => {
                if let Some(binding) = self.atoms.get(var.index())
                    && binding.var == *var
                {
                    return Some(binding.term);
                }
                // A synthetic Farkas atom: lift to its partial-interpolant term.
                self.synthetic.get(var).copied()
            }
            BoolExpr::Not(inner) => {
                let lifted = self.lift(arena, inner)?;
                arena.not(lifted).ok()
            }
            BoolExpr::And(lhs, rhs) => {
                let a = self.lift(arena, lhs)?;
                let b = self.lift(arena, rhs)?;
                arena.and(a, b).ok()
            }
            BoolExpr::Or(lhs, rhs) => {
                let a = self.lift(arena, lhs)?;
                let b = self.lift(arena, rhs)?;
                arena.or(a, b).ok()
            }
        }
    }
}

/// Grows the smaller of two CNF formulas so both have the same
/// [`CnfFormula::variable_count`], as [`propositional_interpolant`] requires.
/// The extra variables are unused private auxiliaries (they appear in no
/// clause), so the colouring is unaffected.
fn equalise_variable_count(a: &mut CnfFormula, b: &mut CnfFormula) {
    let count = a.variable_count().max(b.variable_count());
    grow_to(a, count);
    grow_to(b, count);
}

/// Rebuilds `formula` over `count` variables, preserving its clauses. A no-op
/// when it already has at least `count` variables.
fn grow_to(formula: &mut CnfFormula, count: usize) {
    if count <= formula.variable_count() {
        return;
    }
    let mut grown = CnfFormula::new(count);
    for clause in formula.clauses() {
        // Existing clauses reference only in-range variables, so this add cannot
        // fail; ignore the impossible error rather than panic.
        let _ = grown.add_clause(CnfClause::new(clause.to_vec()));
    }
    *formula = grown;
}

/// Collects every free symbol appearing in any of `terms`.
fn symbols_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for &term in terms {
        collect_symbols(arena, term, &mut out);
    }
    out
}

fn collect_symbols(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) => {
                out.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}
