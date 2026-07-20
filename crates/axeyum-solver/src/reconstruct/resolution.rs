//! Kernel-checked propositional resolution and RUP reconstruction.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, NameId};

use super::{ReconstructCtx, ReconstructError, check_against, clause_key, fresh_axiom};

// ===========================================================================
// Propositional resolution (P3.7 slice 3) — the clausal-layer foundation.
//
// Clauses are encoded as Lean `Prop`s and resolution is reconstructed into a
// kernel-checked proof term, ultimately of type `False` for a refutation.
//
// ## The encoding
//
// - A propositional **atom** `p` (a CNF variable / Boolean atom) ⇒ an opaque
//   `Axiom : Prop` (declared lazily, deterministically, in `prop_atoms`).
// - A **literal** `p` ⇒ the Prop `p`; `(not p)` ⇒ `Not p` (= `p → False`).
// - A **clause** `(cl l1 … ln)` ⇒ the right-nested disjunction
//   `l1 ∨ (l2 ∨ … ∨ ln)`; the **empty clause `(cl)`** ⇒ `False`; a unit clause
//   `(cl l)` ⇒ just `Enc(l)`.
//
// ## Excluded middle
//
// The classical axiom `em : Π (p : Prop), Or p (Not p)` (Lean's `Classical.em`)
// is declared in the context. axeyum's solver is classical, so this is the
// faithful encoding. NOTE: the *binary* resolution reconstruction below is in
// fact constructive — it case-splits (via `Or.rec`) on a premise proof we
// already hold and discharges the pivot branch with `Not l : l → False`, so it
// never consumes `em`. `em` is declared (and reported) to make the classical
// commitment explicit and to back the general pivot-free shape if reached.
//
// ## Soundness
//
// Every reconstructed term is `infer`-checked by the trusted kernel against its
// claimed clause Prop (and the final refutation against `False`). A wrong
// resolvent fails to infer to the claimed type ⇒ `ReconstructError`, never a
// wrong `False`. The only addition to the trusted base is the `em` axiom.
// ===========================================================================

impl ReconstructCtx {
    /// Get (declaring lazily) the `Prop` constant `NameId` for a propositional
    /// atom of the clausal layer. Idempotent: the same atom name always maps to
    /// the same opaque `Axiom : Prop`.
    pub(super) fn prop_atom_const(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.prop_atoms.get(name) {
            return id;
        }
        let decl_name = self.fresh_name("prop");
        let prop = self.kernel.sort_zero();
        self.kernel
            .add_declaration(Declaration::Axiom {
                name: decl_name,
                uparams: vec![],
                ty: prop,
            })
            .expect("propositional atom axiom (_ : Prop) should admit");
        self.prop_atoms.insert(name.to_owned(), decl_name);
        decl_name
    }

    /// Build the Lean proposition `Or a b` (the prelude's `Or`, in `Prop`).
    pub(super) fn mk_or(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let or = self.kernel.const_(self.prelude.or, vec![]);
        let e = self.kernel.app(or, a);
        self.kernel.app(e, b)
    }

    /// Declare (lazily) and return the excluded-middle axiom
    /// `em : Π (p : Prop), Or p (Not p)`.
    ///
    /// # Panics
    ///
    /// Panics only if the fixed, known-good `em` axiom fails to admit, which would
    /// indicate a kernel/prelude regression rather than a caller error.
    pub(super) fn em_axiom(&mut self) -> NameId {
        if let Some(id) = self.em {
            return id;
        }
        let anon = self.kernel.anon();
        let prop = self.kernel.sort_zero();
        // Π (p : Prop), Or p (Not p)  — under the binder `p` = BVar 0.
        let ty = {
            let p0 = self.kernel.bvar(0);
            let not_p = self.mk_not(p0);
            let p0b = self.kernel.bvar(0);
            let or_p = self.mk_or(p0b, not_p);
            self.kernel.pi(anon, prop, or_p, BinderInfo::Default)
        };
        let name = self.fresh_name("em");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty,
            })
            .expect("excluded-middle axiom em : Π (p : Prop), Or p (Not p) should admit");
        self.axiom_roles.insert(name, "em".to_owned());
        self.em = Some(name);
        name
    }

    /// Translate a propositional **literal** into its Lean `Prop`:
    /// a positive literal `p` ⇒ the atom Prop `p`; a negated `(not p)` ⇒ `Not p`.
    fn lit_to_prop(&mut self, lit: &AletheLit) -> ExprId {
        let atom = self.atom_to_prop(&lit.atom);
        if lit.negated { self.mk_not(atom) } else { atom }
    }

    /// Translate a literal **atom** term into its Lean `Prop`. A bare symbol is an
    /// opaque propositional atom; a `(not φ)` application folds to `Not (atom φ)`
    /// so the clausal `negated` flag and a syntactic `(not …)` agree.
    ///
    /// In **bit mode** (the fused bitwise `QF_BV` walk, `bridge` is `Some`) the
    /// translation is *structural* and bridge-substituting: an atom whose key names a
    /// bit-vector predicate maps to that predicate's bit-level Boolean form, and the
    /// Boolean connectives over bits (`and`/`or`/`=`/`xor`/`not`) map to the prelude
    /// connectives — so a predicate's `Prop` is definitionally its bit-level form and
    /// the bridge rules become reflexive. Outside bit mode, atoms are opaque Props.
    fn atom_to_prop(&mut self, term: &AletheTerm) -> ExprId {
        if self.bridge.is_some() {
            return self.gate_term_to_prop(term);
        }
        match term {
            AletheTerm::App(head, args) if head == "not" && args.len() == 1 => {
                let inner = self.atom_to_prop(&args[0]);
                self.mk_not(inner)
            }
            AletheTerm::Const(symbol) => {
                let name = self.prop_atom_const(symbol);
                self.kernel.const_(name, vec![])
            }
            // Any compound atom (e.g. `(= a b)`, `(f x)`) is treated opaquely as a
            // single propositional atom keyed by its s-expression — sound for the
            // clausal layer, where atoms are uninterpreted Props.
            other => {
                let name = self.prop_atom_const(&other.key());
                self.kernel.const_(name, vec![])
            }
        }
    }

    /// Translate a whole **clause** into its Lean `Prop` encoding: the empty
    /// clause ⇒ `False`; a unit clause ⇒ its single literal's Prop; otherwise the
    /// right-nested disjunction `l1 ∨ (l2 ∨ … ∨ ln)`.
    pub(super) fn clause_to_prop(&mut self, clause: &[AletheLit]) -> ExprId {
        let Some((last, rest)) = clause.split_last() else {
            // Empty clause ⇒ False.
            return self.kernel.const_(self.prelude.false_, vec![]);
        };
        let mut acc = self.lit_to_prop(last);
        for lit in rest.iter().rev() {
            let head = self.lit_to_prop(lit);
            acc = self.mk_or(head, acc);
        }
        acc
    }
}

/// A clausal premise during the resolution walk: its literals (for computing the
/// pivot and resolvent structurally) and a kernel proof term of the clause's
/// `Prop` encoding.
#[derive(Clone)]
pub(super) struct Clause {
    pub(super) lits: Vec<AletheLit>,
    pub(super) proof: ExprId,
}

/// A clause in continuation-passing form:
///
/// `forall (P : Prop), (l₁ -> P) -> ... -> (lₙ -> P) -> P`.
///
/// Unlike the ordinary right-nested `Or` encoding, resolving two CPS clauses
/// only wires survivor handlers to the result handlers.  It therefore preserves
/// proof sharing across the long, wide RUP chains emitted by the BV backend.
#[derive(Clone)]
pub(super) struct CpsClause {
    pub(super) lits: Vec<AletheLit>,
    pub(super) proof: ExprId,
}

pub(super) fn cps_clause_prop(ctx: &mut ReconstructCtx, lits: &[AletheLit]) -> ExprId {
    let anon = ctx.kernel.anon();
    let prop = ctx.kernel.sort_zero();
    let target_id = fresh_fvar_id(ctx);
    let target = ctx.kernel.fvar(target_id);
    let mut body = target;
    for literal in lits.iter().rev() {
        let literal_prop = ctx.lit_to_prop(literal);
        let handler = ctx
            .kernel
            .pi(anon, literal_prop, target, BinderInfo::Default);
        body = ctx.kernel.pi(anon, handler, body, BinderInfo::Default);
    }
    let body = ctx.kernel.abstract_fvars(body, &[target_id]);
    ctx.kernel.pi(anon, prop, body, BinderInfo::Default)
}

/// Build a CPS-clause proof from a body expressed against fresh free variables
/// for the target proposition and its literal handlers.
fn build_cps_clause_proof(
    ctx: &mut ReconstructCtx,
    lits: &[AletheLit],
    body: impl FnOnce(&mut ReconstructCtx, ExprId, &[ExprId]) -> Result<ExprId, ReconstructError>,
) -> Result<ExprId, ReconstructError> {
    let target_id = fresh_fvar_id(ctx);
    let target = ctx.kernel.fvar(target_id);
    let handler_ids = (0..lits.len())
        .map(|_| fresh_fvar_id(ctx))
        .collect::<Vec<_>>();
    let handlers = handler_ids
        .iter()
        .map(|&id| ctx.kernel.fvar(id))
        .collect::<Vec<_>>();
    let mut proof = body(ctx, target, &handlers)?;
    let anon = ctx.kernel.anon();
    for (literal, &handler_id) in lits.iter().zip(&handler_ids).rev() {
        proof = ctx.kernel.abstract_fvars(proof, &[handler_id]);
        let literal_prop = ctx.lit_to_prop(literal);
        let handler_ty = ctx
            .kernel
            .pi(anon, literal_prop, target, BinderInfo::Default);
        proof = ctx
            .kernel
            .lam(anon, handler_ty, proof, BinderInfo::Default);
    }
    proof = ctx.kernel.abstract_fvars(proof, &[target_id]);
    let prop = ctx.kernel.sort_zero();
    Ok(ctx.kernel.lam(anon, prop, proof, BinderInfo::Default))
}

pub(super) fn apply_cps_clause(
    ctx: &mut ReconstructCtx,
    clause: &CpsClause,
    target: ExprId,
    handlers: impl IntoIterator<Item = ExprId>,
) -> ExprId {
    let mut proof = ctx.kernel.app(clause.proof, target);
    for handler in handlers {
        proof = ctx.kernel.app(proof, handler);
    }
    proof
}

fn literal_index(lits: &[AletheLit], needle: &AletheLit) -> Option<usize> {
    let key = needle.atom.key();
    lits.iter()
        .position(|literal| literal.atom.key() == key && literal.negated == needle.negated)
}

/// Convert the established right-nested `Or` clause proof to CPS once.  Gate
/// introduction remains small and uses the existing structural reconstructor;
/// all learned resolution clauses stay in CPS after this boundary.
pub(super) fn clause_to_cps(
    ctx: &mut ReconstructCtx,
    clause: &Clause,
) -> Result<CpsClause, ReconstructError> {
    let proof = build_cps_clause_proof(ctx, &clause.lits, |ctx, target, handlers| {
        if clause.lits.is_empty() {
            return Ok(ex_falso(ctx, target, clause.proof));
        }
        clause_elim(
            ctx,
            clause,
            target,
            &clause.lits,
            &|ctx, literal, literal_proof, _| {
                let index = literal_index(&clause.lits, literal).ok_or_else(|| {
                    ReconstructError::UnsupportedResolution {
                        detail: "CPS conversion lost a source literal".to_owned(),
                    }
                })?;
                Ok(ctx.kernel.app(handlers[index], literal_proof))
            },
        )
    })?;
    let expected = cps_clause_prop(ctx, &clause.lits);
    let proof = check_against(ctx, "clause_to_cps", proof, expected)?;
    Ok(CpsClause {
        lits: clause.lits.clone(),
        proof,
    })
}

/// Reconstruct a propositional-**resolution** Alethe proof into a Lean proof term
/// of type `False` that the trusted [`axeyum_lean_kernel::Kernel`] type-checks.
///
/// This is the clausal-layer foundation shared by all clausal proofs (`QF_BV`,
/// SAT).
/// It walks the `Vec<AletheCommand>` shape the clausal emitter produces:
///
/// - **`assume (cl l1 … ln)`** ⇒ a fresh hypothesis `Axiom` of the clause's `Prop`
///   encoding (`l1 ∨ … ∨ ln`, or `False` for `(cl)`, or `Enc(l)` for a unit), and
///   the assumption is recorded under its id.
/// - **`or`** (the emitter's unpacking of an `assume (or φ…)` disjunction into the
///   clause `(cl φ…)`) ⇒ the premise's proof is reused verbatim: the disjunction
///   `(or φ…)` and the clause `(cl φ…)` have the **same** right-nested `Or`
///   encoding, so the unpacking is the identity on the proof term (checked by the
///   kernel against the conclusion).
/// - **`resolution` / `th_resolution`** ⇒ reconstructed by repeated **binary
///   resolution**: the step's premises are resolved pairwise (left fold) on the
///   unique complementary literal of each successive pair, building the conclusion
///   clause's proof; a conclusion of the empty clause `(cl)` yields a term of type
///   `False` (via `binary_resolve_on`, the Davis–Putnam pairwise resolvent).
///
/// The final term — the proof of the conclusion of the step deriving `(cl)` — is
/// `infer`-checked against the prelude's `False`. A wrong reconstruction makes
/// that gate fail, so this returns an error, never a wrong `False`.
///
/// # Errors
///
/// Returns a [`ReconstructError`] for an unknown premise id, an unsupported
/// command/rule shape, a resolution whose premises do not have the expected
/// single complementary pivot, a proof that never derives the empty clause, or a
/// kernel rejection. It never panics on malformed or out-of-scope input.
pub fn reconstruct_resolution_proof(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<ExprId, ReconstructError> {
    // Declare `em` up front so the classical commitment is recorded even when the
    // (constructive) binary path does not consume it.
    let _ = ctx.em_axiom();

    let mut env: BTreeMap<String, Clause> = BTreeMap::new();

    for cmd in commands {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                let prop = ctx.clause_to_prop(clause);
                let proof = fresh_axiom(ctx, prop, "assume")?;
                env.insert(
                    id.clone(),
                    Clause {
                        lits: clause.clone(),
                        proof,
                    },
                );
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => match rule.as_str() {
                // `or` unpacks an assumed disjunction into clause form; the `Prop`
                // encodings coincide, so the proof passes through unchanged (and is
                // kernel-checked against the conclusion encoding).
                "or" => {
                    let [p] = premises.as_slice() else {
                        return Err(ReconstructError::UnsupportedResolution {
                            detail: format!(
                                "`or` step expects exactly one premise, found {}",
                                premises.len()
                            ),
                        });
                    };
                    let premise = lookup(&env, p)?;
                    let expected = ctx.clause_to_prop(clause);
                    let proof = check_against(ctx, "or", premise.proof, expected)?;
                    env.insert(
                        id.clone(),
                        Clause {
                            lits: clause.clone(),
                            proof,
                        },
                    );
                }
                "resolution" | "th_resolution" => {
                    let resolved = reconstruct_resolution_step(ctx, clause, premises, &env)?;
                    if clause.is_empty() {
                        // The empty clause: this is the refutation close. Validate the
                        // term against `False` and return it.
                        return check_false_prop(ctx, resolved.proof);
                    }
                    // A non-empty resolvent: kernel-check it against the stated
                    // conclusion encoding, then record it for later steps.
                    let expected = ctx.clause_to_prop(clause);
                    let proof = check_against(ctx, rule, resolved.proof, expected)?;
                    env.insert(
                        id.clone(),
                        Clause {
                            lits: clause.clone(),
                            proof,
                        },
                    );
                }
                other => {
                    return Err(ReconstructError::UnsupportedRule {
                        rule: other.to_owned(),
                    });
                }
            },
        }
    }

    Err(ReconstructError::NoEmptyClause)
}

/// Look up a premise clause by id, erroring with [`ReconstructError::UnknownPremise`]
/// when it was never defined.
fn lookup<'a>(
    env: &'a BTreeMap<String, Clause>,
    id: &str,
) -> Result<&'a Clause, ReconstructError> {
    env.get(id)
        .ok_or_else(|| ReconstructError::UnknownPremise { id: id.to_owned() })
}

/// Reconstruct one `resolution`/`th_resolution` step from its premise clauses.
///
/// The native emitter supplies LRAT's exact RUP hint order. Replay that order first:
/// falsify the conclusion, propagate every non-final unit hint, require a final
/// conflict, then resolve the chain backwards on the recorded pivots. This is linear
/// in the hint count and mirrors the independent LRAT checker. General Alethe inputs
/// that are not ordered RUP chains retain the complete Davis–Putnam fallback.
///
/// The returned [`Clause`] carries the stated conclusion literals and its
/// kernel-checked proof term.
///
/// Pool-size budget for the Davis–Putnam working set: DP is worst-case exponential,
/// so cap the pool and degrade to a clean error rather than hang/OOM on a
/// pathological proof.
const DP_POOL_BUDGET: usize = 4096;

pub(super) fn reconstruct_resolution_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, Clause>,
) -> Result<Clause, ReconstructError> {
    if premises.is_empty() {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "resolution step has no premises".to_owned(),
        });
    }
    // Polarity-normalize every clause first so syntactic `not` atoms and literal
    // flags match as pivots. Moving a positive `not` is definitional; cancelling
    // double negation is classical, so `normalize_clause` explicitly rebuilds
    // and kernel-checks the clause proof through the declared `em` axiom.
    let raw_pool = premises
        .iter()
        .map(|premise| lookup(env, premise).cloned())
        .collect::<Result<Vec<_>, _>>()?;

    if let Some(resolved) = reconstruct_ordered_rup_step(ctx, conclusion, &raw_pool)? {
        return Ok(resolved);
    }

    let pool = raw_pool
        .iter()
        .map(|clause| normalize_clause(ctx, clause))
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(resolved) = reconstruct_rup_closure_step(ctx, conclusion, &pool)? {
        return Ok(resolved);
    }
    reconstruct_resolution_step_dp(ctx, conclusion, pool)
}

/// Replay an exact LRAT/RUP hint chain and construct its resolution proof.
///
/// `None` means the premises are not in exact RUP order; callers may use a more
/// general reconstruction. Once a valid chain has been recognized, construction or
/// kernel failures are returned rather than hidden behind the fallback.
fn reconstruct_ordered_rup_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[Clause],
) -> Result<Option<Clause>, ReconstructError> {
    let Some((final_hint, unit_hints)) = premises.split_last() else {
        return Ok(None);
    };

    // Seed the assignment with the negation of the claimed clause, exactly as the
    // LRAT verifier does. A tautological conclusion needs no hint chain and is left
    // to the general fallback.
    let mut assignment: BTreeMap<String, bool> = BTreeMap::new();
    for literal in conclusion {
        let key = literal.atom.key();
        let falsifying_value = literal.negated;
        if assignment
            .insert(key, falsifying_value)
            .is_some_and(|previous| previous != falsifying_value)
        {
            return Ok(None);
        }
    }

    // Forward unit propagation records the pivot literal forced by every hint.
    let mut pivots = Vec::with_capacity(unit_hints.len());
    for hint in unit_hints {
        let status = classify_rup_clause(&hint.lits, &assignment);
        let RupClauseStatus::Unit(literal) = status else {
            return Ok(None);
        };
        assignment.insert(literal.atom.key(), !literal.negated);
        pivots.push(literal);
    }
    if !matches!(
        classify_rup_clause(&final_hint.lits, &assignment),
        RupClauseStatus::Conflict
    ) {
        return Ok(None);
    }

    // Reverse resolution is the proof-producing counterpart of forward unit
    // propagation. Each reason owns the propagated literal; the current conflict
    // must own its complement. This is the same chain extraction used by the CNF
    // interpolant builder and by cvc5's explicit chain-resolution utility.
    // Unit propagation must use the emitter's original CNF-variable identity.
    // Only after validating that chain do we polarity-normalize proof clauses:
    // Alethe atoms can themselves be `(not p)`, and collapsing those before replay
    // can merge distinct Tseitin variables and destroy the recorded unit order.
    let normalized_hints = premises
        .iter()
        .map(|clause| normalize_clause(ctx, clause))
        .collect::<Result<Vec<_>, _>>()?;
    let (final_hint, unit_hints) = normalized_hints
        .split_last()
        .expect("non-empty premises established above");
    let mut current = final_hint.clone();
    for (reason, pivot) in unit_hints.iter().zip(pivots.iter()).rev() {
        let pivot = normalize_lit_polarity(pivot);
        let key = pivot.atom.key();
        let reason_has_pivot = reason
            .lits
            .iter()
            .any(|literal| literal.atom.key() == key && literal.negated == pivot.negated);
        let current_has_complement = current
            .lits
            .iter()
            .any(|literal| literal.atom.key() == key && literal.negated != pivot.negated);
        if !reason_has_pivot || !current_has_complement {
            // A redundant propagation or crowding-literal chain is valid RUP but
            // not this direct binary fold. Preserve completeness via DP.
            return Ok(None);
        }
        let current_has_positive = current
            .lits
            .iter()
            .any(|literal| literal.atom.key() == key && !literal.negated);
        let Some(resolvent) = binary_resolve_on(ctx, &current, reason, &key, current_has_positive)?
        else {
            return Ok(None);
        };
        current = resolvent;
    }

    weaken_clause_to_conclusion(ctx, &current, conclusion)
}

enum RupClauseStatus {
    Satisfied,
    Conflict,
    Unit(AletheLit),
    Unresolved,
}

/// Classify a normalized Alethe clause under an atom assignment. Duplicate
/// literals are factored so they do not turn a genuine unit into `Unresolved`.
fn classify_rup_clause(
    clause: &[AletheLit],
    assignment: &BTreeMap<String, bool>,
) -> RupClauseStatus {
    let mut unassigned: BTreeMap<String, AletheLit> = BTreeMap::new();
    for literal in clause {
        let key = literal.atom.key();
        if let Some(&value) = assignment.get(&key) {
            if value != literal.negated {
                return RupClauseStatus::Satisfied;
            }
            continue;
        }
        match unassigned.get(&key) {
            Some(previous) if previous.negated != literal.negated => {
                return RupClauseStatus::Unresolved;
            }
            Some(_) => {}
            None => {
                unassigned.insert(key, literal.clone());
            }
        }
    }
    match unassigned.len() {
        0 => RupClauseStatus::Conflict,
        1 => RupClauseStatus::Unit(
            unassigned
                .into_values()
                .next()
                .expect("one unassigned literal"),
        ),
        _ => RupClauseStatus::Unresolved,
    }
}

/// Construct one binary resolvent in CPS form.  Survivor branches are handler
/// references, so the term size is linear in the two parent widths and does not
/// rebuild an `Or.inl`/`Or.inr` injection path for every survivor.
#[allow(dead_code)]
fn binary_resolve_cps_on(
    ctx: &mut ReconstructCtx,
    c: &CpsClause,
    d: &CpsClause,
    pivot_key: &str,
) -> Result<Option<CpsClause>, ReconstructError> {
    let polarity = |clause: &CpsClause, negated: bool| {
        clause
            .lits
            .iter()
            .any(|literal| literal.atom.key() == pivot_key && literal.negated == negated)
    };
    let c_pos = polarity(c, false);
    let c_neg = polarity(c, true);
    let d_pos = polarity(d, false);
    let d_neg = polarity(d, true);
    if (c_pos && c_neg) || (d_pos && d_neg) {
        return Ok(None);
    }
    let (positive, negative) = if c_pos && d_neg {
        (c, d)
    } else if d_pos && c_neg {
        (d, c)
    } else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: format!("CPS parents do not carry complementary pivot `{pivot_key}`"),
        });
    };

    let mut resolvent = Vec::new();
    for literal in positive.lits.iter().chain(&negative.lits) {
        if literal.atom.key() != pivot_key {
            push_unique(literal, &mut resolvent);
        }
    }
    if resolvent.iter().any(|literal| {
        let key = literal.atom.key();
        resolvent
            .iter()
            .any(|other| other.atom.key() == key && other.negated != literal.negated)
    }) {
        return Ok(None);
    }

    let proof = build_cps_clause_proof(ctx, &resolvent, |ctx, target, result_handlers| {
        let mut positive_handlers = Vec::with_capacity(positive.lits.len());
        for literal in &positive.lits {
            if literal.atom.key() != pivot_key {
                let index = literal_index(&resolvent, literal).ok_or_else(|| {
                    ReconstructError::UnsupportedResolution {
                        detail: "CPS resolvent lost a positive-parent survivor".to_owned(),
                    }
                })?;
                positive_handlers.push(result_handlers[index]);
                continue;
            }

            let positive_id = fresh_fvar_id(ctx);
            let positive_proof = ctx.kernel.fvar(positive_id);
            let mut negative_handlers = Vec::with_capacity(negative.lits.len());
            for negative_literal in &negative.lits {
                if negative_literal.atom.key() != pivot_key {
                    let index = literal_index(&resolvent, negative_literal).ok_or_else(|| {
                        ReconstructError::UnsupportedResolution {
                            detail: "CPS resolvent lost a negative-parent survivor".to_owned(),
                        }
                    })?;
                    negative_handlers.push(result_handlers[index]);
                    continue;
                }

                let negative_id = fresh_fvar_id(ctx);
                let negative_proof = ctx.kernel.fvar(negative_id);
                let contradiction = ctx.kernel.app(negative_proof, positive_proof);
                let body = ex_falso(ctx, target, contradiction);
                let body = ctx.kernel.abstract_fvars(body, &[negative_id]);
                let negative_prop = ctx.lit_to_prop(negative_literal);
                let anon = ctx.kernel.anon();
                negative_handlers.push(ctx.kernel.lam(
                    anon,
                    negative_prop,
                    body,
                    BinderInfo::Default,
                ));
            }
            let body = apply_cps_clause(ctx, negative, target, negative_handlers);
            let body = ctx.kernel.abstract_fvars(body, &[positive_id]);
            let positive_prop = ctx.lit_to_prop(literal);
            let anon = ctx.kernel.anon();
            positive_handlers.push(ctx.kernel.lam(
                anon,
                positive_prop,
                body,
                BinderInfo::Default,
            ));
        }
        Ok(apply_cps_clause(
            ctx,
            positive,
            target,
            positive_handlers,
        ))
    })?;
    let expected = cps_clause_prop(ctx, &resolvent);
    let proof = check_against(ctx, "resolution_cps", proof, expected)?;
    Ok(Some(CpsClause {
        lits: resolvent,
        proof,
    }))
}

#[allow(dead_code)]
fn weaken_cps_to_conclusion(
    ctx: &mut ReconstructCtx,
    derived: &CpsClause,
    conclusion: &[AletheLit],
) -> Result<Option<CpsClause>, ReconstructError> {
    if derived
        .lits
        .iter()
        .any(|literal| literal_index(conclusion, literal).is_none())
    {
        return Ok(None);
    }
    let proof = build_cps_clause_proof(ctx, conclusion, |ctx, target, handlers| {
        let derived_handlers = derived
            .lits
            .iter()
            .map(|literal| {
                literal_index(conclusion, literal)
                    .map(|index| handlers[index])
                    .ok_or_else(|| ReconstructError::UnsupportedResolution {
                        detail: "CPS weakening lost a derived literal".to_owned(),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(apply_cps_clause(ctx, derived, target, derived_handlers))
    })?;
    let expected = cps_clause_prop(ctx, conclusion);
    let proof = check_against(ctx, "resolution_cps_weaken", proof, expected)?;
    Ok(Some(CpsClause {
        lits: conclusion.to_vec(),
        proof,
    }))
}

pub(super) fn normalize_cps_clause(
    ctx: &mut ReconstructCtx,
    clause: &CpsClause,
) -> Result<CpsClause, ReconstructError> {
    let normalized = clause
        .lits
        .iter()
        .map(normalize_lit_polarity)
        .collect::<Vec<_>>();
    if normalized == clause.lits {
        return Ok(clause.clone());
    }
    let proof = build_cps_clause_proof(ctx, &normalized, |ctx, target, handlers| {
        let mut source_handlers = Vec::with_capacity(clause.lits.len());
        for source in &clause.lits {
            let normalized_literal = normalize_lit_polarity(source);
            let index = literal_index(&normalized, &normalized_literal).ok_or_else(|| {
                ReconstructError::UnsupportedResolution {
                    detail: "CPS normalization lost a source literal".to_owned(),
                }
            })?;
            let source_id = fresh_fvar_id(ctx);
            let source_proof = ctx.kernel.fvar(source_id);
            let normalized_proof =
                normalize_lit_proof(ctx, source, source_proof, &normalized_literal)?;
            let body = ctx.kernel.app(handlers[index], normalized_proof);
            let body = ctx.kernel.abstract_fvars(body, &[source_id]);
            let source_prop = ctx.lit_to_prop(source);
            let anon = ctx.kernel.anon();
            source_handlers.push(ctx.kernel.lam(
                anon,
                source_prop,
                body,
                BinderInfo::Default,
            ));
        }
        Ok(apply_cps_clause(ctx, clause, target, source_handlers))
    })?;
    let expected = cps_clause_prop(ctx, &normalized);
    let proof = check_against(ctx, "resolution_cps_normalize", proof, expected)?;
    Ok(CpsClause {
        lits: normalized,
        proof,
    })
}

/// Turn a validated unit-propagation trace directly into a CPS proof of the
/// stated conclusion. For each propagated literal `p`, construct and locally
/// alias exactly one continuation `¬p -> P` from its reason clause. The final
/// conflict clause then consumes the conclusion handlers and those aliases.
/// No intermediate resolvent clause is materialized.
#[allow(clippy::too_many_lines)]
fn construct_cps_rup_from_trace(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[CpsClause],
    propagations: &[(usize, AletheLit)],
    conflict_index: usize,
) -> Result<CpsClause, ReconstructError> {
    let proof = build_cps_clause_proof(ctx, conclusion, |ctx, target, result_handlers| {
        let mut false_handlers = BTreeMap::<(String, bool), ExprId>::new();
        for (literal, &handler) in conclusion.iter().zip(result_handlers) {
            false_handlers.insert((literal.atom.key(), literal.negated), handler);
        }
        let mut lets = Vec::with_capacity(propagations.len());

        for (reason_index, pivot) in propagations {
            let reason = premises.get(*reason_index).ok_or_else(|| {
                ReconstructError::UnsupportedResolution {
                    detail: "CPS RUP propagation references an absent reason".to_owned(),
                }
            })?;
            let complement = AletheLit {
                atom: pivot.atom.clone(),
                negated: !pivot.negated,
            };
            let complement_id = fresh_fvar_id(ctx);
            let complement_proof = ctx.kernel.fvar(complement_id);
            let mut reason_handlers = Vec::with_capacity(reason.lits.len());
            for literal in &reason.lits {
                if literal.atom.key() == pivot.atom.key() && literal.negated == pivot.negated {
                    let pivot_id = fresh_fvar_id(ctx);
                    let pivot_proof = ctx.kernel.fvar(pivot_id);
                    let contradiction = if pivot.negated {
                        ctx.kernel.app(pivot_proof, complement_proof)
                    } else {
                        ctx.kernel.app(complement_proof, pivot_proof)
                    };
                    let body = ex_falso(ctx, target, contradiction);
                    let body = ctx.kernel.abstract_fvars(body, &[pivot_id]);
                    let pivot_prop = ctx.lit_to_prop(literal);
                    let anon = ctx.kernel.anon();
                    reason_handlers.push(ctx.kernel.lam(
                        anon,
                        pivot_prop,
                        body,
                        BinderInfo::Default,
                    ));
                } else {
                    let key = (literal.atom.key(), literal.negated);
                    let handler = false_handlers.get(&key).copied().ok_or_else(|| {
                        ReconstructError::UnsupportedResolution {
                            detail: format!(
                                "CPS RUP reason contains a literal not falsified by the validated prefix: {}{}",
                                if literal.negated { "not " } else { "" },
                                literal.atom.key()
                            ),
                        }
                    })?;
                    reason_handlers.push(handler);
                }
            }
            let body = apply_cps_clause(ctx, reason, target, reason_handlers);
            let body = ctx.kernel.abstract_fvars(body, &[complement_id]);
            let complement_prop = ctx.lit_to_prop(&complement);
            let anon = ctx.kernel.anon();
            let handler = ctx.kernel.lam(
                anon,
                complement_prop,
                body,
                BinderInfo::Default,
            );
            let handler_ty = ctx
                .kernel
                .pi(anon, complement_prop, target, BinderInfo::Default);
            let fvar = fresh_fvar_id(ctx);
            let name = ctx.fresh_name("rup_handler");
            lets.push((fvar, name, handler_ty, handler));
            false_handlers.insert(
                (complement.atom.key(), complement.negated),
                ctx.kernel.fvar(fvar),
            );
        }

        let conflict = premises.get(conflict_index).ok_or_else(|| {
            ReconstructError::UnsupportedResolution {
                detail: "CPS RUP trace references an absent conflict".to_owned(),
            }
        })?;
        let conflict_handlers = conflict
            .lits
            .iter()
            .map(|literal| {
                false_handlers
                    .get(&(literal.atom.key(), literal.negated))
                    .copied()
                    .ok_or_else(|| ReconstructError::UnsupportedResolution {
                        detail: "CPS RUP conflict contains a non-falsified literal".to_owned(),
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut body = apply_cps_clause(ctx, conflict, target, conflict_handlers);
        let fvars = lets
            .iter()
            .map(|(fvar, _, _, _)| *fvar)
            .collect::<Vec<_>>();
        body = ctx.kernel.abstract_fvars(body, &fvars);
        for (index, (_, name, ty, value)) in lets.into_iter().enumerate().rev() {
            let ty = ctx.kernel.abstract_fvars(ty, &fvars[..index]);
            let value = ctx.kernel.abstract_fvars(value, &fvars[..index]);
            body = ctx.kernel.let_(name, ty, value, body);
        }
        Ok(body)
    })?;
    let expected = cps_clause_prop(ctx, conclusion);
    let proof = check_against(ctx, "resolution_cps_rup", proof, expected)?;
    Ok(CpsClause {
        lits: conclusion.to_vec(),
        proof,
    })
}

/// Deterministic unit-closure fallback for RUP hints whose Alethe gate spelling
/// changes the emitter's literal unit order. This mirrors the established
/// right-nested-clause path, but constructs only CPS binary resolvents.
fn reconstruct_rup_closure_cps_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    raw_premises: &[CpsClause],
) -> Result<CpsClause, ReconstructError> {
    let conclusion = conclusion
        .iter()
        .map(normalize_lit_polarity)
        .collect::<Vec<_>>();
    let premises = raw_premises
        .iter()
        .map(|clause| normalize_cps_clause(ctx, clause))
        .collect::<Result<Vec<_>, _>>()?;
    let mut assignment = BTreeMap::new();
    for literal in &conclusion {
        let key = literal.atom.key();
        let falsifying_value = literal.negated;
        if assignment
            .insert(key, falsifying_value)
            .is_some_and(|previous| previous != falsifying_value)
        {
            return Err(ReconstructError::UnsupportedResolution {
                detail: "normalized CPS RUP conclusion is tautological".to_owned(),
            });
        }
    }

    let mut occurrences = BTreeMap::<String, Vec<usize>>::new();
    for (index, clause) in premises.iter().enumerate() {
        let mut seen = BTreeSet::new();
        for literal in &clause.lits {
            let key = literal.atom.key();
            if seen.insert(key.clone()) {
                occurrences.entry(key).or_default().push(index);
            }
        }
    }
    let mut units = BTreeSet::new();
    let mut conflict = None;
    for (index, clause) in premises.iter().enumerate() {
        match classify_rup_clause(&clause.lits, &assignment) {
            RupClauseStatus::Conflict => {
                conflict = Some(index);
                break;
            }
            RupClauseStatus::Unit(_) => {
                units.insert(index);
            }
            RupClauseStatus::Satisfied | RupClauseStatus::Unresolved => {}
        }
    }
    let mut propagations = Vec::new();
    while conflict.is_none() {
        let Some(index) = units.pop_first() else {
            return Err(ReconstructError::UnsupportedResolution {
                detail: "normalized CPS premises do not form a RUP closure".to_owned(),
            });
        };
        let RupClauseStatus::Unit(literal) =
            classify_rup_clause(&premises[index].lits, &assignment)
        else {
            continue;
        };
        let key = literal.atom.key();
        assignment.insert(key.clone(), !literal.negated);
        propagations.push((index, literal));
        for &affected in occurrences
            .get(&key)
            .expect("the propagated atom occurs in its reason")
        {
            match classify_rup_clause(&premises[affected].lits, &assignment) {
                RupClauseStatus::Conflict => {
                    conflict = Some(affected);
                    break;
                }
                RupClauseStatus::Unit(_) => {
                    units.insert(affected);
                }
                RupClauseStatus::Satisfied | RupClauseStatus::Unresolved => {
                    units.remove(&affected);
                }
            }
        }
    }

    construct_cps_rup_from_trace(
        ctx,
        &conclusion,
        &premises,
        &propagations,
        conflict.expect("unit closure found a conflict"),
    )
}

/// Replay the emitter's exact LRAT hint order while keeping every learned
/// clause in CPS form.  The structural RUP validation is independent of the
/// proof-term representation; only after the unit/conflict chain is accepted do
/// we construct the kernel term by resolving the chain backwards.
pub(super) fn reconstruct_ordered_rup_cps_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[String],
    env: &BTreeMap<String, CpsClause>,
) -> Result<CpsClause, ReconstructError> {
    let pool = premises
        .iter()
        .map(|premise| {
            env.get(premise)
                .cloned()
                .ok_or_else(|| ReconstructError::UnknownPremise {
                    id: premise.clone(),
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let Some((final_hint, unit_hints)) = pool.split_last() else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "CPS resolution step has no premises".to_owned(),
        });
    };

    let mut assignment = BTreeMap::new();
    for literal in conclusion {
        let key = literal.atom.key();
        let falsifying_value = literal.negated;
        if assignment
            .insert(key, falsifying_value)
            .is_some_and(|previous| previous != falsifying_value)
        {
            return Err(ReconstructError::UnsupportedResolution {
                detail: "CPS RUP conclusion is tautological".to_owned(),
            });
        }
    }

    let mut pivots = Vec::with_capacity(unit_hints.len());
    for hint in unit_hints {
        let RupClauseStatus::Unit(literal) = classify_rup_clause(&hint.lits, &assignment) else {
            return reconstruct_rup_closure_cps_step(ctx, conclusion, &pool);
        };
        assignment.insert(literal.atom.key(), !literal.negated);
        pivots.push(literal);
    }
    if !matches!(
        classify_rup_clause(&final_hint.lits, &assignment),
        RupClauseStatus::Conflict
    ) {
        return reconstruct_rup_closure_cps_step(ctx, conclusion, &pool);
    }

    let propagations = pivots.into_iter().enumerate().collect::<Vec<_>>();
    construct_cps_rup_from_trace(
        ctx,
        conclusion,
        &pool,
        &propagations,
        pool.len() - 1,
    )
}

/// Reconstruct RUP after Alethe polarity normalization, allowing the premise
/// order to differ from the LRAT variable-level unit order.
///
/// Gate-introduction clauses can spell a Boolean atom differently from learned
/// clauses while remaining classically equivalent. Normalization merges those
/// spellings, so the original hint order may no longer be unit at every position.
/// An occurrence index drives deterministic unit closure over the same premise
/// set, recording one reason per propagation. The backward pass skips irrelevant
/// reasons and resolves only the implication graph that reaches the conflict.
fn reconstruct_rup_closure_step(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    premises: &[Clause],
) -> Result<Option<Clause>, ReconstructError> {
    let mut assignment: BTreeMap<String, bool> = BTreeMap::new();
    for literal in conclusion.iter().map(normalize_lit_polarity) {
        let key = literal.atom.key();
        let falsifying_value = literal.negated;
        if assignment
            .insert(key, falsifying_value)
            .is_some_and(|previous| previous != falsifying_value)
        {
            return Ok(None);
        }
    }

    let mut occurrences: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, clause) in premises.iter().enumerate() {
        let mut seen = BTreeSet::new();
        for literal in &clause.lits {
            let key = literal.atom.key();
            if seen.insert(key.clone()) {
                occurrences.entry(key).or_default().push(index);
            }
        }
    }

    let mut units = BTreeSet::new();
    let mut conflict = None;
    for (index, clause) in premises.iter().enumerate() {
        match classify_rup_clause(&clause.lits, &assignment) {
            RupClauseStatus::Conflict => {
                conflict = Some(index);
                break;
            }
            RupClauseStatus::Unit(_) => {
                units.insert(index);
            }
            RupClauseStatus::Satisfied | RupClauseStatus::Unresolved => {}
        }
    }

    let mut propagations = Vec::new();
    while conflict.is_none() {
        let Some(index) = units.pop_first() else {
            return Ok(None);
        };
        let RupClauseStatus::Unit(literal) =
            classify_rup_clause(&premises[index].lits, &assignment)
        else {
            continue;
        };
        let key = literal.atom.key();
        assignment.insert(key.clone(), !literal.negated);
        propagations.push((index, literal));

        for &affected in occurrences
            .get(&key)
            .expect("the propagated atom occurs in its reason")
        {
            match classify_rup_clause(&premises[affected].lits, &assignment) {
                RupClauseStatus::Conflict => {
                    conflict = Some(affected);
                    break;
                }
                RupClauseStatus::Unit(_) => {
                    units.insert(affected);
                }
                RupClauseStatus::Satisfied | RupClauseStatus::Unresolved => {
                    units.remove(&affected);
                }
            }
        }
    }

    let mut current = premises[conflict.expect("loop exits only with a conflict")].clone();
    for (reason_index, pivot) in propagations.into_iter().rev() {
        let key = pivot.atom.key();
        let current_has_complement = current
            .lits
            .iter()
            .any(|literal| literal.atom.key() == key && literal.negated != pivot.negated);
        if !current_has_complement {
            continue;
        }
        let current_has_positive = current
            .lits
            .iter()
            .any(|literal| literal.atom.key() == key && !literal.negated);
        let Some(resolvent) = binary_resolve_on(
            ctx,
            &current,
            &premises[reason_index],
            &key,
            current_has_positive,
        )?
        else {
            return Ok(None);
        };
        current = resolvent;
    }

    weaken_clause_to_conclusion(ctx, &current, conclusion)
}

/// Weaken a derived subclause to the exact stated conclusion, preserving its
/// literal order and duplicate shape for the outer kernel check.
fn weaken_clause_to_conclusion(
    ctx: &mut ReconstructCtx,
    derived: &Clause,
    conclusion: &[AletheLit],
) -> Result<Option<Clause>, ReconstructError> {
    let normalized = conclusion
        .iter()
        .map(normalize_lit_polarity)
        .collect::<Vec<_>>();
    if derived.lits.iter().any(|literal| {
        !normalized.iter().any(|target| {
            target.atom.key() == literal.atom.key() && target.negated == literal.negated
        })
    }) {
        return Ok(None);
    }

    let target = ctx.clause_to_prop(&normalized);
    let proof = if derived.lits.is_empty() {
        if normalized.is_empty() {
            derived.proof
        } else {
            ex_falso(ctx, target, derived.proof)
        }
    } else {
        clause_elim(
            ctx,
            derived,
            target,
            &normalized,
            &|ctx, literal, literal_proof, normalized| {
                inject_lit(ctx, literal, literal_proof, normalized)
            },
        )?
    };
    let proof = check_against(ctx, "resolution_rup", proof, target)?;
    Ok(Some(Clause {
        lits: normalized,
        proof,
    }))
}

fn reconstruct_resolution_step_dp(
    ctx: &mut ReconstructCtx,
    conclusion: &[AletheLit],
    mut pool: Vec<Clause>,
) -> Result<Clause, ReconstructError> {
    // **Davis–Putnam resolution.** The refutation is a resolution DAG, not a chain
    // (a pivot from one premise cancels against another, not a running
    // accumulator), so any accumulator/greedy/pool fold dead-ends by consuming a
    // clause another subtree needs. Instead, eliminate every **non-conclusion**
    // variable: partition the pool on the variable and replace it with all
    // `pos × neg` resolvents (dropping tautologies). DP is complete for the
    // implied clause, so what remains is the conclusion (the empty clause for a
    // closing refutation). Every `binary_resolve_on` is kernel-checked.
    let conclusion_keys: std::collections::BTreeSet<String> = conclusion
        .iter()
        .map(|l| normalize_lit_polarity(l).atom.key())
        .collect();

    loop {
        // Count, for each non-conclusion variable, how many pool clauses hold it
        // positively vs negatively (each clause counted once per variable).
        let mut counts: std::collections::BTreeMap<String, (usize, usize)> =
            std::collections::BTreeMap::new();
        for c in &pool {
            let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
            for l in &c.lits {
                let k = l.atom.key();
                if conclusion_keys.contains(&k) || !seen.insert(k.clone()) {
                    continue;
                }
                let e = counts.entry(k).or_insert((0, 0));
                if l.negated {
                    e.1 += 1;
                } else {
                    e.0 += 1;
                }
            }
        }
        // Eliminate the variable with the fewest resolvents (`pos × neg`) — the
        // standard Davis–Putnam ordering heuristic that keeps the working set small
        // on structured proofs. Order does not affect correctness (DP is complete),
        // only cost.
        let pivot = counts
            .iter()
            .filter(|(_, (p, n))| *p > 0 && *n > 0)
            .min_by_key(|(_, (p, n))| p * n)
            .map(|(k, _)| k.clone());
        let Some(pivot) = pivot else { break };

        let mut pos: Vec<Clause> = Vec::new();
        let mut neg: Vec<Clause> = Vec::new();
        let mut without: Vec<Clause> = Vec::new();
        for c in std::mem::take(&mut pool) {
            match c.lits.iter().find(|l| l.atom.key() == pivot) {
                Some(l) if !l.negated => pos.push(c),
                Some(_) => neg.push(c),
                None => without.push(c),
            }
        }
        pool = without;
        for p in &pos {
            for n in &neg {
                if let Some(r) = binary_resolve_on(ctx, p, n, &pivot, true)? {
                    // Skip a resolvent already present (cheap subsumption-of-equals).
                    let key = clause_key(&r.lits);
                    if !pool.iter().any(|c| clause_key(&c.lits) == key) {
                        pool.push(r);
                    }
                }
            }
        }
        if pool.len() > DP_POOL_BUDGET {
            return Err(ReconstructError::UnsupportedResolution {
                detail: format!(
                    "Davis–Putnam working set exceeded {DP_POOL_BUDGET} clauses \
                     (proof too large for inlined resolution reconstruction)"
                ),
            });
        }
        if pool.is_empty() {
            return Err(ReconstructError::UnsupportedResolution {
                detail: format!("eliminating `{pivot}` left no clauses"),
            });
        }
    }

    // Every remaining clause has only conclusion literals. Return the one whose
    // literal set matches the conclusion (the empty clause for a closing step).
    let want = normalize_clause_key(conclusion);
    pool.into_iter()
        .find(|c| normalize_clause_key(&c.lits) == want)
        .ok_or_else(|| ReconstructError::UnsupportedResolution {
            detail: format!("resolution did not derive the conclusion `{want}`"),
        })
}

/// A clause's identity key under polarity-normalization, order-independent (sorted
/// `±atom-key` set) — used to compare a derived clause against the step conclusion.
fn normalize_clause_key(lits: &[AletheLit]) -> String {
    let mut parts: Vec<String> = lits
        .iter()
        .map(|l| {
            let n = normalize_lit_polarity(l);
            format!("{}{}", if n.negated { "-" } else { "+" }, n.atom.key())
        })
        .collect();
    parts.sort();
    parts.dedup();
    parts.join(",")
}

/// Canonicalize a literal's polarity by peeling leading `(not …)` atoms into the
/// `negated` flag. [`normalize_clause`] separately derives a proof of the
/// normalized clause because a negative `(not X)` requires classical
/// double-negation elimination before it can become a positive `X`.
pub(super) fn normalize_lit_polarity(lit: &AletheLit) -> AletheLit {
    let mut atom = lit.atom.clone();
    let mut negated = lit.negated;
    while let AletheTerm::App(head, args) = &atom {
        if head == "not" && args.len() == 1 {
            let inner = args[0].clone();
            atom = inner;
            negated = !negated;
        } else {
            break;
        }
    }
    AletheLit { atom, negated }
}

fn normalize_clause(ctx: &mut ReconstructCtx, clause: &Clause) -> Result<Clause, ReconstructError> {
    let normalized = clause
        .lits
        .iter()
        .map(normalize_lit_polarity)
        .collect::<Vec<_>>();
    if normalized == clause.lits {
        return Ok(clause.clone());
    }
    let target = ctx.clause_to_prop(&normalized);
    let proof = clause_elim(
        ctx,
        clause,
        target,
        &normalized,
        &|ctx, literal, literal_proof, normalized| {
            let normalized_literal = normalize_lit_polarity(literal);
            let normalized_proof =
                normalize_lit_proof(ctx, literal, literal_proof, &normalized_literal)?;
            inject_lit(ctx, &normalized_literal, normalized_proof, normalized)
        },
    )?;
    let proof = check_against(ctx, "resolution_normalize", proof, target)?;
    Ok(Clause {
        lits: normalized,
        proof,
    })
}

fn normalize_lit_proof(
    ctx: &mut ReconstructCtx,
    source: &AletheLit,
    source_proof: ExprId,
    target: &AletheLit,
) -> Result<ExprId, ReconstructError> {
    let source_prop = ctx.lit_to_prop(source);
    let target_prop = ctx.lit_to_prop(target);
    if ctx.kernel.def_eq(source_prop, target_prop) {
        return Ok(source_proof);
    }

    let mut current = source.clone();
    let mut proof = source_proof;
    while current != *target {
        let AletheTerm::App(head, args) = &current.atom else {
            return Err(ReconstructError::UnsupportedResolution {
                detail: "polarity normalization changed a non-negation literal".to_owned(),
            });
        };
        if head != "not" || args.len() != 1 {
            return Err(ReconstructError::UnsupportedResolution {
                detail: "polarity normalization changed a non-negation literal".to_owned(),
            });
        }
        let next = AletheLit {
            atom: args[0].clone(),
            negated: !current.negated,
        };
        if current.negated {
            let next_prop = ctx.lit_to_prop(&next);
            proof = double_negation_elim(ctx, next_prop, proof);
        }
        current = next;
    }
    Ok(proof)
}

pub(super) fn double_negation_elim(
    ctx: &mut ReconstructCtx,
    proposition: ExprId,
    proof: ExprId,
) -> ExprId {
    let not_proposition = ctx.mk_not(proposition);
    let disjunction = ctx.mk_or(proposition, not_proposition);
    let anon = ctx.kernel.anon();

    let positive = {
        let body = ctx.kernel.bvar(0);
        ctx.kernel.lam(anon, proposition, body, BinderInfo::Default)
    };
    let negative = {
        let fvar = fresh_fvar_id(ctx);
        let not_proof = ctx.kernel.fvar(fvar);
        let contradiction = ctx.kernel.app(proof, not_proof);
        let body = ex_falso(ctx, proposition, contradiction);
        let body = ctx.kernel.abstract_fvars(body, &[fvar]);
        ctx.kernel
            .lam(anon, not_proposition, body, BinderInfo::Default)
    };
    let motive = ctx
        .kernel
        .lam(anon, disjunction, proposition, BinderInfo::Default);
    let em_name = ctx.em_axiom();
    let em = ctx.kernel.const_(em_name, vec![]);
    let em_proposition = ctx.kernel.app(em, proposition);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let result = ctx.kernel.app(rec, proposition);
    let result = ctx.kernel.app(result, not_proposition);
    let result = ctx.kernel.app(result, motive);
    let result = ctx.kernel.app(result, positive);
    let result = ctx.kernel.app(result, negative);
    ctx.kernel.app(result, em_proposition)
}

/// Push `lit` onto `out` unless a literal of the same atom key and polarity is
/// already present (first-seen-order de-duplication for the resolvent).
fn push_unique(lit: &AletheLit, out: &mut Vec<AletheLit>) {
    let k = (lit.atom.key(), lit.negated);
    if !out.iter().any(|o| (o.atom.key(), o.negated) == k) {
        out.push(lit.clone());
    }
}

/// Build the binary resolvent of clause proofs `hC : Enc(C)` and `hD : Enc(D)` on
/// a **specific** pivot atom (`pivot_key`; `c_has_pos` says `c` holds it
/// positively), proving `Enc(R)` where `R = (C \ {l}) ∪ (D \ {¬l})`.
///
/// This is **constructive**: we case-split (via `Or.rec`) on the premise that
/// carries `l` positively, then on its complement discharge the pivot branch with
/// `¬l : l → False` (`False.rec`) and inject every surviving literal into `Enc(R)`
/// with `Or.inl`/`Or.inr`. No excluded middle is needed.
///
/// Returns `Ok(None)` when the resolvent is a tautology (contains some atom both
/// positively and negatively) — useless, and dropped by Davis–Putnam. Otherwise
/// builds the kernel-checked resolvent clause and its proof.
fn binary_resolve_on(
    ctx: &mut ReconstructCtx,
    c: &Clause,
    d: &Clause,
    pivot_key: &str,
    c_has_pos: bool,
) -> Result<Option<Clause>, ReconstructError> {
    if c.lits.len().max(d.lits.len()) > 16 && c.lits.len().min(d.lits.len()) <= 16 {
        return binary_resolve_wide_on(ctx, c, d, pivot_key);
    }
    // Orient: `pos` is the clause with the pivot positive, `neg` with `¬pivot`.
    let (pos, neg) = if c_has_pos { (c, d) } else { (d, c) };

    // The resolvent literal list: survivors of `pos` (drop positive pivot) then
    // survivors of `neg` (drop negative pivot), de-duplicated by key+polarity in
    // first-seen order.
    let mut resolvent: Vec<AletheLit> = Vec::new();
    for lit in &pos.lits {
        if lit.atom.key() != pivot_key || lit.negated {
            push_unique(lit, &mut resolvent);
        }
    }
    for lit in &neg.lits {
        if lit.atom.key() != pivot_key || !lit.negated {
            push_unique(lit, &mut resolvent);
        }
    }

    // A tautological resolvent (some atom appears both `+` and `-`) is dropped.
    let tautological = resolvent.iter().any(|l| {
        let k = l.atom.key();
        resolvent
            .iter()
            .any(|o| o.atom.key() == k && o.negated != l.negated)
    });
    if tautological {
        return Ok(None);
    }

    // The target Prop `Enc(R)`. Cache every right-nested suffix once: all
    // literal handlers inject into the same resolvent, and rebuilding suffixes
    // per handler makes wide RUP clauses cubic in expression construction.
    let r_prop = ctx.clause_to_prop(&resolvent);

    let resolvent_suffixes = clause_suffix_props(ctx, &resolvent);

    // `neg`-handler: a proof of the pivot `hp : pivot` produces a proof of
    // `Enc(R)` from `neg`'s proof, by case-splitting on `Enc(neg)`. For neg's
    // pivot literal `¬pivot : pivot → False` we get `False`, discharged by
    // `False.rec` into `Enc(R)`; every other literal is injected into `Enc(R)`.
    //
    // We build it as a closed term consuming `hp` and `neg.proof` directly (no
    // binder games): `neg_to_r(hp) : Enc(R)`.
    let neg_to_r = |ctx: &mut ReconstructCtx, hp: ExprId| -> Result<ExprId, ReconstructError> {
        clause_elim(
            ctx,
            neg,
            r_prop,
            &resolvent,
            &|ctx, lit, lit_proof, resolvent| {
                if lit.atom.key() == pivot_key && lit.negated {
                    // lit_proof : Not pivot = pivot → False. Apply to hp, then False.rec.
                    let false_app = ctx.kernel.app(lit_proof, hp);
                    Ok(ex_falso(ctx, r_prop, false_app))
                } else {
                    inject_lit_with_suffixes(
                        ctx,
                        lit,
                        lit_proof,
                        resolvent,
                        &resolvent_suffixes,
                    )
                }
            },
        )
    };

    // `pos`-handler: case-split on `Enc(pos)`. For pos's pivot literal
    // `hp : pivot` we run `neg_to_r(hp)`; every other literal is injected.
    let proof = clause_elim(
        ctx,
        pos,
        r_prop,
        &resolvent,
        &|ctx, lit, lit_proof, resolvent| {
            if lit.atom.key() == pivot_key && !lit.negated {
                neg_to_r(ctx, lit_proof)
            } else {
                inject_lit_with_suffixes(
                    ctx,
                    lit,
                    lit_proof,
                    resolvent,
                    &resolvent_suffixes,
                )
            }
        },
    )?;

    Ok(Some(Clause {
        lits: resolvent,
        proof,
    }))
}

#[allow(clippy::too_many_lines)]
fn binary_resolve_wide_on(
    ctx: &mut ReconstructCtx,
    c: &Clause,
    d: &Clause,
    pivot_key: &str,
) -> Result<Option<Clause>, ReconstructError> {
    let (wide, reason) = if c.lits.len() >= d.lits.len() {
        (c, d)
    } else {
        (d, c)
    };
    let wide_pivots = wide
        .lits
        .iter()
        .filter(|literal| literal.atom.key() == pivot_key)
        .collect::<Vec<_>>();
    let reason_pivots = reason
        .lits
        .iter()
        .filter(|literal| literal.atom.key() == pivot_key)
        .collect::<Vec<_>>();
    let ([wide_pivot], [reason_pivot]) = (wide_pivots.as_slice(), reason_pivots.as_slice()) else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "wide resolution requires one pivot occurrence per parent".to_owned(),
        });
    };
    if wide_pivot.negated == reason_pivot.negated {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "wide resolution parents carry the pivot at the same polarity".to_owned(),
        });
    }

    let mut wide_survivors = Vec::new();
    for literal in &wide.lits {
        if literal.atom.key() != pivot_key {
            push_unique(literal, &mut wide_survivors);
        }
    }
    let mut resolvent = wide_survivors.clone();
    for literal in &reason.lits {
        if literal.atom.key() != pivot_key {
            push_unique(literal, &mut resolvent);
        }
    }
    if resolvent.iter().any(|literal| {
        let key = literal.atom.key();
        resolvent
            .iter()
            .any(|other| other.atom.key() == key && other.negated != literal.negated)
    }) {
        return Ok(None);
    }
    let reordered = move_clause_pivot_to_front(ctx, wide, pivot_key)?;
    let target_suffixes = clause_suffix_props(ctx, &resolvent);
    let target_prop = target_suffixes[0];
    let prove_from_pivot = |ctx: &mut ReconstructCtx,
                            pivot_proof: ExprId|
     -> Result<ExprId, ReconstructError> {
        clause_elim(
            ctx,
            reason,
            target_prop,
            &resolvent,
            &|ctx, literal, literal_proof, resolvent| {
                if literal.atom.key() == pivot_key {
                    let contradiction = if wide_pivot.negated {
                        ctx.kernel.app(pivot_proof, literal_proof)
                    } else {
                        ctx.kernel.app(literal_proof, pivot_proof)
                    };
                    Ok(ex_falso(ctx, target_prop, contradiction))
                } else {
                    inject_lit_with_suffixes(
                        ctx,
                        literal,
                        literal_proof,
                        resolvent,
                        &target_suffixes,
                    )
                }
            },
        )
    };

    let proof = if wide_survivors.is_empty() {
        prove_from_pivot(ctx, reordered)?
    } else {
        let pivot_prop = ctx.lit_to_prop(wide_pivot);
        let survivors_prop = ctx.clause_to_prop(&wide_survivors);
        let pivot_id = fresh_fvar_id(ctx);
        let pivot_proof = ctx.kernel.fvar(pivot_id);
        let pivot_body = prove_from_pivot(ctx, pivot_proof)?;
        let pivot_body = ctx.kernel.abstract_fvars(pivot_body, &[pivot_id]);
        let anon = ctx.kernel.anon();
        let minor_pivot =
            ctx.kernel
                .lam(anon, pivot_prop, pivot_body, BinderInfo::Default);

        let survivors_id = fresh_fvar_id(ctx);
        let survivors_proof = ctx.kernel.fvar(survivors_id);
        let survivors_body = append_clause_suffix(
            ctx,
            &wide_survivors,
            survivors_proof,
            &resolvent,
            &target_suffixes,
        )?;
        let survivors_body = ctx
            .kernel
            .abstract_fvars(survivors_body, &[survivors_id]);
        let minor_survivors = ctx.kernel.lam(
            anon,
            survivors_prop,
            survivors_body,
            BinderInfo::Default,
        );

        let source_prop = ctx.mk_or(pivot_prop, survivors_prop);
        let motive = ctx
            .kernel
            .lam(anon, source_prop, target_prop, BinderInfo::Default);
        let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
        let rec = ctx.kernel.app(rec, pivot_prop);
        let rec = ctx.kernel.app(rec, survivors_prop);
        let rec = ctx.kernel.app(rec, motive);
        let rec = ctx.kernel.app(rec, minor_pivot);
        let rec = ctx.kernel.app(rec, minor_survivors);
        ctx.kernel.app(rec, reordered)
    };
    Ok(Some(Clause {
        lits: resolvent,
        proof,
    }))
}

fn move_clause_pivot_to_front(
    ctx: &mut ReconstructCtx,
    clause: &Clause,
    pivot_key: &str,
) -> Result<ExprId, ReconstructError> {
    move_clause_pivot_suffix_to_front(ctx, &clause.lits, clause.proof, pivot_key)
}

fn move_clause_pivot_suffix_to_front(
    ctx: &mut ReconstructCtx,
    literals: &[AletheLit],
    proof: ExprId,
    pivot_key: &str,
) -> Result<ExprId, ReconstructError> {
    let [head, rest @ ..] = literals else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "cannot reorder an empty clause".to_owned(),
        });
    };
    if head.atom.key() == pivot_key {
        return Ok(proof);
    }
    if rest.is_empty() || !rest.iter().any(|literal| literal.atom.key() == pivot_key) {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "wide clause lost its pivot during reordering".to_owned(),
        });
    }

    let pivot = rest
        .iter()
        .find(|literal| literal.atom.key() == pivot_key)
        .expect("pivot presence checked above");
    let rest_survivors = rest
        .iter()
        .filter(|literal| literal.atom.key() != pivot_key)
        .cloned()
        .collect::<Vec<_>>();
    let mut survivors = vec![head.clone()];
    survivors.extend(rest_survivors.iter().cloned());
    let pivot_prop = ctx.lit_to_prop(pivot);
    let survivors_prop = ctx.clause_to_prop(&survivors);
    let target_prop = ctx.mk_or(pivot_prop, survivors_prop);
    let head_prop = ctx.lit_to_prop(head);
    let rest_prop = ctx.clause_to_prop(rest);
    let anon = ctx.kernel.anon();

    let head_id = fresh_fvar_id(ctx);
    let head_proof = ctx.kernel.fvar(head_id);
    let survivor_head = if rest_survivors.is_empty() {
        head_proof
    } else {
        let rest_survivors_prop = ctx.clause_to_prop(&rest_survivors);
        or_inl(ctx, head_prop, rest_survivors_prop, head_proof)
    };
    let head_body = or_inr(ctx, pivot_prop, survivors_prop, survivor_head);
    let head_body = ctx.kernel.abstract_fvars(head_body, &[head_id]);
    let minor_head = ctx
        .kernel
        .lam(anon, head_prop, head_body, BinderInfo::Default);

    let rest_id = fresh_fvar_id(ctx);
    let rest_proof = ctx.kernel.fvar(rest_id);
    let reordered_rest = move_clause_pivot_suffix_to_front(ctx, rest, rest_proof, pivot_key)?;
    let rest_body = if rest_survivors.is_empty() {
        or_inl(ctx, pivot_prop, survivors_prop, reordered_rest)
    } else {
        insert_survivor_after_pivot(
            ctx,
            pivot_prop,
            head_prop,
            &rest_survivors,
            survivors_prop,
            reordered_rest,
        )?
    };
    let rest_body = ctx.kernel.abstract_fvars(rest_body, &[rest_id]);
    let minor_rest = ctx
        .kernel
        .lam(anon, rest_prop, rest_body, BinderInfo::Default);

    let source_prop = ctx.mk_or(head_prop, rest_prop);
    let motive = ctx
        .kernel
        .lam(anon, source_prop, target_prop, BinderInfo::Default);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let rec = ctx.kernel.app(rec, head_prop);
    let rec = ctx.kernel.app(rec, rest_prop);
    let rec = ctx.kernel.app(rec, motive);
    let rec = ctx.kernel.app(rec, minor_head);
    let rec = ctx.kernel.app(rec, minor_rest);
    Ok(ctx.kernel.app(rec, proof))
}

#[allow(clippy::unnecessary_wraps)]
fn insert_survivor_after_pivot(
    ctx: &mut ReconstructCtx,
    pivot_prop: ExprId,
    inserted_prop: ExprId,
    rest_survivors: &[AletheLit],
    target_survivors_prop: ExprId,
    proof: ExprId,
) -> Result<ExprId, ReconstructError> {
    let rest_prop = ctx.clause_to_prop(rest_survivors);
    let source_prop = ctx.mk_or(pivot_prop, rest_prop);
    let target_prop = ctx.mk_or(pivot_prop, target_survivors_prop);
    let anon = ctx.kernel.anon();

    let pivot_id = fresh_fvar_id(ctx);
    let pivot = ctx.kernel.fvar(pivot_id);
    let pivot_body = or_inl(ctx, pivot_prop, target_survivors_prop, pivot);
    let pivot_body = ctx.kernel.abstract_fvars(pivot_body, &[pivot_id]);
    let minor_pivot = ctx
        .kernel
        .lam(anon, pivot_prop, pivot_body, BinderInfo::Default);

    let rest_id = fresh_fvar_id(ctx);
    let rest = ctx.kernel.fvar(rest_id);
    let inserted_tail = or_inr(ctx, inserted_prop, rest_prop, rest);
    let rest_body = or_inr(ctx, pivot_prop, target_survivors_prop, inserted_tail);
    let rest_body = ctx.kernel.abstract_fvars(rest_body, &[rest_id]);
    let minor_rest = ctx
        .kernel
        .lam(anon, rest_prop, rest_body, BinderInfo::Default);

    let motive = ctx
        .kernel
        .lam(anon, source_prop, target_prop, BinderInfo::Default);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let rec = ctx.kernel.app(rec, pivot_prop);
    let rec = ctx.kernel.app(rec, rest_prop);
    let rec = ctx.kernel.app(rec, motive);
    let rec = ctx.kernel.app(rec, minor_pivot);
    let rec = ctx.kernel.app(rec, minor_rest);
    Ok(ctx.kernel.app(rec, proof))
}

fn append_clause_suffix(
    ctx: &mut ReconstructCtx,
    prefix: &[AletheLit],
    proof: ExprId,
    target: &[AletheLit],
    target_suffixes: &[ExprId],
) -> Result<ExprId, ReconstructError> {
    let [head, rest @ ..] = prefix else {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "cannot append to an empty clause prefix".to_owned(),
        });
    };
    if target.first().is_none_or(|literal| {
        literal.atom.key() != head.atom.key() || literal.negated != head.negated
    }) {
        return Err(ReconstructError::UnsupportedResolution {
            detail: "wide resolvent does not preserve its primary prefix".to_owned(),
        });
    }
    let head_prop = ctx.lit_to_prop(head);
    if rest.is_empty() {
        return if target.len() == 1 {
            Ok(proof)
        } else {
            Ok(or_inl(ctx, head_prop, target_suffixes[1], proof))
        };
    }
    let rest_prop = ctx.clause_to_prop(rest);
    let source_prop = ctx.mk_or(head_prop, rest_prop);
    let target_prop = target_suffixes[0];
    let anon = ctx.kernel.anon();

    let head_id = fresh_fvar_id(ctx);
    let head_proof = ctx.kernel.fvar(head_id);
    let head_body = or_inl(ctx, head_prop, target_suffixes[1], head_proof);
    let head_body = ctx.kernel.abstract_fvars(head_body, &[head_id]);
    let minor_head = ctx
        .kernel
        .lam(anon, head_prop, head_body, BinderInfo::Default);

    let rest_id = fresh_fvar_id(ctx);
    let rest_proof = ctx.kernel.fvar(rest_id);
    let rest_body = append_clause_suffix(
        ctx,
        rest,
        rest_proof,
        &target[1..],
        &target_suffixes[1..],
    )?;
    let rest_body = or_inr(ctx, head_prop, target_suffixes[1], rest_body);
    let rest_body = ctx.kernel.abstract_fvars(rest_body, &[rest_id]);
    let minor_rest = ctx
        .kernel
        .lam(anon, rest_prop, rest_body, BinderInfo::Default);

    let motive = ctx
        .kernel
        .lam(anon, source_prop, target_prop, BinderInfo::Default);
    let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
    let rec = ctx.kernel.app(rec, head_prop);
    let rec = ctx.kernel.app(rec, rest_prop);
    let rec = ctx.kernel.app(rec, motive);
    let rec = ctx.kernel.app(rec, minor_head);
    let rec = ctx.kernel.app(rec, minor_rest);
    Ok(ctx.kernel.app(rec, proof))
}

/// `False.rec`-eliminate a `False` proof into the target Prop `target`:
/// `False.rec.{0} (fun _ => target) h_false : target`.
pub(super) fn ex_falso(ctx: &mut ReconstructCtx, target: ExprId, h_false: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    // motive := fun (_ : False) => target.
    let motive = ctx
        .kernel
        .lam(anon, false_const, target, BinderInfo::Default);
    let z = ctx.kernel.level_zero();
    let rec = ctx.kernel.const_(ctx.prelude.false_rec, vec![z]);
    let e = ctx.kernel.app(rec, motive);
    ctx.kernel.app(e, h_false)
}

/// Inject a single literal proof `lit_proof : Enc(lit)` into the resolvent's `Or`
/// encoding `Enc(resolvent)`, by the `Or.inl`/`Or.inr` nesting that reaches
/// `lit`'s position. `lit` must occur in `resolvent` (matched by key+polarity);
/// otherwise this is a malformed reconstruction and a [`ReconstructError`] fires.
fn inject_lit(
    ctx: &mut ReconstructCtx,
    lit: &AletheLit,
    lit_proof: ExprId,
    resolvent: &[AletheLit],
) -> Result<ExprId, ReconstructError> {
    let suffixes = clause_suffix_props(ctx, resolvent);
    inject_lit_with_suffixes(ctx, lit, lit_proof, resolvent, &suffixes)
}

fn clause_suffix_props(ctx: &mut ReconstructCtx, clause: &[AletheLit]) -> Vec<ExprId> {
    let mut suffixes = Vec::with_capacity(clause.len());
    let Some(last) = clause.last() else {
        return suffixes;
    };
    let mut suffix = ctx.lit_to_prop(last);
    suffixes.push(suffix);
    for literal in clause[..clause.len() - 1].iter().rev() {
        let head = ctx.lit_to_prop(literal);
        suffix = ctx.mk_or(head, suffix);
        suffixes.push(suffix);
    }
    suffixes.reverse();
    suffixes
}

fn inject_lit_with_suffixes(
    ctx: &mut ReconstructCtx,
    lit: &AletheLit,
    lit_proof: ExprId,
    resolvent: &[AletheLit],
    suffixes: &[ExprId],
) -> Result<ExprId, ReconstructError> {
    let want = (lit.atom.key(), lit.negated);
    let idx = resolvent
        .iter()
        .position(|o| (o.atom.key(), o.negated) == want)
        .ok_or_else(|| ReconstructError::UnsupportedResolution {
            detail: format!("literal `{}` not found in resolvent", lit.atom.key()),
        })?;

    // The resolvent is right-nested: `l0 ∨ (l1 ∨ (… ∨ l_{n-1}))`. At index `idx`,
    // the sub-encoding `tail_i = Enc(resolvent[i..])` is reached by `idx` `Or.inr`s,
    // then (if `idx` is not the last literal) a final `Or.inl` carries `lit`.
    let n = resolvent.len();
    debug_assert!(n >= 1);
    debug_assert_eq!(suffixes.len(), n);

    // Build the proof bottom-up over the tail suffixes. We need, for each suffix
    // starting at `i`, the Props of `head_i = Enc(resolvent[i])` and
    // `tail_{i+1} = Enc(resolvent[i+1..])` to type the `Or.inl`/`Or.inr` ctors.
    let mut proof = lit_proof;
    // `i` walks from `idx` back to 0, wrapping the running proof.
    for i in (0..=idx).rev() {
        if i == idx {
            // Innermost: place `lit_proof` at position `idx`.
            if idx == n - 1 {
                // Last literal: the suffix `Enc(resolvent[idx..])` is just `Enc(lit)`.
                // proof already has that type; nothing to wrap.
            } else {
                // `Enc(resolvent[idx..]) = head_idx ∨ tail_{idx+1}`; use `Or.inl`.
                let a = ctx.lit_to_prop(&resolvent[idx]);
                let b = suffixes[idx + 1];
                proof = or_inl(ctx, a, b, proof);
            }
        } else {
            // Wrap: `Enc(resolvent[i..]) = head_i ∨ tail_{i+1}`; we have a proof of
            // `tail_{i+1}` (the running `proof`); use `Or.inr`.
            let a = ctx.lit_to_prop(&resolvent[i]);
            let b = suffixes[i + 1];
            proof = or_inr(ctx, a, b, proof);
        }
    }
    Ok(proof)
}

/// `Or.inl.{0} a b h : Or a b` from `h : a`.
pub(super) fn or_inl(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let inl = ctx.kernel.const_(ctx.prelude.or_inl, vec![]);
    let e = ctx.kernel.app(inl, a);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

/// `Or.inr.{0} a b h : Or a b` from `h : b`.
pub(super) fn or_inr(ctx: &mut ReconstructCtx, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let inr = ctx.kernel.const_(ctx.prelude.or_inr, vec![]);
    let e = ctx.kernel.app(inr, a);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

/// Eliminate a clause proof `clause.proof : Enc(clause)` into the target Prop
/// `target`, by running `per_lit` on each literal's hypothesis to produce a proof
/// of `target`, threaded through the right-nested `Or` via `Or.rec`.
///
/// For a unit clause this is `per_lit(l0, clause.proof)`. For `l0 ∨ rest`, it is
/// `Or.rec A B (fun _ => target) (fun (h0 : A) => per_lit(l0, h0))
///   (fun (hr : B) => <recurse on rest>) clause.proof`, where the minor premises
/// are built as closed lambdas (so the hypothesis flows in as `BVar 0`, then is
/// instantiated through `per_lit`/recursion as an `fvar`-free term).
///
/// `per_lit(ctx, lit, lit_proof, resolvent)` receives the literal, a proof term
/// of `Enc(lit)`, and the resolvent literal list (so it can inject), and returns a
/// proof of `target`.
fn clause_elim(
    ctx: &mut ReconstructCtx,
    clause: &Clause,
    target: ExprId,
    resolvent: &[AletheLit],
    per_lit: &PerLit<'_>,
) -> Result<ExprId, ReconstructError> {
    clause_elim_inner(ctx, &clause.lits, clause.proof, target, resolvent, per_lit)
}

/// The per-literal handler for [`clause_elim`]: given the literal, a proof of its
/// `Enc(lit)`, and the resolvent literal list, produce a proof of the target Prop.
type PerLit<'a> = dyn Fn(&mut ReconstructCtx, &AletheLit, ExprId, &[AletheLit]) -> Result<ExprId, ReconstructError>
    + 'a;

/// The recursive worker for [`clause_elim`] over a literal suffix with proof
/// `proof : Enc(lits)`.
fn clause_elim_inner(
    ctx: &mut ReconstructCtx,
    lits: &[AletheLit],
    proof: ExprId,
    target: ExprId,
    resolvent: &[AletheLit],
    per_lit: &PerLit<'_>,
) -> Result<ExprId, ReconstructError> {
    match lits {
        [] => Err(ReconstructError::UnsupportedResolution {
            detail: "empty clause has no literal to eliminate".to_owned(),
        }),
        // Unit suffix: `proof : Enc(l0)` directly.
        [l0] => per_lit(ctx, l0, proof, resolvent),
        // `l0 ∨ rest`: case-split with `Or.rec`.
        [l0, rest @ ..] => {
            let anon = ctx.kernel.anon();
            let a = ctx.lit_to_prop(l0); // Enc(l0)
            let b = ctx.clause_to_prop(rest); // Enc(rest)

            // minor_inl := fun (h0 : A) => per_lit(l0, h0).
            // Build the body with the hypothesis as a free variable so `per_lit`
            // produces a closed term, then abstract it back to a `BVar 0` lambda.
            let fvar_id = fresh_fvar_id(ctx);
            let h0 = ctx.kernel.fvar(fvar_id);
            let body_inl = per_lit(ctx, l0, h0, resolvent)?;
            let body_inl = ctx.kernel.abstract_fvars(body_inl, &[fvar_id]);
            let minor_inl = ctx.kernel.lam(anon, a, body_inl, BinderInfo::Default);

            // minor_inr := fun (hr : B) => <recurse on rest with hr>.
            let fvar_id2 = fresh_fvar_id(ctx);
            let hr = ctx.kernel.fvar(fvar_id2);
            let body_inr = clause_elim_inner(ctx, rest, hr, target, resolvent, per_lit)?;
            let body_inr = ctx.kernel.abstract_fvars(body_inr, &[fvar_id2]);
            let minor_inr = ctx.kernel.lam(anon, b, body_inr, BinderInfo::Default);

            // motive := fun (_ : Or A B) => target.
            let or_ab = ctx.mk_or(a, b);
            let motive = ctx.kernel.lam(anon, or_ab, target, BinderInfo::Default);

            // Or.rec A B motive minor_inl minor_inr proof : target.
            let rec = ctx.kernel.const_(ctx.prelude.or_rec, vec![]);
            let e = ctx.kernel.app(rec, a);
            let e = ctx.kernel.app(e, b);
            let e = ctx.kernel.app(e, motive);
            let e = ctx.kernel.app(e, minor_inl);
            let e = ctx.kernel.app(e, minor_inr);
            Ok(ctx.kernel.app(e, proof))
        }
    }
}

/// Mint a fresh free-variable id for building open `Or.rec` minor-premise bodies.
/// Reuses the deterministic `next_id` counter, offset into a private range so it
/// never collides with declaration-name numbering semantics.
pub(super) fn fresh_fvar_id(ctx: &mut ReconstructCtx) -> u64 {
    let id = ctx.next_id;
    ctx.next_id += 1;
    id
}

/// The soundness gate for the final propositional refutation term: `infer` it and
/// require the inferred type to be [`Kernel::def_eq`] to the prelude's `False`.
pub(super) fn check_false_prop(
    ctx: &mut ReconstructCtx,
    proof: ExprId,
) -> Result<ExprId, ReconstructError> {
    let false_ = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    check_against(ctx, "resolution", proof, false_)
}
