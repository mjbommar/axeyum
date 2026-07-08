//! A Constrained Horn Clause (`CHC`) front-end — the standard SMT-LIB input
//! format Z3's Spacer engine consumes — generalizing the single-predicate
//! [`TransitionSystem`](crate::TransitionSystem) to arbitrary Horn clauses, with
//! a *verify-guarded* solver that reduces the tractable case to the
//! model-checking engines already built ([`prove_safety_pdr_lra`],
//! [`prove_safety_imc_lra`], [`prove_safety_pdr`], [`prove_safety_imc`]).
//!
//! # Representation (no new IR — a predicate is a Bool-result uninterpreted function)
//!
//! A predicate `P` is a [`FuncId`] declared with result [`Sort::Bool`] (via
//! [`TermArena::declare_fun`](axeyum_ir::TermArena::declare_fun)); a predicate
//! application `P(args)` is an [`Op::Apply`] term over it (built with
//! [`TermArena::apply`](axeyum_ir::TermArena::apply)). A [`HornClause`] is a body
//! (a conjunction of predicate applications), a theory `constraint` (an arbitrary
//! Boolean formula over the clause variables), and a `head` that is either a
//! predicate application or `None` (the query head `false`):
//!
//! ```text
//!   (⋀ body_i) ∧ constraint  ⇒  head        (head = Some(P(t…)) | None = false)
//! ```
//!
//! # The fragment this slice solves (and what it declines)
//!
//! The supported systems are the **multi-predicate stratified** ones: any number
//! of predicates `P₁…Pₘ`. A clause is **linear** when its body holds at most one
//! predicate application and **nonlinear** (`k ≥ 2` atoms) otherwise. The
//! predicate dependency graph is **condensed into strongly-connected components
//! (`SCC`s)** and the `SCC`s are processed in topological order. A **trivial**
//! `SCC` (a single predicate that is either non-recursive or self-recursive) is
//! solved by the existing direct / self-recursive reduction. A **non-trivial**
//! `SCC` (`≥ 2` mutually-recursive predicates — *mutual recursion*) is handled by
//! the **merge-to-tagged-predicate** reduction described below. The acyclic
//! single-`SCC`-per-predicate case is the special case where every `SCC` is
//! trivial.
//!
//! ## Stratified nonlinear bodies — solved-predecessor folding
//!
//! A nonlinear clause `B₁(…) ∧ … ∧ B_k(…) ∧ φ ⇒ R(head)` (`k ≥ 2`) is handled
//! **when, within the contribution to solving `R`'s `SCC`, every body atom whose
//! predicate is NOT in `R`'s own `SCC` is already solved** (a strictly-lower
//! stratum). Each such solved atom `Bᵢ` is *folded into the constraint*: it is
//! replaced by its interpretation formula `I_{Bᵢ}(argsᵢ)`, giving an enriched
//! constraint `φ' = φ ∧ ⋀ I_{Bᵢ}(argsᵢ)`. After folding, the clause is classified
//! by how many body atoms remain in `R`'s own (recursive) `SCC`:
//!
//! * **0 remaining** — a pure fact / init / nonlinear query, a direct obligation;
//! * **1 remaining** — the existing **linear** shape (one recursive body atom plus
//!   the enriched constraint), routed to `solve_direct` / `solve_self_recursive` /
//!   the mutual-`SCC` merge unchanged;
//! * **`≥ 2` remaining** — genuine **nonlinear recursion** (a product / k-fold
//!   transition system); this slice **declines the whole system to
//!   [`HornOutcome::Unknown`]** rather than guess.
//!
//! A clause whose body exceeds [`MAX_BODY_ATOMS`] atoms, references an unsolved /
//! circular non-self predecessor, or whose folding hits an arity mismatch declines
//! cleanly. Folding several solved atoms reuses the same arg-binding substitution
//! the single-predecessor linear case already used. Genuine nonlinear recursion
//! and a non-sort-compatible mutually-recursive `SCC` remain out of fragment.
//!
//! ## Mutual recursion — the merge-to-tagged-predicate reduction
//!
//! A non-trivial `SCC` `{P₁…Pₖ}` is merged into **one self-recursive predicate
//! `P*`** over a *control-tagged* state `(tag, x₁…xₙ)`: a fresh `tag` selector
//! (a real or bit-vector constant column, chosen to match the engine family)
//! records which original member is active, and `(x₁…xₙ)` carries the members'
//! shared argument tuple. This slice handles the **sort-compatible** case — every
//! `SCC` member must declare the **same argument sort vector** `(τ₁…τₙ)`, so the
//! union state is just that shared vector plus the tag. Each intra-`SCC` clause
//! `Pⱼ(body) ∧ constraint ⇒ Pᵢ(head)` is rewritten over `P*` by pinning the
//! body's tag to `j` and the head's tag to `i`; inter-`SCC` clauses from an
//! already-solved predecessor fold in exactly as the self-recursive path already
//! does. `P*` is solved by the **existing self-recursive solver**
//! ([`solve_self_recursive`]); its invariant `I*(tag, x…)` is then **projected**
//! back to each member by restricting the tag to that member's constant,
//! `Iᵢ(x…) := I*(i, x…)`, populating the [`HornModel`] for every member. If the
//! members are **not** sort-compatible, the `SCC` exceeds the size/width caps, or
//! the underlying solver returns unknown/refuted, the whole query declines to
//! [`HornOutcome::Unknown`] — never a guess.
//!
//! For one predicate `P` the clauses are:
//!
//! * **Fact / init** — `constraint ⇒ P(t…)` (empty body).
//! * **Inductive** — `P(s…) ∧ constraint ⇒ P(s'…)` (one body atom).
//! * **Query** — `P(s…) ∧ constraint ⇒ false` (head `None`).
//!
//! With several predicates a clause `Q(t…) ∧ constraint ⇒ P(u…)` records the
//! dependency edge `P → Q` (`P` depends on `Q`). The predicates are solved in
//! **topological order** so every predicate is solved after its non-self
//! dependencies; a solved predecessor `Q` is folded into the later clauses by
//! substituting its interpretation `I_Q` for each `Q`-atom.
//!
//! Anything outside this fragment — genuine nonlinear recursion (`≥ 2` body atoms
//! remaining in the recursive `SCC` after folding), a non-sort-compatible
//! mutually-recursive `SCC`, or an unsupported argument shape — is **out of
//! fragment** and declines cleanly to [`HornOutcome::Unknown`]. The full
//! tagged-disjoint-union merge (members of *different* arities/sorts) and genuine
//! nonlinear recursion are the natural next slices; both would ride the same
//! verify-before-return discipline.
//!
//! # Reduction to a transition system (untrusted)
//!
//! The single predicate `P` over argument sorts `(τ₁…τₙ)` becomes a state of `n`
//! variables. A fresh state symbol `p@{step}_{i}` of sort `τᵢ` is declared per
//! step. The three transition-system components are disjunctions over the clause
//! classes; each clause contributes its `constraint` with the predicate-argument
//! **variables substituted to the matching state variables** — body arguments to
//! the pre-state `s`, head arguments to the post-state `s'`. Substitution (rather
//! than equality binding) is what keeps the reduced `init`/`trans`/`bad` — and
//! hence the engine's returned invariant — expressed purely over the state
//! vocabulary, never contaminated by a clause-local variable.
//!
//! For substitution to be sound and contamination-free this slice requires each
//! predicate application's arguments to be **distinct variable symbols** (the
//! dominant SMT-LIB CHC shape). A compound or constant argument such as `P(x+1)`,
//! a repeated argument, or a variable shared between a clause's body and head
//! arguments is **out of fragment** and declines — it is naturally re-modeled by
//! moving the term into the `constraint` (`P(x+1)` ↦ `P(x') ∧ x' = x + 1`).
//! Either way it does not matter if the reduction is wrong: the result is
//! re-validated clause-by-clause before any `Sat`.
//!
//! # The soundness contract (verify-before-return — non-negotiable)
//!
//! The classification, reduction, and argument binding are **entirely untrusted**.
//! Soundness rests on two trusted gates:
//!
//! * **`Sat`** — the candidate interpretation `P := I` (the invariant the engine
//!   returns, *itself* already verified as inductive by the engine's own 3-check
//!   gate) is re-validated against **every original Horn clause**: for each clause
//!   `(⋀ bodyᵢ) ∧ constraint ⇒ head`, the term
//!   `(⋀ bodyᵢ[P ↦ I]) ∧ constraint ∧ ¬(head[P ↦ I])` must be `unsat` under the
//!   trusted [`check_auto`](crate::check_auto) decider (`head = None` ⇒
//!   `¬false = true`, so the obligation is just `bodies ∧ constraint`). Only when
//!   **all** clauses pass is [`HornOutcome::Sat`] returned; any non-`unsat`,
//!   unknown, or error on any clause ⇒ [`HornOutcome::Unknown`].
//! * **`Unsat`** — the engine's `Reachable` is already a replay-checked
//!   counterexample (a genuine derivation of `false`); its depth is surfaced as
//!   [`HornOutcome::Unsat`].
//!
//! Every resource cap and unsupported construct degrades to
//! [`HornOutcome::Unknown`]; the solver never panics on adversarial or malformed
//! input.

use std::collections::BTreeMap;

use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::bmc::TransitionSystem;
use crate::imc::{ImcOutcome, prove_safety_imc};
use crate::imc_lra::{ImcLraOutcome, prove_safety_imc_lra};
use crate::pdr::{PdrOutcome, prove_safety_pdr};
use crate::pdr_lra::{PdrLraOutcome, prove_safety_pdr_lra};

/// A single Constrained Horn Clause: `(⋀ body) ∧ constraint ⇒ head`.
///
/// Each entry of `body` is a predicate application (an [`Op::Apply`] over a
/// Bool-result [`FuncId`]). `constraint` is an arbitrary theory Boolean formula
/// over the clause variables (it may be `true`). `head` is a predicate
/// application, or `None` for the query head `false`.
#[derive(Debug, Clone)]
pub struct HornClause {
    /// Predicate applications `P_i(args_i)` in the body (each an [`Op::Apply`]
    /// over a Bool-result [`FuncId`]). An empty body is a fact / init clause.
    pub body: Vec<TermId>,
    /// A theory Boolean formula over the clause variables (`LRA`/`LIA`/`BV`/`EUF`…);
    /// may be the constant `true`.
    pub constraint: TermId,
    /// The head predicate application, or `None` for the query head `false`.
    pub head: Option<TermId>,
}

/// A Constrained Horn Clause system: a set of predicate symbols and the clauses
/// constraining them.
#[derive(Debug, Clone)]
pub struct HornSystem {
    /// The uninterpreted (Bool-result) predicate symbols.
    pub predicates: Vec<FuncId>,
    /// The Horn clauses.
    pub clauses: Vec<HornClause>,
}

/// One predicate's interpretation in a [`HornModel`]: a parameter symbol vector
/// and the Boolean body term over those parameters.
#[derive(Debug, Clone)]
struct PredInterpretation {
    /// The interpretation's formal parameters (one per predicate argument).
    params: Vec<SymbolId>,
    /// The Boolean body `I(params)` defining the predicate.
    body: TermId,
}

/// A satisfying interpretation of a [`HornSystem`]: for each predicate `P`, a
/// parameter vector and a Boolean body term `I(params)` such that substituting
/// `P ↦ I` makes every clause valid. Returned only after the verify-before-return
/// clause re-check passes.
#[derive(Debug, Clone)]
pub struct HornModel {
    /// Per-predicate interpretations, keyed by predicate [`FuncId`] for
    /// deterministic lookup.
    interpretations: BTreeMap<FuncId, PredInterpretation>,
}

impl HornModel {
    /// The interpretation of `pred`: its parameter symbols and Boolean body term
    /// `I(params)`, or `None` if `pred` has no interpretation in this model.
    #[must_use]
    pub fn interpretation(&self, pred: FuncId) -> Option<(&[SymbolId], TermId)> {
        self.interpretations
            .get(&pred)
            .map(|interp| (interp.params.as_slice(), interp.body))
    }
}

/// The outcome of [`solve_horn`].
#[derive(Debug, Clone)]
pub enum HornOutcome {
    /// **Safe**: an interpretation of each predicate satisfying every clause,
    /// re-validated clause-by-clause by the trusted decider before return.
    Sat(HornModel),
    /// **Unsafe**: the query head `false` is derivable — a replay-checked
    /// counterexample of depth `steps` witnesses the derivation.
    Unsat {
        /// The number of transitions to the derivation of `false`.
        steps: usize,
    },
    /// Undecided: out of the supported fragment, a resource cap, an unsupported
    /// construct, or a candidate interpretation that failed its clause re-check.
    /// First-class and honest — never a (possibly wrong) `Sat`/`Unsat`.
    Unknown {
        /// A human-readable reason for declining.
        reason: String,
    },
}

/// Solves a Constrained Horn Clause `system`: is there an interpretation of the
/// predicates that satisfies every clause (`Sat`), or is the query head `false`
/// derivable (`Unsat`)?
///
/// This slice handles the **multi-predicate stratified** fragment (see the module
/// docs): any number of predicates, and bodies with several predicate atoms
/// (**nonlinear** clauses) as long as all but at most one body atom belong to
/// already-solved (strictly-lower-stratum) predicates. With one predicate it
/// reduces to a [`TransitionSystem`](crate::TransitionSystem) and dispatches to
/// the model-checking engines by the predicate's argument sorts — `Real` to the
/// `LRA` engines, `BitVec`/`Bool` to the bit-level engines. With several
/// predicates it condenses the dependency graph into strongly-connected
/// components and processes them in topological order: when solving a component,
/// every solved lower-stratum body atom is **folded into the clause constraint**
/// (its interpretation replaces the atom); a trivial component (one non-recursive
/// or self-recursive predicate) then solves the folded clauses, and a non-trivial
/// (mutually-recursive) **sort-compatible** component is merged into one
/// control-tagged self-recursive predicate, solved, and projected back per
/// member. **Genuine nonlinear recursion** (`≥ 2` body atoms remaining in the
/// component's own `SCC` after folding), a non-sort-compatible `SCC`, an
/// over-cap body, or an unsupported shape declines to [`HornOutcome::Unknown`].
///
/// Soundness is total and rests on the verify-before-return discipline: a `Sat`
/// is returned only after the candidate **whole-system** model re-validates
/// against every original clause under [`check_auto`](crate::check_auto), and an
/// `Unsat` carries the engine's replay-checked counterexample or a query-SAT
/// witness. The dependency analysis, topological order, substitution, and
/// per-predicate solving are all untrusted; a bug there can only ever cause an
/// over-eager `Unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] only for a genuine internal failure while building the
/// system's terms; an undecided query, an unsupported construct, or a failed
/// clause re-check is reported as [`HornOutcome::Unknown`], never an error.
pub fn solve_horn(
    arena: &mut TermArena,
    system: &HornSystem,
    config: &SolverConfig,
) -> Result<HornOutcome, SolverError> {
    // Multi-predicate systems take the acyclic topological-order path; a single
    // predicate is the m = 1 special case handled by the original reduction.
    if system.predicates.len() != 1 {
        return solve_horn_multi(arena, system, config);
    }

    // 1. Classify. Outside the single-predicate-linear fragment ⇒ decline.
    let classified = match classify(arena, system) {
        Ok(classified) => classified,
        Err(reason) => return Ok(unknown(&reason)),
    };

    // 2. Reduce to a transition system over the single predicate's argument sorts.
    let reduced = ReducedSystem::new(system, &classified);

    // 3. Dispatch to the engine by the state sort; collect the verified-inductive
    //    invariant (Safe) or the replay-checked depth (Unsat), or decline. The
    //    returned `state_params` are the exact step-0 symbols the engine proved
    //    the invariant over — the interpretation's parameters.
    let (dispatched, state_params) = dispatch(arena, &reduced, config)?;
    let invariant = match dispatched {
        Dispatch::Safe { invariant } => invariant,
        Dispatch::Unsat { steps } => return Ok(HornOutcome::Unsat { steps }),
        Dispatch::Unknown(reason) => return Ok(unknown(&reason)),
    };

    // 4. VERIFY-BEFORE-RETURN: the candidate P := I must make every clause valid.
    let interp = PredInterpretation {
        params: state_params,
        body: invariant,
    };
    if verify_horn_solution(arena, system, classified.predicate, &interp, config)? {
        let mut interpretations = BTreeMap::new();
        interpretations.insert(classified.predicate, interp);
        Ok(HornOutcome::Sat(HornModel { interpretations }))
    } else {
        Ok(unknown(
            "Horn candidate interpretation failed the per-clause re-check; declining",
        ))
    }
}

/// The result of classifying a [`HornSystem`] into the single-predicate-linear
/// fragment: the one predicate, its argument sorts, and the clauses partitioned
/// by class. Each predicate application's argument **variable symbols** are
/// retained for the substitution reduction (a non-variable argument declines —
/// see [`predicate_app_arg_vars`]).
struct Classified {
    /// The single predicate symbol `P`.
    predicate: FuncId,
    /// `P`'s argument sorts `(τ₁…τₙ)`.
    arg_sorts: Vec<Sort>,
    /// Fact / init clauses: `(constraint, head argument variables)`.
    facts: Vec<FactClause>,
    /// Inductive clauses: `(constraint, body argument variables, head argument
    /// variables)`.
    inductives: Vec<InductiveClause>,
    /// Query clauses: `(constraint, body argument variables)`.
    queries: Vec<QueryClause>,
}

/// A fact / init clause `constraint ⇒ P(head_vars)` (empty body).
struct FactClause {
    constraint: TermId,
    head_vars: Vec<SymbolId>,
}

/// An inductive clause `P(body_vars) ∧ constraint ⇒ P(head_vars)`.
struct InductiveClause {
    constraint: TermId,
    body_vars: Vec<SymbolId>,
    head_vars: Vec<SymbolId>,
}

/// A query clause `P(body_vars) ∧ constraint ⇒ false`.
struct QueryClause {
    constraint: TermId,
    body_vars: Vec<SymbolId>,
}

/// Classifies `system` into the single-predicate-linear fragment, or returns a
/// human-readable decline reason. Never panics on malformed input.
fn classify(arena: &TermArena, system: &HornSystem) -> Result<Classified, String> {
    if system.predicates.len() != 1 {
        return Err(format!(
            "out of fragment: expected exactly one predicate, found {} (multi-predicate CHC is a \
             later slice)",
            system.predicates.len()
        ));
    }
    let predicate = system.predicates[0];
    let (_, params, result) = arena.function(predicate);
    if result != Sort::Bool {
        return Err("out of fragment: the predicate must have a Bool result sort".to_owned());
    }
    let arg_sorts: Vec<Sort> = params.to_vec();

    let mut facts = Vec::new();
    let mut inductives = Vec::new();
    let mut queries = Vec::new();

    for clause in &system.clauses {
        // Every body atom must be an application of the single predicate.
        if clause.body.len() > 1 {
            return Err(format!(
                "out of fragment: a clause body has {} predicate atoms; this slice handles linear \
                 Horn (at most one body atom)",
                clause.body.len()
            ));
        }
        let body_vars = match clause.body.first() {
            None => None,
            Some(&atom) => Some(predicate_app_arg_vars(arena, atom, predicate, &arg_sorts)?),
        };
        let head_vars = match clause.head {
            None => None,
            Some(head) => Some(predicate_app_arg_vars(arena, head, predicate, &arg_sorts)?),
        };

        match (body_vars, head_vars) {
            // constraint ⇒ P(head): a fact / init clause.
            (None, Some(head_vars)) => facts.push(FactClause {
                constraint: clause.constraint,
                head_vars,
            }),
            // P(body) ∧ constraint ⇒ P(head): an inductive clause. A variable
            // shared between the body and head argument lists cannot be bound to
            // both a pre- and a post-state position; decline.
            (Some(body_vars), Some(head_vars)) => {
                if body_vars.iter().any(|v| head_vars.contains(v)) {
                    return Err(
                        "out of fragment: an inductive clause shares a variable between its body \
                         and head predicate arguments (ambiguous pre/post binding)"
                            .to_owned(),
                    );
                }
                inductives.push(InductiveClause {
                    constraint: clause.constraint,
                    body_vars,
                    head_vars,
                });
            }
            // P(body) ∧ constraint ⇒ false: a query clause.
            (Some(body_vars), None) => queries.push(QueryClause {
                constraint: clause.constraint,
                body_vars,
            }),
            // constraint ⇒ false: no predicate at all. This is a pure theory
            // obligation with no recursion; out of the reachability fragment.
            (None, None) => {
                return Err(
                    "out of fragment: a clause has neither a body atom nor a head predicate \
                     (a predicate-free theory obligation)"
                        .to_owned(),
                );
            }
        }
    }

    Ok(Classified {
        predicate,
        arg_sorts,
        facts,
        inductives,
        queries,
    })
}

/// Extracts the argument **variable symbols** of a predicate application
/// `P(v₀…vₙ)`, requiring it to be an [`Op::Apply`] over exactly `predicate` whose
/// arguments are **distinct variable symbols** of the declared argument sorts.
///
/// This is the slice boundary for the reduction: a predicate argument that is a
/// compound term (e.g. `x+1`), a constant, a repeated variable, or a sort
/// mismatch declines cleanly. Distinct variables let the reduction *substitute*
/// each argument variable to its state variable (rather than add an equality
/// constraint), so the resulting `init`/`trans`/`bad` — and hence the engine's
/// returned invariant — are expressed purely over the state vocabulary, never
/// contaminated by the clause-local variables. A non-variable head argument such
/// as `P(x+1)` is naturally re-modeled by the caller as `P(x') ∧ x' = x + 1`
/// (move the term into the `constraint`); supporting it directly is a later slice.
fn predicate_app_arg_vars(
    arena: &TermArena,
    term: TermId,
    predicate: FuncId,
    arg_sorts: &[Sort],
) -> Result<Vec<SymbolId>, String> {
    let args = match arena.node(term) {
        TermNode::App {
            op: Op::Apply(func),
            args,
        } if *func == predicate => args.clone(),
        TermNode::App {
            op: Op::Apply(_), ..
        } => {
            return Err(
                "out of fragment: a clause references a predicate other than the single declared \
                 one (multi-predicate CHC is a later slice)"
                    .to_owned(),
            );
        }
        _ => {
            return Err(
                "malformed: a body/head entry is not a predicate application (Op::Apply over a \
                 Bool-result function)"
                    .to_owned(),
            );
        }
    };

    let mut vars = Vec::with_capacity(args.len());
    for (i, &arg) in args.iter().enumerate() {
        match arena.node(arg) {
            TermNode::Symbol(sym) => {
                let sort = arena.sort_of(arg);
                if arg_sorts.get(i) != Some(&sort) {
                    return Err(
                        "malformed: a predicate argument's sort does not match the declared \
                         signature"
                            .to_owned(),
                    );
                }
                if vars.contains(sym) {
                    return Err(
                        "out of fragment: a predicate application repeats a variable argument \
                         (distinct-variable arguments are required by this slice's substitution \
                         reduction; an implicit equality is a later slice)"
                            .to_owned(),
                    );
                }
                vars.push(*sym);
            }
            _ => {
                return Err(
                    "out of fragment: a predicate argument is not a plain variable symbol (a \
                     compound or constant argument such as P(x+1) must be re-modeled as \
                     P(x') ∧ x' = x + 1; direct support is a later slice)"
                        .to_owned(),
                );
            }
        }
    }
    Ok(vars)
}

/// The reduced single-predicate system, exposed to the engines as a
/// [`TransitionSystem`](crate::TransitionSystem). Holds the classification by
/// reference (the clause data).
struct ReducedSystem<'a> {
    classified: &'a Classified,
}

impl<'a> ReducedSystem<'a> {
    fn new(_system: &HornSystem, classified: &'a Classified) -> Self {
        ReducedSystem { classified }
    }
}

impl ReducedSystem<'_> {
    /// Declares the `n` fresh state symbols `p@{step}_{i}` of the predicate's
    /// argument sorts.
    fn declare_state(
        &self,
        arena: &mut TermArena,
        step: usize,
    ) -> Result<Vec<SymbolId>, SolverError> {
        let mut vars = Vec::with_capacity(self.classified.arg_sorts.len());
        for (i, &sort) in self.classified.arg_sorts.iter().enumerate() {
            vars.push(arena.declare_internal(&format!("p@{step}_{i}"), sort)?);
        }
        Ok(vars)
    }

    /// Rewrites `constraint` by substituting each predicate argument variable to
    /// its state variable: `body_varsᵢ ↦ preᵢ` and (optionally) `head_varsᵢ ↦
    /// postᵢ`. This is the contamination-free reduction — the result mentions only
    /// the state vocabulary and any genuinely clause-local (existential) variables,
    /// never a variable that doubles as a state position elsewhere.
    ///
    /// Returns `None` if a variable appears in **both** the body and head argument
    /// lists (an ambiguous pre/post binding the slice declines), so the caller
    /// degrades to `Unknown` rather than mis-bind.
    fn bind(
        arena: &mut TermArena,
        constraint: TermId,
        body_vars: &[SymbolId],
        pre: &[SymbolId],
        head_vars: &[SymbolId],
        post: &[SymbolId],
    ) -> Option<TermId> {
        let mut mapping: Vec<(SymbolId, SymbolId)> = Vec::new();
        for (&from, &to) in body_vars.iter().zip(pre.iter()) {
            mapping.push((from, to));
        }
        for (&from, &to) in head_vars.iter().zip(post.iter()) {
            // A body/head argument-variable collision cannot be soundly bound to
            // both a pre- and a post-state variable. Decline.
            if mapping.iter().any(|&(src, _)| src == from) {
                return None;
            }
            mapping.push((from, to));
        }
        mapping.sort_by_key(|&(src, _)| src);
        Some(substitute_symbols(arena, constraint, &mapping))
    }
}

impl TransitionSystem for ReducedSystem<'_> {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        self.declare_state(arena, step)
    }

    /// `init(s0)` = ⋁ over fact clauses of `constraint[head_vars ↦ s0]`.
    /// No facts ⇒ `false` (the predicate is empty initially). A clause that cannot
    /// be bound (a body/head variable collision) maps to an `Unsupported` error so
    /// the caller degrades to `Unknown`.
    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for fact in &self.classified.facts {
            let Some(bound) =
                ReducedSystem::bind(arena, fact.constraint, &[], &[], &fact.head_vars, s0)
            else {
                return Err(SolverError::Unsupported(
                    "Horn fact clause has an unbindable argument shape".to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }

    /// `trans(s,s')` = ⋁ over inductive clauses of
    /// `constraint[body_vars ↦ s, head_vars ↦ s']`.
    /// No inductive clauses ⇒ `false` (no transitions; only init states reachable).
    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for ind in &self.classified.inductives {
            let Some(bound) = ReducedSystem::bind(
                arena,
                ind.constraint,
                &ind.body_vars,
                pre,
                &ind.head_vars,
                post,
            ) else {
                return Err(SolverError::Unsupported(
                    "Horn inductive clause shares a variable between its body and head arguments \
                     (ambiguous pre/post binding)"
                        .to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }

    /// `bad(s)` = ⋁ over query clauses of `constraint[body_vars ↦ s]`.
    /// No queries ⇒ `false` (nothing to violate; trivially safe).
    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for query in &self.classified.queries {
            let Some(bound) =
                ReducedSystem::bind(arena, query.constraint, &query.body_vars, s, &[], &[])
            else {
                return Err(SolverError::Unsupported(
                    "Horn query clause has an unbindable argument shape".to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }
}

/// The verified-inductive engine result for the reduced system.
enum Dispatch {
    /// A verified-inductive invariant `I(state_params)` proving safety.
    Safe { invariant: TermId },
    /// A replay-checked counterexample of depth `steps` (query reachable).
    Unsat { steps: usize },
    /// Declined (out of an engine's reach, a cap, or an unsupported sort).
    Unknown(String),
}

/// Dispatches the reduced system to the model-checking engine matching the
/// predicate's argument sorts, returning the engine result together with the
/// step-0 state symbols (the interpretation parameters the invariant is over).
///
/// * `Real` state ⇒ try [`prove_safety_pdr_lra`], then [`prove_safety_imc_lra`].
/// * `BitVec`/`Bool` state ⇒ try [`prove_safety_pdr`], then [`prove_safety_imc`].
/// * `Int` (and any other sort) ⇒ decline (an `Int` real-relaxation cannot be
///   verified over ℤ in this slice).
fn dispatch(
    arena: &mut TermArena,
    reduced: &ReducedSystem,
    config: &SolverConfig,
) -> Result<(Dispatch, Vec<SymbolId>), SolverError> {
    // Pin the step-0 state symbols as the interpretation parameters. The engines
    // declare these same symbols internally; re-declaring is idempotent (the IR
    // returns the existing symbol on a name+sort match).
    let state_params = reduced.declare_state(arena, 0)?;

    // A wrapper that carries the pinned params so the engine proves the invariant
    // over exactly the vocabulary verification re-checks against.
    let pinned = PinnedReduced {
        inner: reduced,
        state_params: state_params.clone(),
    };

    let dispatch = match state_class(&reduced.classified.arg_sorts) {
        StateClass::Real => match prove_safety_pdr_lra(arena, &pinned, config)? {
            PdrLraOutcome::Safe { invariant } => Dispatch::Safe { invariant },
            PdrLraOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
            // Fall back to interpolation-based model checking.
            PdrLraOutcome::Unknown { .. } => match prove_safety_imc_lra(arena, &pinned, config)? {
                ImcLraOutcome::Safe { invariant } => Dispatch::Safe { invariant },
                ImcLraOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
                ImcLraOutcome::Unknown { reason } => Dispatch::Unknown(reason),
            },
        },
        StateClass::Finite => match prove_safety_pdr(arena, &pinned, config)? {
            PdrOutcome::Safe { invariant } => Dispatch::Safe { invariant },
            PdrOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
            PdrOutcome::Unknown { .. } => match prove_safety_imc(arena, &pinned, config)? {
                ImcOutcome::Safe { invariant } => Dispatch::Safe { invariant },
                ImcOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
                ImcOutcome::Unknown { reason } => Dispatch::Unknown(reason),
            },
        },
        StateClass::Unsupported => Dispatch::Unknown(
            "Horn predicate argument sorts are outside this slice's reach (only Real, BitVec, and \
             Bool are dispatched; Int/Array/etc. decline)"
                .to_owned(),
        ),
    };

    Ok((dispatch, state_params))
}

/// A [`TransitionSystem`] wrapper that pins the step-0 state symbols, so the
/// engine proves the invariant over exactly the vocabulary the verification stage
/// re-checks against. Steps `> 0` declare fresh symbols as usual.
struct PinnedReduced<'a> {
    inner: &'a ReducedSystem<'a>,
    state_params: Vec<SymbolId>,
}

impl TransitionSystem for PinnedReduced<'_> {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        if step == 0 {
            return Ok(self.state_params.clone());
        }
        self.inner.declare_state(arena, step)
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        self.inner.init(arena, s0)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        self.inner.trans(arena, pre, post)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        self.inner.bad(arena, s)
    }
}

/// The engine family a state vocabulary dispatches to.
enum StateClass {
    /// All-`Real` state ⇒ the `LRA` engines.
    Real,
    /// All-`BitVec`/`Bool` state ⇒ the bit-level engines.
    Finite,
    /// A mixed or unsupported sort (e.g. `Int`, `Array`) ⇒ decline.
    Unsupported,
}

/// Classifies the argument sorts into an engine family. An empty argument list (a
/// nullary predicate) is `Finite` (a single Boolean reachability bit).
fn state_class(sorts: &[Sort]) -> StateClass {
    if sorts.iter().all(|s| *s == Sort::Real) {
        // All Real (or empty — but empty is caught by the Finite branch first).
        if sorts.is_empty() {
            return StateClass::Finite;
        }
        return StateClass::Real;
    }
    if sorts
        .iter()
        .all(|s| matches!(s, Sort::Bool | Sort::BitVec(_)))
    {
        return StateClass::Finite;
    }
    StateClass::Unsupported
}

/// **The verify-before-return clause-validity check.** Re-validates the candidate
/// interpretation `P := interp` against **every** original Horn clause. For each
/// clause `(⋀ bodyᵢ) ∧ constraint ⇒ head`, builds
/// `(⋀ bodyᵢ[P ↦ I]) ∧ constraint ∧ ¬(head[P ↦ I])` and requires it `unsat`
/// (`head = None` ⇒ `¬false = true`, so the obligation is `bodies ∧ constraint`).
/// Returns `true` only when **all** clauses are `unsat` under the trusted
/// [`check_auto`](crate::check_auto); any non-`unsat`, unknown, unsupported, or
/// error on any clause ⇒ `false` (a sound decline).
fn verify_horn_solution(
    arena: &mut TermArena,
    system: &HornSystem,
    predicate: FuncId,
    interp: &PredInterpretation,
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    for clause in &system.clauses {
        let mut assertions: Vec<TermId> = Vec::new();

        // Body atoms with P ↦ I.
        for &atom in &clause.body {
            let Some(args) = app_args_of(arena, atom, predicate) else {
                // A body atom that is not an application of P cannot be soundly
                // re-checked here; decline conservatively.
                return Ok(false);
            };
            let Some(inst) = instantiate(arena, interp, &args) else {
                return Ok(false);
            };
            assertions.push(inst);
        }

        // The theory constraint.
        assertions.push(clause.constraint);

        // ¬(head with P ↦ I); head None ⇒ ¬false = true (a no-op, omitted).
        if let Some(head) = clause.head {
            let Some(args) = app_args_of(arena, head, predicate) else {
                return Ok(false);
            };
            let Some(inst) = instantiate(arena, interp, &args) else {
                return Ok(false);
            };
            let neg = arena.not(inst)?;
            assertions.push(neg);
        }

        // The clause is valid iff this obligation is UNSAT under the trusted decider.
        match check_auto(arena, &assertions, config) {
            Ok(CheckResult::Unsat) => {}
            Ok(_) | Err(SolverError::Unsupported(_)) => return Ok(false),
            Err(other) => return Err(other),
        }
    }
    Ok(true)
}

/// The argument terms of `term` if it is an application of `predicate`, else
/// `None`.
fn app_args_of(arena: &TermArena, term: TermId, predicate: FuncId) -> Option<Vec<TermId>> {
    match arena.node(term) {
        TermNode::App {
            op: Op::Apply(func),
            args,
        } if *func == predicate => Some(args.to_vec()),
        _ => None,
    }
}

/// Instantiates `interp.body` with each formal parameter `interp.params[i]`
/// replaced by the application argument `args[i]` — the meaning of `P(args)`
/// under `P := I`. Returns `None` on an arity mismatch.
fn instantiate(
    arena: &mut TermArena,
    interp: &PredInterpretation,
    args: &[TermId],
) -> Option<TermId> {
    if interp.params.len() != args.len() {
        return None;
    }
    let mut mapping: Vec<(SymbolId, TermId)> = interp
        .params
        .iter()
        .copied()
        .zip(args.iter().copied())
        .collect();
    mapping.sort_by_key(|&(sym, _)| sym);
    Some(substitute(arena, interp.body, &mapping))
}

/// Structurally rebuilds `term`, replacing each parameter symbol leaf per
/// `mapping` (sorted by source symbol) with its argument term. Symbols absent
/// from `mapping` are left untouched.
fn substitute(arena: &mut TermArena, term: TermId, mapping: &[(SymbolId, TermId)]) -> TermId {
    match arena.node(term).clone() {
        TermNode::Symbol(sym) => match mapping.binary_search_by_key(&sym, |&(src, _)| src) {
            Ok(i) => mapping[i].1,
            Err(_) => term,
        },
        TermNode::App { args, .. } => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(substitute(arena, arg, mapping));
            }
            arena.rebuild_with_args(term, &new_args)
        }
        _ => term,
    }
}

/// Structurally rebuilds `term`, replacing each symbol leaf per `mapping` (sorted
/// by source symbol) with its target **symbol's** variable term. Symbols absent
/// from `mapping` are left untouched. The symbol-to-symbol reduction binding used
/// by [`ReducedSystem::bind`].
fn substitute_symbols(
    arena: &mut TermArena,
    term: TermId,
    mapping: &[(SymbolId, SymbolId)],
) -> TermId {
    match arena.node(term).clone() {
        TermNode::Symbol(sym) => match mapping.binary_search_by_key(&sym, |&(src, _)| src) {
            Ok(i) => arena.var(mapping[i].1),
            Err(_) => term,
        },
        TermNode::App { args, .. } => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(substitute_symbols(arena, arg, mapping));
            }
            arena.rebuild_with_args(term, &new_args)
        }
        _ => term,
    }
}

fn unknown(reason: &str) -> HornOutcome {
    HornOutcome::Unknown {
        reason: reason.to_owned(),
    }
}

// ===========================================================================
// Acyclic multi-predicate linear CHC
// ===========================================================================

/// A clause's predicate shape: every body predicate application (a clause is
/// **linear** with `≤ 1` and **nonlinear** with `≥ 2`) and the (optional) head
/// predicate (`None` ⇒ a query head `false`).
struct ClauseShape {
    /// Every body predicate application `(predicate, args)`, in clause order. An
    /// empty vector is a fact / init clause; one entry is linear; two or more is
    /// a nonlinear clause (handled by solved-predecessor folding).
    bodies: Vec<(FuncId, Vec<TermId>)>,
    /// The head predicate application, if any: `(predicate, args)`; `None` is a
    /// query head.
    head: Option<(FuncId, Vec<TermId>)>,
}

/// Solves a **multi-predicate linear** [`HornSystem`]: builds the predicate
/// dependency graph, condenses it into strongly-connected components, processes
/// the `SCC`s in topological order (a trivial `SCC` via the direct/self-recursive
/// path; a non-trivial mutually-recursive sort-compatible `SCC` via the
/// merge-to-tagged-predicate reduction), then re-validates the whole model
/// against every clause before returning `Sat`. Declines a nonlinear (`≥ 2`-atom)
/// body or a non-sort-compatible `SCC`.
fn solve_horn_multi(
    arena: &mut TermArena,
    system: &HornSystem,
    config: &SolverConfig,
) -> Result<HornOutcome, SolverError> {
    if system.predicates.is_empty() {
        return Ok(unknown(
            "out of fragment: a Horn system needs at least one predicate",
        ));
    }

    // Every predicate must be a Bool-result function.
    for &pred in &system.predicates {
        let (_, _, result) = arena.function(pred);
        if result != Sort::Bool {
            return Ok(unknown(
                "out of fragment: every Horn predicate must have a Bool result sort",
            ));
        }
    }

    // Per-clause body/head predicate shapes; declines a nonlinear body.
    let shapes = match clause_shapes(arena, system) {
        Ok(shapes) => shapes,
        Err(reason) => return Ok(unknown(&reason)),
    };

    // Condense the dependency graph into strongly-connected components, listed in
    // topological order (dependencies first). Mutual recursion ⇒ a non-trivial
    // SCC handled by the merge reduction rather than declined.
    let sccs = scc_condensation(&system.predicates, &shapes);

    // Solve each SCC in topological order, accumulating a partial model.
    let mut model = BTreeMap::new();
    for scc in &sccs {
        // A trivial SCC (a single predicate, recursive or not) takes the existing
        // direct / self-loop path; a non-trivial SCC (≥ 2 mutually-recursive
        // predicates) takes the merge-to-tagged-predicate reduction.
        let solved = if scc.len() == 1 {
            // solve_one_predicate dispatches the direct vs self-recursive path.
            solve_one_predicate(arena, system, &shapes, scc[0], &model, config)?
        } else {
            // Returns one interpretation per member, or declines.
            match solve_mutual_scc(arena, system, &shapes, scc, &model, config)? {
                SolveScc::Interps(interps) => {
                    for (pred, interp) in interps {
                        model.insert(pred, interp);
                    }
                    continue;
                }
                SolveScc::Unsat { steps } => return Ok(HornOutcome::Unsat { steps }),
                SolveScc::Decline(reason) => return Ok(unknown(&reason)),
            }
        };
        match solved {
            SolveOne::Interp(interp) => {
                model.insert(scc[0], interp);
            }
            SolveOne::Unsat { steps } => {
                // A self-recursive predicate's own reachability already derives
                // false (it has a reachable query). The whole system is Unsat.
                return Ok(HornOutcome::Unsat { steps });
            }
            SolveOne::Decline(reason) => return Ok(unknown(&reason)),
        }
    }

    // Query clauses: under the solved model, every query body must be
    // unsatisfiable. A satisfiable query body is a reachable derivation of false.
    match check_queries(arena, system, &shapes, &model, config)? {
        QueryCheck::Reachable { steps } => return Ok(HornOutcome::Unsat { steps }),
        QueryCheck::Unreachable => {}
        QueryCheck::Decline => {
            return Ok(unknown(
                "a Horn query body could not be discharged under the candidate model; declining",
            ));
        }
    }

    // VERIFY-BEFORE-RETURN: the full multi-predicate model must make EVERY clause
    // valid. This is the only trusted gate; all of the above is untrusted.
    if verify_horn_model(arena, system, &model, config)? {
        Ok(HornOutcome::Sat(HornModel {
            interpretations: model,
        }))
    } else {
        Ok(unknown(
            "Horn candidate model failed the whole-system per-clause re-check; declining",
        ))
    }
}

/// Determines the body/head predicate shape of every clause. A nonlinear (`≥ 2`
/// predicate atoms in the body) clause is **retained** for solved-predecessor
/// folding; only a malformed atom or an over-[`MAX_BODY_ATOMS`] body declines.
fn clause_shapes(arena: &TermArena, system: &HornSystem) -> Result<Vec<ClauseShape>, String> {
    let known: std::collections::BTreeSet<FuncId> = system.predicates.iter().copied().collect();
    let mut shapes = Vec::with_capacity(system.clauses.len());
    for clause in &system.clauses {
        if clause.body.len() > MAX_BODY_ATOMS {
            return Err(format!(
                "out of cap: a clause body has {} predicate atoms (cap {MAX_BODY_ATOMS}); declining",
                clause.body.len()
            ));
        }
        let mut bodies = Vec::with_capacity(clause.body.len());
        for &atom in &clause.body {
            bodies.push(predicate_app(arena, atom, &known)?);
        }
        let head = match clause.head {
            None => None,
            Some(head) => Some(predicate_app(arena, head, &known)?),
        };
        if bodies.is_empty() && head.is_none() {
            return Err(
                "out of fragment: a clause has neither a body atom nor a head predicate (a \
                 predicate-free theory obligation)"
                    .to_owned(),
            );
        }
        shapes.push(ClauseShape { bodies, head });
    }
    Ok(shapes)
}

/// The maximum number of predicate atoms in a clause body this slice will fold.
/// A wider body declines to [`HornOutcome::Unknown`] rather than risk a blow-up.
const MAX_BODY_ATOMS: usize = 8;

/// Extracts `(predicate, args)` from a predicate application `P(args)`, requiring
/// `P` to be one of the system's declared predicates. Arguments may be arbitrary
/// terms here (the distinct-variable restriction is imposed only where the
/// transition-system reduction needs it).
fn predicate_app(
    arena: &TermArena,
    term: TermId,
    known: &std::collections::BTreeSet<FuncId>,
) -> Result<(FuncId, Vec<TermId>), String> {
    match arena.node(term) {
        TermNode::App {
            op: Op::Apply(func),
            args,
        } if known.contains(func) => Ok((*func, args.to_vec())),
        _ => Err(
            "malformed: a body/head entry is not an application of a declared predicate (Op::Apply \
             over a Bool-result predicate function)"
                .to_owned(),
        ),
    }
}

/// The result of folding a clause's body atoms while solving an `SCC`: the body
/// atoms that remain in the recursive `SCC` (`≤ 1` for a routable clause) and the
/// constraint with every solved lower-stratum atom folded in.
struct FoldedBody {
    /// The body predicate atoms still in the `SCC` being solved (recursive). A
    /// linear-shaped clause has at most one; `≥ 2` is genuine nonlinear recursion
    /// and the caller declines.
    recursive: Vec<(FuncId, Vec<TermId>)>,
    /// The clause constraint conjoined with each solved lower-stratum atom's
    /// interpretation `I_{Bᵢ}(argsᵢ)`.
    constraint: TermId,
}

/// Folds a clause's body atoms relative to the `SCC` currently being solved.
/// Partitions the body into atoms whose predicate is in `scc_set` (recursive —
/// kept) and atoms whose predicate is already in `model` (solved lower stratum —
/// replaced by their interpretation and conjoined into the constraint).
///
/// Returns `Ok(folded)` with the recursive remainder and enriched constraint, or
/// `Err(reason)` (a sound decline) if a non-recursive body atom is **not** solved
/// (an unsolved/circular non-self predecessor — impossible under a correct
/// topological order, but checked conservatively) or its interpretation has an
/// arity mismatch. The outer `Result` carries a genuine arena error.
///
/// The caller decides what `recursive.len()` means: `0` is a fact/init/query
/// obligation, `1` routes to the existing linear machinery, and `≥ 2` is genuine
/// nonlinear recursion that declines.
fn fold_solved_bodies(
    arena: &mut TermArena,
    bodies: &[(FuncId, Vec<TermId>)],
    constraint: TermId,
    scc_set: &std::collections::BTreeSet<FuncId>,
    model: &BTreeMap<FuncId, PredInterpretation>,
) -> Result<Result<FoldedBody, String>, SolverError> {
    let mut recursive: Vec<(FuncId, Vec<TermId>)> = Vec::new();
    let mut acc = constraint;
    for (pred, args) in bodies {
        if scc_set.contains(pred) {
            recursive.push((*pred, args.clone()));
            continue;
        }
        let Some(interp) = model.get(pred) else {
            return Ok(Err(
                "out of fragment: a nonlinear clause references a body predicate that is neither \
                 in the SCC being solved nor already solved (an unsolved/circular dependency); \
                 declining"
                    .to_owned(),
            ));
        };
        let Some(inst) = instantiate(arena, interp, args) else {
            return Ok(Err(
                "out of fragment: a folded body predicate application has an arity mismatch; \
                 declining"
                    .to_owned(),
            ));
        };
        acc = arena.and(inst, acc)?;
    }
    Ok(Ok(FoldedBody {
        recursive,
        constraint: acc,
    }))
}

/// Condenses the predicate dependency graph into its strongly-connected
/// components, returned in **topological order** (dependencies first), so each
/// `SCC` is processed only after every `SCC` it depends on. Each component is a
/// list of its member predicates in stable (declaration) order. A single
/// predicate (whether or not self-recursive) is a one-element component; a cycle
/// among distinct predicates (mutual recursion) is a multi-element component.
///
/// The dependency edge `P → Q` (P depends on Q) is added for every clause whose
/// body predicate is `Q` and head predicate is `P`. Self-loops are recorded
/// implicitly (a single predicate is always its own component) and do not affect
/// the component structure.
///
/// Determinism: this is Tarjan's algorithm driven over `predicates` in
/// declaration order, with each adjacency list collected via a
/// [`std::collections::BTreeSet`] and iterated in that stable order, so the
/// component list and the order within each component are reproducible.
fn scc_condensation(predicates: &[FuncId], shapes: &[ClauseShape]) -> Vec<Vec<FuncId>> {
    // Adjacency over the dependency edge P → Q (P depends on Q). BTreeSet keeps a
    // stable, de-duplicated successor order.
    let mut adj: BTreeMap<FuncId, std::collections::BTreeSet<FuncId>> = predicates
        .iter()
        .map(|&p| (p, std::collections::BTreeSet::new()))
        .collect();
    for shape in shapes {
        if let Some((head_pred, _)) = &shape.head {
            // A head P depends on every body predicate Q (P → Q) in a nonlinear
            // clause; a self-loop (Q == P) does not affect the component structure.
            for (body_pred, _) in &shape.bodies {
                if body_pred != head_pred {
                    adj.entry(*head_pred).or_default().insert(*body_pred);
                }
            }
        }
    }

    // A stable index per predicate, in declaration order.
    let index_of: BTreeMap<FuncId, usize> = predicates
        .iter()
        .copied()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();

    let n = predicates.len();
    let mut indices: Vec<Option<usize>> = vec![None; n];
    let mut lowlink: Vec<usize> = vec![0; n];
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next_index: usize = 0;
    // Components in Tarjan's emission order. With the dependency edge P → Q (P
    // depends on Q), a component is finalized only after every component it can
    // reach (its dependencies) is finalized — so this emission order is already
    // topological (dependencies first), no reversal needed.
    let mut components: Vec<Vec<FuncId>> = Vec::new();

    // Iterative Tarjan to avoid recursion depth concerns. Each frame tracks the
    // node and the position of its next successor to visit.
    for start in 0..n {
        if indices[start].is_some() {
            continue;
        }
        let mut call_stack: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&(v, succ_pos)) = call_stack.last() {
            if succ_pos == 0 {
                indices[v] = Some(next_index);
                lowlink[v] = next_index;
                next_index += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            let successors: Vec<usize> = adj
                .get(&predicates[v])
                .map(|s| s.iter().map(|q| index_of[q]).collect())
                .unwrap_or_default();
            if succ_pos < successors.len() {
                let w = successors[succ_pos];
                // Advance this frame's cursor before descending.
                call_stack.last_mut().expect("frame present").1 += 1;
                if indices[w].is_none() {
                    call_stack.push((w, 0));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(indices[w].expect("visited node has an index"));
                }
            } else {
                // All successors processed: settle v.
                if lowlink[v] == indices[v].expect("v has an index") {
                    let mut component: Vec<FuncId> = Vec::new();
                    loop {
                        let w = stack.pop().expect("non-empty SCC stack");
                        on_stack[w] = false;
                        component.push(predicates[w]);
                        if w == v {
                            break;
                        }
                    }
                    // Stable within-component order: by declaration index.
                    component.sort_by_key(|p| index_of[p]);
                    components.push(component);
                }
                call_stack.pop();
                if let Some(&(parent, _)) = call_stack.last() {
                    lowlink[parent] = lowlink[parent].min(lowlink[v]);
                }
            }
        }
    }

    components
}

/// The result of solving one predicate in topological order.
enum SolveOne {
    /// The predicate's interpretation `I_P(params)`.
    Interp(PredInterpretation),
    /// The predicate's own reachability already derives `false` ⇒ the whole
    /// system is `Unsat` with this counterexample depth.
    Unsat {
        /// The counterexample depth.
        steps: usize,
    },
    /// Decline (out of fragment / a cap / an engine that could not decide).
    Decline(String),
}

/// Solves a single predicate `P` given the already-solved `model` of its
/// dependencies. Non-self-recursive predicates get a direct formula; self-
/// recursive ones build a [`TransitionSystem`] with solved predecessors folded
/// into `init`/`trans`/`bad` and dispatch to a model-checking engine.
fn solve_one_predicate(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    pred: FuncId,
    model: &BTreeMap<FuncId, PredInterpretation>,
    config: &SolverConfig,
) -> Result<SolveOne, SolverError> {
    let (_, params_sorts, _) = arena.function(pred);
    let arg_sorts: Vec<Sort> = params_sorts.to_vec();

    // A trivial SCC is the single predicate P; its own recursive atoms are exactly
    // the P-atoms. Every other body atom belongs to a strictly-lower stratum and is
    // folded into the constraint.
    let scc_set: std::collections::BTreeSet<FuncId> = std::iter::once(pred).collect();

    // Is P self-recursive? (some clause has P among its body atoms and as head.)
    let self_recursive = shapes.iter().any(|shape| {
        matches!(&shape.head, Some((h, _)) if *h == pred)
            && shape.bodies.iter().any(|(b, _)| *b == pred)
    });

    // Defining clauses: those whose head is P.
    let defining: Vec<usize> = shapes
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(&s.head, Some((h, _)) if *h == pred))
        .map(|(i, _)| i)
        .collect();

    if self_recursive {
        solve_self_recursive(
            arena, system, shapes, pred, &arg_sorts, &scc_set, &defining, model, config,
        )
    } else {
        solve_direct(
            arena, system, shapes, pred, &arg_sorts, &scc_set, &defining, model,
        )
    }
}

/// Builds a **direct** interpretation for a non-self-recursive predicate `P`:
/// `I_P(p) := ⋁ over P's defining clauses of (⋀ I_{bodyᵢ} ∧ constraint)[head args ↦ p]`.
///
/// Each defining clause's solved body predicates are folded into the constraint by
/// [`fold_solved_bodies`] (`scc_set = {P}`, so a non-self-recursive `P` has no
/// recursive remainder); the head arguments (required to be distinct variable
/// symbols) are bound to fresh parameter symbols. If any disjunct retains a free
/// variable outside the parameters, the interpretation would be unsound to
/// re-check under the existential semantics of [`check_auto`], so the construction
/// declines.
#[allow(clippy::too_many_arguments)]
fn solve_direct(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    pred: FuncId,
    arg_sorts: &[Sort],
    scc_set: &std::collections::BTreeSet<FuncId>,
    defining: &[usize],
    model: &BTreeMap<FuncId, PredInterpretation>,
) -> Result<SolveOne, SolverError> {
    // Fresh parameter symbols, one per predicate argument.
    let mut params = Vec::with_capacity(arg_sorts.len());
    for (i, &sort) in arg_sorts.iter().enumerate() {
        params.push(arena.declare_internal(&format!("q@{}_{i}", pred.index()), sort)?);
    }
    let param_set: std::collections::BTreeSet<SymbolId> = params.iter().copied().collect();

    let mut disjuncts: Vec<TermId> = Vec::new();
    for &ci in defining {
        let clause = &system.clauses[ci];
        let shape = &shapes[ci];

        // Bind the head arguments (distinct variable symbols) to the parameters.
        let Some((_, head_args)) = &shape.head else {
            continue;
        };
        let Some(head_vars) = distinct_arg_vars(arena, head_args, arg_sorts) else {
            return Ok(SolveOne::Decline(
                "out of fragment: a defining clause's head predicate has a non-distinct-variable \
                 argument (re-model P(t…) as P(p…) ∧ p = t…); declining"
                    .to_owned(),
            ));
        };

        // Fold every solved lower-stratum body atom into the constraint. A
        // non-self-recursive P has no recursive remainder; a stray recursive atom
        // would mean P was mis-classified, so decline.
        let folded =
            match fold_solved_bodies(arena, &shape.bodies, clause.constraint, scc_set, model)? {
                Ok(folded) => folded,
                Err(reason) => return Ok(SolveOne::Decline(reason)),
            };
        if !folded.recursive.is_empty() {
            return Ok(SolveOne::Decline(
                "internal: a non-self-recursive predicate's defining clause retained a recursive \
                 body atom; declining"
                    .to_owned(),
            ));
        }
        let term = folded.constraint;

        // Bind head argument variables → parameter symbols.
        let mapping: Vec<(SymbolId, SymbolId)> = head_vars
            .iter()
            .copied()
            .zip(params.iter().copied())
            .collect();
        let mut sorted = mapping;
        sorted.sort_by_key(|&(src, _)| src);
        let bound = substitute_symbols(arena, term, &sorted);

        // The disjunct must be closed over the parameters: a stray free variable
        // would be existential under check_auto where the head re-check needs it
        // universal — unsound. Decline.
        let mut frees = std::collections::BTreeSet::new();
        collect_free_symbols(arena, bound, &mut frees);
        if !frees.is_subset(&param_set) {
            return Ok(SolveOne::Decline(
                "out of fragment: a non-recursive predicate's defining clause leaves a free \
                 variable outside the predicate arguments (an existential body); declining"
                    .to_owned(),
            ));
        }
        disjuncts.push(bound);
    }

    // I_P(p) = ⋁ disjuncts; no defining clause ⇒ false (P is empty).
    let body = match disjuncts.split_first() {
        None => arena.bool_const(false),
        Some((&first, rest)) => {
            let mut acc = first;
            for &d in rest {
                acc = arena.or(acc, d)?;
            }
            acc
        }
    };

    Ok(SolveOne::Interp(PredInterpretation { params, body }))
}

/// Builds a self-recursive predicate's interpretation by reducing it to a
/// single-predicate [`TransitionSystem`] with the solved predecessors folded in,
/// then dispatching to a model-checking engine.
///
/// Each defining/query clause's solved lower-stratum body atoms are folded into
/// the constraint by [`fold_solved_bodies`] (`scc_set = {P}`); what remains is the
/// linear recursive shape:
///
/// * `init` — facts (`constraint ⇒ P(head)`) and clauses whose only remaining body
///   atom is a solved predecessor `Q`, folded as `I_Q(args) ∧ constraint`.
/// * `trans` — the inductive clauses (one remaining recursive `P(s)` body atom).
/// * `bad` — the query clauses whose remaining body atom is `P`.
///
/// A clause that retains **two or more** recursive `P`-atoms after folding is
/// genuine nonlinear recursion and declines.
#[allow(clippy::too_many_arguments)]
fn solve_self_recursive(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    pred: FuncId,
    arg_sorts: &[Sort],
    scc_set: &std::collections::BTreeSet<FuncId>,
    defining: &[usize],
    model: &BTreeMap<FuncId, PredInterpretation>,
    config: &SolverConfig,
) -> Result<SolveOne, SolverError> {
    // Split P's defining clauses into init-disjuncts and inductive (trans) ones.
    // An init-disjunct is `(solved-body-invariant ∧ constraint, head_vars)`; an
    // inductive is `(constraint, body_vars, head_vars)`.
    let mut inits: Vec<SelfInit> = Vec::new();
    let mut inductives: Vec<InductiveClause> = Vec::new();
    for &ci in defining {
        let clause = &system.clauses[ci];
        let shape = &shapes[ci];
        let Some((_, head_args)) = &shape.head else {
            continue;
        };
        let Some(head_vars) = distinct_arg_vars(arena, head_args, arg_sorts) else {
            return Ok(SolveOne::Decline(
                "out of fragment: a self-recursive predicate's head has a non-distinct-variable \
                 argument; declining"
                    .to_owned(),
            ));
        };

        // Fold solved lower-stratum body atoms; what remains is the recursive part.
        let folded =
            match fold_solved_bodies(arena, &shape.bodies, clause.constraint, scc_set, model)? {
                Ok(folded) => folded,
                Err(reason) => return Ok(SolveOne::Decline(reason)),
            };
        match folded.recursive.as_slice() {
            // No recursive atom left: an init (a fact, or solved predecessors only).
            [] => inits.push(SelfInit {
                constraint: folded.constraint,
                head_vars,
            }),
            // Exactly one recursive `P`-atom: an inductive transition. Body args
            // must be distinct vars disjoint from the head vars (pre/post binding).
            [(_, body_args)] => {
                let Some(body_vars) = distinct_arg_vars(arena, body_args, arg_sorts) else {
                    return Ok(SolveOne::Decline(
                        "out of fragment: a self-recursive body has a non-distinct-variable \
                         argument; declining"
                            .to_owned(),
                    ));
                };
                if body_vars.iter().any(|v| head_vars.contains(v)) {
                    return Ok(SolveOne::Decline(
                        "out of fragment: an inductive clause shares a variable between its body \
                         and head predicate arguments (ambiguous pre/post binding); declining"
                            .to_owned(),
                    ));
                }
                inductives.push(InductiveClause {
                    constraint: folded.constraint,
                    body_vars,
                    head_vars,
                });
            }
            // Two or more recursive atoms: genuine nonlinear recursion. Decline.
            _ => {
                return Ok(SolveOne::Decline(
                    "out of fragment: a clause retains two or more recursive body atoms after \
                     folding (genuine nonlinear recursion — a product/k-fold transition system); \
                     declining"
                        .to_owned(),
                ));
            }
        }
    }

    // The query clauses whose remaining body atom is P become `bad`.
    let queries =
        match collect_self_queries(arena, system, shapes, pred, arg_sorts, scc_set, model)? {
            Ok(queries) => queries,
            Err(reason) => return Ok(SolveOne::Decline(reason)),
        };

    let reduced = SelfReduced {
        arg_sorts: arg_sorts.to_vec(),
        inits,
        inductives,
        queries,
    };

    let (dispatched, state_params) = dispatch_self(arena, &reduced, config)?;
    match dispatched {
        Dispatch::Safe { invariant } => Ok(SolveOne::Interp(PredInterpretation {
            params: state_params,
            body: invariant,
        })),
        Dispatch::Unsat { steps } => Ok(SolveOne::Unsat { steps }),
        Dispatch::Unknown(reason) => Ok(SolveOne::Decline(reason)),
    }
}

/// Collects the `bad`-state query clauses of a self-recursive predicate `P`: every
/// head-free clause that mentions `P`. Its solved lower-stratum body atoms are
/// folded into the constraint; exactly one recursive `P`-atom must remain (a query
/// retaining `≥ 2` recursive atoms is genuine nonlinear recursion and declines).
/// The inner `Err(reason)` is a sound decline; the outer `Result` an arena error.
#[allow(clippy::too_many_arguments)]
fn collect_self_queries(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    pred: FuncId,
    arg_sorts: &[Sort],
    scc_set: &std::collections::BTreeSet<FuncId>,
    model: &BTreeMap<FuncId, PredInterpretation>,
) -> Result<Result<Vec<QueryClause>, String>, SolverError> {
    let mut queries: Vec<QueryClause> = Vec::new();
    for (clause, shape) in system.clauses.iter().zip(shapes) {
        if shape.head.is_some() {
            continue;
        }
        // Only a query that mentions P at all is relevant to P's bad states.
        if !shape.bodies.iter().any(|(b, _)| *b == pred) {
            continue;
        }
        let folded =
            match fold_solved_bodies(arena, &shape.bodies, clause.constraint, scc_set, model)? {
                Ok(folded) => folded,
                Err(reason) => return Ok(Err(reason)),
            };
        let [(_, body_args)] = folded.recursive.as_slice() else {
            return Ok(Err(
                "out of fragment: a query retains zero or more than one recursive body atom after \
                 folding (genuine nonlinear recursion); declining"
                    .to_owned(),
            ));
        };
        let Some(body_vars) = distinct_arg_vars(arena, body_args, arg_sorts) else {
            return Ok(Err(
                "out of fragment: a query over a self-recursive predicate has a \
                 non-distinct-variable argument; declining"
                    .to_owned(),
            ));
        };
        queries.push(QueryClause {
            constraint: folded.constraint,
            body_vars,
        });
    }
    Ok(Ok(queries))
}

/// A self-recursive predicate's init disjunct: a constraint (with any solved
/// predecessor already folded in) and the head argument variables.
struct SelfInit {
    constraint: TermId,
    head_vars: Vec<SymbolId>,
}

/// The reduced single-predicate transition system for a self-recursive predicate,
/// with solved predecessors already folded into `inits`.
struct SelfReduced {
    arg_sorts: Vec<Sort>,
    inits: Vec<SelfInit>,
    inductives: Vec<InductiveClause>,
    queries: Vec<QueryClause>,
}

impl SelfReduced {
    fn declare_state(
        &self,
        arena: &mut TermArena,
        step: usize,
    ) -> Result<Vec<SymbolId>, SolverError> {
        let mut vars = Vec::with_capacity(self.arg_sorts.len());
        for (i, &sort) in self.arg_sorts.iter().enumerate() {
            vars.push(arena.declare_internal(&format!("p@{step}_{i}"), sort)?);
        }
        Ok(vars)
    }
}

impl TransitionSystem for SelfReduced {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        self.declare_state(arena, step)
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for fact in &self.inits {
            let Some(bound) =
                ReducedSystem::bind(arena, fact.constraint, &[], &[], &fact.head_vars, s0)
            else {
                return Err(SolverError::Unsupported(
                    "Horn fact/init clause has an unbindable argument shape".to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for ind in &self.inductives {
            let Some(bound) = ReducedSystem::bind(
                arena,
                ind.constraint,
                &ind.body_vars,
                pre,
                &ind.head_vars,
                post,
            ) else {
                return Err(SolverError::Unsupported(
                    "Horn inductive clause shares a variable between its body and head arguments"
                        .to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        let mut acc: Option<TermId> = None;
        for query in &self.queries {
            let Some(bound) =
                ReducedSystem::bind(arena, query.constraint, &query.body_vars, s, &[], &[])
            else {
                return Err(SolverError::Unsupported(
                    "Horn query clause has an unbindable argument shape".to_owned(),
                ));
            };
            acc = Some(match acc {
                None => bound,
                Some(prev) => arena.or(prev, bound)?,
            });
        }
        Ok(match acc {
            Some(term) => term,
            None => arena.bool_const(false),
        })
    }
}

/// Dispatches a [`SelfReduced`] system to the model-checking engine for its state
/// sort, returning the engine result with the pinned step-0 parameters.
fn dispatch_self(
    arena: &mut TermArena,
    reduced: &SelfReduced,
    config: &SolverConfig,
) -> Result<(Dispatch, Vec<SymbolId>), SolverError> {
    let state_params = reduced.declare_state(arena, 0)?;
    let pinned = PinnedSelf {
        inner: reduced,
        state_params: state_params.clone(),
    };
    let dispatch = match state_class(&reduced.arg_sorts) {
        StateClass::Real => match prove_safety_pdr_lra(arena, &pinned, config)? {
            PdrLraOutcome::Safe { invariant } => Dispatch::Safe { invariant },
            PdrLraOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
            PdrLraOutcome::Unknown { .. } => match prove_safety_imc_lra(arena, &pinned, config)? {
                ImcLraOutcome::Safe { invariant } => Dispatch::Safe { invariant },
                ImcLraOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
                ImcLraOutcome::Unknown { reason } => Dispatch::Unknown(reason),
            },
        },
        StateClass::Finite => match prove_safety_pdr(arena, &pinned, config)? {
            PdrOutcome::Safe { invariant } => Dispatch::Safe { invariant },
            PdrOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
            PdrOutcome::Unknown { .. } => match prove_safety_imc(arena, &pinned, config)? {
                ImcOutcome::Safe { invariant } => Dispatch::Safe { invariant },
                ImcOutcome::Reachable { steps, .. } => Dispatch::Unsat { steps },
                ImcOutcome::Unknown { reason } => Dispatch::Unknown(reason),
            },
        },
        StateClass::Unsupported => Dispatch::Unknown(
            "Horn predicate argument sorts are outside this slice's reach (only Real, BitVec, and \
             Bool are dispatched)"
                .to_owned(),
        ),
    };
    Ok((dispatch, state_params))
}

/// A [`SelfReduced`] wrapper pinning the step-0 state symbols (mirrors
/// [`PinnedReduced`] for the single-predicate path).
struct PinnedSelf<'a> {
    inner: &'a SelfReduced,
    state_params: Vec<SymbolId>,
}

impl TransitionSystem for PinnedSelf<'_> {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        if step == 0 {
            return Ok(self.state_params.clone());
        }
        self.inner.declare_state(arena, step)
    }

    fn init(&self, arena: &mut TermArena, s0: &[SymbolId]) -> Result<TermId, SolverError> {
        self.inner.init(arena, s0)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        self.inner.trans(arena, pre, post)
    }

    fn bad(&self, arena: &mut TermArena, s: &[SymbolId]) -> Result<TermId, SolverError> {
        self.inner.bad(arena, s)
    }
}

// ===========================================================================
// Mutual recursion: the merge-to-tagged-predicate reduction (sort-compatible SCC)
// ===========================================================================

/// The maximum number of members in a mutually-recursive `SCC` this slice merges.
/// Beyond this, the tagged-union state and clause count grow past a safe bound and
/// the `SCC` declines to `Unknown`.
const MAX_SCC_MEMBERS: usize = 16;

/// The maximum argument width (number of state columns, excluding the tag) of an
/// `SCC` member. A wider tuple declines rather than risk an engine blow-up.
const MAX_SCC_STATE_WIDTH: usize = 32;

/// The result of solving a non-trivial (mutually-recursive) `SCC`.
enum SolveScc {
    /// One interpretation per `SCC` member, projected from the merged predicate.
    Interps(Vec<(FuncId, PredInterpretation)>),
    /// The merged predicate's own reachability derives `false` ⇒ the whole system
    /// is `Unsat` with this counterexample depth.
    Unsat {
        /// The counterexample depth.
        steps: usize,
    },
    /// Decline (not sort-compatible, a cap, an unsupported sort, or an engine that
    /// could not decide).
    Decline(String),
}

/// Solves a non-trivial (`≥ 2`-member) mutually-recursive `SCC` by the
/// **merge-to-tagged-predicate** reduction (the sort-compatible slice).
///
/// All members must share the same argument sort vector `(τ₁…τₙ)`. The members
/// are merged into one self-recursive predicate `P*` over a control-tagged state
/// `(tag, x₁…xₙ)`, where `tag` is a fresh real/bit-vector column whose constant
/// value selects the active member. Each defining clause is rewritten over `P*`:
///
/// * a **fact / inter-`SCC`** clause into member `Pᵢ` becomes an init disjunct
///   pinning the post tag to `i` (an inter-`SCC` body folds in its already-solved
///   predecessor exactly as [`solve_self_recursive`] does);
/// * an **intra-`SCC`** clause `Pⱼ(body) ∧ constraint ⇒ Pᵢ(head)` becomes an
///   inductive transition pinning the pre tag to `j` and the post tag to `i`;
/// * a **query** off member `Pⱼ` becomes a bad disjunct pinning the tag to `j`.
///
/// The merged system is solved by the existing [`SelfReduced`] dispatch, and the
/// invariant `I*(tag, x…)` is projected back per member as `Iᵢ(x…) := I*(i, x…)`.
/// Any non-sort-compatible member, an unbindable argument, a cap, or an engine
/// `Unknown` declines the whole `SCC`.
fn solve_mutual_scc(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    scc: &[FuncId],
    model: &BTreeMap<FuncId, PredInterpretation>,
    config: &SolverConfig,
) -> Result<SolveScc, SolverError> {
    if scc.len() > MAX_SCC_MEMBERS {
        return Ok(SolveScc::Decline(format!(
            "out of cap: a mutually-recursive SCC has {} members (cap {MAX_SCC_MEMBERS}); declining",
            scc.len()
        )));
    }

    // Sort-compatibility: every member must declare the SAME argument sort vector.
    let (_, first_sorts, _) = arena.function(scc[0]);
    let member_sorts: Vec<Sort> = first_sorts.to_vec();
    if member_sorts.len() > MAX_SCC_STATE_WIDTH {
        return Ok(SolveScc::Decline(format!(
            "out of cap: an SCC member has arity {} (cap {MAX_SCC_STATE_WIDTH}); declining",
            member_sorts.len()
        )));
    }
    for &pred in scc {
        let (_, sorts, _) = arena.function(pred);
        if sorts != member_sorts.as_slice() {
            return Ok(SolveScc::Decline(
                "out of fragment: a mutually-recursive SCC has members of differing argument sort \
                 vectors (the full tagged-disjoint-union merge is a later slice; this slice handles \
                 only sort-compatible SCCs)"
                    .to_owned(),
            ));
        }
    }

    // The tag column's sort matches the engine family the member sorts dispatch to
    // (Real members ⇒ a Real tag; BitVec/Bool members ⇒ a BitVec tag), so the
    // merged state stays in one engine family rather than mixing sorts.
    let Some(tag_sort) = tag_sort_for(&member_sorts, scc.len()) else {
        return Ok(SolveScc::Decline(
            "out of fragment: a mutually-recursive SCC's argument sorts are outside this slice's \
             reach (only all-Real or all-BitVec/Bool members are merged); declining"
                .to_owned(),
        ));
    };

    // The merged state sort vector: [tag, τ₁…τₙ].
    let mut merged_sorts: Vec<Sort> = Vec::with_capacity(member_sorts.len() + 1);
    merged_sorts.push(tag_sort);
    merged_sorts.extend_from_slice(&member_sorts);

    // A stable tag constant per member, by the SCC's (declaration-order) position.
    let tag_of: BTreeMap<FuncId, usize> = scc
        .iter()
        .copied()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();

    // Build the merged self-recursive system's init/inductive/query lists.
    let merged = match build_merged_clauses(
        arena,
        system,
        shapes,
        scc,
        &tag_of,
        &member_sorts,
        tag_sort,
        model,
    )? {
        Ok(merged) => merged,
        Err(reason) => return Ok(SolveScc::Decline(reason)),
    };

    // Solve the merged self-recursive predicate with the existing machinery.
    let reduced = SelfReduced {
        arg_sorts: merged_sorts,
        inits: merged.inits,
        inductives: merged.inductives,
        queries: merged.queries,
    };
    let (dispatched, state_params) = dispatch_self(arena, &reduced, config)?;
    let invariant = match dispatched {
        Dispatch::Safe { invariant } => invariant,
        Dispatch::Unsat { steps } => return Ok(SolveScc::Unsat { steps }),
        Dispatch::Unknown(reason) => return Ok(SolveScc::Decline(reason)),
    };

    // Project I*(tag, x…) back to each member: Iᵢ(x…) := I*(i, x…). state_params
    // is [tag, x₁…xₙ]; the tag is position 0, the member params are positions 1..n.
    let (&tag_param, member_params) = state_params
        .split_first()
        .expect("merged state has at least the tag column");
    let member_params = member_params.to_vec();

    let mut interps: Vec<(FuncId, PredInterpretation)> = Vec::with_capacity(scc.len());
    for &pred in scc {
        let tag_const = tag_constant(arena, tag_sort, tag_of[&pred]);
        let mapping = vec![(tag_param, tag_const)];
        let projected = substitute(arena, invariant, &mapping);
        interps.push((
            pred,
            PredInterpretation {
                params: member_params.clone(),
                body: projected,
            },
        ));
    }
    Ok(SolveScc::Interps(interps))
}

/// The merged self-recursive transition-system clause lists built from an `SCC`'s
/// clauses (each carrying a leading control-tag column).
struct MergedClauses {
    inits: Vec<SelfInit>,
    inductives: Vec<InductiveClause>,
    queries: Vec<QueryClause>,
}

/// The merged clause a clause whose head is an `SCC` member rewrites to: an init
/// disjunct (a fact / inter-`SCC` body) or an inductive transition (an intra-`SCC`
/// body).
enum MergedHead {
    Init(SelfInit),
    Inductive(InductiveClause),
}

/// Rewrites a single clause whose head is an `SCC` member into its merged init /
/// inductive form, pinning the relevant control-tag column(s). The outer `Result`
/// carries a genuine arena error; the inner `Result`'s `Err(reason)` is a sound
/// decline of the whole `SCC`.
#[allow(clippy::too_many_arguments)]
fn merge_head_clause(
    arena: &mut TermArena,
    clause: &HornClause,
    shape: &ClauseShape,
    scc_set: &std::collections::BTreeSet<FuncId>,
    tag_of: &BTreeMap<FuncId, usize>,
    member_sorts: &[Sort],
    tag_sort: Sort,
    model: &BTreeMap<FuncId, PredInterpretation>,
    ci: usize,
    fresh: &mut usize,
) -> Result<Result<MergedHead, String>, SolverError> {
    let Some((head_pred, head_args)) = &shape.head else {
        return Ok(Err(
            "internal: merge_head_clause on a head-free clause".to_owned()
        ));
    };
    let Some(head_vars) = distinct_arg_vars(arena, head_args, member_sorts) else {
        return Ok(Err(
            "out of fragment: an SCC clause's head has a non-distinct-variable argument; declining"
                .to_owned(),
        ));
    };
    let head_tag = tag_of[head_pred];

    // Fold every solved inter-SCC body atom into the constraint; what remains is
    // the intra-SCC recursive part (0 ⇒ an init, 1 ⇒ an inductive transition,
    // ≥ 2 ⇒ genuine nonlinear recursion within the SCC, declined).
    let folded = match fold_solved_bodies(arena, &shape.bodies, clause.constraint, scc_set, model)?
    {
        Ok(folded) => folded,
        Err(reason) => return Ok(Err(reason)),
    };

    match folded.recursive.as_slice() {
        // No intra-SCC body left ⇒ an init pinning the post tag (a fact, or an
        // inter-SCC clause whose solved predecessors were all folded in).
        [] => {
            let Some((constraint, tag_var)) =
                pin_tag_head(arena, folded.constraint, tag_sort, head_tag, ci, fresh)
            else {
                return Ok(Err(
                    "internal: failed to build a tagged init constraint".to_owned()
                ));
            };
            Ok(Ok(MergedHead::Init(SelfInit {
                constraint,
                head_vars: prepend(tag_var, head_vars),
            })))
        }
        // One intra-SCC body ⇒ an inductive transition pinning pre and post tags.
        [(body_pred, body_args)] => {
            let Some(body_vars) = distinct_arg_vars(arena, body_args, member_sorts) else {
                return Ok(Err(
                    "out of fragment: an intra-SCC body has a non-distinct-variable argument; \
                     declining"
                        .to_owned(),
                ));
            };
            if body_vars.iter().any(|v| head_vars.contains(v)) {
                return Ok(Err(
                    "out of fragment: an intra-SCC clause shares a variable between its body and \
                     head predicate arguments (ambiguous pre/post binding); declining"
                        .to_owned(),
                ));
            }
            let body_tag = tag_of[body_pred];
            let Some((constraint, body_tag_var, head_tag_var)) = pin_tag_trans(
                arena,
                folded.constraint,
                tag_sort,
                body_tag,
                head_tag,
                ci,
                fresh,
            ) else {
                return Ok(Err(
                    "internal: failed to build a tagged transition constraint".to_owned(),
                ));
            };
            Ok(Ok(MergedHead::Inductive(InductiveClause {
                constraint,
                body_vars: prepend(body_tag_var, body_vars),
                head_vars: prepend(head_tag_var, head_vars),
            })))
        }
        // Two or more intra-SCC body atoms ⇒ genuine nonlinear recursion. Decline.
        _ => Ok(Err(
            "out of fragment: an SCC clause retains two or more intra-SCC body atoms after folding \
             (genuine nonlinear recursion within the SCC); declining"
                .to_owned(),
        )),
    }
}

/// Rewrites every clause relevant to the `SCC` (head an `SCC` member, or a query
/// off an `SCC` member) into the merged self-recursive system's init/inductive/
/// query lists, threading a fresh per-clause control-tag variable as the leading
/// argument so the existing [`SelfReduced::bind`] binds it to the leading state
/// column. The outer `Result` carries a genuine arena error; the inner `Result`'s
/// `Err(reason)` is a sound decline of the whole `SCC`.
#[allow(clippy::too_many_arguments)]
fn build_merged_clauses(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    scc: &[FuncId],
    tag_of: &BTreeMap<FuncId, usize>,
    member_sorts: &[Sort],
    tag_sort: Sort,
    model: &BTreeMap<FuncId, PredInterpretation>,
) -> Result<Result<MergedClauses, String>, SolverError> {
    let mut inits: Vec<SelfInit> = Vec::new();
    let mut inductives: Vec<InductiveClause> = Vec::new();
    let mut queries: Vec<QueryClause> = Vec::new();
    let mut fresh: usize = 0;
    let scc_set: std::collections::BTreeSet<FuncId> = scc.iter().copied().collect();

    for (ci, (clause, shape)) in system.clauses.iter().zip(shapes).enumerate() {
        // A clause is relevant to this SCC iff its head is an SCC member, or it is
        // a query with at least one SCC-member body atom.
        let head_in_scc = matches!(&shape.head, Some((h, _)) if scc_set.contains(h));
        let query_in_scc =
            shape.head.is_none() && shape.bodies.iter().any(|(b, _)| scc_set.contains(b));
        if !head_in_scc && !query_in_scc {
            continue;
        }

        if head_in_scc {
            match merge_head_clause(
                arena,
                clause,
                shape,
                &scc_set,
                tag_of,
                member_sorts,
                tag_sort,
                model,
                ci,
                &mut fresh,
            )? {
                Ok(MergedHead::Init(init)) => inits.push(init),
                Ok(MergedHead::Inductive(ind)) => inductives.push(ind),
                Err(reason) => return Ok(Err(reason)),
            }
        } else {
            // A query off an SCC member ⇒ a bad disjunct pinning the tag. Fold the
            // solved lower-stratum atoms; exactly one intra-SCC body must remain.
            let folded =
                match fold_solved_bodies(arena, &shape.bodies, clause.constraint, &scc_set, model)?
                {
                    Ok(folded) => folded,
                    Err(reason) => return Ok(Err(reason)),
                };
            let [(body_pred, body_args)] = folded.recursive.as_slice() else {
                return Ok(Err(
                    "out of fragment: a query off an SCC member retains zero or more than one \
                     intra-SCC body atom after folding (genuine nonlinear recursion); declining"
                        .to_owned(),
                ));
            };
            let Some(body_vars) = distinct_arg_vars(arena, body_args, member_sorts) else {
                return Ok(Err("out of fragment: a query over an SCC member has a \
                               non-distinct-variable argument; declining"
                    .to_owned()));
            };
            let body_tag = tag_of[body_pred];
            let Some((constraint, tag_var)) =
                pin_tag_head(arena, folded.constraint, tag_sort, body_tag, ci, &mut fresh)
            else {
                return Ok(Err(
                    "internal: failed to build a tagged query constraint".to_owned()
                ));
            };
            queries.push(QueryClause {
                constraint,
                body_vars: prepend(tag_var, body_vars),
            });
        }
    }

    Ok(Ok(MergedClauses {
        inits,
        inductives,
        queries,
    }))
}

/// Prepends a single symbol to a vector, returning the new vector.
fn prepend(first: SymbolId, rest: Vec<SymbolId>) -> Vec<SymbolId> {
    let mut out = Vec::with_capacity(rest.len() + 1);
    out.push(first);
    out.extend(rest);
    out
}

/// The tag column's sort for an `SCC` whose members share `member_sorts`: a `Real`
/// tag for all-`Real` members, a `BitVec` tag wide enough to hold `member_count`
/// distinct values for all-`BitVec`/`Bool` members, else `None` (unsupported).
fn tag_sort_for(member_sorts: &[Sort], member_count: usize) -> Option<Sort> {
    match state_class(member_sorts) {
        StateClass::Real => Some(Sort::Real),
        StateClass::Finite => {
            // A width holding values 0..member_count (≥ 1 bit).
            let mut width: u32 = 1;
            while (1u128 << width) < u128::try_from(member_count).ok()? {
                width += 1;
            }
            Some(Sort::BitVec(width))
        }
        StateClass::Unsupported => None,
    }
}

/// The tag constant term for member index `tag` of sort `tag_sort`: a real literal
/// for a `Real` tag, a bit-vector constant for a `BitVec` tag.
fn tag_constant(arena: &mut TermArena, tag_sort: Sort, tag: usize) -> TermId {
    match tag_sort {
        Sort::Real => {
            let n = i128::try_from(tag).expect("tag fits i128");
            arena.real_ratio(n, 1)
        }
        Sort::BitVec(w) => {
            let v = u128::try_from(tag).expect("tag fits u128");
            arena
                .bv_const(w, v)
                .expect("tag value fits the tag width by construction")
        }
        // tag_sort_for only ever returns Real/BitVec; a Bool/other tag is unreachable.
        _ => arena.bool_const(false),
    }
}

/// Builds a fresh tag variable bound (by an added `tag_var = const(tag)` equality)
/// for a clause that pins **one** tag (an init / inter-`SCC` init / query head or
/// body). Returns the augmented constraint and the fresh tag variable symbol.
fn pin_tag_head(
    arena: &mut TermArena,
    constraint: TermId,
    tag_sort: Sort,
    tag: usize,
    clause_index: usize,
    fresh: &mut usize,
) -> Option<(TermId, SymbolId)> {
    let tag_var = arena
        .declare(
            &format!("scc_tag@{clause_index}_{}", next_fresh(fresh)),
            tag_sort,
        )
        .ok()?;
    let tag_term = arena.var(tag_var);
    let tag_const = tag_constant(arena, tag_sort, tag);
    let tag_eq = arena.eq(tag_term, tag_const).ok()?;
    let augmented = arena.and(tag_eq, constraint).ok()?;
    Some((augmented, tag_var))
}

/// Builds two fresh tag variables (pre and post) bound to `body_tag` and
/// `head_tag` for an intra-`SCC` inductive clause. Returns the augmented
/// constraint and the two fresh tag variable symbols.
#[allow(clippy::too_many_arguments)]
fn pin_tag_trans(
    arena: &mut TermArena,
    constraint: TermId,
    tag_sort: Sort,
    body_tag: usize,
    head_tag: usize,
    clause_index: usize,
    fresh: &mut usize,
) -> Option<(TermId, SymbolId, SymbolId)> {
    let body_var = arena
        .declare(
            &format!("scc_tagb@{clause_index}_{}", next_fresh(fresh)),
            tag_sort,
        )
        .ok()?;
    let head_var = arena
        .declare(
            &format!("scc_tagh@{clause_index}_{}", next_fresh(fresh)),
            tag_sort,
        )
        .ok()?;
    let body_term = arena.var(body_var);
    let head_term = arena.var(head_var);
    let body_const = tag_constant(arena, tag_sort, body_tag);
    let head_const = tag_constant(arena, tag_sort, head_tag);
    let body_eq = arena.eq(body_term, body_const).ok()?;
    let head_eq = arena.eq(head_term, head_const).ok()?;
    let tags = arena.and(body_eq, head_eq).ok()?;
    let augmented = arena.and(tags, constraint).ok()?;
    Some((augmented, body_var, head_var))
}

/// Returns the current fresh counter and advances it (a unique-suffix source for
/// the per-clause tag variable names).
fn next_fresh(fresh: &mut usize) -> usize {
    let v = *fresh;
    *fresh += 1;
    v
}

/// The query check under a solved model.
enum QueryCheck {
    /// Some query body is satisfiable under the model ⇒ `false` is derivable.
    Reachable {
        /// A surfaced depth (0 when no model-checking depth is available).
        steps: usize,
    },
    /// Every query body is unsatisfiable under the model.
    Unreachable,
    /// A query could not be discharged (an engine `Unknown`/unsupported).
    Decline,
}

/// Checks every query clause `(⋀ Pⱼ(argsⱼ)) ∧ constraint ⇒ false` under the
/// solved model: the conjunction `(⋀ I_{Pⱼ}(argsⱼ)) ∧ constraint` must be UNSAT.
/// A `Sat` is a reachable derivation of `false` (the whole system is `Unsat`).
/// Every body atom of a (possibly nonlinear) query is instantiated; at the top
/// level every predicate is solved, so each atom has an interpretation.
fn check_queries(
    arena: &mut TermArena,
    system: &HornSystem,
    shapes: &[ClauseShape],
    model: &BTreeMap<FuncId, PredInterpretation>,
    config: &SolverConfig,
) -> Result<QueryCheck, SolverError> {
    for (clause, shape) in system.clauses.iter().zip(shapes) {
        if shape.head.is_some() {
            continue;
        }
        let mut assertions: Vec<TermId> = Vec::new();
        for (body_pred, body_args) in &shape.bodies {
            let Some(interp) = model.get(body_pred) else {
                return Ok(QueryCheck::Decline);
            };
            let Some(inst) = instantiate(arena, interp, body_args) else {
                return Ok(QueryCheck::Decline);
            };
            assertions.push(inst);
        }
        assertions.push(clause.constraint);
        match check_auto(arena, &assertions, config) {
            Ok(CheckResult::Unsat) => {}
            Ok(CheckResult::Sat(_)) => return Ok(QueryCheck::Reachable { steps: 0 }),
            Ok(_) | Err(SolverError::Unsupported(_)) => return Ok(QueryCheck::Decline),
            Err(other) => return Err(other),
        }
    }
    Ok(QueryCheck::Unreachable)
}

/// **The whole-system verify-before-return clause-validity check.** Re-validates
/// the full multi-predicate `model` against **every** original Horn clause. For
/// each clause `(⋀ body P_j → I_{P_j}) ∧ constraint ∧ ¬(head P → I_P)` (head
/// `None` ⇒ no head term) the obligation must be `unsat` under the trusted
/// [`check_auto`](crate::check_auto). Returns `true` only when **all** clauses
/// pass; any non-`unsat`, unknown, unsupported, or error ⇒ `false` (a sound
/// decline). This is the only trusted gate of the multi-predicate solver.
fn verify_horn_model(
    arena: &mut TermArena,
    system: &HornSystem,
    model: &BTreeMap<FuncId, PredInterpretation>,
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    for clause in &system.clauses {
        let mut assertions: Vec<TermId> = Vec::new();

        // Body atoms: P_j(args) ↦ I_{P_j}(args).
        for &atom in &clause.body {
            let Some((func, args)) = app_args_with_func(arena, atom, model) else {
                return Ok(false);
            };
            let interp = &model[&func];
            let Some(inst) = instantiate(arena, interp, &args) else {
                return Ok(false);
            };
            assertions.push(inst);
        }

        // The theory constraint.
        assertions.push(clause.constraint);

        // ¬(head with P ↦ I); head None ⇒ ¬false = true (a no-op, omitted).
        if let Some(head) = clause.head {
            let Some((func, args)) = app_args_with_func(arena, head, model) else {
                return Ok(false);
            };
            let interp = &model[&func];
            let Some(inst) = instantiate(arena, interp, &args) else {
                return Ok(false);
            };
            let neg = arena.not(inst)?;
            assertions.push(neg);
        }

        match check_auto(arena, &assertions, config) {
            Ok(CheckResult::Unsat) => {}
            Ok(_) | Err(SolverError::Unsupported(_)) => return Ok(false),
            Err(other) => return Err(other),
        }
    }
    Ok(true)
}

/// The `(predicate, args)` of `term` if it is an application of a predicate the
/// `model` interprets, else `None`.
fn app_args_with_func(
    arena: &TermArena,
    term: TermId,
    model: &BTreeMap<FuncId, PredInterpretation>,
) -> Option<(FuncId, Vec<TermId>)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::Apply(func),
            args,
        } if model.contains_key(func) => Some((*func, args.to_vec())),
        _ => None,
    }
}

/// Extracts the argument **variable symbols** of a list of predicate-application
/// argument terms, requiring each to be a **distinct** variable symbol of the
/// matching declared sort. Returns `None` on any non-variable, repeated, or
/// sort-mismatched argument (the reduction's distinct-variable boundary).
fn distinct_arg_vars(
    arena: &TermArena,
    args: &[TermId],
    arg_sorts: &[Sort],
) -> Option<Vec<SymbolId>> {
    if args.len() != arg_sorts.len() {
        return None;
    }
    let mut vars = Vec::with_capacity(args.len());
    for (i, &arg) in args.iter().enumerate() {
        match arena.node(arg) {
            TermNode::Symbol(sym) => {
                if arena.sort_of(arg) != arg_sorts[i] || vars.contains(sym) {
                    return None;
                }
                vars.push(*sym);
            }
            _ => return None,
        }
    }
    Some(vars)
}

/// Collects the free variable symbols of `term` into `out` (every [`TermNode::Symbol`]
/// leaf). Used to confirm a direct interpretation is closed over its parameters.
fn collect_free_symbols(
    arena: &TermArena,
    term: TermId,
    out: &mut std::collections::BTreeSet<SymbolId>,
) {
    match arena.node(term) {
        TermNode::Symbol(sym) => {
            out.insert(*sym);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for arg in args {
                collect_free_symbols(arena, arg, out);
            }
        }
        _ => {}
    }
}
