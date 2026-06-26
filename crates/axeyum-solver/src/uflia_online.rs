//! Online (model-based) `Nelson–Oppen` combination of `EUF` + linear integer
//! arithmetic — `QF_UFLIA` by **equality sharing** (Track 1, P1.6, the integer
//! analogue of the `EUF` + `LRA` combination [`crate::uflra_online`]).
//!
//! axeyum already decides `QF_UFLIA` *offline* by eager Ackermann
//! ([`crate::euf::check_with_uf_arithmetic`]): it eliminates every
//! uninterpreted-function application up front and solves the resulting
//! linear-integer conjunction. This module is the **warm, equality-sharing**
//! alternative — the standard model-based theory combination (MBTC) / `Nelson–Oppen`
//! loop over the two *online* theory solvers that already landed:
//!
//! - [`crate::euf_egraph::EufTheory`] — the backtrackable congruence-closure `EUF`
//!   solver (equality atoms, congruence over `Op::Apply`); its e-graph is the
//!   arrangement of the **shared** terms on the `EUF` side, and
//!   [`crate::theory_combination::classify_interface_equalities`] reads entailed /
//!   refuted equalities off it.
//! - [`crate::lia_online::LiaTheory`] — the backtrackable online integer solver (order
//!   / equality atoms over the integers, re-deciding feasibility through the trusted
//!   offline simplex-with-tightening decider); feasibility of the live constraints
//!   under added interface equalities is the arrangement on the `LIA` side.
//!
//! **Shared (interface) terms** are the integer-sorted terms that occur both in an
//! `EUF` context (a UF argument / result) and in a `LIA` atom.
//!
//! **`LIA` is NOT convex** (unlike `LRA` over ℝ). A satisfiable integer conjunction
//! need not *force* a single interface equality even when it entails a *disjunction*
//! of them, so a purely deductive equality exchange would be incomplete here. The
//! model-based split is convexity-free and stays complete regardless: it reads each
//! theory's concrete arrangement and case-splits the undetermined shared pairs (`s = t`
//! vs `s ≠ t`, the disequality branch realized as `s < t ∨ s > t` on the `LIA` side,
//! recorded as a disequality on the `EUF` side) until a leaf consistent in **both**
//! theories or all branches infeasible. Every undetermined pair the `EUF` congruence
//! already pins (entailed / refuted) prunes a branch — the equality-sharing exchange.
//!
//! **What this slice implements.**
//!
//! - The sound *conjunctive* MBTC (`decide_conjunction`): flatten the assertions to a
//!   conjunction of literals, assert each theory's atoms, and DFS-split on the shared
//!   pairs. A leaf consistent in both theories yields a combined model that is
//!   **replayed against the original assertions**; all branches infeasible ⇒ `UNSAT`.
//!   This is the conjunctive fast-path and its behaviour is unchanged.
//!
//! - Full (Boolean-structured) `QF_UFLIA` (`check_qf_uflia_boolean`): when the
//!   assertions are *not* a conjunction, a **`DPLL(T)`** layer (the online `CDCL(T)`
//!   payoff) wraps the combination. The Boolean structure (`and` / `or` / `not` /
//!   `xor` / `=>` / `ite` over the distinct `EUF` / `LIA` atoms) is Tseitin-encoded
//!   into a propositional skeleton with one variable per distinct theory atom. An
//!   enumerative `DPLL` search assigns those propositions; on each total propositional
//!   model the corresponding conjunction of theory literals is decided by the **same**
//!   `decide_conjunction` combination above. A model whose combination is `sat`
//!   (replay-checked) ⇒ `SAT`; a model whose combination is `unsat` is blocked by a
//!   theory-conflict clause (the negation of the model's theory-literal assignment) and
//!   the search continues; when every propositional model is blocked ⇒ `UNSAT`. A
//!   combination that returns `Unknown` on some model, or any of the enumeration caps,
//!   degrades the whole query to a conservative [`CheckResult::Unknown`] — never a wrong
//!   `sat` / `unsat`. This is the sound **enumerative `DPLL(T)`** slice: it handles
//!   arbitrary Boolean structure by reusing the conjunctive combination as the theory
//!   oracle behind a propositional search, with theory-conflict blocking clauses for
//!   pruning.
//!
//! **Trust.** This is a decision procedure; its soundness is established by the
//! differential gate against the trusted offline
//! [`crate::euf::check_with_uf_arithmetic`] (eager Ackermann) plus model replay (see
//! `tests/uflia_online.rs`), exactly as the online [`crate::lia_online::LiaTheory`] was
//! validated against [`crate::lra::check_with_lia_simplex`] and the online `EUF`
//! against the offline `EUF` path. Every `sat` is a replay-checked **integer** model of
//! the *original* query; a model the combination cannot justify degrades to
//! [`CheckResult::Unknown`], never a wrong `sat`. Every `unsat` is reported only when
//! all interface branches are infeasible — trusted because it agrees with the offline
//! decider on the differential corpus. The interface split is bounded (finitely many
//! shared pairs) and the recursion depth capped, so a resource cap degrades to
//! [`CheckResult::Unknown`].

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

use axeyum_ir::{
    Assignment, FuncValue, Op, Sort, TermArena, TermId, TermNode, Value, eval, well_founded_default,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::euf_egraph::{EufTheory, TheorySolver};
use crate::lia_online::LiaTheory;
use crate::model::Model;
use crate::theory_combination::{InterfaceStatus, classify_interface_equalities};

/// Hard ceiling on interface case-split recursion depth (one level per shared pair).
/// Above it the search declines to a graceful [`CheckResult::Unknown`] — never a
/// wrong verdict.
const MAX_SPLIT_DEPTH: usize = 64;

/// Hard ceiling on the number of propositional models the Boolean `DPLL(T)` layer
/// enumerates before declining to a graceful [`CheckResult::Unknown`]. Bounds the
/// enumerative search so a pathological skeleton degrades, never a wrong verdict.
const MAX_BOOLEAN_MODELS: usize = 100_000;

/// Hard ceiling on the number of distinct theory atoms in the Boolean skeleton.
/// Above it the layer declines (the propositional search space is too large to
/// enumerate soundly within budget).
///
/// This is deliberately above the current `QF_AUFLIA` fair-slice frontier
/// (`bug330` has 339 atoms) so the deadline-aware CDCL(T) spine, not admission,
/// decides whether that scalar abstraction is tractable.
const MAX_BOOLEAN_ATOMS: usize = 512;

/// Opaque Int-UF applications make each online LIA feasibility/probe call use the
/// heavier opaque-app arithmetic abstraction. That path is sound, but it is not
/// yet deadline-aware during combined-state construction and theory assertion, so
/// keep the online slice bounded and let larger generated rows use the production
/// lazy UFLIA route.
const MAX_OPAQUE_BOOLEAN_ATOMS: usize = 128;

/// Hard ceiling on Tseitin clauses produced for the Boolean skeleton; above it the
/// layer declines rather than build an unbounded encoding.
const MAX_BOOLEAN_CLAUSES: usize = 200_000;

/// A classified literal of the conjunction: the atom term and its asserted polarity.
///
/// `pub(crate)` so the warm [`crate::combined_theory_lia::CombinedTheoryLia`] (the
/// equality-sharing theory oracle the Boolean `DPLL(T)` layer calls) can hand the same
/// literal shape to the shared conjunctive core.
#[derive(Clone, Copy)]
pub(crate) struct Literal {
    pub(crate) atom: TermId,
    pub(crate) value: bool,
}

/// Decides an **arbitrary Boolean combination** of `QF_UFLIA` literals (`EUF` + linear
/// integer arithmetic) by the **online** model-based `Nelson–Oppen` combination,
/// returning a **replay-checked** integer model on `sat`. The warm, equality-sharing
/// alternative to the eager-Ackermann [`crate::euf::check_with_uf_arithmetic`].
///
/// A conjunctive query takes the fast-path: the literals are partitioned between
/// [`crate::euf_egraph::EufTheory`] and [`crate::lia_online::LiaTheory`] and the two
/// arrangements over the shared (interface) integer terms are reconciled by exchanging
/// `EUF`-entailed equalities and **model-based** case-splitting the remaining pairs
/// (`LIA` is not convex, so the split — not a single forced equality — is what keeps the
/// combination complete; `decide_conjunction`). A non-conjunctive (Boolean-structured)
/// query is driven by an enumerative `DPLL(T)` layer (`check_qf_uflia_boolean`) that
/// Tseitin-encodes the Boolean structure over the distinct theory atoms and decides each
/// propositional model's conjunction by that same combination. Either way a consistent
/// arrangement yields a combined model **replayed against the original assertions** before
/// being returned — the soundness gate, so a model the combination cannot justify yields
/// [`CheckResult::Unknown`], never a wrong `sat`. `unsat` is reported only when every
/// branch / propositional model is infeasible.
///
/// Returns [`CheckResult::Unknown`] (a sound decline, never a guess) when an atom is
/// outside `EUF` / `LIA` (`BV` / `Real` / arrays / quantifiers), when the Boolean
/// skeleton uses a connective the encoder does not cover, when the interface split or the
/// propositional enumeration exceeds an internal cap (depth, model count, atom count,
/// clauses, or `config.timeout`), or when arithmetic overflow / a resource limit made a
/// feasibility check inconclusive.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches the sibling
/// deciders for interchange.
pub fn check_qf_uflia_online(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // 1. The conjunctive fast-path: if every assertion flattens to a conjunction of
    //    literals, decide it directly by the model-based combination — the behaviour
    //    this module shipped with, kept verbatim.
    let mut literals: Vec<Literal> = Vec::new();
    let mut conjunctive = true;
    for &assertion in assertions {
        if !flatten_conjunction(arena, assertion, true, &mut literals) {
            conjunctive = false;
            break;
        }
    }
    // `flatten_conjunction` returns a leaf literal for any non-`And`/`Not` shape,
    // including a positive `or` / `ite` / Boolean leaf — those are not atoms. The
    // fast-path applies only when every flattened literal is a genuine theory atom (an
    // equality or an order atom); otherwise the Boolean layer handles it.
    if conjunctive && !literals.iter().all(|l| is_theory_atom(arena, l.atom)) {
        conjunctive = false;
    }
    if conjunctive {
        if literals.is_empty() {
            return Ok(decline("no UFLIA literals for the online combination path"));
        }
        let opaque_atoms = opaque_lia_order_literal_count(arena, &literals);
        if opaque_atoms > MAX_OPAQUE_BOOLEAN_ATOMS {
            return Ok(decline(large_opaque_online_detail(
                literals.len(),
                opaque_atoms,
            )));
        }
        return Ok(decide_conjunction(arena, &literals));
    }

    // 2. Boolean-structured QF_UFLIA: drive the combination from the real CDCL(T) layer —
    //    a single generic `Dpll` over the live `CombinedIncrementalLia` (EUF + LIA with
    //    registered interface-equality variables) over the extended Tseitin skeleton plus
    //    the interface structural clauses. The interface case-split is ordinary SAT
    //    branching on the registered interface vars (no private DFS enumeration).
    Ok(check_qf_uflia_boolean(arena, assertions, config))
}

/// Test-only entry that runs the Boolean-structured `DPLL(T)` layer with early
/// pruning toggleable and returns the enumeration metrics `(prunes_fired,
/// models_tried)` alongside the verdict. Lets the pruning-metric test prove that
/// early theory-conflict detection both fires and strictly reduces the number of
/// total propositional models enumerated, without disturbing the verdict. Not part
/// of the production surface.
#[doc(hidden)]
#[must_use]
pub fn check_qf_uflia_boolean_with_metrics(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    enable_early_prune: bool,
) -> (CheckResult, usize, usize) {
    let mut metrics = Metrics::default();
    let result = check_qf_uflia_boolean_enumerative(
        arena,
        assertions,
        config,
        enable_early_prune,
        Some(&mut metrics),
    );
    (result, metrics.prunes_fired, metrics.models_tried)
}

/// Test-only entry returning the Boolean-`DPLL(T)` verdict together with the
/// **combined-theory-propagation** fire count (slice 2): how many genuinely-entailed
/// literals the joint (Boolean + theory) propagation fixpoint assigned (or conflicts it
/// learned) across the search — so the slice-2 "propagation fires through the integrated
/// path" assertion can observe that theory propagation actually engages. Not part of the
/// production surface.
#[doc(hidden)]
#[must_use]
pub fn check_qf_uflia_boolean_prop_metrics(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> (CheckResult, usize) {
    let mut metrics = Metrics::default();
    let result =
        check_qf_uflia_boolean_enumerative(arena, assertions, config, true, Some(&mut metrics));
    (result, metrics.props_fired)
}

/// Decides a **conjunction** of `QF_UFLIA` literals by the model-based combination (the
/// original conjunctive core, factored out so both the fast-path and the Boolean
/// `DPLL(T)` layer call it). Returns a replay-checked model on `sat`, `Unsat` when every
/// interface branch is infeasible, and a conservative [`CheckResult::Unknown`] otherwise
/// (an unsupported atom, the depth cap, or a leaf model that did not replay).
pub(crate) fn decide_conjunction(arena: &mut TermArena, literals: &[Literal]) -> CheckResult {
    // 2. Partition the literals; decline an unsupported atom.
    let Some(part) = partition(arena, literals) else {
        return decline("atom outside QF_UFLIA for the online combination path");
    };

    // 3. The interface pairs. Each `EUF`-interface integer term (a UF argument /
    //    result) is paired with every other `EUF`-interface term AND every `LIA`-atom
    //    integer term, so the model-based split can equate a UF argument with the
    //    integer value(s) the `LIA` side pins. (Unlike `LRA`, an integer-tight bound
    //    such as `0 < x ∧ x < 2` forces `x = 1`; the constant `1` may be a UF argument
    //    only — `f(1)` — and never appear in a `LIA` atom, so a bare intersection would
    //    miss the load-bearing `(x, 1)` pair. Pairs with at least one `EUF`-interface
    //    endpoint suffice for congruence; a pure `LIA`-`LIA` pair adds no `EUF` fact.)
    let interface = interface_terms(arena, &part);
    let pairs = interface_pairs(&interface);
    if pairs.len() > MAX_SPLIT_DEPTH {
        return decline("too many interface pairs for the online combination split");
    }

    // 4. The initial EUF assertions (original equalities / disequalities). A
    //    single-theory EUF conflict is UNSAT.
    let euf_assertions = build_euf_assertions(arena, &part.euf);
    if euf_unsat(arena, &euf_assertions) {
        return CheckResult::Unsat;
    }

    // 5. Register the `LiaTheory` over the original LIA atoms PLUS, per shared pair,
    //    the three interface terms `s = t`, `s < t`, `s > t` (asserted by index in the
    //    DFS — the public `assert` surface, no dynamic atom registration). The
    //    original LIA atoms occupy indices `0..lia_atom_count`.
    let mut lia_atom_terms: Vec<TermId> = part.lia.iter().map(|l| l.atom).collect();
    let mut pair_atoms: Vec<PairAtoms> = Vec::with_capacity(pairs.len());
    for &(s, t) in &pairs {
        let Ok(eq) = arena.eq(s, t) else {
            return decline("interface equality term build failed");
        };
        let Ok(lt) = arena.int_lt(s, t) else {
            return decline("interface order term build failed");
        };
        let Ok(gt) = arena.int_gt(s, t) else {
            return decline("interface order term build failed");
        };
        let base = lia_atom_terms.len();
        lia_atom_terms.push(eq);
        lia_atom_terms.push(lt);
        lia_atom_terms.push(gt);
        pair_atoms.push(PairAtoms {
            eq: base,
            lt: base + 1,
            gt: base + 2,
        });
    }

    let mut lia = LiaTheory::new_with_opaque_apps(arena, &lia_atom_terms);
    for (index, lit) in part.lia.iter().enumerate() {
        if lia.assert(index, lit.value).is_err() {
            return CheckResult::Unsat;
        }
    }

    // 6. The interface case-split (DFS).
    run_interface_search(
        arena,
        literals,
        &part.euf,
        euf_assertions,
        &pairs,
        &pair_atoms,
        &mut lia,
    )
}

/// Runs the interface case-split DFS (step 6 of the conjunctive combination) over a
/// **prepared** `LiaTheory` whose atom indices are already the original `LIA` literals
/// (positions `0..part.lia.len()`) plus the per-pair interface atoms named by
/// `pair_atoms`. Factored out of [`decide_conjunction`] so the warm
/// [`crate::combined_theory_lia::CombinedTheoryLia`] runs the *exact same* DFS over its
/// persistent `LiaTheory`, guaranteeing the warm oracle returns the identical verdict to
/// the from-scratch core (the parallel-run equivalence gate).
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_interface_search(
    arena: &mut TermArena,
    literals: &[Literal],
    euf_atoms: &[Literal],
    euf_assertions: Vec<TermId>,
    pairs: &[(TermId, TermId)],
    pair_atoms: &[PairAtoms],
    lia: &mut LiaTheory,
) -> CheckResult {
    let mut search = Search {
        arena,
        literals,
        euf_atoms,
        euf_assertions,
        pairs,
        pair_atoms,
    };
    match search.run(lia, &mut Vec::new(), 0) {
        Outcome::Sat(model) => CheckResult::Sat(model),
        Outcome::Unsat => CheckResult::Unsat,
        Outcome::Unknown(detail) => decline(detail),
    }
}

/// The `LiaTheory` atom indices of a shared pair's three interface terms.
#[derive(Clone, Copy)]
pub(crate) struct PairAtoms {
    pub(crate) eq: usize,
    pub(crate) lt: usize,
    pub(crate) gt: usize,
}

/// The carried state for the interface DFS.
struct Search<'a> {
    arena: &'a mut TermArena,
    /// Every original literal — the replay target at a consistent leaf.
    literals: &'a [Literal],
    /// The `EUF` atom literals (for the leaf model's function interpretations).
    euf_atoms: &'a [Literal],
    /// The original `EUF` equality / disequality assertion terms.
    euf_assertions: Vec<TermId>,
    /// The shared pairs, in [`TermId`] order.
    pairs: &'a [(TermId, TermId)],
    /// The `LiaTheory` atom indices per shared pair.
    pair_atoms: &'a [PairAtoms],
}

/// The result of the interface search at a node.
enum Outcome {
    Sat(Model),
    Unsat,
    Unknown(&'static str),
}

impl Search<'_> {
    /// Explores the interface arrangement from pair `index` onward; `lia` holds the
    /// original `LIA` atoms plus the interface atoms asserted on the path, and `forced`
    /// records the `(pair_index, equal?)` decisions for the `EUF` classifier.
    fn run(
        &mut self,
        lia: &mut LiaTheory,
        forced: &mut Vec<(usize, bool)>,
        index: usize,
    ) -> Outcome {
        if forced.len() > MAX_SPLIT_DEPTH {
            return Outcome::Unknown("interface split exceeded the depth bound");
        }
        if index >= self.pairs.len() {
            return self.leaf(lia, forced);
        }
        let (s, t) = self.pairs[index];

        match self.euf_status(s, t, forced) {
            InterfaceStatus::Refuted => self.distinct(lia, forced, index),
            InterfaceStatus::Entailed => self.equal(lia, forced, index),
            // Try equal; a `Sat` wins immediately, an `Unsat` falls through to
            // distinct, and an `Unknown` still tries distinct (a sibling may be `Sat`)
            // before reporting the conservative `Unknown`.
            InterfaceStatus::Undetermined => match self.equal(lia, forced, index) {
                Outcome::Sat(model) => Outcome::Sat(model),
                Outcome::Unsat => self.distinct(lia, forced, index),
                Outcome::Unknown(detail) => match self.distinct(lia, forced, index) {
                    Outcome::Sat(model) => Outcome::Sat(model),
                    _ => Outcome::Unknown(detail),
                },
            },
        }
    }

    /// The `s = t` branch: assert the equality on the `LIA` side and recurse.
    fn equal(
        &mut self,
        lia: &mut LiaTheory,
        forced: &mut Vec<(usize, bool)>,
        index: usize,
    ) -> Outcome {
        let eq = self.pair_atoms[index].eq;
        lia.push();
        let outcome = if lia.assert(eq, true).is_err() {
            Outcome::Unsat
        } else {
            forced.push((index, true));
            let r = self.run(lia, forced, index + 1);
            forced.pop();
            r
        };
        lia.pop();
        outcome
    }

    /// The `s ≠ t` branch: a disequality on the `LIA` side is `s < t ∨ s > t`, so try
    /// each strict order; on the `EUF` side the pair is recorded distinct.
    fn distinct(
        &mut self,
        lia: &mut LiaTheory,
        forced: &mut Vec<(usize, bool)>,
        index: usize,
    ) -> Outcome {
        forced.push((index, false));
        let mut saw_unknown = false;
        for order in [self.pair_atoms[index].lt, self.pair_atoms[index].gt] {
            lia.push();
            let outcome = if lia.assert(order, true).is_err() {
                Outcome::Unsat
            } else {
                self.run(lia, forced, index + 1)
            };
            lia.pop();
            match outcome {
                Outcome::Sat(model) => {
                    forced.pop();
                    return Outcome::Sat(model);
                }
                Outcome::Unknown(_) => saw_unknown = true,
                Outcome::Unsat => {}
            }
        }
        forced.pop();
        if saw_unknown {
            Outcome::Unknown("interface distinct branch inconclusive")
        } else {
            Outcome::Unsat
        }
    }

    /// A consistent leaf: the `LIA` system holds the originals plus the chosen
    /// interface relations, and the `EUF` arrangement is consistent by construction.
    /// Build the combined model and **replay it against the original literals**.
    fn leaf(&mut self, lia: &mut LiaTheory, forced: &[(usize, bool)]) -> Outcome {
        // Defensive re-confirmation of EUF consistency at the leaf (the arrangement is
        // already EUF-consistent because `run` only takes branches `euf_status` allows).
        let augmented = self.augmented_euf(forced);
        if euf_unsat(self.arena, &augmented) {
            return Outcome::Unsat;
        }
        let Some(model) = self.combined_model(lia, &augmented) else {
            return Outcome::Unknown("combined model build failed (overflow / coverage)");
        };
        if replays_literals(self.arena, self.literals, &model) {
            Outcome::Sat(model)
        } else {
            // The arrangement is consistent in both theories (the leaf passed the
            // EUF/LIA checks) but the assembled model did not replay — the combination
            // could not *certify* a model here. This is a sound decline, NOT an UNSAT:
            // the offline decider may still find a model. Return Unknown so the search
            // reports a conservative `unknown` rather than a wrong `unsat`.
            Outcome::Unknown("combined leaf model did not replay")
        }
    }

    /// Builds the combined model: the `LIA` integer witness (integer symbol values) plus
    /// a function interpretation for every uninterpreted function, assembled from the
    /// integer values of the applications appearing in the query so the two theories
    /// agree on the shared terms.
    ///
    /// Scalar (`Bool` / `BitVec`) functions are taken from the `EUF` e-graph model;
    /// integer-sorted functions — which the `EUF` model builder does not cover — are
    /// built here from the `LIA` witness: each application `f(a₁,…)` is assigned the
    /// value its result class must take, keyed by the *integer values* of its arguments
    /// under the `LIA` model (so equal-argument applications share a result, matching
    /// congruence). The replay check then validates the whole assembly.
    fn combined_model(&mut self, lia: &LiaTheory, augmented: &[TermId]) -> Option<Model> {
        let mut model = lia.integer_model()?;
        complete_non_int_symbols(self.arena, &mut model);
        let assignment = model.to_assignment();

        // Scalar UF interpretations from the EUF e-graph model (Bool/BitVec results).
        let euf_atom_terms: Vec<TermId> = self.euf_atoms.iter().map(|l| l.atom).collect();
        let mut euf = EufTheory::new(self.arena, &euf_atom_terms);
        for (index, lit) in self.euf_atoms.iter().enumerate() {
            if euf.assert(index, lit.value).is_err() {
                return None; // inconsistent (should not happen at a checked leaf)
            }
        }
        if let Some(euf_model) = euf.model(self.arena) {
            for (func, interp) in euf_model.functions() {
                model.set_function(func, interp.clone());
            }
        }

        // Integer-sorted UF interpretations, built from the LIA witness. Collect every
        // integer-result application in the query, deterministically.
        let mut apps: BTreeSet<TermId> = BTreeSet::new();
        for lit in self.literals {
            collect_int_apps(self.arena, lit.atom, &mut apps);
        }
        if apps.is_empty() {
            return Some(model);
        }

        // Congruence classes over the augmented EUF assertions (originals + chosen
        // interface relations): equal terms must share an integer value. Each
        // application's result value is its class value — pinned by any LIA-valued class
        // member, else fresh-and-distinct. This makes the interpretation respect both
        // the asserted equalities and functionality (equal arguments ⇒ equal results,
        // since congruence merges such applications).
        let mut classes = Congruence::new();
        for &assertion in augmented {
            classes.absorb(self.arena, assertion);
        }
        let class_value = classes.assign_int_values(self.arena, &assignment, &apps);

        // Assign every integer *symbol* (including EUF-only ones the LIA witness did not
        // pin, e.g. a disequality side never in a LIA atom) its congruence-class value,
        // so the combined model is total over the integer symbols and the replay can
        // evaluate every application argument.
        for term in classes.int_symbols(self.arena) {
            if let TermNode::Symbol(symbol) = self.arena.node(term) {
                let symbol = *symbol;
                if model.get(symbol).is_none() {
                    let root = classes.root_of(term);
                    if let Some(value) = class_value.get(&root) {
                        model.set(symbol, value.clone());
                    }
                }
            }
        }
        // Rebuild the assignment now that every integer symbol has a value.
        let assignment = model.to_assignment();

        let mut tables: BTreeMap<axeyum_ir::FuncId, IntTable> = BTreeMap::new();
        for &app in &apps {
            let TermNode::App {
                op: Op::Apply(func),
                args,
            } = self.arena.node(app)
            else {
                continue;
            };
            let func = *func;
            let args = args.clone();
            let mut arg_values: Vec<Value> = Vec::with_capacity(args.len());
            for &a in &args {
                // An argument that is itself an application uses its own class value
                // (its result is not yet in the function table); a non-application
                // evaluates directly.
                let value = if is_int_app(self.arena, a) {
                    class_value.get(&classes.root_of(a)).cloned()?
                } else {
                    eval(self.arena, a, &assignment).ok()?
                };
                arg_values.push(value);
            }
            let result = class_value.get(&classes.root_of(app)).cloned()?;
            let (_, params, result_sort) = self.arena.function(func);
            let entry = tables
                .entry(func)
                .or_insert_with(|| IntTable::new(params.to_vec(), result_sort));
            entry.define(arg_values, result);
        }
        for (func, table) in tables {
            model.set_function(func, table.into_func_value());
        }

        Some(model)
    }

    /// The `EUF` status of `(s, t)` given the original assertions plus the equalities /
    /// disequalities forced on the current path.
    fn euf_status(&mut self, s: TermId, t: TermId, forced: &[(usize, bool)]) -> InterfaceStatus {
        let augmented = self.augmented_euf(forced);
        classify_interface_equalities(self.arena, &augmented, &[(s, t)])
            .first()
            .map_or(InterfaceStatus::Undetermined, |classified| classified.1)
    }

    /// The `EUF` assertion list augmented with the interface relations chosen so far.
    fn augmented_euf(&mut self, forced: &[(usize, bool)]) -> Vec<TermId> {
        let mut out = self.euf_assertions.clone();
        for &(pair_index, equal) in forced {
            let (s, t) = self.pairs[pair_index];
            if let Ok(eq) = self.arena.eq(s, t) {
                if equal {
                    out.push(eq);
                } else if let Ok(ne) = self.arena.not(eq) {
                    out.push(ne);
                }
            }
        }
        out
    }
}

/// Flattens `term` (asserted at `polarity`) into a conjunction of literals. Descends
/// through `And` (positive), `not` (flipping polarity), and `¬(or ..) ≡ ⋀ ¬disjunct`.
/// Returns `false` for any other Boolean structure (a positive disjunction,
/// `ite`/`xor`/`implies`) — a non-conjunctive skeleton this slice declines.
pub(crate) fn flatten_conjunction(
    arena: &TermArena,
    term: TermId,
    polarity: bool,
    out: &mut Vec<Literal>,
) -> bool {
    match arena.node(term) {
        // A satisfied constant conjunct (`true` at this polarity) drops silently; a
        // contradiction constant (the other polarity) falls through to the wildcard
        // arm, recorded as an atom the partition rejects (declining the query soundly).
        TermNode::BoolConst(b) if *b == polarity => true,
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if polarity => {
            let args = args.clone();
            args.iter()
                .all(|&a| flatten_conjunction(arena, a, true, out))
        }
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if !polarity => {
            let args = args.clone();
            args.iter()
                .all(|&a| flatten_conjunction(arena, a, false, out))
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => {
            let inner = args[0];
            flatten_conjunction(arena, inner, !polarity, out)
        }
        // An atom (equality / order / predicate) or a bare Boolean leaf.
        _ => {
            out.push(Literal {
                atom: term,
                value: polarity,
            });
            true
        }
    }
}

/// The classification of the flattened literals into the two theories.
pub(crate) struct Partition {
    pub(crate) lia: Vec<Literal>,
    pub(crate) euf: Vec<Literal>,
}

/// Partitions the flattened literals, or `None` if any literal is outside `QF_UFLIA`
/// (a non-`LIA`, non-`EUF` atom — `BV` / `Real` / array / quantifier / bare predicate).
pub(crate) fn partition(arena: &TermArena, literals: &[Literal]) -> Option<Partition> {
    let mut lia = Vec::new();
    let mut euf = Vec::new();

    for &lit in literals {
        match arena.node(lit.atom) {
            // Integer order atoms are pure LIA.
            TermNode::App {
                op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
                args,
            } => {
                if !is_linear_int_or_opaque(arena, args[0])
                    || !is_linear_int_or_opaque(arena, args[1])
                {
                    return None;
                }
                lia.push(lit);
            }
            // An equality: a linear integer equality is LIA; one touching a UF
            // application (or a non-linear integer side) is EUF; a linear integer
            // equality with a UF side is both.
            TermNode::App { op: Op::Eq, args } => {
                let (a, b) = (args[0], args[1]);
                let int = arena.sort_of(a) == Sort::Int;
                let has_uf = mentions_uf(arena, a) || mentions_uf(arena, b);
                let linear = int && is_linear_int(arena, a) && is_linear_int(arena, b);
                if linear {
                    lia.push(lit);
                }
                if has_uf || (int && !linear) {
                    euf.push(lit);
                }
                if !linear && !has_uf {
                    // Neither a linear-integer equality nor UF-touching: out of scope
                    // (e.g. a Bool equality, or a non-linear integer equality with no
                    // UF).
                    return None;
                }
            }
            _ => return None,
        }
    }

    Some(Partition { lia, euf })
}

/// Whether `term` is a genuine `QF_UFLIA` theory atom — an equality (`(= s t)`) or an
/// integer order atom (`<`, `<=`, `>`, `>=`). Used to tell a conjunction of integer
/// atoms (the fast-path) from a flattened literal that is itself Boolean structure (a
/// positive `or` / `ite` / Boolean leaf), which the Boolean layer must handle.
pub(crate) fn is_theory_atom(arena: &TermArena, term: TermId) -> bool {
    is_uflia_theory_atom(arena, term)
}

fn is_uflia_theory_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            args,
        } => is_linear_int_or_opaque(arena, args[0]) && is_linear_int_or_opaque(arena, args[1]),
        TermNode::App { op: Op::Eq, args } => {
            let (a, b) = (args[0], args[1]);
            let int = arena.sort_of(a) == Sort::Int;
            let has_uf = mentions_uf(arena, a) || mentions_uf(arena, b);
            int || has_uf
        }
        _ => false,
    }
}

fn is_opaque_lia_order_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            args,
        } => {
            is_linear_int_or_opaque(arena, args[0])
                && is_linear_int_or_opaque(arena, args[1])
                && (!is_linear_int(arena, args[0]) || !is_linear_int(arena, args[1]))
        }
        _ => false,
    }
}

fn opaque_lia_order_literal_count(arena: &TermArena, literals: &[Literal]) -> usize {
    literals
        .iter()
        .filter(|lit| is_opaque_lia_order_atom(arena, lit.atom))
        .count()
}

fn opaque_lia_order_atom_count(arena: &TermArena, atoms: &[TermId]) -> usize {
    atoms
        .iter()
        .filter(|&&atom| is_opaque_lia_order_atom(arena, atom))
        .count()
}

fn large_opaque_online_detail(total_atoms: usize, opaque_atoms: usize) -> String {
    format!(
        "too many theory atoms for opaque-app online UFLIA: opaque_app_order_atoms={opaque_atoms} \
         > {MAX_OPAQUE_BOOLEAN_ATOMS}, total={total_atoms}"
    )
}

/// The `EUF` assertion terms for the `EUF` literals: a `true` equality literal is its
/// atom, a `false` one its negation `(not (= ..))`. Consumed by
/// [`classify_interface_equalities`] (which reads exactly those two shapes).
pub(crate) fn build_euf_assertions(arena: &mut TermArena, euf: &[Literal]) -> Vec<TermId> {
    let mut out = Vec::with_capacity(euf.len());
    for lit in euf {
        if lit.value {
            out.push(lit.atom);
        } else if let Ok(ne) = arena.not(lit.atom) {
            out.push(ne);
        }
    }
    out
}

/// Whether `term` is a linear integer expression (integer-sorted, built only from
/// integer constants, integer symbols, `+`/`-`/unary `-`, and constant-scaled `*`).
fn is_linear_int(arena: &TermArena, term: TermId) -> bool {
    if arena.sort_of(term) != Sort::Int {
        return false;
    }
    match arena.node(term) {
        TermNode::IntConst(_) | TermNode::Symbol(_) => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => is_linear_int(arena, args[0]),
        TermNode::App {
            op: Op::IntAdd | Op::IntSub,
            args,
        } => !args.is_empty() && args.iter().all(|&arg| is_linear_int(arena, arg)),
        TermNode::App {
            op: Op::IntMul,
            args,
        } => linear_product(arena, args, is_linear_int),
        _ => false,
    }
}

fn linear_product(
    arena: &TermArena,
    args: &[TermId],
    linear: fn(&TermArena, TermId) -> bool,
) -> bool {
    let mut nonconstant = 0usize;
    for &arg in args {
        if is_int_constant_expr(arena, arg) {
            continue;
        }
        if !linear(arena, arg) {
            return false;
        }
        nonconstant += 1;
        if nonconstant > 1 {
            return false;
        }
    }
    true
}

/// Whether `term` is linear integer arithmetic when Int-sorted UF applications are
/// treated as fresh opaque integer variables. The online UFLIA path uses this only for
/// conflict/UNSAT reasoning; satisfiable opaque abstractions still require a separate
/// model-lifting path and therefore degrade to `Unknown` rather than `Sat`.
fn is_linear_int_or_opaque(arena: &TermArena, term: TermId) -> bool {
    if arena.sort_of(term) != Sort::Int {
        return false;
    }
    match arena.node(term) {
        TermNode::IntConst(_)
        | TermNode::Symbol(_)
        | TermNode::App {
            op: Op::Apply(_), ..
        } => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => is_linear_int_or_opaque(arena, args[0]),
        TermNode::App {
            op: Op::IntAdd | Op::IntSub,
            args,
        } => !args.is_empty() && args.iter().all(|&arg| is_linear_int_or_opaque(arena, arg)),
        TermNode::App {
            op: Op::IntMul,
            args,
        } => linear_product(arena, args, is_linear_int_or_opaque),
        _ => false,
    }
}

/// Whether `term` is an integer constant expression, so it can be a scalar factor
/// in a linear product. This mirrors the arithmetic collector's ability to
/// linearize parsed forms such as `(- 1)` before deciding whether a product is
/// constant-scaled.
fn is_int_constant_expr(arena: &TermArena, term: TermId) -> bool {
    if arena.sort_of(term) != Sort::Int {
        return false;
    }
    match arena.node(term) {
        TermNode::IntConst(_) => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => args.len() == 1 && is_int_constant_expr(arena, args[0]),
        TermNode::App {
            op: Op::IntAdd | Op::IntSub | Op::IntMul,
            args,
        } => !args.is_empty() && args.iter().all(|&arg| is_int_constant_expr(arena, arg)),
        _ => false,
    }
}

/// Whether `term` is an integer-sorted uninterpreted-function application.
fn is_int_app(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App {
            op: Op::Apply(_),
            ..
        }
    ) && arena.sort_of(term) == Sort::Int
}

/// Whether `term` mentions an uninterpreted-function application anywhere.
fn mentions_uf(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::Apply(_), ..
        } => true,
        TermNode::App { args, .. } => args.iter().any(|&a| mentions_uf(arena, a)),
        _ => false,
    }
}

/// The interface integer terms, split into the `EUF`-interface set (the **atomic**
/// integer UF arguments — symbols and constants — over which a congruence-relevant
/// equality can be exchanged) and the `LIA`-atom atomic integer subterm set. Both
/// deterministic — stored as sorted [`BTreeSet`]s.
///
/// Only atomic terms (integer symbols / constants) are interface candidates: a
/// compound UF application (e.g. `f(x)`) is valued through the assembled function table
/// and reconciled by congruence, not by an explicit interface split, and a linear `LIA`
/// term is determined by its symbol values — so splitting them adds no fact while
/// exploding the search.
pub(crate) struct Interface {
    /// Atomic integer terms occurring as a UF argument (a symbol / constant).
    pub(crate) euf: BTreeSet<TermId>,
    /// Atomic integer subterms of the `LIA` atoms (symbols / constants).
    pub(crate) lia: BTreeSet<TermId>,
}

/// Collects the [`Interface`] integer terms of the two partitions.
pub(crate) fn interface_terms(arena: &TermArena, part: &Partition) -> Interface {
    let mut euf: BTreeSet<TermId> = BTreeSet::new();
    let mut lia: BTreeSet<TermId> = BTreeSet::new();

    for lit in &part.euf {
        if let TermNode::App { args, .. } = arena.node(lit.atom) {
            for &a in args {
                collect_uf_interface(arena, a, &mut euf);
            }
        }
    }
    for lit in &part.lia {
        if let TermNode::App { args, .. } = arena.node(lit.atom) {
            for &a in args {
                collect_int_subterms(arena, a, &mut lia);
            }
        }
    }

    euf.retain(|&t| is_atomic_int(arena, t));
    lia.retain(|&t| is_atomic_int(arena, t));
    Interface { euf, lia }
}

/// Whether `term` is an atomic integer term: an integer symbol or integer constant
/// (the interface-split candidates — a `LIA`-valuable, congruence-relevant atom).
fn is_atomic_int(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Int
        && matches!(
            arena.node(term),
            TermNode::Symbol(_) | TermNode::IntConst(_)
        )
}

/// The interface case-split pairs: every unordered pair of distinct atomic integer
/// terms with **at least one `EUF`-interface endpoint**, drawn from `EUF`-interface ∪
/// `LIA`-atom atomic terms. (A pure `LIA`-`LIA` pair would add no `EUF` congruence
/// fact, so it is excluded — it only inflates the split. Pairing a UF argument with a
/// `LIA` constant matters because integer tightening such as `0 < x ∧ x < 2` forces
/// `x = 1`, where `1` may be a UF argument only — `f(1)` — and never in a `LIA` atom.)
/// Deterministic: the candidate set is the sorted union, pairs in [`TermId`] order.
pub(crate) fn interface_pairs(interface: &Interface) -> Vec<(TermId, TermId)> {
    let candidates: BTreeSet<TermId> = interface.euf.union(&interface.lia).copied().collect();
    let candidates: Vec<TermId> = candidates.into_iter().collect();
    let mut pairs = Vec::new();
    for (i, &s) in candidates.iter().enumerate() {
        for &t in &candidates[i + 1..] {
            // Keep the pair iff it can change the EUF arrangement: at least one side is
            // an EUF-interface term.
            if interface.euf.contains(&s) || interface.euf.contains(&t) {
                pairs.push((s, t));
            }
        }
    }
    pairs
}

/// Collects the integer-sorted terms `EUF`-relevant under `term`: an integer-sorted UF
/// application and the integer-sorted arguments of any UF application.
fn collect_uf_interface(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    let is_int = arena.sort_of(term) == Sort::Int;
    match arena.node(term) {
        TermNode::App {
            op: Op::Apply(_),
            args,
        } => {
            if is_int {
                out.insert(term);
            }
            for &a in args {
                if arena.sort_of(a) == Sort::Int {
                    out.insert(a);
                }
                collect_uf_interface(arena, a, out);
            }
        }
        TermNode::App { args, .. } => {
            for &a in args {
                collect_uf_interface(arena, a, out);
            }
        }
        _ => {}
    }
}

/// Collects every integer-sorted subterm of `term` (the `LIA` view).
fn collect_int_subterms(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if arena.sort_of(term) == Sort::Int {
        out.insert(term);
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &a in args {
            collect_int_subterms(arena, a, out);
        }
    }
}

/// Whether the `EUF` assertions are already UNSAT by congruence — an asserted
/// disequality whose sides are congruent (detected by classifying each disequality's
/// `(a, b)` against the full assertion set: an `Entailed` verdict on a pair that is
/// also asserted distinct is the conflict).
pub(crate) fn euf_unsat(arena: &TermArena, euf_assertions: &[TermId]) -> bool {
    let mut diseq_pairs: Vec<(TermId, TermId)> = Vec::new();
    for &assertion in euf_assertions {
        if let TermNode::App {
            op: Op::BoolNot,
            args,
        } = arena.node(assertion)
        {
            if let TermNode::App {
                op: Op::Eq,
                args: eq_args,
            } = arena.node(args[0])
            {
                diseq_pairs.push((eq_args[0], eq_args[1]));
            }
        }
    }
    if diseq_pairs.is_empty() {
        return false;
    }
    classify_interface_equalities(arena, euf_assertions, &diseq_pairs)
        .iter()
        .any(|&(_, status)| status == InterfaceStatus::Entailed)
}

/// Whether `model` satisfies every literal (`atom == value`) under the ground
/// evaluator. Any evaluation error, non-Boolean, or mismatch makes it not replay
/// (→ no `sat`, never a wrong one).
fn replays_literals(arena: &TermArena, literals: &[Literal], model: &Model) -> bool {
    let assignment: Assignment = model.to_assignment();
    literals.iter().all(|lit| {
        matches!(
            eval(arena, lit.atom, &assignment),
            Ok(Value::Bool(b)) if b == lit.value
        )
    })
}

/// Completes non-integer symbols in a combined `EUF+LIA` model.
///
/// `LiaTheory::integer_model` only assigns integer symbols. Mixed AUFLIA terms
/// can use array symbols as arguments to integer-result UF applications, and the
/// function-table projection must evaluate those arguments to concrete values.
/// Any well-founded value of the right sort is enough for unconstrained
/// non-integer symbols; replay remains the gate that rejects a bad assembly.
fn complete_non_int_symbols(arena: &TermArena, model: &mut Model) {
    for (symbol, _name, sort) in arena.symbols() {
        if sort == Sort::Int || model.get(symbol).is_some() {
            continue;
        }
        if let Some(value) = well_founded_default(arena, sort) {
            model.set(symbol, value);
        }
    }
}

/// Collects every integer-result uninterpreted-function application under `term`
/// (including nested ones), deterministically into `out`.
fn collect_int_apps(arena: &TermArena, term: TermId, out: &mut BTreeSet<TermId>) {
    if let TermNode::App { op, args } = arena.node(term) {
        if matches!(op, Op::Apply(_)) && arena.sort_of(term) == Sort::Int {
            out.insert(term);
        }
        let args = args.clone();
        for a in args {
            collect_int_apps(arena, a, out);
        }
    }
}

/// A congruence closure over the `EUF` assertion terms, used to assign each integer
/// congruence class one integer value when building the combined model. Wraps an
/// [`axeyum_egraph::EGraph`] with a term→e-node interner so structurally identical
/// terms share a node and congruence (equal arguments ⇒ equal applications) holds.
struct Congruence {
    egraph: axeyum_egraph::EGraph,
    decls: BTreeMap<String, u32>,
    nodes: BTreeMap<TermId, axeyum_egraph::ENodeId>,
    next_decl: u32,
}

impl Congruence {
    fn new() -> Self {
        Self {
            egraph: axeyum_egraph::EGraph::new(),
            decls: BTreeMap::new(),
            nodes: BTreeMap::new(),
            next_decl: 0,
        }
    }

    fn decl(&mut self, key: String) -> u32 {
        if let Some(&d) = self.decls.get(&key) {
            return d;
        }
        let d = self.next_decl;
        self.next_decl += 1;
        self.decls.insert(key, d);
        d
    }

    /// Interns `term` (and its subterms) into the e-graph, returning its e-node.
    fn node(&mut self, arena: &TermArena, term: TermId) -> axeyum_egraph::ENodeId {
        if let Some(&n) = self.nodes.get(&term) {
            return n;
        }
        let n = match arena.node(term) {
            TermNode::App { op, args } => {
                let args: Vec<TermId> = args.to_vec();
                let kids: Vec<axeyum_egraph::ENodeId> =
                    args.iter().map(|&a| self.node(arena, a)).collect();
                let decl = self.decl(format!("op:{op:?}"));
                self.egraph.add(decl, &kids)
            }
            TermNode::Symbol(s) => {
                let decl = self.decl(format!("sym:{}", s.index()));
                self.egraph.add(decl, &[])
            }
            other => {
                let decl = self.decl(format!("const:{other:?}"));
                self.egraph.add(decl, &[])
            }
        };
        self.nodes.insert(term, n);
        n
    }

    /// Merges the sides of a top-level `(= a b)` assertion (ignores disequalities and
    /// other shapes — they do not add equalities).
    fn absorb(&mut self, arena: &TermArena, assertion: TermId) {
        if let TermNode::App { op: Op::Eq, args } = arena.node(assertion) {
            let (l, r) = (args[0], args[1]);
            let nl = self.node(arena, l);
            let nr = self.node(arena, r);
            self.egraph.merge(nl, nr, 0);
        }
    }

    /// The class root of `term`.
    fn root_of(&mut self, term: TermId) -> axeyum_egraph::ENodeId {
        let n = self.node_for(term);
        self.egraph.root(n)
    }

    /// The interned integer-sorted symbol terms (for assigning their model values), as a
    /// stable, sorted snapshot so iteration order is deterministic.
    fn int_symbols(&self, arena: &TermArena) -> Vec<TermId> {
        let mut out: Vec<TermId> = self
            .nodes
            .keys()
            .copied()
            .filter(|&t| {
                arena.sort_of(t) == Sort::Int && matches!(arena.node(t), TermNode::Symbol(_))
            })
            .collect();
        out.sort_unstable();
        out
    }

    /// The e-node for an already-interned `term`, interning lazily if needed. (Apps
    /// reached here are always already interned via `absorb`/`assign_int_values`.)
    fn node_for(&mut self, term: TermId) -> axeyum_egraph::ENodeId {
        self.nodes.get(&term).copied().unwrap_or_else(|| {
            // Not yet interned (a standalone app): interning without an arena would be
            // impossible, so this path is unreachable in practice — `assign_int_values`
            // interns every app first. Fall back to a fresh nullary node.
            let decl = self.decl(format!("app:{}", term.index()));
            self.egraph.add(decl, &[])
        })
    }

    /// Assigns each integer congruence class an integer value: any class member that
    /// evaluates under `assignment` (an integer symbol / constant / linear term) pins
    /// the class; otherwise a fresh value distinct from every pinned and
    /// previously-issued value. Returns the class-root → value map (for the application
    /// result lookups). Every application in `apps` is interned first so its class root
    /// is known.
    fn assign_int_values(
        &mut self,
        arena: &TermArena,
        assignment: &Assignment,
        apps: &BTreeSet<TermId>,
    ) -> BTreeMap<axeyum_egraph::ENodeId, Value> {
        // Intern every application and its arguments so the classes are complete.
        for &app in apps {
            let _ = self.node(arena, app);
        }

        // Gather every interned integer term, grouped by class root.
        let terms: Vec<TermId> = self.nodes.keys().copied().collect();
        let mut by_root: BTreeMap<axeyum_egraph::ENodeId, Vec<TermId>> = BTreeMap::new();
        for term in terms {
            if arena.sort_of(term) == Sort::Int {
                let root = self.root_of(term);
                by_root.entry(root).or_default().push(term);
            }
        }

        let mut used: BTreeSet<i128> = BTreeSet::new();
        let mut class_value: BTreeMap<axeyum_egraph::ENodeId, Value> = BTreeMap::new();
        // First pass: pin every class that has an evaluable member.
        for (root, members) in &by_root {
            for &m in members {
                if let Ok(Value::Int(value)) = eval(arena, m, assignment) {
                    class_value.insert(*root, Value::Int(value));
                    used.insert(value);
                    break;
                }
            }
        }
        // Second pass: fresh distinct values for the unpinned classes.
        let mut next: i128 = 0;
        for root in by_root.keys() {
            if class_value.contains_key(root) {
                continue;
            }
            while used.contains(&next) {
                next = match next.checked_add(1) {
                    Some(v) => v,
                    None => return class_value, // overflow: caller declines via missing key
                };
            }
            used.insert(next);
            class_value.insert(*root, Value::Int(next));
        }
        class_value
    }
}

/// An integer-valued function interpretation under construction: argument-`Value`
/// tuples → result `Value`, materialized into a [`FuncValue`] for the model.
struct IntTable {
    params: Vec<Sort>,
    result: Sort,
    entries: Vec<(Vec<Value>, Value)>,
}

impl IntTable {
    fn new(params: Vec<Sort>, result: Sort) -> Self {
        Self {
            params,
            result,
            entries: Vec::new(),
        }
    }

    /// Records `args → result`, keeping the first binding for a given argument tuple
    /// (functionality — congruence already guarantees consistency at a checked leaf).
    fn define(&mut self, args: Vec<Value>, result: Value) {
        if self.entries.iter().any(|(a, _)| *a == args) {
            return;
        }
        self.entries.push((args, result));
    }

    /// Materializes the interpretation. The default is the first defined result (any
    /// value of the result sort is sound — the query only constrains defined points).
    fn into_func_value(self) -> FuncValue {
        let default = self
            .entries
            .first()
            .map_or(Value::Int(0), |(_, v)| v.clone());
        let mut fv = FuncValue::constant_value(self.params, self.result, default);
        for (args, result) in self.entries {
            fv = fv.define_value(&args, result);
        }
        fv
    }
}

// --- The Boolean (DPLL(T)) layer over the conjunctive combination. ----------
//
// Full QF_UFLIA with arbitrary Boolean structure: Tseitin-encode the skeleton over one
// proposition per distinct theory atom, enumerate propositional models with a
// self-contained DPLL search, and decide each total model's conjunction with the
// conjunctive combination [`decide_conjunction`] above (the theory oracle). The search
// prunes with theory-conflict blocking clauses (the negation of an UNSAT model's
// theory-literal assignment). It is the sound enumerative DPLL(T): SAT if some model's
// combination is consistent (replay-checked), UNSAT if every model is blocked, and a
// conservative Unknown on any cap or an Unknown combination.

/// A propositional literal in the Boolean skeleton: a variable index and polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoolLit {
    var: usize,
    positive: bool,
}

impl BoolLit {
    fn negate(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// Decides a Boolean-structured `QF_UFLIA` query by the **real `CDCL(T)`** layer
/// (slice 3c-lia): a single generic [`crate::lra_online::Dpll`] drives a
/// [`crate::combined_theory_lia::CombinedIncrementalLia`] (the live `EUF` + `LIA`
/// combination with registered interface-equality variables) over the **extended**
/// Tseitin skeleton (theory atoms ++ interface `eq`/`lt`/`gt` vars ++ Tseitin auxiliaries)
/// plus the interface **structural clauses** (`eq ∨ lt ∨ gt` totality + pairwise
/// exclusion). The `Dpll`'s joint unit + theory propagation and `1-UIP` conflict analysis
/// now span the Boolean, theory, **and** interface-equality literals: the interface
/// case-split that the retired [`BoolSearch`] enumeration ran as a private DFS is now
/// ordinary `SAT` branching on the registered interface variables.
///
/// On a Boolean- and theory-consistent total assignment the original theory atoms' truth
/// values are read off the `Dpll` leaf and the corresponding conjunction is handed to the
/// trusted conjunctive core [`decide_conjunction`], which rebuilds and **replays** the
/// combined **integer** model — the soundness gate. The verdict is translated to the
/// [`check_qf_uflia_online`] contract: `Sat` (replay-checked) on a replaying leaf model,
/// `Unsat` on a root-level refutation, and a conservative [`CheckResult::Unknown`]
/// otherwise (a leaf whose model did not rebuild / replay, or any cap). **Never a wrong
/// `Unsat`**: a leaf the conjunctive core cannot certify degrades to `Unknown`.
///
/// Falls back to the retained enumerative layer ([`check_qf_uflia_boolean_enumerative`])
/// only when the incremental combined state cannot be built (an arena failure or an
/// oversized interface split) — a sound decline-or-enumerate, never a wrong verdict.
fn check_qf_uflia_boolean(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> CheckResult {
    // The distinct theory atoms over the whole assertion set become propositional
    // variables 0..atom_count (deterministic left-to-right scan).
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &a in assertions {
        collect_uflia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return decline("no UFLIA atoms for the online combination boolean layer");
    }
    if atom_terms.len() > MAX_BOOLEAN_ATOMS {
        return decline(format!(
            "too many theory atoms for the online combination boolean layer: {} > {}",
            atom_terms.len(),
            MAX_BOOLEAN_ATOMS
        ));
    }
    let opaque_atoms = opaque_lia_order_atom_count(arena, &atom_terms);
    if opaque_atoms > MAX_OPAQUE_BOOLEAN_ATOMS {
        return decline(large_opaque_online_detail(atom_terms.len(), opaque_atoms));
    }
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return timeout_unknown("timeout in the online combination boolean layer");
    }

    // Build the live combined state: it registers the interface eq/lt/gt variables beyond
    // the original `atom_count`. If it cannot be built, fall back to the enumerative layer.
    let Some(combined) = crate::combined_theory_lia::CombinedIncrementalLia::new_with_deadline(
        arena,
        &atom_terms,
        deadline,
    ) else {
        return check_qf_uflia_boolean_enumerative(arena, assertions, config, true, None);
    };
    cdclt_combined(arena, assertions, &atom_terms, combined, deadline)
}

/// The real-`CDCL(T)` body (slice 3c-lia): build the extended skeleton (theory atoms ++
/// interface vars ++ Tseitin auxiliaries) and the interface structural clauses, run the
/// generic [`crate::lra_online::Dpll`] over
/// [`crate::combined_theory_lia::CombinedIncrementalLia`], and translate the outcome to the
/// verdict contract (rebuilding + replaying the leaf **integer** model through
/// [`decide_conjunction`]).
fn cdclt_combined(
    arena: &mut TermArena,
    assertions: &[TermId],
    atom_terms: &[TermId],
    mut combined: crate::combined_theory_lia::CombinedIncrementalLia,
    deadline: Option<Instant>,
) -> CheckResult {
    let atom_count = atom_terms.len();
    let interface_count = combined.interface_pairs().len() * 3;
    // The combined variable count: theory atoms, then the three interface vars per pair.
    // Tseitin auxiliaries are numbered *after* this block so they never collide with the
    // interface variables `CombinedIncrementalLia` registered at `atom_count..combined_count`.
    let combined_count = atom_count + interface_count;

    let mut enc = BoolEncoder::with_reserved(atom_terms, combined_count);
    let mut bool_clauses: Vec<Vec<BoolLit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut bool_clauses) else {
            return decline(format!(
                "boolean skeleton outside the online combination encoder: {}",
                enc.unsupported_detail()
            ));
        };
        if bool_clauses.len() > MAX_BOOLEAN_CLAUSES {
            return decline("too many clauses for the online combination boolean layer");
        }
        bool_clauses.push(vec![BoolLit {
            var: top,
            positive: true,
        }]);
    }
    // The interface structural clauses (eq ∨ lt ∨ gt totality + pairwise exclusion) over
    // the registered interface variables — so the SAT layer branches the case-split.
    for structural in combined.structural_clauses() {
        bool_clauses.push(
            structural
                .into_iter()
                .map(|(var, positive)| BoolLit { var, positive })
                .collect(),
        );
    }

    let lit_clauses: Vec<Vec<crate::lra_online::Lit>> = bool_clauses
        .into_iter()
        .map(|clause| {
            clause
                .into_iter()
                .map(|l| crate::lra_online::Lit {
                    var: l.var,
                    positive: l.positive,
                })
                .collect()
        })
        .collect();

    if deadline.is_some_and(|d| Instant::now() >= d) {
        return timeout_unknown("timeout in the online combination boolean layer");
    }

    // The generic Dpll drives the live combination: vars `0..combined_count` are forwarded
    // to `CombinedIncrementalLia` (theory atoms + interface vars); the rest are Tseitin aux.
    let mut solver = crate::lra_online::Dpll::new(enc.var_count, combined_count, lit_clauses);
    match solver.solve_with_deadline(&mut combined, deadline) {
        Some(true) => return CheckResult::Unsat,
        Some(false) => {}
        None => {
            return timeout_unknown("timeout in the online combination boolean layer");
        }
    }
    // A Boolean- and theory-consistent total assignment. Read the original theory atoms'
    // truth values off the leaf and rebuild + replay the combined integer model through the
    // trusted conjunctive core. NEVER a wrong Unsat: an unbuildable / non-replaying leaf
    // degrades to Unknown.
    let mut literals: Vec<Literal> = Vec::with_capacity(atom_count);
    for (var, &atom) in atom_terms.iter().enumerate() {
        if let Some(value) = solver.value_of(var) {
            literals.push(Literal { atom, value });
        }
    }
    match decide_conjunction(arena, &literals) {
        CheckResult::Sat(model) => CheckResult::Sat(model),
        // The Dpll found the combined theory consistent at this leaf, but the conjunctive
        // core could not certify a replaying model. Degrade — never call it Unsat.
        CheckResult::Unsat | CheckResult::Unknown(_) => {
            decline("combined CDCL(T) leaf did not rebuild a replaying model")
        }
    }
}

/// One learned 1-UIP clause from the real-`CDCL(T)` combined driver, reported over
/// **terms** (the slice-3c-lia soundness-gate harness shape): the clause literals as
/// `(refuting atom term, polarity)` pairs (so the test re-validates entailment by
/// conjoining their negation), whether it is a pure theory lemma, and the level-0 atom
/// facts `(term, value)` it rests on.
#[cfg(test)]
pub(crate) type CombinedLemmaReport = (Vec<(TermId, bool)>, bool, Vec<(TermId, bool)>);

/// The diagnostics the real-`CDCL(T)` combined driver reports (slice-3c-lia gate
/// harness): the verdict code (`0` `Unsat` / `1` `Sat` / `2` `Unknown`), the number of
/// registered shared-interface pairs (`> 0` proves the interface case-split machinery is
/// wired), the number of 1-UIP analyses that fired, and every learned 1-UIP clause over
/// terms.
#[cfg(test)]
pub(crate) struct CombinedCdcltDiag {
    /// `0` = `Unsat`, `1` = `Sat`, `2` = `Unknown`.
    pub(crate) verdict: u8,
    /// The registered shared-interface pairs (`eq`/`lt`/`gt` variable triples).
    pub(crate) interface_pairs: usize,
    /// The number of 1-UIP conflict analyses the driver ran ("the loop fires").
    pub(crate) analyze_fires: usize,
    /// The learned 1-UIP clauses over terms, for the entailment re-validation.
    pub(crate) lemmas: Vec<CombinedLemmaReport>,
}

/// **Slice-3c-lia soundness-gate harness** (test-only): drive a Boolean-structured
/// `QF_UFLIA` query through the real-`CDCL(T)` combined layer
/// (`Dpll<CombinedIncrementalLia>`) and report its diagnostics ([`CombinedCdcltDiag`]) —
/// the verdict, the registered interface-pair count, the 1-UIP fire count, and every
/// learned 1-UIP clause **over terms**. The slice-3c-lia gate uses it to assert (a) the
/// new loop fires (interface pairs registered, 1-UIP analyses run) and (b) every learned
/// theory lemma is genuinely entailed (its term-level negation conjoined with the level-0
/// facts is `UNSAT` under the trusted conjunctive decider over ℤ — the
/// 1-UIP-over-combination soundness check).
///
/// Returns `None` when the incremental combined state cannot be built (the same shapes the
/// production path falls back on) — out of this gate's scope.
///
/// Not part of the production surface.
#[cfg(test)]
#[must_use]
pub(crate) fn combined_cdclt_diag(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<CombinedCdcltDiag> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &a in assertions {
        collect_uflia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() || atom_terms.len() > MAX_BOOLEAN_ATOMS {
        return None;
    }
    let combined = crate::combined_theory_lia::CombinedIncrementalLia::new(arena, &atom_terms)?;

    // Reconstruct the full combined var→term map: the original atoms, then per pair the
    // eq/lt/gt interface terms (in the same order `CombinedIncrementalLia::new` registered).
    let interface_pairs = combined.interface_pairs().len();
    let mut var_term: Vec<TermId> = atom_terms.clone();
    for p in combined.interface_pairs() {
        let (s, t) = p.terms;
        let (Ok(eq), Ok(lt), Ok(gt)) = (arena.eq(s, t), arena.int_lt(s, t), arena.int_gt(s, t))
        else {
            return None;
        };
        var_term.push(eq);
        var_term.push(lt);
        var_term.push(gt);
    }
    let combined_count = var_term.len();

    let mut enc = BoolEncoder::with_reserved(&atom_terms, combined_count);
    let mut bool_clauses: Vec<Vec<BoolLit>> = Vec::new();
    for &assertion in assertions {
        let top = enc.encode(arena, assertion, &mut bool_clauses)?;
        bool_clauses.push(vec![BoolLit {
            var: top,
            positive: true,
        }]);
    }
    for structural in combined.structural_clauses() {
        bool_clauses.push(
            structural
                .into_iter()
                .map(|(var, positive)| BoolLit { var, positive })
                .collect(),
        );
    }
    let lit_clauses: Vec<Vec<crate::lra_online::Lit>> = bool_clauses
        .into_iter()
        .map(|clause| {
            clause
                .into_iter()
                .map(|l| crate::lra_online::Lit {
                    var: l.var,
                    positive: l.positive,
                })
                .collect()
        })
        .collect();

    let mut state = combined;
    let mut solver = crate::lra_online::Dpll::new(enc.var_count, combined_count, lit_clauses);
    let unsat = solver.solve(&mut state);
    let verdict = if unsat {
        0
    } else {
        let mut literals: Vec<Literal> = Vec::new();
        for (var, &atom) in atom_terms.iter().enumerate() {
            if let Some(value) = solver.value_of(var) {
                literals.push(Literal { atom, value });
            }
        }
        match decide_conjunction(arena, &literals) {
            CheckResult::Sat(_) => 1,
            _ => 2,
        }
    };

    // Map each learned clause / level-0 fact back to terms (only vars in range — a learned
    // clause references only combined or Tseitin-aux variables; an aux var has no atom term
    // and is dropped from the term-level report, which only weakens the re-validation claim
    // conservatively, never strengthens it).
    let term_of = |var: usize| var_term.get(var).copied();
    let lemmas: Vec<CombinedLemmaReport> = solver
        .learned_lemmas()
        .into_iter()
        .map(|(clause, is_lemma, level0)| {
            let lits: Vec<(TermId, bool)> = clause
                .iter()
                .filter_map(|l| term_of(l.var).map(|term| (term, l.positive)))
                .collect();
            let facts: Vec<(TermId, bool)> = level0
                .iter()
                .filter_map(|&(v, value)| term_of(v).map(|term| (term, value)))
                .collect();
            (lits, is_lemma, facts)
        })
        .collect();

    Some(CombinedCdcltDiag {
        verdict,
        interface_pairs,
        analyze_fires: solver.analyze_fires(),
        lemmas,
    })
}

/// Decides a Boolean-structured `QF_UFLIA` query by the **enumerative** `DPLL(T)` layer
/// (the retained slice-1/2 components: warm
/// [`crate::combined_theory_lia::CombinedTheoryLia`] oracle, early theory-conflict pruning,
/// and combined theory propagation, behind a chronological [`BoolSearch`] enumeration). The
/// production path ([`check_qf_uflia_boolean`]) now uses the real `CDCL(T)` driver
/// (`Dpll<CombinedIncrementalLia>`); this enumerative layer remains as the fallback for the
/// rare unbuildable-incremental-state case and as the harness the slice-1/2 metric gates
/// exercise.
///
/// The distinct theory atoms (`EUF` equalities, `LIA` order atoms) become the first
/// propositional variables; the Boolean structure is Tseitin-encoded over them. A
/// self-contained `DPLL` search enumerates total propositional models; each model's
/// conjunction of theory literals is decided by [`decide_conjunction`]. A `sat`
/// (replay-checked) combination wins immediately; an `unsat` combination blocks the
/// model and the search continues; an `unknown` combination degrades the whole query to
/// a conservative [`CheckResult::Unknown`]. `UNSAT` is reported only when every
/// propositional model is blocked.
fn check_qf_uflia_boolean_enumerative(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    enable_early_prune: bool,
    metrics: Option<&mut Metrics>,
) -> CheckResult {
    // The distinct theory atoms over the whole assertion set become the proposition
    // variables 0..atom_count (deterministic left-to-right scan).
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    for &a in assertions {
        collect_uflia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return decline("no UFLIA atoms for the online combination boolean layer");
    }
    if atom_terms.len() > MAX_BOOLEAN_ATOMS {
        return decline(format!(
            "too many theory atoms for the online combination boolean layer: {} > {}",
            atom_terms.len(),
            MAX_BOOLEAN_ATOMS
        ));
    }
    let opaque_atoms = opaque_lia_order_atom_count(arena, &atom_terms);
    if opaque_atoms > MAX_OPAQUE_BOOLEAN_ATOMS {
        return decline(large_opaque_online_detail(atom_terms.len(), opaque_atoms));
    }

    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return timeout_unknown("timeout in the online combination boolean layer");
    }

    // Tseitin-encode each assertion; assert each top variable.
    let mut enc = BoolEncoder::new(&atom_terms);
    let mut clauses: Vec<Vec<BoolLit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return decline(format!(
                "boolean skeleton outside the online combination encoder: {}",
                enc.unsupported_detail()
            ));
        };
        if clauses.len() > MAX_BOOLEAN_CLAUSES {
            return decline("too many clauses for the online combination boolean layer");
        }
        clauses.push(vec![BoolLit {
            var: top,
            positive: true,
        }]);
    }

    // Build the warm equality-sharing oracle once over the atom set (the indices align
    // with the BoolSearch variables). The enumeration is unchanged — only this theory
    // oracle is warm across the per-model checks.
    let combined = crate::combined_theory_lia::CombinedTheoryLia::new_with_deadline(
        arena,
        &atom_terms,
        deadline,
    );
    let mut search = BoolSearch {
        var_count: enc.var_count,
        atom_count: atom_terms.len(),
        atom_terms: &atom_terms,
        clauses,
        value: vec![None; enc.var_count],
        trail: Vec::new(),
        models_tried: 0,
        last_early_atoms: 0,
        last_prop_atoms: 0,
        prunes_fired: 0,
        props_fired: 0,
        enable_early_prune,
        deadline,
        combined,
    };
    let result = search.solve(arena);
    if let Some(out) = metrics {
        out.prunes_fired = search.prunes_fired;
        out.models_tried = search.models_tried;
        out.props_fired = search.props_fired;
    }
    result
}

/// The control-flow outcome of an early (partial-assignment) theory-conflict check
/// in [`BoolSearch::early_theory_prune`].
enum EarlyPrune {
    /// A partial theory conflict was blocked and backtracked: re-run `BCP`.
    Pruned,
    /// The conflict left no decision to flip: the whole query is `UNSAT`.
    Exhausted,
    /// No pruning (no new atoms, a total assignment, or a non-`Unsat` check): keep going.
    Continue,
}

/// The enumeration metrics the Boolean `DPLL(T)` layer reports back (test-only): the
/// early-prune fire count, the total propositional models decided, and the
/// combined-theory-propagation fire count (slice 2).
#[derive(Default)]
struct Metrics {
    prunes_fired: usize,
    models_tried: usize,
    props_fired: usize,
}

/// The reason clause `¬(reason) ∨ lit` for a combined-theory propagation
/// `reason ⊨ lit`: each reason literal contributes its negation, plus the propagated
/// literal at its proven polarity. Under the current assignment (every reason literal
/// asserted, `lit` asserted at the *opposite* polarity) this clause is falsified — the
/// theory-conflict clause the search learns and backtracks on (and once the conflict is
/// resolved it remains a valid implication, forcing `lit` whenever its reason holds).
fn reason_clause(prop: &crate::euf_egraph::TheoryProp) -> Vec<BoolLit> {
    let mut clause: Vec<BoolLit> = prop
        .reason
        .iter()
        .map(|r| BoolLit {
            var: r.atom,
            positive: !r.value,
        })
        .collect();
    clause.push(BoolLit {
        var: prop.lit.atom,
        positive: prop.lit.value,
    });
    clause
}

/// The propositional enumeration search of the Boolean `DPLL(T)` layer. Chronological
/// backtracking over the Tseitin skeleton; on each total propositional model the theory
/// atoms' conjunction is decided by [`decide_conjunction`], and an `unsat` model is
/// blocked by a theory-conflict clause.
struct BoolSearch<'a> {
    var_count: usize,
    /// The first `atom_count` variables are the theory atoms (the rest are Tseitin
    /// auxiliaries / Boolean leaves).
    atom_count: usize,
    /// The atom term per atom variable index (`0..atom_count`).
    atom_terms: &'a [TermId],
    clauses: Vec<Vec<BoolLit>>,
    value: Vec<Option<bool>>,
    /// `(var, is_decision)` in assignment order — the backtrack trail.
    trail: Vec<(usize, bool)>,
    /// How many total propositional models have been decided (the enumeration cap).
    models_tried: usize,
    /// The number of assigned atom variables at the most recent early theory check —
    /// the load-bearing guard that skips internal `BCP` fixpoints which added no new
    /// theory atom (each early check pays a full from-scratch `Nelson–Oppen` run).
    last_early_atoms: usize,
    /// The number of assigned atom variables at the most recent theory-propagation pass
    /// — the analogous guard that skips the (from-scratch) combined propagation rebuild
    /// on internal nodes that added no theory atom.
    last_prop_atoms: usize,
    /// How many partial-assignment early theory conflicts pruned the search.
    prunes_fired: usize,
    /// How many combined-theory propagations fired (an implied literal assigned or a
    /// propagated-literal conflict learned) — the slice-2 "propagation engages" metric.
    props_fired: usize,
    /// Whether early theory-conflict detection on partial assignments is enabled
    /// (always `true` in production; toggled off only by the pruning-metric test to
    /// establish the no-pruning baseline).
    enable_early_prune: bool,
    deadline: Option<Instant>,
    /// The **warm** equality-sharing theory oracle (slice 1): it decides each model's
    /// conjunction with the *same* combination as the cold [`decide_conjunction`] —
    /// identical verdict and model — but caches the constructed-and-base-asserted
    /// `LiaTheory` and reuses it when the `LIA` atom layout repeats across the
    /// enumeration. The enumeration above is unchanged — only the theory oracle is warmed.
    combined: crate::combined_theory_lia::CombinedTheoryLia,
}

impl BoolSearch<'_> {
    fn lit_sat(&self, lit: BoolLit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// Boolean unit propagation to fixpoint. `Err` carries the (Boolean) conflict clause
    /// `¬clause` on an all-false clause; `Ok(())` at a consistent fixpoint.
    fn unit_propagate(&mut self) -> Result<(), Vec<BoolLit>> {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.clauses.len() {
                let mut unassigned: Option<BoolLit> = None;
                let mut satisfied = false;
                let mut count = 0;
                for &lit in &self.clauses[ci] {
                    match self.lit_sat(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned = Some(lit);
                            count += 1;
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if count == 0 {
                    return Err(self.clauses[ci].iter().map(|l| l.negate()).collect());
                }
                if count == 1 {
                    let lit = unassigned.expect("count == 1 has the unit literal");
                    self.value[lit.var] = Some(lit.positive);
                    self.trail.push((lit.var, false));
                    changed = true;
                }
            }
        }
        Ok(())
    }

    /// Undoes the trail back to (and excluding) the most recent decision, returning that
    /// decision's `(var, value)`; `None` when no decision remains.
    fn backtrack_to_decision(&mut self) -> Option<(usize, bool)> {
        loop {
            let (var, is_decision) = self.trail.pop()?;
            let value = self.value[var].expect("trail var is assigned");
            self.value[var] = None;
            if is_decision {
                return Some((var, value));
            }
        }
    }

    /// The lowest-index unassigned variable, or `None` when the assignment is total.
    fn pick_unassigned(&self) -> Option<usize> {
        (0..self.var_count).find(|&v| self.value[v].is_none())
    }

    /// Records `clause` (the learned/blocking clause), backtracks past the most recent
    /// decision, and flips it as an implied assignment. `false` when no decision remains
    /// (the propositional search is exhausted).
    fn learn_and_backtrack(&mut self, clause: Vec<BoolLit>) -> bool {
        if !clause.is_empty() {
            self.clauses.push(clause);
        }
        let Some((var, value)) = self.backtrack_to_decision() else {
            return false;
        };
        self.value[var] = Some(!value);
        self.trail.push((var, false));
        true
    }

    /// The theory-literal conjunction of the current total propositional model: each atom
    /// variable's term at its assigned polarity.
    fn model_literals(&self) -> Vec<Literal> {
        let mut lits = Vec::with_capacity(self.atom_count);
        for (var, &atom) in self.atom_terms.iter().enumerate() {
            if let Some(value) = self.value[var] {
                lits.push(Literal { atom, value });
            }
        }
        lits
    }

    /// The theory-conflict blocking clause for an `unsat` model: the negation of the
    /// model's theory-literal assignment (`¬⋀ atom-literals`), so the propositional
    /// search never revisits a model agreeing on every theory atom.
    fn blocking_clause(&self) -> Vec<BoolLit> {
        (0..self.atom_count)
            .filter_map(|var| {
                self.value[var].map(|value| BoolLit {
                    var,
                    positive: !value,
                })
            })
            .collect()
    }

    /// Early theory-conflict detection on the *partial* propositional assignment at a
    /// `BCP` fixpoint, before deciding (`pick_unassigned`). When new theory atoms have
    /// been assigned since the last check (the `assigned > last_early_atoms` guard,
    /// which skips internal nodes that added no theory atom — each check pays a full
    /// from-scratch `Nelson–Oppen` run, with no cross-call incrementality) and the
    /// assignment is not yet total, the conjunction of the assigned atom-literals is
    /// decided:
    ///
    /// - `Unsat` ⇒ the *only* verdict-affecting transition, and it is sound: a partial
    ///   theory `Unsat` means every total extension agreeing on those atoms is unsat,
    ///   so the blocking clause prunes them all. Returns `Pruned` (re-run `BCP`) or
    ///   `Exhausted` when no decision remains (the whole query is `UNSAT`).
    /// - `Sat` / `Unknown` ⇒ never prune; fall through to keep deciding (`Continue`).
    ///   A partial-consistent or inconclusive check must not change the verdict.
    fn early_theory_prune(&mut self, arena: &mut TermArena) -> EarlyPrune {
        if !self.enable_early_prune {
            return EarlyPrune::Continue;
        }
        let assigned = (0..self.atom_count)
            .filter(|&v| self.value[v].is_some())
            .count();
        if assigned <= self.last_early_atoms || assigned >= self.atom_count {
            return EarlyPrune::Continue;
        }
        self.last_early_atoms = assigned;
        let literals = self.model_literals();
        if matches!(self.combined.check(arena, &literals), CheckResult::Unsat) {
            self.prunes_fired += 1;
            let clause = self.blocking_clause();
            if !self.learn_and_backtrack(clause) {
                return EarlyPrune::Exhausted;
            }
            return EarlyPrune::Pruned;
        }
        EarlyPrune::Continue
    }

    /// **Combined theory propagation** on the current `BCP`-fixpoint partial assignment
    /// (slice 2): pull every literal the warm `EUF` + `LIA` combination genuinely
    /// entails ([`crate::combined_theory_lia::CombinedTheoryLia::propagate`]) and assign
    /// each as an *implied* literal, so the joint (Boolean + theory) propagation reaches
    /// a fixpoint before the next decision. **Additive** pruning — it only assigns more
    /// genuinely-entailed literals, never changing the `Sat` / `Unsat` verdict.
    ///
    /// A propagated literal that agrees with an already-assigned value is a no-op; an
    /// unassigned one is assigned implied (recorded on the trail); a conflicting one is a
    /// theory conflict whose reason clause `¬(reason) ∨ lit` is falsified — learned and
    /// backtracked exactly like a Boolean conflict. The `assigned > last_prop_atoms`
    /// guard skips the (from-scratch) rebuild on internal nodes that added no theory atom.
    fn theory_propagate(&mut self, arena: &mut TermArena) -> EarlyPrune {
        let assigned = (0..self.atom_count)
            .filter(|&v| self.value[v].is_some())
            .count();
        if assigned <= self.last_prop_atoms || assigned >= self.atom_count {
            return EarlyPrune::Continue;
        }
        self.last_prop_atoms = assigned;
        let literals = self.model_literals();
        let props = self.combined.propagate(arena, &literals);
        let mut progressed = false;
        for prop in props {
            match self.value[prop.lit.atom] {
                Some(v) if v == prop.lit.value => {} // already entailed this way: no-op
                Some(_) => {
                    self.props_fired += 1;
                    let clause = reason_clause(&prop);
                    if !self.learn_and_backtrack(clause) {
                        return EarlyPrune::Exhausted;
                    }
                    return EarlyPrune::Pruned;
                }
                None => {
                    self.props_fired += 1;
                    self.value[prop.lit.atom] = Some(prop.lit.value);
                    self.trail.push((prop.lit.atom, false));
                    progressed = true;
                }
            }
        }
        if progressed {
            EarlyPrune::Pruned
        } else {
            EarlyPrune::Continue
        }
    }

    /// Runs the enumerative search. Returns `SAT` (replay-checked) for the first total
    /// propositional model whose theory-combination is consistent, `UNSAT` when every
    /// model is blocked, and a conservative `Unknown` on a cap or an `Unknown`
    /// combination.
    fn solve(&mut self, arena: &mut TermArena) -> CheckResult {
        loop {
            // Resolve any pending Boolean conflict by backtracking.
            loop {
                match self.unit_propagate() {
                    Ok(()) => break,
                    Err(clause) => {
                        if !self.learn_and_backtrack(clause) {
                            return CheckResult::Unsat;
                        }
                    }
                }
            }
            // Early theory-conflict detection on the partial assignment.
            match self.early_theory_prune(arena) {
                EarlyPrune::Pruned => continue,
                EarlyPrune::Exhausted => return CheckResult::Unsat,
                EarlyPrune::Continue => {}
            }
            // Combined theory propagation to a joint (Boolean + theory) fixpoint: assign
            // every genuinely-entailed literal as implied before deciding. Pruning only.
            match self.theory_propagate(arena) {
                EarlyPrune::Pruned => continue,
                EarlyPrune::Exhausted => return CheckResult::Unsat,
                EarlyPrune::Continue => {}
            }
            match self.pick_unassigned() {
                None => {
                    // A total propositional model: decide its theory conjunction.
                    if self.models_tried >= MAX_BOOLEAN_MODELS {
                        return decline(
                            "propositional model budget exhausted in the boolean layer",
                        );
                    }
                    self.models_tried += 1;
                    if self.deadline.is_some_and(|d| Instant::now() >= d) {
                        return decline("timeout in the online combination boolean layer");
                    }
                    let literals = self.model_literals();
                    match self.combined.check(arena, &literals) {
                        CheckResult::Sat(model) => return CheckResult::Sat(model),
                        CheckResult::Unsat => {
                            // Block this model and keep enumerating.
                            let clause = self.blocking_clause();
                            if !self.learn_and_backtrack(clause) {
                                return CheckResult::Unsat;
                            }
                        }
                        // The combination could not certify this model either way: a sound
                        // decline (the offline decider may still settle it). We cannot
                        // soundly call the whole query UNSAT, so degrade.
                        CheckResult::Unknown(reason) => {
                            return decline(format!(
                                "theory combination inconclusive on a boolean-layer model: {}",
                                reason.detail
                            ));
                        }
                    }
                }
                Some(var) => {
                    self.value[var] = Some(true);
                    self.trail.push((var, true));
                }
            }
        }
    }
}

/// Collects the distinct `QF_UFLIA` theory atoms in `term` — `EUF` equalities
/// (`(= s t)`) and `LIA` order atoms (`<`, `<=`, `>`, `>=`) — in a stable left-to-right
/// scan (so the proposition indexing is deterministic). An atom is not descended into
/// (its sides are theory terms, not Boolean structure).
pub(crate) fn collect_uflia_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut BTreeSet<TermId>,
) {
    if is_uflia_theory_atom(arena, term) {
        if seen.insert(term) {
            out.push(term);
        }
        return;
    }

    if let TermNode::App { args, .. } = arena.node(term) {
        let args = args.clone();
        for a in args {
            collect_uflia_atoms(arena, a, out, seen);
        }
    }
}

/// Tseitin encoder from the typed Boolean IR into the propositional skeleton, with the
/// first `atom_terms.len()` variables reserved for the theory atoms (numbered to match
/// the [`BoolSearch`] atom variables). Mirrors the encoder in [`crate::uflra_online`],
/// retargeted to the integer combination's atom set.
struct BoolEncoder {
    term_var: HashMap<TermId, usize>,
    var_count: usize,
    unsupported: Option<String>,
}

impl BoolEncoder {
    fn new(atom_terms: &[TermId]) -> Self {
        Self::with_reserved(atom_terms, atom_terms.len())
    }

    /// Builds the encoder with the theory atoms numbered `0..atom_terms.len()` but the
    /// fresh-variable counter started at `reserved` (≥ `atom_terms.len()`), so the Tseitin
    /// auxiliaries it allocates begin **after** a reserved block — the interface
    /// `eq`/`lt`/`gt` variables the real-`CDCL(T)` layer registers between the atoms and the
    /// auxiliaries. With `reserved == atom_terms.len()` this is exactly [`Self::new`].
    fn with_reserved(atom_terms: &[TermId], reserved: usize) -> Self {
        let mut term_var = HashMap::new();
        for (i, &t) in atom_terms.iter().enumerate() {
            term_var.insert(t, i);
        }
        Self {
            term_var,
            var_count: reserved.max(atom_terms.len()),
            unsupported: None,
        }
    }

    fn fresh(&mut self) -> usize {
        let v = self.var_count;
        self.var_count += 1;
        v
    }

    /// Encodes Boolean term `t`, returning the variable whose truth equals `t`, or `None`
    /// for structure outside the supported connectives (a sound give-up).
    fn encode(
        &mut self,
        arena: &TermArena,
        t: TermId,
        clauses: &mut Vec<Vec<BoolLit>>,
    ) -> Option<usize> {
        if let Some(&v) = self.term_var.get(&t) {
            return Some(v);
        }
        let v = match arena.node(t) {
            TermNode::Symbol(_) if arena.sort_of(t) == Sort::Bool => self.fresh(),
            TermNode::BoolConst(b) => {
                let value = *b;
                let g = self.fresh();
                clauses.push(vec![BoolLit {
                    var: g,
                    positive: value,
                }]);
                g
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                self.encode_app(arena, op, &args, clauses)?
            }
            _ => {
                self.record_unsupported(format!(
                    "non-Boolean term with sort {:?}: {:?}",
                    arena.sort_of(t),
                    arena.node(t)
                ));
                return None;
            }
        };
        self.term_var.insert(t, v);
        Some(v)
    }

    fn encode_app(
        &mut self,
        arena: &TermArena,
        op: Op,
        args: &[TermId],
        clauses: &mut Vec<Vec<BoolLit>>,
    ) -> Option<usize> {
        let supported = matches!(
            op,
            Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor | Op::Ite
        ) || (op == Op::Eq
            && args
                .first()
                .is_some_and(|&arg| arena.sort_of(arg) == Sort::Bool));
        if !supported {
            self.record_unsupported(format!(
                "unsupported Boolean op {op:?} with {} args",
                args.len()
            ));
            return None;
        }
        let lits: Vec<BoolLit> = args
            .iter()
            .map(|&a| {
                self.encode(arena, a, clauses).map(|var| BoolLit {
                    var,
                    positive: true,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let g = self.fresh();
        let gl = BoolLit {
            var: g,
            positive: true,
        };
        match (op, lits.as_slice()) {
            (Op::BoolNot, [a]) => {
                clauses.push(vec![gl.negate(), a.negate()]);
                clauses.push(vec![gl, *a]);
            }
            (Op::BoolAnd, children) => {
                for child in children {
                    clauses.push(vec![gl.negate(), *child]);
                }
                let mut down = Vec::with_capacity(children.len() + 1);
                down.push(gl);
                down.extend(children.iter().map(|child| child.negate()));
                clauses.push(down);
            }
            (Op::BoolOr, children) => {
                for child in children {
                    clauses.push(vec![gl, child.negate()]);
                }
                let mut down = Vec::with_capacity(children.len() + 1);
                down.push(gl.negate());
                down.extend(children.iter().copied());
                clauses.push(down);
            }
            (Op::BoolImplies, [a, b]) => {
                clauses.push(vec![gl, *a]);
                clauses.push(vec![gl, b.negate()]);
                clauses.push(vec![gl.negate(), a.negate(), *b]);
            }
            (Op::BoolXor, [a, b]) => {
                clauses.push(vec![gl.negate(), *a, *b]);
                clauses.push(vec![gl.negate(), a.negate(), b.negate()]);
                clauses.push(vec![gl, a.negate(), *b]);
                clauses.push(vec![gl, *a, b.negate()]);
            }
            (Op::Eq, [a, b]) if arena.sort_of(args[0]) == Sort::Bool => {
                clauses.push(vec![*a, *b, gl]);
                clauses.push(vec![a.negate(), b.negate(), gl]);
                clauses.push(vec![*a, b.negate(), gl.negate()]);
                clauses.push(vec![a.negate(), *b, gl.negate()]);
            }
            (Op::Ite, [c, x, y]) => {
                clauses.push(vec![c.negate(), x.negate(), gl]);
                clauses.push(vec![c.negate(), *x, gl.negate()]);
                clauses.push(vec![*c, y.negate(), gl]);
                clauses.push(vec![*c, *y, gl.negate()]);
            }
            _ => {
                self.record_unsupported(format!(
                    "unsupported Boolean op {op:?} with {} args",
                    args.len()
                ));
                return None;
            }
        }
        Some(g)
    }

    fn record_unsupported(&mut self, detail: String) {
        if self.unsupported.is_none() {
            self.unsupported = Some(detail);
        }
    }

    fn unsupported_detail(&self) -> &str {
        self.unsupported
            .as_deref()
            .unwrap_or("unsupported Boolean structure")
    }
}

/// A classified `unknown` reason for the online `UFLIA` path.
pub(crate) fn decline(detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.into(),
    })
}

fn timeout_unknown(detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Timeout,
        detail: detail.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::SolverConfig;
    use crate::euf::check_with_uf_arithmetic;
    use axeyum_ir::Sort;

    fn iconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.int_const(n)
    }

    fn ivar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Int).expect("declare int");
        arena.var(s)
    }

    fn next_rand(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        u32::try_from(*state >> 33).expect("32-bit shift fits u32")
    }

    /// A Boolean-structured `QF_UFLIA` query with shared interface terms (a unary integer
    /// `f` applied to the same vars that occur in `LIA` atoms), so the combined layer
    /// registers interface pairs and the `Dpll` branches them — the case the slice-3c-lia
    /// loop must drive.
    fn build_bool_case(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let x = ivar(arena, "x");
        let y = ivar(arena, "y");
        let mut pool: Vec<TermId> = vec![x, y];
        for _ in 0..2 {
            let n = i128::from(next_rand(state) % 4);
            pool.push(iconst(arena, n));
        }
        let fx = arena.apply(f, &[x]).expect("apply f");
        let fy = arena.apply(f, &[y]).expect("apply f");
        pool.push(fx);
        pool.push(fy);

        let mut atoms: Vec<TermId> = Vec::new();
        for _ in 0..4 {
            let lhs = pool[(next_rand(state) as usize) % pool.len()];
            let rhs = pool[(next_rand(state) as usize) % pool.len()];
            let atom = match next_rand(state) % 4 {
                0 => arena.int_lt(lhs, rhs).expect("lt"),
                1 => arena.int_le(lhs, rhs).expect("le"),
                2 => arena.int_ge(lhs, rhs).expect("ge"),
                _ => arena.eq(lhs, rhs).expect("eq"),
            };
            atoms.push(atom);
        }
        // Combine into an (a ∨ b) ∧ (c ∨ d) Boolean skeleton — genuinely non-conjunctive,
        // so the real-CDCL(T) layer (not the conjunctive fast-path) handles it.
        let ab = arena.or(atoms[0], atoms[1]).expect("or");
        let cd = arena.or(atoms[2], atoms[3]).expect("or");
        vec![arena.and(ab, cd).expect("and")]
    }

    /// Builds the assertion that puts `atom` at `value` (`atom` itself or its negation),
    /// for the lemma-entailment re-validation.
    fn lit_assertion(arena: &mut TermArena, atom: TermId, value: bool) -> TermId {
        if value {
            atom
        } else {
            arena.not(atom).expect("negate atom")
        }
    }

    /// **Slice-3c-lia gate (a): the new loop fires.** Over a deterministic batch of
    /// Boolean-structured `QF_UFLIA` queries with shared interface terms, the
    /// real-`CDCL(T)` combined driver (`Dpll<CombinedIncrementalLia>`) must engage: at
    /// least one case registers shared-interface pairs *and* runs a 1-UIP conflict analysis
    /// (so the Boolean + theory + interface-equality search genuinely drives the
    /// combination, not a trivial pass-through).
    #[test]
    fn combined_cdclt_loop_fires() {
        let config = SolverConfig::default();
        let mut state: u64 = 0xfeed_face_dead_beef;
        let mut saw_interface = false;
        let mut saw_analyze = false;
        for _ in 0..200usize {
            let mut arena = TermArena::new();
            let assertions = build_bool_case(&mut arena, &mut state);
            let Some(diag) = combined_cdclt_diag(&mut arena, &assertions) else {
                continue;
            };
            if diag.interface_pairs > 0 {
                saw_interface = true;
            }
            if diag.analyze_fires > 0 {
                saw_analyze = true;
            }
            // The diag-path verdict must agree with the trusted offline decider on every
            // jointly-decided case — a second guard that the loop's verdict is sound.
            let offline =
                check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline");
            let off = match offline {
                CheckResult::Sat(_) => Some(1u8),
                CheckResult::Unsat => Some(0u8),
                CheckResult::Unknown(_) => None,
            };
            if let Some(off) = off {
                if diag.verdict != 2 {
                    assert_eq!(
                        diag.verdict, off,
                        "real-CDCL(T) diag verdict disagrees with offline Ackermann"
                    );
                }
            }
        }
        assert!(
            saw_interface,
            "the real-CDCL(T) combined layer must register shared-interface pairs"
        );
        assert!(
            saw_analyze,
            "the real-CDCL(T) combined layer must run 1-UIP conflict analysis (the loop fires)"
        );
    }

    /// **Slice-3c-lia gate (b): 1-UIP-over-combination soundness.** Every learned *theory
    /// lemma* the combined `Dpll` derives must be genuinely entailed by the theory: the
    /// conjunction of the level-0 facts it rests on with the negation of the lemma clause is
    /// `UNSAT` over ℤ under the trusted offline conjunctive decider (eager Ackermann).
    /// Mirrors the `UFLRA` driver's 1-UIP soundness gate, extended over the EUF + LIA +
    /// interface-equality combination. A learned lemma that is NOT entailed would be an
    /// unsound resolvent — a hard failure.
    #[test]
    fn combined_cdclt_learned_theory_lemmas_are_entailed() {
        let config = SolverConfig::default();
        let mut state: u64 = 0x0123_4567_89ab_cdef;
        let mut checked = 0usize;
        for _ in 0..300usize {
            let mut arena = TermArena::new();
            let assertions = build_bool_case(&mut arena, &mut state);
            let Some(diag) = combined_cdclt_diag(&mut arena, &assertions) else {
                continue;
            };
            for (clause, is_lemma, level0) in diag.lemmas {
                if !is_lemma {
                    continue; // only pure theory lemmas are entailed by the theory alone
                }
                // ¬clause ∧ level0_facts must be UNSAT (the lemma is entailed).
                let mut probe: Vec<TermId> = Vec::new();
                for (term, positive) in &clause {
                    // The clause literal is `(term, positive)`; its negation asserts the
                    // opposite polarity.
                    probe.push(lit_assertion(&mut arena, *term, !positive));
                }
                for (term, value) in &level0 {
                    probe.push(lit_assertion(&mut arena, *term, *value));
                }
                if probe.is_empty() {
                    continue;
                }
                let offline =
                    check_with_uf_arithmetic(&mut arena, &probe, &config).expect("offline decider");
                // A genuinely-entailed lemma ⇒ the negation+facts is UNSAT. We only fail on
                // a definite SAT (a counter-model to entailment); an offline Unknown is not
                // a soundness violation of the lemma (the offline decider declined).
                assert!(
                    !matches!(offline, CheckResult::Sat(_)),
                    "learned theory lemma is NOT entailed (negation+level0 is SAT): \
                     clause={clause:?} level0={level0:?}"
                );
                checked += 1;
            }
        }
        assert!(
            checked > 0,
            "expected to validate at least one learned theory lemma"
        );
    }
}
