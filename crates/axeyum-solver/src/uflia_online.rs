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
//! **What this slice implements.** The sound *conjunctive* MBTC: flatten the
//! assertions to a conjunction of literals (declining a non-conjunctive Boolean
//! skeleton to a graceful [`CheckResult::Unknown`]), assert each theory's atoms, and
//! DFS-split on the shared pairs. A leaf consistent in both theories yields a combined
//! model that is **replayed against the original assertions**; all branches infeasible
//! ⇒ `UNSAT`.
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

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, FuncValue, Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::euf_egraph::{EufTheory, TheorySolver};
use crate::lia_online::LiaTheory;
use crate::model::Model;
use crate::theory_combination::{InterfaceStatus, classify_interface_equalities};

/// Hard ceiling on interface case-split recursion depth (one level per shared pair).
/// Above it the search declines to a graceful [`CheckResult::Unknown`] — never a
/// wrong verdict.
const MAX_SPLIT_DEPTH: usize = 64;

/// A classified literal of the conjunction: the atom term and its asserted polarity.
#[derive(Clone, Copy)]
struct Literal {
    atom: TermId,
    value: bool,
}

/// Decides a conjunctive `QF_UFLIA` query (`EUF` + linear integer arithmetic) by the
/// **online** model-based `Nelson–Oppen` combination, returning a **replay-checked**
/// integer model on `sat`. The warm, equality-sharing alternative to the
/// eager-Ackermann [`crate::euf::check_with_uf_arithmetic`].
///
/// The assertions are flattened to a conjunction of literals and partitioned between
/// [`crate::euf_egraph::EufTheory`] and [`crate::lia_online::LiaTheory`]; the two
/// arrangements over the shared (interface) integer terms are reconciled by exchanging
/// `EUF`-entailed equalities and **model-based** case-splitting the remaining pairs
/// (`LIA` is not convex, so the split — not a single forced equality — is what keeps the
/// combination complete). A consistent arrangement yields a combined model **replayed
/// against the original assertions** before being returned — the soundness gate, so a
/// model the combination cannot justify yields [`CheckResult::Unknown`], never a wrong
/// `sat`. `unsat` is reported only when every branch is infeasible.
///
/// Returns [`CheckResult::Unknown`] (a sound decline, never a guess) when the query is
/// not conjunctive `QF_UFLIA` (a non-conjunctive Boolean skeleton, or an atom outside
/// `EUF` / `LIA` — `BV` / `Real` / arrays / quantifiers), when the interface split
/// exceeds the internal depth cap, or when arithmetic overflow / a resource limit made
/// a feasibility check inconclusive.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches the sibling
/// deciders for interchange.
pub fn check_qf_uflia_online(
    arena: &mut TermArena,
    assertions: &[TermId],
    _config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // 1. Flatten to a conjunction of literals; decline a non-conjunctive skeleton.
    let mut literals: Vec<Literal> = Vec::new();
    for &assertion in assertions {
        if !flatten_conjunction(arena, assertion, true, &mut literals) {
            return Ok(decline(
                "non-conjunctive boolean skeleton for the online UFLIA path",
            ));
        }
    }
    if literals.is_empty() {
        return Ok(decline("no UFLIA literals for the online combination path"));
    }

    // 2. Partition the literals; decline an unsupported atom.
    let Some(part) = partition(arena, &literals) else {
        return Ok(decline(
            "atom outside QF_UFLIA for the online combination path",
        ));
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
        return Ok(decline(
            "too many interface pairs for the online combination split",
        ));
    }

    // 4. The initial EUF assertions (original equalities / disequalities). A
    //    single-theory EUF conflict is UNSAT.
    let euf_assertions = build_euf_assertions(arena, &part.euf);
    if euf_unsat(arena, &euf_assertions) {
        return Ok(CheckResult::Unsat);
    }

    // 5. Register the `LiaTheory` over the original LIA atoms PLUS, per shared pair,
    //    the three interface terms `s = t`, `s < t`, `s > t` (asserted by index in the
    //    DFS — the public `assert` surface, no dynamic atom registration). The
    //    original LIA atoms occupy indices `0..lia_atom_count`.
    let mut lia_atom_terms: Vec<TermId> = part.lia.iter().map(|l| l.atom).collect();
    let mut pair_atoms: Vec<PairAtoms> = Vec::with_capacity(pairs.len());
    for &(s, t) in &pairs {
        let Ok(eq) = arena.eq(s, t) else {
            return Ok(decline("interface equality term build failed"));
        };
        let Ok(lt) = arena.int_lt(s, t) else {
            return Ok(decline("interface order term build failed"));
        };
        let Ok(gt) = arena.int_gt(s, t) else {
            return Ok(decline("interface order term build failed"));
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

    let mut lia = LiaTheory::new(arena, &lia_atom_terms);
    for (index, lit) in part.lia.iter().enumerate() {
        if lia.assert(index, lit.value).is_err() {
            return Ok(CheckResult::Unsat);
        }
    }

    // 6. The interface case-split (DFS).
    let mut search = Search {
        arena,
        literals: &literals,
        euf_atoms: &part.euf,
        euf_assertions,
        pairs: &pairs,
        pair_atoms: &pair_atoms,
    };
    match search.run(&mut lia, &mut Vec::new(), 0) {
        Outcome::Sat(model) => Ok(CheckResult::Sat(model)),
        Outcome::Unsat => Ok(CheckResult::Unsat),
        Outcome::Unknown(detail) => Ok(decline(detail)),
    }
}

/// The `LiaTheory` atom indices of a shared pair's three interface terms.
#[derive(Clone, Copy)]
struct PairAtoms {
    eq: usize,
    lt: usize,
    gt: usize,
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
fn flatten_conjunction(
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
struct Partition {
    lia: Vec<Literal>,
    euf: Vec<Literal>,
}

/// Partitions the flattened literals, or `None` if any literal is outside `QF_UFLIA`
/// (a non-`LIA`, non-`EUF` atom — `BV` / `Real` / array / quantifier / bare predicate).
fn partition(arena: &TermArena, literals: &[Literal]) -> Option<Partition> {
    let mut lia = Vec::new();
    let mut euf = Vec::new();

    for &lit in literals {
        match arena.node(lit.atom) {
            // Integer order atoms are pure LIA.
            TermNode::App {
                op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
                args,
            } => {
                if !is_linear_int(arena, args[0]) || !is_linear_int(arena, args[1]) {
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

/// The `EUF` assertion terms for the `EUF` literals: a `true` equality literal is its
/// atom, a `false` one its negation `(not (= ..))`. Consumed by
/// [`classify_interface_equalities`] (which reads exactly those two shapes).
fn build_euf_assertions(arena: &mut TermArena, euf: &[Literal]) -> Vec<TermId> {
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
        } => is_linear_int(arena, args[0]) && is_linear_int(arena, args[1]),
        TermNode::App {
            op: Op::IntMul,
            args,
        } => {
            (is_int_const(arena, args[0]) && is_linear_int(arena, args[1]))
                || (is_int_const(arena, args[1]) && is_linear_int(arena, args[0]))
        }
        _ => false,
    }
}

/// Whether `term` is an integer constant.
fn is_int_const(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::IntConst(_))
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
struct Interface {
    /// Atomic integer terms occurring as a UF argument (a symbol / constant).
    euf: BTreeSet<TermId>,
    /// Atomic integer subterms of the `LIA` atoms (symbols / constants).
    lia: BTreeSet<TermId>,
}

/// Collects the [`Interface`] integer terms of the two partitions.
fn interface_terms(arena: &TermArena, part: &Partition) -> Interface {
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
fn interface_pairs(interface: &Interface) -> Vec<(TermId, TermId)> {
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
fn euf_unsat(arena: &TermArena, euf_assertions: &[TermId]) -> bool {
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

/// A classified `unknown` reason for the online `UFLIA` path.
fn decline(detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.into(),
    })
}
