//! E-matching quantifier instantiation on the e-graph keystone (Track 2, P2.6).
//!
//! [`instantiate_forall_via_egraph`] is the keystone-driven path for instantiating
//! a universal `∀x. body`: it builds an [`EGraph`] over the ground terms, selects a
//! trigger — a function-application subterm mentioning the bound variable, which
//! may be **nested** (`f(g(x))`) or **multi-argument with ground parts**
//! (`g(x, a)`) — e-matches it against the e-graph **modulo congruence**
//! ([`EGraph::ematch`]), and for each match substitutes the bound variable with a
//! representative of the matched argument class, producing the ground instances to
//! add and re-check. The solver loop evaluates equality-clause instances lazily:
//! already-true clauses are suppressed, while all-false and unit-like clauses are
//! checked before unresolved traffic. Unit-like equality clauses may detach one
//! literal only with source-bound or bounded-recursive checked provenance; the
//! public instantiation API remains the complete match set. Within one solve,
//! triggers compile/intern once and a shared bridge grows only with asserted source
//! instances; all unique patterns use one batched e-graph index per round
//! (ADR-0111). A revision-checked persistent index and root-symbol candidate
//! queues extend add-only rounds from the new node suffix and rematch only
//! affected patterns (ADR-0112). Merge rounds consume the e-graph union journal,
//! follow inverted parent paths, and root-canonicalize cached substitutions so
//! only reachable trigger roots need rematching (ADR-0113). Shared exact path
//! tries, class/ground filters, and retained top-application delta queues reduce
//! merge work without changing complete source instances (ADR-0114/0115/0116).
//!
//! Matching on the e-graph is congruence-aware for free: if the ground terms force
//! `a = b`, then `f(a)` and `f(b)` are one class and the trigger fires once, so the
//! instances follow the *semantic* term structure, not the syntactic one. This is
//! the migration of trigger instantiation onto the backtrackable, independently
//! checkable keystone (vs the bespoke congruence closure the existing
//! `axeyum_rewrite::instantiate_with_triggers` carries); deeper triggers,
//! inference, and the full instantiation loop build on it.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use axeyum_egraph::{EGraph, EMatchIndex, ENodeId, Pattern, Substitution};
use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::auto::{check_auto, config_with_remaining_timeout};
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome as CdcltOutcome};
use crate::euf_egraph::{Encoder as EufEncoder, EufTheory, collect_euf_atoms};

/// Historical e-matching round budget. It is now the *cadence anchor* for the
/// interleaved refutation checks: the first mid-loop ground refutation check
/// fires after this many rounds (exactly where the loop used to exit), so every
/// refutation the historical budget found is still found at the same cost.
const MAX_INSTANTIATION_ROUNDS: usize = 8;

/// Hard ceiling on instantiation rounds. The wall clock (deadline) and the
/// accumulated-ground cap are the practical bounds; this keeps the loop
/// deterministic (the "never hang" rule) when neither is configured.
const MAX_EXTENDED_INSTANTIATION_ROUNDS: usize = 512;

/// Mid-loop (extended-cadence) ground checks run under `remaining / divisor`
/// of the shared budget, so a single check whose inner routes would spend the
/// whole remaining wall clock cannot starve later rounds or the final check.
const MID_LOOP_CHECK_BUDGET_DIVISOR: u32 = 4;

/// A new instantiation round is started only when the remaining budget is at
/// least this multiple of the previous round's duration: per-round work has
/// grown 10x+ round-over-round on real corpora, and the e-matcher runs with
/// no internal deadline, so starting a round without growth headroom risks a
/// deadline overshoot as large as the round itself.
const ROUND_GROWTH_HEADROOM: u32 = 8;

/// Deterministic cap on accumulated ground terms: e-matching a universal whose
/// instances generate ever-deeper terms (e.g. `∀x.(x≤y ∨ x≥y+1)` ⇒ `y, y+1, y+2, …`)
/// can explode a single round's `check_auto`, so the loop bails to `unknown` past this
/// many ground terms even with no wall-clock budget (the "never hang" rule).
const MAX_GROUND_TERMS: usize = 8192;

/// Flood-regime budget for one round's *deferred* (undetermined-clause)
/// admissions; conflict and unit instances stay eager and unbudgeted. The
/// measured flood mechanism (2026-08-01, `AXEYUM_FLOODPROBE` on the UF parity
/// residual): once a round had no conflict/unit traffic the loop dumped the
/// WHOLE deferred pool — geometric pools of 34 -> 57 -> 129 -> ... -> 5957
/// candidates per round — reaching [`MAX_GROUND_TERMS`] around round 9-15
/// with almost entirely inert traffic (`dl_copy_invariant_19_2`: 8164 of
/// 8166 admitted instances still undetermined at the cap, 8080 of them
/// derived-from-derived). Above this budget the pool is admitted in ascending
/// instantiation-generation order (Z3 `qi_queue.cpp` cost
/// `(+ weight generation)`), `FLOOD_ROUND_ADMISSION_CAP` per round, so
/// shallow-derivation instances flow while deep derived noise waits — it is
/// re-materialized and re-classified (possibly as a conflict by then) on
/// every later round, never dropped. Pools at or under the budget keep the
/// historical admit-everything behavior byte-identical. Budgeting the UNIT
/// pool the same way was measured net-negative (three ~3s unit-heavy
/// refuters lost, no unit-flood file won) and reverted.
const FLOOD_ROUND_ADMISSION_CAP: usize = 256;

/// Z3's `qi.eager_threshold` analogue on the generation axis: deferred
/// instances at or under this generation are admitted eagerly even in the
/// flood regime — delaying them was measured to LOSE refuters main wins by
/// dumping the pool fast (`x2015..1276224`: an early 418-candidate deferred
/// dump carries the refutation; capping it to 256 turned a 4s unsat into
/// unknown). Only deeper-derived traffic waits for the budget.
const FLOOD_EAGER_GENERATION_MAX: u32 = 1;

/// The deferred throttle engages only once the accumulated ground set is at
/// least this large — below it every release behaves exactly like the
/// historical dump-everything admission. Early dumps are cheap and often
/// carry the refutation outright (`uf.1001519`: a ~7000-candidate release at
/// ground=1150 is what main refutes from in 4.4s; throttling its deep tail
/// changed WHICH instances filled the 8192 cap and lost the file). Flood
/// prevention only needs to act when the cap is actually at risk.
const FLOOD_THROTTLE_MIN_GROUND: usize = 2048;

/// The generation-layered final-check lever engages only when the accumulated
/// ground set is at least this large (the measured wall: a final check over
/// 8192 conjuncts burned 26.7s on `uf.1158058` and returned unknown).
const FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND: usize = 2048;

/// Generation ceiling for the subset-first final refutation check: sources
/// (generation 0) plus instances derived purely from source terms.
const FLOOD_FINAL_SUBSET_MAX_GENERATION: u32 = 1;

/// Internal tuple-join cap per retained matching round. This prevents a
/// multi-pattern Cartesian product from allocating beyond the solver's own
/// accumulated-ground budget. The public one-shot witness API remains complete.
const MAX_JOINED_SUBSTITUTIONS_PER_ROUND: usize = MAX_GROUND_TERMS;

/// Slice-3 lazy-discovery caps (`AXEYUM_NESTED_QUANT` only; all zero-effect
/// with the flag off). Discovery adds *formulas*, not just terms, so it is
/// budgeted separately from the ground ceiling: a registration whose join
/// emits ten thousand tuples must not convert the whole budget into positive
/// replacements before the ordinary schedules get a round.
const MAX_POSITIVE_TUPLES_PER_ROUND: usize = 256;
/// Total positive replacements admitted or promoted over one attempt.
const MAX_POSITIVE_INSTANCES: usize = 4096;
/// Registrations discovered inside admitted formulas, over one attempt.
const MAX_DISCOVERED_REGISTRATIONS: usize = 256;
/// Universals promoted from a positive replacement that kept binders.
const MAX_PROMOTED_UNIVERSALS: usize = 64;
/// Matcher rebuilds triggered by discovery. A rebuild re-compiles patterns and
/// re-ingests the ground set, so the count is what bounds discovery's overhead.
const MAX_DISCOVERY_REBUILDS: usize = 8;

/// Deterministic retained-CDCL(T) admission caps (ADR-0119). Exceeding one
/// disables only the accelerator; the established fresh-QF route remains live.
const ONLINE_QUANTIFIER_LIMITS: OnlineQuantifierLimits = OnlineQuantifierLimits {
    variables: 65_536,
    clauses: 262_144,
    literals: 262_144,
};

/// Candidate equalities are a bounded search hint, never a proof premise
/// (ADR-0120). Exceeding either cap declines scoped candidate matching only.
const MAX_CANDIDATE_EQUALITIES: usize = 4096;
const MAX_CANDIDATE_APPLICATIONS: usize = 16_384;

/// Term-invention caps for the **term-starved** fixpoint class (measured on
/// the scored UF corpus, e.g. `Arrow_Order/uf.616692`: the loop reaches its
/// instantiation fixpoint in *microseconds* with `ground=2` because no ground
/// application of any trigger's function exists — every application in the
/// file sits under a binder, so e-matching has nothing to match and no
/// selection policy can help; the terms a refutation needs must be BUILT,
/// not found). Invention substitutes seed constants (free symbols anywhere
/// in the assertions, including Skolem constants inside universal bodies,
/// plus ground application terms the e-graph already holds) into the
/// compiled triggers, staged by digit-sum depth, and seeds the resulting
/// ground terms into the **matcher's e-graph only** — never into the
/// asserted ground set — so it asserts no facts and merges no classes.
/// Instances found by matching invented terms flow through the unchanged
/// [`QuantifierInstanceCertificate`] admission gate, so invention adds no
/// trust surface.
const MAX_INVENTED_TERMS_TOTAL: usize = 2048;
/// New invented terms per fixpoint step (across all patterns). Deliberately
/// small: one 64-term step measured on `Arrow_Order/uf.616692` blasted the
/// joined-instance admission from 2 to 4098 ground terms in a single round,
/// drowning the (about nine) refuting instances; small steps keep each
/// admission wave small and the interleaved ground checks meaningful.
const MAX_INVENTED_TERMS_PER_STEP: usize = 32;
/// New invented terms per pattern per fixpoint step.
const MAX_INVENTED_TERMS_PER_PATTERN_STEP: usize = 4;
/// Enumerated (visited) seed tuples per pattern per fixpoint step; bounds the
/// re-enumeration cost on wide prefixes independently of how many tuples are
/// new.
const MAX_INVENTION_TUPLE_VISITS_PER_PATTERN_STEP: usize = 512;
/// Seed terms considered per sort (constants first, then existing ground
/// application representatives, both in deterministic term order).
const MAX_INVENTION_SEEDS_PER_SORT: usize = 12;
/// Invention runs only while the accumulated ground set is comfortably below
/// [`MAX_GROUND_TERMS`]: the flood class (fixpoint-free files that drive
/// ground to the cap) must not gain extra term traffic from this route.
const INVENTION_GROUND_CEILING: usize = MAX_GROUND_TERMS / 2;
/// Direct staged instances for universals the matching/join schedules starve
/// completely (measured on `Arrow_Order/uf.616692`: the 4-var universal's
/// 9^4 cartesian consumes the whole shared per-round join budget every
/// round, so the 6-var universal the refutation actually needs emitted ZERO
/// tuples across 12 rounds — `starved_joins=12, admitted=0`). Only
/// universals with no admitted instance at an invention step get direct
/// tuples, each flowing through the unchanged certificate admission gate.
const MAX_DIRECT_INSTANCES_TOTAL: usize = 1024;
const MAX_DIRECT_INSTANCES_PER_UNIVERSAL_STEP: usize = 8;
const MAX_DIRECT_TUPLE_VISITS_PER_UNIVERSAL_STEP: usize = 512;

/// Tries to refute a (possibly quantified) conjunction by **e-matching
/// instantiation on the e-graph** (Track 2, P2.6): it separates the ground
/// assertions from the universals, and repeatedly instantiates each universal over
/// the current ground terms ([`instantiate_forall_via_egraph`]), adds the fresh
/// instances, and re-checks the ground set with [`check_auto`] — until the ground
/// set is `unsat` (⇒ the original is `unsat`, since the universals entail every
/// instance), a round adds no new instance (instantiation fixpoint), or the round
/// budget is exhausted.
///
/// **Sound, incomplete:** a ground `unsat` is a real refutation; otherwise the
/// result is `unknown` (e-matching may simply not have found the refuting
/// instance). Quantifier-free inputs go straight to [`check_auto`].
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground solver.
pub fn prove_quantified_unsat_via_egraph(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut stats = QuantifierLoopStats::default();
    // Distribute top-level universals over conjunctions when that shrinks a
    // binder prefix (`∀x⃗.(A ∧ B)` ⟺ `(∀x⃗∩vars(A). A) ∧ (∀x⃗∩vars(B). B)` — a
    // logical equivalence, so unsat transfers exactly). The prenexed chains
    // the skolemizer produces glue INDEPENDENT conjunct universals into one
    // wide prefix (measured on `Arrow_Order/uf.616692`: a 6-var chain that is
    // really a 3-var + 1-var + 2-var conjunction), and every schedule
    // downstream — trigger cover, join products, staged tuple enumeration —
    // pays the cartesian price of the glued prefix. The split assertions are
    // the loop's trust anchor exactly as the skolemized assertions already
    // are: instance certificates bind to them syntactically.
    if crate::quant_skolemize::nested_quantifiers_enabled() {
        // Slice 2: the nesting-preserving layout needs a nesting-aware
        // decomposition. `split_universal_conjunctions` only reaches conjuncts
        // directly under one top-level prefix; `extract_nested_universals`
        // descends the whole conjunctive skeleton and additionally *registers*
        // the universals sitting in non-entailed (disjunctive) positions.
        let extraction = extract_nested_universals(arena, assertions);
        return prove_quantified_unsat_via_egraph_impl(
            arena,
            &extraction.assertions,
            &extraction.nested,
            config,
            true,
            true,
            &mut stats,
        );
    }
    let split = split_universal_conjunctions(arena, assertions);
    prove_quantified_unsat_via_egraph_impl(arena, &split, &[], config, true, true, &mut stats)
}

/// One universal occurring at a position the assertion set does **not** entail
/// standalone — under a disjunction, so `∀x⃗. body` is not itself a consequence.
///
/// It is registered in the driver (own binder prefix, own body, own triggers
/// derived from that body) so matching state exists for it, but no instance of it
/// is ever admitted to the ground set on its own: `A ∨ (∀y. B(y))` does not
/// entail `B(t)`.
///
/// What **is** entailed — and what slice 3 admits — is the *enclosing formula
/// with the universal replaced by its instance*: `A ∨ (∀y. B(y)) ⊨ A ∨ B(t)`,
/// because the universal sits at a positive (monotone) position of an NNF
/// formula. That replacement needs the enclosing formula and the exact position,
/// which [`PositiveContext`] carries.
#[derive(Debug, Clone)]
struct NestedRegistration {
    /// Synthesized `∀vars. body`, for identity and tracing only. Never asserted.
    quantifier: TermId,
    vars: Vec<SymbolId>,
    body: TermId,
    /// The positive-position replacement context, when the universal is reachable
    /// from its owner's matrix through `and`/`or` arguments only. `None` when a
    /// binder sits on the path (see [`PositiveContext`]) — such a registration
    /// stays inert exactly as in slice 2.
    context: Option<PositiveContext>,
}

/// Where a [`NestedRegistration`] sits inside a formula that is already trusted
/// (an original assertion, or a ground term admitted with a checked derivation).
///
/// `owner` is `∀outer⃗. matrix`; `path` is the sequence of argument indices from
/// `matrix` down to the registered `forall` node. **Every step is a `BoolAnd` or
/// `BoolOr` argument** — never a `Forall` body, and never a negation, an
/// implication, an `ite`, or a boolean `=`/`xor`. Two consequences, both
/// load-bearing for soundness:
///
/// * `and`/`or` are monotone, so a path made only of them lands on a positive
///   position of a formula that is asserted true, and replacing the subformula
///   there by anything it implies keeps the owner's truth: `∀y.B(y) → B(t)`,
///   hence `owner ⊨ owner[∀y.B(y) := B(t)]`. This does not depend on the input
///   being in NNF — the whitelist is what establishes monotonicity, so a
///   negation anywhere off the path is irrelevant.
/// * Forbidding `Forall` steps is not conservatism, it blocks a real unsoundness:
///   in `A ∨ ∀u.(B(u) ∨ ∀y.Q(u,y))` a positive replacement that also substituted
///   `u := c` would yield `A ∨ ∀u.(B(u) ∨ Q(c,d))`, which the original does *not*
///   entail (it only entails the `u := c` instance of that disjunct).
#[derive(Debug, Clone)]
struct PositiveContext {
    owner: TermId,
    path: Vec<u32>,
}

/// The nesting-aware decomposition of an assertion list.
#[derive(Debug, Default)]
struct UniversalExtraction {
    /// Assertions that are logically **equivalent** to the input list: the
    /// conjunctive skeleton is flattened and each universal chain is re-attached
    /// over only the binders its body actually uses. These are the loop's trust
    /// anchor exactly as the split assertions already are — instance certificates
    /// bind to them syntactically.
    assertions: Vec<TermId>,
    /// Universals in non-entailed positions (see [`NestedRegistration`]).
    nested: Vec<NestedRegistration>,
}

/// Decomposes each assertion along its **conjunctive** skeleton (top-level
/// `forall` chains and `and` spines), emitting one assertion per leaf with a
/// minimized binder prefix, and registering every universal found in a
/// non-entailed position.
///
/// Only conjunctive descent is used, so every emitted assertion is entailed by
/// (in fact equivalent to) the input:
/// `∀x⃗.(A ∧ B) ⟺ (∀x⃗. A) ∧ (∀x⃗. B)`, and dropping a binder the body does not
/// mention is vacuous. Any arena failure abandons that assertion's decomposition
/// and keeps the original untouched.
fn extract_nested_universals(arena: &mut TermArena, assertions: &[TermId]) -> UniversalExtraction {
    let mut out = UniversalExtraction::default();
    for &assertion in assertions {
        let mut local = UniversalExtraction::default();
        let mut prefix = Vec::new();
        if extract_entailed(arena, assertion, &mut prefix, &mut local) {
            out.assertions.append(&mut local.assertions);
            out.nested.append(&mut local.nested);
        } else {
            out.assertions.push(assertion);
        }
    }
    out
}

/// Conjunctive descent; returns `false` if the arena refused a rebuild, in which
/// case the caller keeps the original assertion.
fn extract_entailed(
    arena: &mut TermArena,
    term: TermId,
    prefix: &mut Vec<SymbolId>,
    out: &mut UniversalExtraction,
) -> bool {
    if let Some((var, body)) = as_forall(arena, term) {
        prefix.push(var);
        let ok = extract_entailed(arena, body, prefix, out);
        prefix.pop();
        return ok;
    }
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(term)
    {
        let args = args.clone();
        return args
            .into_iter()
            .all(|arg| extract_entailed(arena, arg, prefix, out));
    }
    // A leaf of the conjunctive skeleton. Universals inside it (necessarily under
    // a disjunction or another non-conjunctive connective) are registered, not
    // asserted.
    let used = used_prefix(arena, term, prefix);
    let Some(wrapped) = wrap_foralls(arena, term, &used) else {
        return false;
    };
    // The owner of every registration below is the emitted leaf assertion, so
    // the positive-replacement certificate names a formula the checker already
    // trusts. `used` is exactly the prefix `wrapped` re-attaches, and `term` is
    // its matrix — so paths are rooted at `term`.
    collect_nested_registrations(
        arena,
        term,
        &mut prefix.clone(),
        wrapped,
        &mut Vec::new(),
        true,
        &mut out.nested,
    );
    out.assertions.push(wrapped);
    true
}

/// Registers every universal reachable inside a non-conjunctive leaf.
///
/// `path` accumulates the argument indices walked from `owner`'s matrix. While
/// `positive` holds, every step so far has been an `and`/`or` argument, so the
/// current position admits the positive replacement of [`PositiveContext`]; once
/// a `forall` body is entered the flag clears permanently for that subtree and
/// the deeper registrations are recorded without a context (inert, as in slice 2).
fn collect_nested_registrations(
    arena: &mut TermArena,
    term: TermId,
    prefix: &mut Vec<SymbolId>,
    owner: TermId,
    path: &mut Vec<u32>,
    positive: bool,
    out: &mut Vec<NestedRegistration>,
) {
    let node = arena.node(term).clone();
    let TermNode::App { op, args } = node else {
        return;
    };
    if matches!(op, Op::Forall(_)) {
        let (inner_vars, inner_body) = peel_foralls(arena, term);
        // The enclosing binders this body actually uses, then its own — the
        // smallest prefix under which the body is closed with respect to the
        // universals above it.
        let mut vars = used_prefix(arena, inner_body, prefix);
        vars.extend(inner_vars.iter().copied());
        if let Some(quantifier) = wrap_foralls(arena, inner_body, &vars) {
            out.push(NestedRegistration {
                quantifier,
                vars,
                body: inner_body,
                context: positive.then(|| PositiveContext {
                    owner,
                    path: path.clone(),
                }),
            });
        }
        // Keep descending: a universal may nest further universals, and those
        // see this chain's binders too. The path would now cross this binder, so
        // positivity is dropped (see `PositiveContext`).
        let depth = prefix.len();
        prefix.extend(inner_vars);
        collect_nested_registrations(arena, inner_body, prefix, owner, path, false, out);
        prefix.truncate(depth);
        return;
    }
    let step_positive = positive && matches!(op, Op::BoolAnd | Op::BoolOr);
    for (index, arg) in args.into_iter().enumerate() {
        path.push(u32::try_from(index).unwrap_or(u32::MAX));
        collect_nested_registrations(arena, arg, prefix, owner, path, step_positive, out);
        path.pop();
    }
}

/// The trusted constructor **and** checker for **positive-position universal
/// instantiation**, the one inference slice 3 adds.
///
/// Read the arguments as a certificate: from `owner` (already trusted), the
/// universal at `owner`'s positive position `path` is replaced by its instance
/// under `vars ↦ bindings`, and any `owner` binder named in `vars` is
/// instantiated with the same substitution. The returned term is the conclusion.
///
/// It re-derives the conclusion from nothing but `(owner, path, vars, bindings)`
/// and enforces every side condition, returning `None` on any violation:
///
/// * the path reaches the universal through `BoolAnd`/`BoolOr` arguments only —
///   monotone connectives in NNF, so the position is positive, and no binder is
///   crossed (crossing one is genuinely unsound, see [`PositiveContext`]);
/// * every binder of the reached universal is instantiated (a partially
///   instantiated universal leaves free symbols, which is *not* entailed);
/// * every named variable is actually in scope, sorts match, and no binding
///   mentions any bound symbol (no capture);
/// * only `owner`'s own binders are substituted outside the replaced position —
///   an inner binder's name occurring elsewhere in the matrix is a free symbol
///   there and keeps its identity;
/// * `owner` binders left uninstantiated stay universally quantified.
///
/// Producer and admission both call this; admission additionally requires
/// `owner` to be in the trusted set and the recomputed conclusion to equal the
/// recorded one.
fn positive_instance_formula(
    arena: &mut TermArena,
    owner: TermId,
    path: &[u32],
    vars: &[SymbolId],
    bindings: &[TermId],
) -> Option<TermId> {
    if vars.is_empty() || vars.len() != bindings.len() {
        return None;
    }
    let (outer, matrix) = peel_foralls(arena, owner);
    let mut node = matrix;
    let mut spine: Vec<(Op, Vec<TermId>, usize)> = Vec::new();
    for &step in path {
        let TermNode::App { op, args } = arena.node(node).clone() else {
            return None;
        };
        if !matches!(op, Op::BoolAnd | Op::BoolOr) {
            return None;
        }
        let index = usize::try_from(step).ok()?;
        let next = *args.get(index)?;
        spine.push((op, args.to_vec(), index));
        node = next;
    }
    let (inner, inner_body) = peel_foralls(arena, node);
    if inner.is_empty() {
        return None;
    }
    let outer_set: HashSet<SymbolId> = outer.iter().copied().collect();
    let named: HashSet<SymbolId> = vars.iter().copied().collect();
    if named.len() != vars.len() || !inner.iter().all(|var| named.contains(var)) {
        return None;
    }
    let mut bound = outer_set.clone();
    bound.extend(inner.iter().copied());
    if !vars.iter().all(|var| bound.contains(var)) {
        return None;
    }
    let mut full: HashMap<TermId, TermId> = HashMap::new();
    let mut outer_only: HashMap<TermId, TermId> = HashMap::new();
    for (&var, &binding) in vars.iter().zip(bindings) {
        if arena.symbol(var).1 != arena.sort_of(binding)
            || contains_any_symbol(arena, binding, &bound)
        {
            return None;
        }
        let var_term = arena.var(var);
        full.insert(var_term, binding);
        if outer_set.contains(&var) {
            outer_only.insert(var_term, binding);
        }
    }
    // `replace_subterms` is binder-blind: it rewrites a variable term wherever it
    // occurs, including under a `forall` that re-binds the same symbol. The
    // skolemizer renames apart so shadowing should never reach here, but a
    // shadowed name would make the substitution capture, so refuse it outright
    // rather than rely on an upstream invariant.
    if binds_any_symbol(arena, inner_body, &named) {
        return None;
    }
    let mut memo = HashMap::new();
    let mut rebuilt = replace_subterms(arena, inner_body, &full, &mut memo).ok()?;
    for (op, mut args, index) in spine.into_iter().rev() {
        args[index] = rebuilt;
        rebuilt = axeyum_rewrite::build_app(arena, op, &args).ok()?;
    }
    let outer_named: HashSet<SymbolId> = outer_set.intersection(&named).copied().collect();
    if binds_any_symbol(arena, rebuilt, &outer_named) {
        return None;
    }
    let mut memo = HashMap::new();
    let instantiated = replace_subterms(arena, rebuilt, &outer_only, &mut memo).ok()?;
    let remaining: Vec<SymbolId> = outer
        .into_iter()
        .filter(|var| !named.contains(var))
        .collect();
    let used = used_prefix(arena, instantiated, &remaining);
    wrap_foralls(arena, instantiated, &used)
}

/// Slice-3 lazy discovery: the staging state that makes a nested registration
/// productive, and that finds the quantifiers an *instantiation* exposes.
///
/// Two mechanisms, one trust discipline:
///
/// * **Positive replacement.** Every registration's matched tuple is turned into
///   `owner[∀y⃗.B := B(t⃗)]` by [`positive_instance_formula`], which re-derives the
///   conclusion from the certificate fields alone and refuses anything outside
///   the entailed shape. A binder-free conclusion is admitted to the ground set;
///   a conclusion that kept binders is *promoted* to a full universal.
/// * **Lazy discovery.** Every formula that becomes trusted — an admitted
///   instance, an admitted replacement, a promoted universal — is scanned for
///   universals at its own positive positions, which become new registrations.
///   This is the staging a flat prefix cannot express: the inner quantifier of
///   `∀x.(¬P(x) ∨ ∀y.Q(x,y))` only becomes reachable *after* `x := a` is
///   instantiated, and only then does `¬P(a) ∨ Q(a,b)` exist to be admitted.
///
/// `trusted` is the induction hypothesis: it starts as the assertion list and
/// only ever gains formulas that were checked at the moment they were added, so
/// every owner named by a replacement is a consequence of the input.
#[derive(Debug, Default)]
struct NestedDiscovery {
    /// Formulas already scanned for positive-position universals.
    scanned: HashSet<TermId>,
    /// Formulas usable as a replacement `owner`. Grows only via checked steps.
    trusted: HashSet<TermId>,
    /// Conclusions already produced, so a re-fired trigger is not re-derived.
    produced: HashSet<TermId>,
    pending_registrations: Vec<NestedRegistration>,
    positive_instances: usize,
    discovered_registrations: usize,
    promoted: usize,
    admitted_ground: usize,
    rebuilds: usize,
    /// Replacements the checker refused. Non-zero is a defect signal, not a
    /// soundness one — a refusal is always fail-closed.
    rejected: usize,
}

impl NestedDiscovery {
    fn new(assertions: &[TermId]) -> Self {
        Self {
            // The extraction already registered every assertion-level nested
            // universal, so the assertions are trusted but not re-scanned.
            scanned: assertions.iter().copied().collect(),
            trusted: assertions.iter().copied().collect(),
            ..Self::default()
        }
    }

    fn is_trusted(
        &self,
        term: TermId,
        retained: &HashMap<TermId, QuantifierGroundDerivation>,
    ) -> bool {
        // `retained` holds only terms whose derivation passed
        // `check_quantifier_ground_derivation` at admission.
        self.trusted.contains(&term) || retained.contains_key(&term)
    }

    /// Registers the universals sitting at positive positions of each trusted
    /// formula not yet scanned. Returns how many registrations were added.
    fn scan(
        &mut self,
        arena: &mut TermArena,
        formulas: &[TermId],
        retained: &HashMap<TermId, QuantifierGroundDerivation>,
    ) -> usize {
        let mut added = 0;
        for &formula in formulas {
            if self.discovered_registrations >= MAX_DISCOVERED_REGISTRATIONS {
                break;
            }
            if !self.is_trusted(formula, retained) || !self.scanned.insert(formula) {
                continue;
            }
            let (prefix, matrix) = peel_foralls(arena, formula);
            let mut found = Vec::new();
            collect_nested_registrations(
                arena,
                matrix,
                &mut prefix.clone(),
                formula,
                &mut Vec::new(),
                true,
                &mut found,
            );
            for registration in found {
                if registration.context.is_none()
                    || self.discovered_registrations >= MAX_DISCOVERED_REGISTRATIONS
                {
                    continue;
                }
                self.discovered_registrations += 1;
                added += 1;
                self.pending_registrations.push(registration);
            }
        }
        added
    }

    /// Turns every registration tuple the matcher produced this round into its
    /// entailed positive replacement. Binder-free conclusions land in `ground`;
    /// conclusions that kept binders are queued for promotion to universals.
    /// Returns `(newly admitted ground formulas, newly promoted universals)`.
    #[allow(
        clippy::too_many_arguments,
        reason = "one staging step over the loop's admission state"
    )]
    fn stage(
        &mut self,
        arena: &mut TermArena,
        matcher: &mut IncrementalEmatchSession,
        retained: &HashMap<TermId, QuantifierGroundDerivation>,
        seen: &mut HashSet<TermId>,
        ground: &mut Vec<TermId>,
        generations: &mut TermGenerations,
    ) -> (Vec<TermId>, Vec<TermId>) {
        let pending = std::mem::take(&mut matcher.pending_positive);
        let mut admitted = Vec::new();
        let mut promoted = Vec::new();
        for (index, tuple) in pending {
            if self.positive_instances >= MAX_POSITIVE_INSTANCES {
                break;
            }
            let Some(quantifier) = matcher.quantifiers.get(index) else {
                continue;
            };
            let Some(context) = quantifier.context.clone() else {
                continue;
            };
            let vars = quantifier.vars.clone();
            if vars.len() != tuple.len() || !self.is_trusted(context.owner, retained) {
                self.rejected += 1;
                continue;
            }
            let Some(formula) =
                positive_instance_formula(arena, context.owner, &context.path, &vars, &tuple)
            else {
                self.rejected += 1;
                continue;
            };
            self.positive_instances += 1;
            if !self.produced.insert(formula) {
                continue;
            }
            // The conclusion is a checked consequence either way, so it is a
            // legitimate owner for further replacements from here on.
            self.trusted.insert(formula);
            let generation = tuple
                .iter()
                .map(|&binding| generations.generation(binding))
                .max()
                .unwrap_or(0)
                .saturating_add(1);
            if peel_foralls(arena, formula).0.is_empty() {
                if ground.len() < MAX_GROUND_TERMS && seen.insert(formula) {
                    generations.record_admitted(arena, formula, generation);
                    ground.push(formula);
                    self.admitted_ground += 1;
                    admitted.push(formula);
                }
            } else if self.promoted < MAX_PROMOTED_UNIVERSALS {
                self.promoted += 1;
                generations.record_admitted(arena, formula, generation);
                promoted.push(formula);
            }
        }
        (admitted, promoted)
    }
}

/// What one [`nested_discovery_step`] contributed to the round.
struct DiscoveryOutcome {
    /// Ground formulas admitted by positive replacement this round.
    admitted: Vec<TermId>,
    /// Whether the matcher was rebuilt over a grown universal/registration set.
    rebuilt: bool,
}

/// One lazy-discovery step: stage the registrations' tuples, scan everything
/// newly trusted for further nested universals, and — when the compiled set
/// actually grew — rebuild the matcher over it.
///
/// Rebuilding is the coarse but honest way to add a universal mid-attempt: the
/// pattern set, the index, and the join plans are all derived from the compiled
/// set at construction. `ground`, `seen`, `retained`, and the generation table
/// all survive, and the fresh session re-ingests the ground set on its next
/// round, so no admitted work is lost — only matching state is recomputed.
#[allow(
    clippy::too_many_arguments,
    reason = "the discovery step reads and extends the loop's whole admission state"
)]
fn nested_discovery_step(
    arena: &mut TermArena,
    discovery: &mut NestedDiscovery,
    matcher: &mut IncrementalEmatchSession,
    assertions: &mut Vec<TermId>,
    foralls: &mut Vec<TermId>,
    nested: &mut Vec<NestedRegistration>,
    admitted: &[TermId],
    retained: &HashMap<TermId, QuantifierGroundDerivation>,
    seen: &mut HashSet<TermId>,
    ground: &mut Vec<TermId>,
    generations: &mut TermGenerations,
) -> DiscoveryOutcome {
    let (staged, promoted) = discovery.stage(arena, matcher, retained, seen, ground, generations);
    let mut found = discovery.scan(arena, admitted, retained);
    found += discovery.scan(arena, &staged, retained);
    // A promoted universal joins the trust anchor *before* it is scanned or
    // compiled, so its own instances take the ordinary certificate route. Past
    // the rebuild budget it is never compiled and is simply inert: it is a
    // checked consequence, so its presence in the anchor is sound either way.
    for &universal in &promoted {
        assertions.push(universal);
        foralls.push(universal);
    }
    found += discovery.scan(arena, &promoted, retained);
    let grew = !discovery.pending_registrations.is_empty() || !promoted.is_empty();
    let mut rebuilt = false;
    if grew && discovery.rebuilds < MAX_DISCOVERY_REBUILDS {
        nested.append(&mut discovery.pending_registrations);
        *matcher = IncrementalEmatchSession::new_with_nested(arena, foralls, nested);
        discovery.rebuilds += 1;
        rebuilt = true;
    }
    if !staged.is_empty() || found > 0 || !promoted.is_empty() {
        crate::auto::qtrace(
            "nested-quant",
            Instant::now(),
            &format!(
                "discovery staged={} promoted={} registered={found} rebuilds={} \
                 totals: positive={} ground={} regs={} rejected={}",
                staged.len(),
                promoted.len(),
                discovery.rebuilds,
                discovery.positive_instances,
                discovery.admitted_ground,
                discovery.discovered_registrations,
                discovery.rejected,
            ),
        );
    }
    DiscoveryOutcome {
        admitted: staged,
        rebuilt,
    }
}

/// Whether any `forall`/`exists` inside `term` binds a symbol in `symbols` —
/// i.e. whether substituting for that symbol would capture.
fn binds_any_symbol(arena: &TermArena, term: TermId, symbols: &HashSet<SymbolId>) -> bool {
    if symbols.is_empty() {
        return false;
    }
    let mut seen = HashSet::new();
    let mut stack = vec![term];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Forall(var) | Op::Exists(var) = op
                && symbols.contains(var)
            {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// The members of `prefix` that occur free in `term`, in prefix order.
fn used_prefix(arena: &TermArena, term: TermId, prefix: &[SymbolId]) -> Vec<SymbolId> {
    if prefix.is_empty() {
        return Vec::new();
    }
    let index: HashMap<SymbolId, u32> = prefix
        .iter()
        .enumerate()
        .map(|(position, &var)| (var, u32::try_from(position).unwrap_or(u32::MAX)))
        .collect();
    let mut used = HashSet::new();
    collect_vars(arena, term, &index, &mut used);
    prefix
        .iter()
        .copied()
        .filter(|var| used.contains(var))
        .collect()
}

/// Re-attaches `vars` over `body`, outermost first. `None` on an arena failure.
fn wrap_foralls(arena: &mut TermArena, body: TermId, vars: &[SymbolId]) -> Option<TermId> {
    let mut wrapped = body;
    for &var in vars.iter().rev() {
        wrapped = arena.forall(var, wrapped).ok()?;
    }
    Some(wrapped)
}

/// Applies the shrinking `forall`-over-`and` distribution to every top-level
/// universal; assertions it cannot improve are passed through untouched. A
/// universal is split only when at least one conjunct of its (flattened)
/// conjunction body uses a proper subset of the binder prefix, so files
/// outside the glued-prefix shape keep byte-identical behavior.
fn split_universal_conjunctions(arena: &mut TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        let (vars, body) = peel_foralls(arena, assertion);
        if vars.is_empty() {
            out.push(assertion);
            continue;
        }
        let mut conjuncts = Vec::new();
        flatten_conjunction(arena, body, &mut conjuncts);
        if conjuncts.len() < 2 {
            out.push(assertion);
            continue;
        }
        let var_index: HashMap<SymbolId, u32> = vars
            .iter()
            .enumerate()
            .map(|(index, &var)| (var, u32::try_from(index).unwrap_or(u32::MAX)))
            .collect();
        let used_per_conjunct: Vec<HashSet<SymbolId>> = conjuncts
            .iter()
            .map(|&conjunct| {
                let mut used = HashSet::new();
                collect_vars(arena, conjunct, &var_index, &mut used);
                used
            })
            .collect();
        if used_per_conjunct
            .iter()
            .all(|used| used.len() == vars.len())
        {
            out.push(assertion);
            continue;
        }
        let mut split_ok = true;
        let mut split_terms = Vec::with_capacity(conjuncts.len());
        for (&conjunct, used) in conjuncts.iter().zip(&used_per_conjunct) {
            let mut rebuilt = conjunct;
            for &var in vars.iter().rev() {
                if used.contains(&var) {
                    if let Ok(term) = arena.forall(var, rebuilt) {
                        rebuilt = term;
                    } else {
                        split_ok = false;
                        break;
                    }
                }
            }
            if !split_ok {
                break;
            }
            split_terms.push(rebuilt);
        }
        if split_ok {
            out.extend(split_terms);
        } else {
            out.push(assertion);
        }
    }
    out
}

/// Flattens a `BoolAnd` spine into its conjuncts (a non-conjunction is its
/// own single conjunct).
fn flatten_conjunction(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            let args = args.clone();
            for arg in args {
                flatten_conjunction(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

#[derive(Debug, Default, Clone, Copy)]
struct QuantifierLoopStats {
    qf_checks: usize,
    online_solves: usize,
    online_clauses: usize,
    candidate_checks: usize,
    candidate_equalities: usize,
    candidate_instances: usize,
    candidate_pattern_executions: usize,
    candidate_applications_scanned: usize,
}

/// Memoized "contains a quantifier" test over the shared term DAG. The
/// instantiation loop's accumulated set is *not* always quantifier-free: an
/// original non-top-level assertion (`(or … (forall …))`) or an instance of a
/// universal whose matrix nests another quantifier keeps `Forall`/`Exists`
/// nodes, and one such conjunct makes every QF backend decline the whole set.
/// The refutation checks filter those conjuncts out (sound: the conjuncts are
/// all asserted, so an `unsat` subset refutes the full conjunction).
#[derive(Default)]
struct QuantifierTermCache {
    known: HashMap<TermId, bool>,
}

impl QuantifierTermCache {
    fn contains_quantifier(&mut self, arena: &TermArena, root: TermId) -> bool {
        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            if !expanded && self.known.contains_key(&term) {
                continue;
            }
            match arena.node(term) {
                TermNode::App { op, args } => {
                    if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                        self.known.insert(term, true);
                        continue;
                    }
                    if expanded {
                        let any = args
                            .iter()
                            .any(|arg| self.known.get(arg).copied().unwrap_or(false));
                        self.known.insert(term, any);
                    } else {
                        let args = args.clone();
                        stack.push((term, true));
                        for arg in args {
                            if !self.known.contains_key(&arg) {
                                stack.push((arg, false));
                            }
                        }
                    }
                }
                _ => {
                    self.known.insert(term, false);
                }
            }
        }
        self.known[&root]
    }

    /// The quantifier-free conjuncts of `ground`, or `None` when every conjunct
    /// is already quantifier-free (the caller then uses `ground` unchanged).
    fn quantifier_free_subset(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
    ) -> Option<Vec<TermId>> {
        let subset: Vec<TermId> = ground
            .iter()
            .copied()
            .filter(|&term| !self.contains_quantifier(arena, term))
            .collect();
        (subset.len() != ground.len()).then_some(subset)
    }
}

/// The loop's ground refutation check. It first runs the established check on
/// the full accumulated set (byte-identical to the historical behavior); when
/// that does not refute *and* the set carries quantified conjuncts — which the
/// QF backends decline wholesale — it re-checks the quantifier-free subset.
/// Subset `unsat` is sound: every conjunct is asserted, so refuting a subset
/// refutes the conjunction. This is strictly additive: it can only turn an
/// `unknown` round into `unsat`.
fn quantifier_qf_refutation_check(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
    cache: &mut QuantifierTermCache,
) -> Result<CheckResult, SolverError> {
    let probe_started = floodprobe_enabled().then(Instant::now);
    let result = quantifier_qf_refutation_check_impl(arena, ground, config, deadline, stats, cache);
    if let Some(started) = probe_started {
        let detail = match &result {
            Ok(CheckResult::Unknown(reason)) => format!(" unknown_detail={:?}", reason.detail),
            _ => String::new(),
        };
        eprintln!(
            "FLOODPROBE qf-check ground={} result={:?} ms={}{detail}",
            ground.len(),
            result.as_ref().map(|r| match r {
                CheckResult::Unsat => "unsat",
                CheckResult::Sat(_) => "sat",
                CheckResult::Unknown(_) => "unknown",
            }),
            started.elapsed().as_millis(),
        );
    }
    result
}

fn quantifier_qf_refutation_check_impl(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
    cache: &mut QuantifierTermCache,
) -> Result<CheckResult, SolverError> {
    let subset = cache.quantifier_free_subset(arena, ground);
    let full = match quantifier_qf_check(arena, ground, config, deadline, stats) {
        Ok(result) => result,
        // Some routes *reject* a quantified conjunct outright rather than
        // declining it, and that must not abort the loop: `unknown` is a first
        // class result here and the quantifier-free subset below is still a
        // sound refutation attempt. Narrow on purpose — with no quantified
        // conjunct there is no subset to retry, and the error propagates exactly
        // as it always has.
        Err(_) if subset.is_some() => CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "ground check declined a quantified conjunct".to_owned(),
        }),
        Err(error) => return Err(error),
    };
    if matches!(full, CheckResult::Unsat) {
        return Ok(full);
    }
    let Some(subset) = subset else {
        return Ok(full);
    };
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return Ok(full);
    }
    quantifier_qf_check(arena, &subset, config, deadline, stats)
}

/// A tighter deadline reserving `1/divisor` of the remaining budget: mid-loop
/// interleaved checks run under this so no single check (whose inner routes
/// spend their whole remaining budget on a large skeleton) can starve the
/// remaining rounds and the final ground check. `divisor <= 1` or no deadline
/// keeps the shared deadline unchanged.
fn fractional_deadline(deadline: Option<Instant>, divisor: u32) -> Option<Instant> {
    let d = deadline?;
    if divisor <= 1 {
        return Some(d);
    }
    let now = Instant::now();
    // An already-expired deadline stays expired (never unbounded).
    let Some(remaining) = d.checked_duration_since(now) else {
        return Some(d);
    };
    Some(now.checked_add(remaining / divisor).unwrap_or(d))
}

#[allow(clippy::too_many_lines)]
fn prove_quantified_unsat_via_egraph_impl(
    arena: &mut TermArena,
    assertions: &[TermId],
    nested: &[NestedRegistration],
    config: &SolverConfig,
    enable_online_clauses: bool,
    enable_candidate_equalities: bool,
    stats: &mut QuantifierLoopStats,
) -> Result<CheckResult, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let trace_start = Instant::now();
    // Slice 3 grows this list: a universal *promoted* from a positive-position
    // replacement is a checked consequence of the input, so it joins the trust
    // anchor and its instances take the ordinary certificate route unchanged.
    // With discovery off (`AXEYUM_NESTED_QUANT` unset) nothing is ever appended
    // and this is the input list verbatim.
    let mut assertions: Vec<TermId> = assertions.to_vec();
    let (mut ground, mut foralls) = partition_top_level_foralls(arena, &assertions);
    if foralls.is_empty() {
        if nested.is_empty() {
            return quantifier_qf_check(arena, &ground, config, deadline, stats);
        }
        // A registration always comes from an assertion that still carries a
        // quantifier, so the "ground" set here is not quantifier-free and its
        // verdict is not the query's. Refute on the quantifier-free subset only:
        // dropping a conjunct weakens, so `unsat` transfers back and nothing
        // else does.
        let mut cache = QuantifierTermCache::default();
        let result =
            quantifier_qf_refutation_check(arena, &ground, config, deadline, stats, &mut cache)?;
        return Ok(match result {
            CheckResult::Unsat => CheckResult::Unsat,
            _ => CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "e-matching: no universal is asserted; the nested \
                         quantifiers present are registered, not instantiated"
                    .to_owned(),
            }),
        });
    }

    if try_closed_universal_refutations(arena, &foralls, config, deadline)? {
        return Ok(CheckResult::Unsat);
    }
    crate::auto::qtrace("egraph-seg", trace_start, "closed-universal done");

    if try_targeted_quantifier_refutations(arena, &ground, &foralls, config, deadline, stats)? {
        return Ok(CheckResult::Unsat);
    }
    crate::auto::qtrace("egraph-seg", trace_start, "targeted done");

    // Share the wall clock and cap ground growth so explosion declines cleanly.
    let mut seen: HashSet<TermId> = ground.iter().copied().collect();
    let mut ground_derivations: HashMap<TermId, QuantifierGroundDerivation> = HashMap::new();
    // Slice 3 grows the registration set as instantiation exposes quantifiers.
    let mut nested: Vec<NestedRegistration> = nested.to_vec();
    // Discovery is exactly as live as registration is. A registration can only
    // exist under the nested layout, and a substitution instance cannot *create*
    // a `forall` that the assertion set did not already carry in a non-entailed
    // position — so an empty registration set means there is nothing to discover,
    // and the default (prenexed) path never allocates this at all.
    let mut discovery = (!nested.is_empty()).then(|| NestedDiscovery::new(&assertions));
    let mut matcher = IncrementalEmatchSession::new_with_nested(arena, &foralls, &nested);
    if !nested.is_empty() {
        let detail: Vec<String> = matcher
            .quantifiers
            .iter()
            .filter(|quantifier| !quantifier.active)
            .map(|quantifier| {
                format!(
                    "vars={} triggers={}",
                    quantifier.vars.len(),
                    quantifier.pattern_indices.len()
                )
            })
            .collect();
        crate::auto::qtrace(
            "nested-quant",
            trace_start,
            &format!(
                "registered active={} nested={} patterns={} | {}",
                foralls.len(),
                nested.len(),
                matcher.patterns.len(),
                detail.join(" | ")
            ),
        );
    }
    let mut quantifier_cache = QuantifierTermCache::default();
    let mut online_clauses = None;
    let mut online_attempted = !enable_online_clauses;
    let mut candidate_equalities_enabled = enable_candidate_equalities;
    let mut invention = TermInventionState::default();
    // Seed from the full assertion list (not just the ground partition): a
    // constant that first occurs under a binder is still a source-vocabulary
    // term, and its appearance inside an instance must not inflate that
    // instance's subterm generations.
    let mut generations = TermGenerations::seed_sources(arena, &assertions);
    let mut last_round_duration = std::time::Duration::ZERO;
    for round in 0..MAX_EXTENDED_INSTANTIATION_ROUNDS {
        let round_started = Instant::now();
        if deadline.is_some_and(|d| round_started >= d) {
            return Ok(egraph_timeout());
        }
        // One matching/admission round is the loop's largest deadline-blind
        // unit: the e-matcher has no internal deadline, and per-round work has
        // grown 10x+ round-over-round on real corpora (a 4s round forecasting
        // a 40s+ successor). Do not start a round the remaining budget cannot
        // plausibly fit with growth headroom — break to the final ground
        // check instead, which both bounds the overshoot and keeps the
        // refutation-completing step inside the budget.
        if let Some(d) = deadline
            && d.checked_duration_since(round_started)
                .is_none_or(|remaining| remaining < last_round_duration * ROUND_GROWTH_HEADROOM)
        {
            break;
        }
        if ground.len() > MAX_GROUND_TERMS {
            if floodprobe_enabled() {
                eprintln!("FLOODPROBE cap-hit round={round} ground={}", ground.len());
                floodprobe_cap_census(arena, &matcher, &ground_derivations, &assertions);
            }
            if matches!(
                quantifier_qf_refutation_check(
                    arena,
                    &ground,
                    config,
                    deadline,
                    stats,
                    &mut quantifier_cache
                )?,
                CheckResult::Unsat
            ) {
                return Ok(CheckResult::Unsat);
            }
            return Ok(egraph_ground_limit());
        }
        // The first round and accelerator fallbacks use the full QF route. The
        // historical 8-round window keeps its per-round check; the extended
        // rounds throttle to the exponential cadence so re-deciding a large,
        // barely-grown ground set does not dominate the added rounds.
        if online_clauses.is_none() {
            // Historical rounds keep the full shared deadline; the extended
            // cadence runs under a fractional budget so one large mid-loop
            // check cannot starve later rounds and the final ground check.
            let check_deadline = if round < MAX_INSTANTIATION_ROUNDS {
                deadline
            } else {
                fractional_deadline(deadline, MID_LOOP_CHECK_BUDGET_DIVISOR)
            };
            if interleaved_check_due(round) {
                let seg = Instant::now();
                let check = quantifier_qf_refutation_check(
                    arena,
                    &ground,
                    config,
                    check_deadline,
                    stats,
                    &mut quantifier_cache,
                )?;
                crate::auto::qtrace(
                    "egraph-seg",
                    seg,
                    &format!("qf-check round={round} ground={}", ground.len()),
                );
                if matches!(check, CheckResult::Unsat) {
                    return Ok(CheckResult::Unsat);
                }
            }
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return Ok(egraph_timeout());
            }
            if !online_attempted {
                // The retained CDCL(T) accelerator abstracts equality clauses;
                // quantified conjuncts make its encoder decline outright, so it
                // sees only the quantifier-free subset (its refutations are
                // re-validated by the full QF route either way).
                let session_ground = quantifier_cache
                    .quantifier_free_subset(arena, &ground)
                    .unwrap_or_else(|| ground.clone());
                online_clauses =
                    OnlineQuantifierClauseSession::new(arena, &session_ground, deadline);
                online_attempted = true;
            }
        }
        // Schedule conflict/unit-like instances globally before noisier clauses.
        let work_started = Instant::now();
        let mut admitted = admit_next_source_batch(
            arena,
            &assertions,
            &mut matcher,
            &mut seen,
            &mut ground,
            &mut ground_derivations,
            &mut generations,
            deadline,
        );
        crate::auto::qtrace(
            "egraph-seg",
            work_started,
            &format!("admit-batch round={round} ground={}", ground.len()),
        );
        if let Some(discovery) = discovery.as_mut() {
            let outcome = nested_discovery_step(
                arena,
                discovery,
                &mut matcher,
                &mut assertions,
                &mut foralls,
                &mut nested,
                &admitted,
                &ground_derivations,
                &mut seen,
                &mut ground,
                &mut generations,
            );
            // Staged replacements are ordinary ground facts from here on: they
            // feed the e-graph, the online session, and the interleaved checks
            // exactly as matched instances do. A rebuild alone is progress too —
            // the fresh triggers have not run yet, so the round must not be
            // read as a fixpoint.
            let rebuilt = outcome.rebuilt;
            admitted.extend(outcome.admitted);
            admitted.sort_by_key(|term| term.index());
            admitted.dedup();
            if admitted.is_empty() && rebuilt {
                last_round_duration = work_started.elapsed();
                continue;
            }
        }
        if admitted.is_empty() && candidate_equalities_enabled {
            match scoped_candidate_fixpoint_step(
                arena,
                &assertions,
                &mut ground,
                config,
                &mut matcher,
                &mut online_clauses,
                &mut seen,
                &mut ground_derivations,
                &mut generations,
                deadline,
                stats,
                &mut quantifier_cache,
            )? {
                CandidateFixpointStep::Refuted => return Ok(CheckResult::Unsat),
                CandidateFixpointStep::Added(terms) => admitted = terms,
                CandidateFixpointStep::Disable => candidate_equalities_enabled = false,
                CandidateFixpointStep::NoProgress => {}
            }
        }
        if admitted.is_empty() {
            // TERM INVENTION for the starved fixpoint: the schedules above
            // only *match* existing terms, so a file whose applications all
            // sit under binders reaches this point with a near-empty e-graph
            // and no way forward (measured class: fixpoint in microseconds
            // with ground=2). Seed ground trigger instances over the free
            // constants (Skolems included) into the matcher's e-graph — no
            // asserted fact, no merge, no new trust surface — and give the
            // matching schedules another round over them. Bounded by the
            // invention caps and gated away from the flood class by the
            // ground ceiling.
            // The ceiling is a hard gate, both on starting and on continuing:
            // a file that floods ground without help must not get extra term
            // traffic, and — measured on `QEpres/smtlib.678332` — an active
            // route allowed past the ceiling turns a ground=2 starved file
            // into a self-inflicted 8192-term flood (150+ invention steps
            // seeding joins that admit thousands of irrelevant instances
            // while the budget drains). The refutations this route wins are
            // small-ground refutations; past the ceiling the final ground
            // check is the better spend.
            if ground.len() <= INVENTION_GROUND_CEILING
                && deadline.is_none_or(|d| Instant::now() < d)
            {
                let seeded =
                    matcher.invent_starved_trigger_terms(arena, &assertions, &mut invention);
                let direct = matcher.invent_starved_universal_instances(
                    arena,
                    &assertions,
                    &mut invention,
                    &mut seen,
                    &mut ground,
                    &mut ground_derivations,
                    &mut generations,
                );
                if std::env::var_os("AXEYUM_QPROBE").is_some() && (seeded > 0 || !direct.is_empty())
                {
                    eprintln!(
                        "QPROBE term-invention round={round} seeded={seeded} direct={} \
                         totals={}/{} ground={}",
                        direct.len(),
                        invention.invented_total,
                        invention.direct_total,
                        ground.len(),
                    );
                }
                if !direct.is_empty() {
                    // Direct instances flow through the same downstream path
                    // as matched ones (online session insertion, interleaved
                    // ground checks).
                    admitted = direct;
                } else if seeded > 0 {
                    last_round_duration = work_started.elapsed();
                    continue;
                }
            }
            if admitted.is_empty() {
                if std::env::var_os("AXEYUM_QPROBE").is_some() {
                    let triggerless = matcher
                        .quantifiers
                        .iter()
                        .filter(|q| q.pattern_indices.is_empty() && !q.vars.is_empty())
                        .count();
                    eprintln!(
                        "QPROBE egraph-fixpoint round={round} ground={} foralls={} \
                         patterns={} triggerless={triggerless}",
                        ground.len(),
                        matcher.quantifiers.len(),
                        matcher.patterns.len(),
                    );
                    let mut admitted_per_universal: Vec<usize> = vec![0; matcher.quantifiers.len()];
                    for derivation in matcher.ground_derivations.values() {
                        if let QuantifierGroundDerivation::Instance(certificate) = derivation
                            && let Some(index) = matcher
                                .quantifiers
                                .iter()
                                .position(|q| q.assertion == certificate.assertion)
                        {
                            admitted_per_universal[index] += 1;
                        }
                    }
                    for (index, quantifier) in matcher.quantifiers.iter().enumerate() {
                        let (emitted, starved) =
                            matcher.join_stats.get(index).copied().unwrap_or((0, 0));
                        eprintln!(
                            "QPROBE   universal[{index}] vars={} patterns={} joined={emitted} \
                             starved_joins={starved} admitted={}",
                            quantifier.vars.len(),
                            quantifier.pattern_indices.len(),
                            admitted_per_universal[index],
                        );
                    }
                }
                if floodprobe_enabled() {
                    eprintln!("FLOODPROBE fixpoint round={round} ground={}", ground.len());
                    floodprobe_cap_census(arena, &matcher, &ground_derivations, &assertions);
                }
                break; // source, scoped-candidate, and invention fixpoint
            }
        }
        let online_outcome = online_clauses.as_mut().and_then(|session| {
            let outcome =
                session.add_checked_batch(arena, &assertions, &admitted, &ground_derivations);
            if outcome.is_some() {
                stats.online_solves += 1;
                stats.online_clauses = session.inserted_clauses;
            }
            outcome
        });
        match online_outcome {
            Some(CdcltOutcome::Unsat) => {
                if replay_online_refutation(
                    arena,
                    &ground,
                    config,
                    deadline,
                    stats,
                    &mut quantifier_cache,
                )? {
                    return Ok(CheckResult::Unsat);
                }
                online_clauses = None;
            }
            Some(CdcltOutcome::Sat) => {}
            Some(CdcltOutcome::Unknown) | None => online_clauses = None,
        }
        // Record the matching/admission/session work only — the ground checks
        // run under their own (fractional) budgets, and counting them here
        // would make the headroom guard forecast check cost as round cost and
        // cut the extended rounds off after their first check.
        last_round_duration = work_started.elapsed();
        // Interleaved ground refutation checks at exponentially spaced rounds
        // (8, 16, 32, …): the retained CDCL(T) session skips the per-round QF
        // check while it stays satisfiable, so without these the extended
        // rounds would defer the only refutation-completing step to the final
        // check — which a deadline exit skips. The first check fires exactly
        // where the historical 8-round loop exited, preserving its reach.
        if online_clauses.is_some()
            && round + 1 >= MAX_INSTANTIATION_ROUNDS
            && (round + 1).is_power_of_two()
            && deadline.is_none_or(|d| Instant::now() < d)
            && matches!(
                quantifier_qf_refutation_check(
                    arena,
                    &ground,
                    config,
                    fractional_deadline(deadline, MID_LOOP_CHECK_BUDGET_DIVISOR),
                    stats,
                    &mut quantifier_cache
                )?,
                CheckResult::Unsat
            )
        {
            return Ok(CheckResult::Unsat);
        }
    }
    if !nested.is_empty() {
        let detail: Vec<String> = matcher
            .quantifiers
            .iter()
            .enumerate()
            .filter(|(_, quantifier)| !quantifier.active)
            .map(|(index, quantifier)| {
                let (emitted, starved) = matcher.join_stats.get(index).copied().unwrap_or((0, 0));
                format!(
                    "vars={} triggers={} tuples={emitted} starved={starved}",
                    quantifier.vars.len(),
                    quantifier.pattern_indices.len(),
                )
            })
            .collect();
        crate::auto::qtrace(
            "nested-quant",
            trace_start,
            &format!("nested-activity | {}", detail.join(" | ")),
        );
    }
    finish_quantified_ground_check(
        arena,
        &ground,
        config,
        deadline,
        stats,
        &mut quantifier_cache,
        &generations,
    )
}

/// Whether the session-less per-round ground check is due: every round inside
/// the historical [`MAX_INSTANTIATION_ROUNDS`] window, then rounds whose
/// 1-based index is a power of two (the same cadence as the retained-session
/// interleaved checks).
fn interleaved_check_due(round: usize) -> bool {
    round < MAX_INSTANTIATION_ROUNDS || (round + 1).is_power_of_two()
}

fn egraph_timeout() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: "e-matching: instantiation time budget exhausted".to_owned(),
    })
}

fn egraph_ground_limit() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: "e-matching: ground-term count budget exhausted".to_owned(),
    })
}

enum CandidateFixpointStep {
    Refuted,
    Added(Vec<TermId>),
    Disable,
    NoProgress,
}

#[allow(clippy::too_many_arguments)]
fn scoped_candidate_fixpoint_step(
    arena: &mut TermArena,
    assertions: &[TermId],
    ground: &mut Vec<TermId>,
    config: &SolverConfig,
    matcher: &mut IncrementalEmatchSession,
    online_clauses: &mut Option<OnlineQuantifierClauseSession>,
    seen: &mut HashSet<TermId>,
    ground_derivations: &mut HashMap<TermId, QuantifierGroundDerivation>,
    generations: &mut TermGenerations,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
    cache: &mut QuantifierTermCache,
) -> Result<CandidateFixpointStep, SolverError> {
    let Some(session) = online_clauses.as_mut() else {
        return Ok(CandidateFixpointStep::NoProgress);
    };
    let outcome = if let Some(outcome) = session.last_outcome {
        outcome
    } else {
        stats.online_solves += 1;
        let outcome = session.solve_current();
        stats.online_clauses = session.inserted_clauses;
        outcome
    };
    match outcome {
        CdcltOutcome::Unsat => {
            if replay_online_refutation(arena, ground, config, deadline, stats, cache)? {
                return Ok(CandidateFixpointStep::Refuted);
            }
            *online_clauses = None;
            Ok(CandidateFixpointStep::NoProgress)
        }
        CdcltOutcome::Unknown => {
            *online_clauses = None;
            Ok(CandidateFixpointStep::NoProgress)
        }
        CdcltOutcome::Sat => {
            let candidate_equalities = session.true_equality_terms(arena);
            stats.candidate_checks += 1;
            stats.candidate_equalities += candidate_equalities.len();
            let Some(candidate) =
                matcher.scoped_candidate_instances(arena, &candidate_equalities, deadline)
            else {
                return Ok(CandidateFixpointStep::Disable);
            };
            stats.candidate_instances += candidate.batch.urgent.len();
            stats.candidate_pattern_executions += candidate.pattern_executions;
            stats.candidate_applications_scanned += candidate.applications_scanned;
            let GeneratedGroundBatch {
                urgent,
                derivations,
                ..
            } = candidate.batch;
            Ok(CandidateFixpointStep::Added(admit_generated_ground(
                arena,
                assertions,
                urgent,
                seen,
                ground,
                ground_derivations,
                &derivations,
                generations,
            )))
        }
    }
}

fn replay_online_refutation(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
    cache: &mut QuantifierTermCache,
) -> Result<bool, SolverError> {
    Ok(matches!(
        quantifier_qf_refutation_check(arena, ground, config, deadline, stats, cache)?,
        CheckResult::Unsat
    ))
}

fn partition_top_level_foralls(
    arena: &TermArena,
    assertions: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    assertions.iter().copied().partition(|&assertion| {
        !matches!(arena.node(assertion), TermNode::App { op, .. } if matches!(op, Op::Forall(_)))
    })
}

/// Refutes a closed universal sentence by solving its existentially witnessed
/// negated body once. A satisfiable negation makes the top-level universal false;
/// every other outcome declines to ordinary instantiation. The valid direction
/// is handled by `quant_valid_universal` before this route.
fn try_closed_universal_refutations(
    arena: &mut TermArena,
    foralls: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<bool, SolverError> {
    for &quantifier in foralls {
        let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
            return Ok(false);
        };
        if let Some(CheckResult::Unsat) = refute_closed_universal(arena, quantifier, &remaining)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Runs narrow checked refuters and ADR-0095/0097/0099 instance proposers. The
/// predecessor-recurrence route proves its sign result directly from exact
/// original-IR structure; the remaining routes require an independent theorem
/// checker to recognize the source universal before the ordinary QF solver tests
/// a proposed instance. No untrusted match is itself a verdict.
fn try_targeted_quantifier_refutations(
    arena: &mut TermArena,
    ground: &[TermId],
    foralls: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
) -> Result<bool, SolverError> {
    for &quantifier in foralls {
        if predecessor_recurrence_sign_refutation(arena, ground, quantifier) {
            return Ok(true);
        }
    }
    for &quantifier in foralls {
        if crate::quant_nested_xor_cert::int_nested_xor_refutation(arena, &[quantifier]).is_some()
            && let Some(instance) = nested_xor_discriminator_instance(arena, quantifier)?
        {
            let mut probe = ground.to_vec();
            probe.push(instance);
            if matches!(
                quantifier_qf_check(arena, &probe, config, deadline, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    for &quantifier in foralls {
        if crate::quant_residue_cert::int_euclidean_residue_refutation(arena, &[quantifier])
            .is_some()
            && let Some(instance) = euclidean_residue_instance(arena, quantifier)?
        {
            let mut probe = ground.to_vec();
            probe.push(instance);
            if matches!(
                quantifier_qf_check(arena, &probe, config, deadline, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    for &quantifier in foralls {
        if crate::quant_affine_growth_cert::int_affine_growth_refutation(arena, &[quantifier])
            .is_some()
            && let Some(instances) = affine_growth_instances(arena, quantifier)?
        {
            let mut probe = ground.to_vec();
            probe.extend(instances);
            if matches!(
                quantifier_qf_check(arena, &probe, config, deadline, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

const MAX_PREDECESSOR_RECURRENCE_INDEX: i128 = 64;

/// Proves a bounded sign contradiction for
/// `f(0)=b ∧ ∀x>0. f(x)=c*f(x-1)`. Integer induction gives
/// `sign(f(n)) = sign(b) * sign(c)^n` (with zero absorbing), so a contrary
/// strict sign assertion is impossible. Every source term is matched exactly;
/// no expanded `c^n` value is computed, avoiding overflow on bignumber rows.
fn predecessor_recurrence_sign_refutation(
    arena: &TermArena,
    ground: &[TermId],
    quantifier: TermId,
) -> bool {
    let (binders, body) = peel_foralls(arena, quantifier);
    let [binder] = binders.as_slice() else {
        return false;
    };
    if arena.symbol(*binder).1 != Sort::Int {
        return false;
    }
    let Some((function, coefficient)) = match_predecessor_recurrence(arena, body, *binder) else {
        return false;
    };

    let mut bases = Vec::new();
    let mut sign_targets = Vec::new();
    for &assertion in ground {
        if let Some(base) = match_recurrence_base(arena, assertion, function) {
            bases.push(base);
        }
        if let Some(target) = match_recurrence_sign_target(arena, assertion, function) {
            sign_targets.push(target);
        }
    }
    for base in bases {
        for &(index, requires_positive) in &sign_targets {
            let sign = if coefficient == 0 {
                0
            } else if coefficient < 0 && index % 2 != 0 {
                -base.signum()
            } else {
                base.signum()
            };
            if (requires_positive && sign <= 0) || (!requires_positive && sign >= 0) {
                return true;
            }
        }
    }
    false
}

fn is_binder_predecessor(arena: &TermArena, term: TermId, binder: SymbolId) -> bool {
    let TermNode::App { op, args } = arena.node(term) else {
        return false;
    };
    match op {
        Op::IntSub if args.len() == 2 => {
            matches!(arena.node(args[0]), TermNode::Symbol(symbol) if *symbol == binder)
                && search_int_constant(arena, args[1]) == Some(1)
        }
        Op::IntAdd if args.len() == 2 => {
            (matches!(arena.node(args[0]), TermNode::Symbol(symbol) if *symbol == binder)
                && search_int_constant(arena, args[1]) == Some(-1))
                || (matches!(arena.node(args[1]), TermNode::Symbol(symbol) if *symbol == binder)
                    && search_int_constant(arena, args[0]) == Some(-1))
        }
        _ => false,
    }
}

fn match_predecessor_recurrence(
    arena: &TermArena,
    body: TermId,
    binder: SymbolId,
) -> Option<(FuncId, i128)> {
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [guard, equation] = &**args else {
        return None;
    };
    if !is_positive_binder_guard(arena, *guard, binder) {
        return None;
    }
    let TermNode::App { op: Op::Eq, args } = arena.node(*equation) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match_recurrence_equation_sides(arena, *left, *right, binder)
        .or_else(|| match_recurrence_equation_sides(arena, *right, *left, binder))
}

fn match_recurrence_equation_sides(
    arena: &TermArena,
    direct: TermId,
    product: TermId,
    binder: SymbolId,
) -> Option<(FuncId, i128)> {
    let (function, argument) = as_unary_apply(arena, direct)?;
    if !matches!(arena.node(argument), TermNode::Symbol(symbol) if *symbol == binder) {
        return None;
    }
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(product)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    for (constant, recurrence) in [(*left, *right), (*right, *left)] {
        let Some(coefficient) = search_int_constant(arena, constant) else {
            continue;
        };
        let Some((found, predecessor)) = as_unary_apply(arena, recurrence) else {
            continue;
        };
        if found == function && is_binder_predecessor(arena, predecessor, binder) {
            return Some((function, coefficient));
        }
    }
    None
}

fn is_positive_binder_guard(arena: &TermArena, term: TermId, binder: SymbolId) -> bool {
    let TermNode::App { op, args } = arena.node(term) else {
        return false;
    };
    let [left, right] = &**args else {
        return false;
    };
    match op {
        Op::IntGt => {
            matches!(arena.node(*left), TermNode::Symbol(symbol) if *symbol == binder)
                && search_int_constant(arena, *right) == Some(0)
        }
        Op::IntLt => {
            search_int_constant(arena, *left) == Some(0)
                && matches!(arena.node(*right), TermNode::Symbol(symbol) if *symbol == binder)
        }
        _ => false,
    }
}

fn match_recurrence_base(arena: &TermArena, term: TermId, function: FuncId) -> Option<i128> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    for (application, value) in [(*left, *right), (*right, *left)] {
        let Some((found, argument)) = as_unary_apply(arena, application) else {
            continue;
        };
        if found == function && search_int_constant(arena, argument) == Some(0) {
            return search_int_constant(arena, value);
        }
    }
    None
}

fn match_recurrence_sign_target(
    arena: &TermArena,
    term: TermId,
    function: FuncId,
) -> Option<(i128, bool)> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let (application, requires_positive) = match op {
        Op::IntLt if search_int_constant(arena, *right) == Some(0) => (*left, false),
        Op::IntLt if search_int_constant(arena, *left) == Some(0) => (*right, true),
        Op::IntGt if search_int_constant(arena, *right) == Some(0) => (*left, true),
        Op::IntGt if search_int_constant(arena, *left) == Some(0) => (*right, false),
        _ => return None,
    };
    let (found, argument) = as_unary_apply(arena, application)?;
    let index = search_int_constant(arena, argument)?;
    (found == function && (1..=MAX_PREDECESSOR_RECURRENCE_INDEX).contains(&index))
        .then_some((index, requires_positive))
}

fn as_unary_apply(arena: &TermArena, term: TermId) -> Option<(FuncId, TermId)> {
    let TermNode::App {
        op: Op::Apply(function),
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [argument] = &**args else {
        return None;
    };
    Some((*function, *argument))
}

fn quantifier_qf_check(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
) -> Result<CheckResult, SolverError> {
    stats.qf_checks += 1;
    let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
        return Ok(egraph_timeout());
    };
    check_auto(arena, ground, &remaining)
}

#[allow(clippy::too_many_arguments)]
fn admit_next_source_batch(
    arena: &mut TermArena,
    assertions: &[TermId],
    matcher: &mut IncrementalEmatchSession,
    seen: &mut HashSet<TermId>,
    ground: &mut Vec<TermId>,
    retained: &mut HashMap<TermId, QuantifierGroundDerivation>,
    generations: &mut TermGenerations,
    deadline: Option<Instant>,
) -> Vec<TermId> {
    matcher.extend_ground_with_derivations(arena, ground, retained);
    let GeneratedGroundBatch {
        mut urgent,
        units,
        mut deferred,
        derivations,
    } = collect_generated_ground(matcher, arena, assertions, deadline);
    urgent.sort_by_key(|term| term.index());
    urgent.dedup();
    deferred.sort_by_key(|term| term.index());
    deferred.dedup();

    let urgent_candidates = urgent.len();
    let unit_candidates = units.len();
    let deferred_candidates = deferred.len();
    // Conflict AND unit/propagation traffic is admitted eagerly and
    // unbudgeted, exactly as the historical single urgent pool (index-sorted
    // merge). A measured attempt to budget the unit pool shallow-first
    // regressed three unit-heavy refuters that main solves in ~3s by dumping
    // units fast (uf.590503, uf.651233, x2015..1276224 all went
    // unsat -> unknown) while flipping none of the unit-flood files — the
    // unit budget was net-negative, so only the deferred pool is budgeted.
    urgent.extend(units);
    urgent.sort_by_key(|term| term.index());
    urgent.dedup();
    let mut admitted = admit_generated_ground(
        arena,
        assertions,
        urgent,
        seen,
        ground,
        retained,
        &derivations,
        generations,
    );
    let mut pool = "urgent";
    // Once urgent traffic is exhausted, release unresolved clauses so mutually
    // constraining instances preserve the legacy loop's reach.
    if admitted.is_empty() {
        if ground.len() >= FLOOD_THROTTLE_MIN_GROUND {
            deferred = budget_flood_slice(deferred, seen, &derivations, generations);
        }
        admitted = admit_generated_ground(
            arena,
            assertions,
            deferred,
            seen,
            ground,
            retained,
            &derivations,
            generations,
        );
        pool = "deferred";
    }
    if floodprobe_enabled() {
        eprintln!(
            "FLOODPROBE round-admit urgent_cand={urgent_candidates} unit_cand={unit_candidates} \
             deferred_cand={deferred_candidates} admitted={} pool={pool} ground={}",
            admitted.len(),
            ground.len(),
        );
    }
    admitted
}

/// Flood-regime slicing for the deferred admission pool: pools at or under
/// [`FLOOD_ROUND_ADMISSION_CAP`] pass through untouched (byte-identical
/// historical admission). Larger pools keep every candidate at or under
/// [`FLOOD_EAGER_GENERATION_MAX`] eagerly, in the historical index order
/// (Z3's `qi.eager_threshold`: shallow-derivation instances are never
/// delayed — delaying them was measured to lose ~3-4s refuters that win off
/// the dump itself), and narrow only the deeper-derived remainder to the
/// shallowest-generation slice of the candidates NOT yet admitted (the pool
/// re-materializes already-admitted instances every round; without the `seen`
/// filter the deep prefix is all stale and the loop reaches a false fixpoint
/// with thousands of unseen candidates waiting). The deep remainder is never
/// dropped — the retained matcher re-materializes and re-classifies it
/// (possibly as a conflict by then) on every later round.
fn budget_flood_slice(
    pool: Vec<TermId>,
    seen: &HashSet<TermId>,
    derivations: &HashMap<TermId, QuantifierGroundDerivation>,
    generations: &TermGenerations,
) -> Vec<TermId> {
    if pool.len() <= FLOOD_ROUND_ADMISSION_CAP {
        return pool;
    }
    let mut eager = Vec::new();
    let mut deep: Vec<(u32, TermId)> = Vec::new();
    for term in pool {
        let generation = derivations.get(&term).map_or(u32::MAX, |derivation| {
            generations.derivation_generation(derivation)
        });
        if generation <= FLOOD_EAGER_GENERATION_MAX {
            eager.push(term);
        } else if !seen.contains(&term) {
            deep.push((generation, term));
        }
    }
    deep.sort_by_key(|&(generation, term)| (generation, term.index()));
    deep.truncate(FLOOD_ROUND_ADMISSION_CAP);
    eager.extend(deep.into_iter().map(|(_, term)| term));
    eager
}

fn floodprobe_enabled() -> bool {
    std::env::var_os("AXEYUM_FLOODPROBE").is_some()
}

/// Z3-style instantiation generations (T2.6.4; `qi_queue.cpp` cost
/// `(+ weight generation)`): subterms of the original assertions are
/// generation 0, and every term first introduced by an admitted instance
/// carries `1 + max(generation of the instance's binding tuple)`. Generations
/// only ORDER and BUDGET deferred admission in the flood regime and select the
/// subset-first final check — they never drop an instance outright, so the
/// admission fixpoint's reach on sub-flood files is unchanged.
struct TermGenerations {
    by_term: HashMap<TermId, u32>,
}

impl TermGenerations {
    fn seed_sources(arena: &TermArena, assertions: &[TermId]) -> Self {
        let mut by_term = HashMap::new();
        let mut stack: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if by_term.insert(term, 0).is_some() {
                continue;
            }
            if let TermNode::App { args, .. } = arena.node(term) {
                stack.extend(args.iter().copied());
            }
        }
        Self { by_term }
    }

    fn generation(&self, term: TermId) -> u32 {
        self.by_term.get(&term).copied().unwrap_or(0)
    }

    /// The generation an admitted term derived by `derivation` carries:
    /// one past the deepest binding in its witness tuple.
    fn derivation_generation(&self, derivation: &QuantifierGroundDerivation) -> u32 {
        let bindings = match derivation {
            QuantifierGroundDerivation::Instance(certificate) => &certificate.bindings,
            QuantifierGroundDerivation::Propagation(propagation) => &propagation.bindings,
        };
        bindings
            .iter()
            .map(|&binding| self.generation(binding))
            .max()
            .unwrap_or(0)
            .saturating_add(1)
    }

    /// Records `generation` for every subterm of an admitted term that has no
    /// generation yet (earlier-assigned subterms keep their shallower value).
    fn record_admitted(&mut self, arena: &TermArena, term: TermId, generation: u32) {
        let mut stack = vec![term];
        while let Some(term) = stack.pop() {
            if self.by_term.contains_key(&term) {
                continue;
            }
            self.by_term.insert(term, generation);
            if let TermNode::App { args, .. } = arena.node(term) {
                stack.extend(args.iter().copied());
            }
        }
    }
}

/// `AXEYUM_FLOODPROBE` diagnostics at the ground-cap exit: how much of the
/// admitted instance traffic was ever *determined* by the equality reasoning
/// (an instance whose clause value is still `Undetermined` against the final
/// e-graph never interacted with any refutation attempt's equality core), and
/// how deep the derivation chain ran (`gen1` = every binding is a subterm of
/// the original assertions; `deeper` = at least one binding was itself created
/// by instantiation — Z3's "generation" axis).
fn floodprobe_cap_census(
    arena: &TermArena,
    matcher: &IncrementalEmatchSession,
    retained: &HashMap<TermId, QuantifierGroundDerivation>,
    assertions: &[TermId],
) {
    let mut source_subterms: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !source_subterms.insert(term) {
            continue;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    let (mut instances, mut propagations) = (0usize, 0usize);
    let (mut val_true, mut val_false, mut val_unit, mut val_undet) =
        (0usize, 0usize, 0usize, 0usize);
    let (mut gen1, mut deeper) = (0usize, 0usize);
    let mut per_universal: HashMap<TermId, usize> = HashMap::new();
    for derivation in retained.values() {
        let QuantifierGroundDerivation::Instance(certificate) = derivation else {
            propagations += 1;
            continue;
        };
        instances += 1;
        *per_universal.entry(certificate.assertion).or_default() += 1;
        if certificate
            .bindings
            .iter()
            .all(|binding| source_subterms.contains(binding))
        {
            gen1 += 1;
        } else {
            deeper += 1;
        }
        match evaluate_equality_clause_with(arena, certificate.instance, &mut |lhs, rhs| {
            matcher.equality(lhs, rhs)
        }) {
            Some(ClauseValue::True) => val_true += 1,
            Some(ClauseValue::False) => val_false += 1,
            Some(ClauseValue::Unit) => val_unit += 1,
            Some(ClauseValue::Undetermined) | None => val_undet += 1,
        }
    }
    eprintln!(
        "FLOODPROBE cap-census instances={instances} propagations={propagations} \
         clause_true={val_true} clause_false={val_false} clause_unit={val_unit} \
         clause_undet={val_undet} gen1={gen1} deeper={deeper}"
    );
    let mut per: Vec<(TermId, usize)> = per_universal.into_iter().collect();
    per.sort_by_key(|(term, _)| term.index());
    for (assertion, count) in per {
        eprintln!(
            "FLOODPROBE   universal assertion_term={} instances={count}",
            assertion.index()
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn admit_generated_ground(
    arena: &mut TermArena,
    assertions: &[TermId],
    terms: Vec<TermId>,
    seen: &mut HashSet<TermId>,
    ground: &mut Vec<TermId>,
    retained: &mut HashMap<TermId, QuantifierGroundDerivation>,
    candidates: &HashMap<TermId, QuantifierGroundDerivation>,
    generations: &mut TermGenerations,
) -> Vec<TermId> {
    let mut added = Vec::new();
    for term in terms {
        if ground.len() >= MAX_GROUND_TERMS {
            break;
        }
        let Some(derivation) = candidates.get(&term) else {
            continue;
        };
        if !check_quantifier_ground_derivation(arena, assertions, derivation) {
            continue;
        }
        if seen.insert(term) {
            let generation = generations.derivation_generation(derivation);
            generations.record_admitted(arena, term, generation);
            retained.insert(term, derivation.clone());
            ground.push(term);
            added.push(term);
        }
    }
    added
}

struct GeneratedGroundBatch {
    urgent: Vec<TermId>,
    /// Unit-clause instances and checked propagation literals: e-graph-driving
    /// equality traffic, budgeted shallow-first in the flood regime.
    units: Vec<TermId>,
    deferred: Vec<TermId>,
    derivations: HashMap<TermId, QuantifierGroundDerivation>,
}

struct ScopedCandidateBatch {
    batch: GeneratedGroundBatch,
    pattern_executions: usize,
    applications_scanned: usize,
}

/// Retained equality-abstraction CDCL(T) state for checked generated clauses
/// (ADR-0119). It can prove refutations early but never produces product SAT.
struct OnlineQuantifierClauseSession {
    solver: CdclT,
    theory: EufTheory,
    atom_terms: Vec<TermId>,
    atom_variables: HashMap<TermId, usize>,
    inserted_clauses: usize,
    inserted_literals: usize,
    solve_calls: usize,
    last_outcome: Option<CdcltOutcome>,
    limits: OnlineQuantifierLimits,
    /// The loop's wall-clock bound. Batch admission re-checks thousands of
    /// derivations per round; without a per-term deadline check that single
    /// unit can overrun the whole budget on predicate-heavy files.
    deadline: Option<Instant>,
}

#[derive(Debug, Clone, Copy)]
struct OnlineQuantifierLimits {
    variables: usize,
    clauses: usize,
    literals: usize,
}

impl OnlineQuantifierClauseSession {
    fn new(arena: &TermArena, ground: &[TermId], deadline: Option<Instant>) -> Option<Self> {
        Self::new_with_limits(arena, ground, deadline, ONLINE_QUANTIFIER_LIMITS)
    }

    fn new_with_limits(
        arena: &TermArena,
        ground: &[TermId],
        deadline: Option<Instant>,
        limits: OnlineQuantifierLimits,
    ) -> Option<Self> {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return None;
        }
        let mut atom_terms = Vec::new();
        let mut seen = HashSet::new();
        for &assertion in ground {
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return None;
            }
            collect_euf_atoms(arena, assertion, &mut atom_terms, &mut seen);
        }
        let atom_variables: HashMap<TermId, usize> = atom_terms
            .iter()
            .copied()
            .enumerate()
            .map(|(variable, term)| (term, variable))
            .collect();
        let mut encoder = EufEncoder::new(&atom_terms).with_bool_apply_atoms();
        let mut clauses = Vec::new();
        for &assertion in ground {
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return None;
            }
            let top = encoder.encode(arena, assertion, &mut clauses)?;
            clauses.push(vec![crate::euf_egraph::Lit {
                var: top,
                positive: true,
            }]);
        }
        let literal_count = clauses.iter().map(Vec::len).sum::<usize>();
        if encoder.var_count > limits.variables
            || clauses.len() > limits.clauses
            || literal_count > limits.literals
        {
            return None;
        }
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                clause
                    .into_iter()
                    .map(|literal| CdcltLit {
                        var: literal.var,
                        positive: literal.positive,
                    })
                    .collect()
            })
            .collect();
        let theory = EufTheory::new(arena, &atom_terms).with_deadline(deadline);
        let solver = CdclT::new(encoder.var_count, atom_terms.len(), clauses, deadline);
        Some(Self {
            solver,
            theory,
            atom_terms,
            atom_variables,
            inserted_clauses: 0,
            inserted_literals: 0,
            solve_calls: 0,
            last_outcome: None,
            limits,
            deadline,
        })
    }

    /// Rechecks and inserts one batch at level zero, then resumes the retained
    /// search. `None` disables the accelerator and leaves fresh-QF fallback live.
    fn add_checked_batch(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        terms: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
    ) -> Option<CdcltOutcome> {
        self.solver.backtrack_to_root(&mut self.theory);
        for &term in terms {
            // Deadline-bound the per-term derivation re-checks: a multi-
            // thousand-instance batch is otherwise a deadline-blind unit that
            // can overrun the whole budget. Expiry only disables the
            // accelerator; the fresh-QF fallback stays live.
            if self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                return None;
            }
            let derivation = derivations.get(&term)?;
            if !check_quantifier_ground_derivation(arena, assertions, derivation) {
                return None;
            }
            self.add_equality_clause(arena, term)?;
        }
        Some(self.solve_current())
    }

    fn solve_current(&mut self) -> CdcltOutcome {
        self.solve_calls += 1;
        let outcome = self.solver.solve(&mut self.theory);
        self.last_outcome = Some(outcome);
        outcome
    }

    /// Equality atoms true in the current complete SAT candidate, in stable
    /// theory-atom order. Predicate atoms are excluded — the scoped candidate
    /// matcher merges equality endpoints only. Non-SAT states expose no
    /// candidate facts.
    fn true_equality_terms(&self, arena: &TermArena) -> Vec<TermId> {
        if self.last_outcome != Some(CdcltOutcome::Sat) {
            return Vec::new();
        }
        self.atom_terms
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(atom, term)| {
                if !matches!(arena.node(term), TermNode::App { op: Op::Eq, args } if args.len() == 2)
                {
                    return None;
                }
                let variable = self.solver.theory_variable(atom)?;
                (self.solver.value(variable) == Some(true)).then_some(term)
            })
            .collect()
    }

    fn add_equality_clause(&mut self, arena: &TermArena, term: TermId) -> Option<()> {
        let atoms = match equality_clause_atoms(arena, term) {
            OnlineClauseShape::Unsupported => return None,
            OnlineClauseShape::Tautology => return Some(()),
            OnlineClauseShape::Atoms(atoms) => atoms,
        };
        if self.solver.clause_count() >= self.limits.clauses
            || self.inserted_literals.saturating_add(atoms.len()) > self.limits.literals
        {
            return None;
        }
        let mut clause = Vec::with_capacity(atoms.len());
        for (atom_term, positive) in atoms {
            let variable = self.ensure_atom(arena, atom_term)?;
            clause.push(CdcltLit {
                var: variable,
                positive,
            });
        }
        clause.sort_by_key(|literal| (literal.var, literal.positive));
        if clause
            .windows(2)
            .any(|pair| pair[0].var == pair[1].var && pair[0].positive != pair[1].positive)
        {
            return Some(()); // complementary literals make the clause true
        }
        clause.dedup();
        self.inserted_literals += clause.len();
        self.inserted_clauses += 1;
        self.solver.add_permanent_clause(clause);
        Some(())
    }

    fn ensure_atom(&mut self, arena: &TermArena, atom_term: TermId) -> Option<usize> {
        if let Some(&variable) = self.atom_variables.get(&atom_term) {
            return Some(variable);
        }
        if self.solver.variable_count() >= self.limits.variables {
            return None;
        }
        let (variable, solver_atom) = self.solver.add_theory_variable();
        let theory_atom = self.theory.add_atom_at_root(arena, atom_term).ok()?;
        if solver_atom != theory_atom {
            return None;
        }
        self.atom_terms.push(atom_term);
        self.atom_variables.insert(atom_term, variable);
        Some(variable)
    }
}

enum OnlineClauseShape {
    Unsupported,
    Tautology,
    Atoms(Vec<(TermId, bool)>),
}

/// Classifies a generated term as an unsupported shape, a tautology, or an
/// equality/predicate clause represented by underlying atom terms and
/// polarities. Atoms are data-sorted equalities and Boolean predicate
/// applications — exactly the shapes [`EufTheory`] registers.
fn equality_clause_atoms(arena: &TermArena, term: TermId) -> OnlineClauseShape {
    let mut literals = Vec::new();
    collect_clause_literals(arena, term, &mut literals);
    let mut atoms = Vec::new();
    for literal in literals {
        match arena.node(literal) {
            TermNode::BoolConst(true) => return OnlineClauseShape::Tautology,
            TermNode::BoolConst(false) => {}
            TermNode::App {
                op: Op::BoolNot,
                args,
            } if args.len() == 1 && online_clause_atom(arena, args[0]) => {
                atoms.push((args[0], false));
            }
            _ if online_clause_atom(arena, literal) => {
                atoms.push((literal, true));
            }
            _ => return OnlineClauseShape::Unsupported,
        }
    }
    OnlineClauseShape::Atoms(atoms)
}

/// Whether `term` is an atom shape the online session's [`EufTheory`] registers:
/// a binary equality (Boolean equality merges its sides, which is sound: `iff`
/// is Boolean equality and congruence respects it — the historical session
/// behavior) or a Boolean-sorted predicate application.
fn online_clause_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App { op: Op::Eq, args } => args.len() == 2,
        TermNode::App {
            op: Op::Apply(_), ..
        } => arena.sort_of(term) == Sort::Bool,
        _ => false,
    }
}

fn collect_generated_ground(
    matcher: &mut IncrementalEmatchSession,
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> GeneratedGroundBatch {
    let mut urgent = Vec::new();
    let mut units = Vec::new();
    let mut deferred = Vec::new();
    let mut propagations = Vec::new();
    let mut derivations = HashMap::new();
    for batch in matcher.lazy_clause_batches(arena, deadline) {
        urgent.extend(batch.urgent);
        units.extend(batch.units);
        propagations.extend(batch.propagations);
        deferred.extend(batch.deferred);
        for (instance, certificate) in batch.instance_certificates {
            derivations
                .entry(instance)
                .or_insert(QuantifierGroundDerivation::Instance(certificate));
        }
    }
    for (term, derivation) in checked_propagation_additions(arena, assertions, &propagations) {
        units.push(term);
        derivations.entry(term).or_insert(derivation);
    }
    GeneratedGroundBatch {
        urgent,
        units,
        deferred,
        derivations,
    }
}

#[allow(clippy::too_many_arguments)]
fn finish_quantified_ground_check(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    stats: &mut QuantifierLoopStats,
    cache: &mut QuantifierTermCache,
    generations: &TermGenerations,
) -> Result<CheckResult, SolverError> {
    // Flood regime: the full-set final check over a near-cap conjunction is
    // itself a wall (measured 26.7s-then-unknown over 8192 conjuncts on
    // `uf.1158058`). First try the shallow-generation subset — sources plus
    // instances derived purely from source terms — under a fractional budget;
    // subset unsat refutes the conjunction (every conjunct is asserted or an
    // admitted instance of an asserted universal), so this is strictly
    // additive: it can only turn an unknown into unsat.
    if ground.len() >= FLOOD_FINAL_SUBSET_CHECK_MIN_GROUND {
        let subset: Vec<TermId> = ground
            .iter()
            .copied()
            .filter(|&term| generations.generation(term) <= FLOOD_FINAL_SUBSET_MAX_GENERATION)
            .collect();
        if subset.len() < ground.len()
            && deadline.is_none_or(|d| Instant::now() < d)
            && matches!(
                quantifier_qf_refutation_check(
                    arena,
                    &subset,
                    config,
                    fractional_deadline(deadline, MID_LOOP_CHECK_BUDGET_DIVISOR),
                    stats,
                    cache,
                )?,
                CheckResult::Unsat
            )
        {
            return Ok(CheckResult::Unsat);
        }
    }
    match quantifier_qf_refutation_check(arena, ground, config, deadline, stats, cache)? {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        _ => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "e-matching instantiation did not refute within the round budget".to_owned(),
        })),
    }
}

fn checked_propagation_additions(
    arena: &mut TermArena,
    assertions: &[TermId],
    propagations: &[QuantifierClausePropagationCertificate],
) -> Vec<(TermId, QuantifierGroundDerivation)> {
    let checked = check_quantifier_clause_propagations(arena, assertions, propagations);
    propagations
        .iter()
        .map(|propagation| {
            if checked {
                (
                    propagation.propagated_literal,
                    QuantifierGroundDerivation::Propagation(Box::new(propagation.clone())),
                )
            } else {
                (
                    propagation.source_instance,
                    QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                        assertion: propagation.assertion,
                        bindings: propagation.bindings.clone(),
                        instance: propagation.source_instance,
                    }),
                )
            }
        })
        .collect()
}

/// Instantiates the universal `forall_term` by e-matching a trigger against the
/// `ground` terms, returning the ground instances of its body. Returns an empty
/// vector when `forall_term` is not a universal, has no trigger covering all bound
/// variables, or the trigger's symbols do not occur in the ground terms.
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn instantiate_forall_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Vec<TermId> {
    let Some((vars, body, tuples)) = witness_tuples_via_egraph(arena, ground, forall_term) else {
        return Vec::new();
    };
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut instances = Vec::new();
    for tuple in &tuples {
        let replacements: HashMap<TermId, TermId> = var_terms
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) {
            instances.push(instance);
        }
    }
    instances.sort_by_key(|t| t.index());
    instances.dedup();
    instances
}

/// One round of conservative lazy clause evaluation (ADR-0110).
///
/// `urgent` contains complete source instances whose equality clause is
/// already false (conflicts). `units` contains instances with exactly one
/// undetermined literal whose detached propagation could not be certified.
/// `deferred` contains multi-undetermined clauses and every shape outside the
/// supported clause fragment. Clauses already true in the recorded ground
/// equality context are omitted.
#[derive(Debug, Default)]
struct LazyClauseBatch {
    urgent: Vec<TermId>,
    units: Vec<TermId>,
    propagations: Vec<QuantifierClausePropagationCertificate>,
    deferred: Vec<TermId>,
    instance_certificates: BTreeMap<TermId, QuantifierInstanceCertificate>,
    redundant: usize,
}

struct CompiledUniversal {
    assertion: TermId,
    vars: Vec<SymbolId>,
    var_terms: Vec<TermId>,
    body: TermId,
    pattern_indices: Vec<usize>,
    /// Whether instances of this universal may be **asserted**. `true` for every
    /// universal that is itself an assertion (the historical case, and the only
    /// case when the nested layout is off). `false` for a [`NestedRegistration`]:
    /// its triggers are compiled and matched so the driver holds first-class
    /// state for it, but `A ∨ (∀y. B(y))` does not entail `B(t)`, so nothing it
    /// produces may enter the ground set or a certificate.
    active: bool,
    /// For a registration (`active == false`), where it sits inside its trusted
    /// owner. Present exactly when the positive replacement `owner ⊨
    /// owner[∀y.B := B(t)]` applies; the driver turns each matched tuple into
    /// that replacement instead of the (unentailed) bare instance.
    context: Option<PositiveContext>,
}

/// The source trigger a compiled [`Pattern`] came from, kept so term invention
/// can build ground trigger instances by substitution. `var_terms` are the
/// owning universal's bound-variable terms occurring in `trigger`, in
/// first-occurrence order.
#[derive(Debug, Clone)]
struct PatternTrigger {
    trigger: TermId,
    var_terms: Vec<TermId>,
}

/// Named facts that replay one false sibling of a detached quantified clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierFalseSiblingJustification {
    /// The exact false equality/disequality literal from the source instance.
    pub literal: TermId,
    /// Sorted source or recursively derived equality/disequality terms sufficient
    /// to make `literal` false in a fresh congruence closure.
    pub reasons: Vec<TermId>,
}

/// Exact provenance for one complete ground universal instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierInstanceCertificate {
    /// The untouched original universal assertion.
    pub assertion: TermId,
    /// Ground terms substituted for the universal prefix, outermost first.
    pub bindings: Vec<TermId>,
    /// The exact reconstructed ground instance.
    pub instance: TermId,
}

/// A generated ground equality/disequality derivation used by a later
/// false-sibling justification (ADR-0118).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifierGroundDerivation {
    /// A complete exact universal instance.
    Instance(QuantifierInstanceCertificate),
    /// An earlier independently checked detached propagation.
    Propagation(Box<QuantifierClausePropagationCertificate>),
}

impl QuantifierGroundDerivation {
    fn conclusion(&self) -> TermId {
        match self {
            Self::Instance(certificate) => certificate.instance,
            Self::Propagation(certificate) => certificate.propagated_literal,
        }
    }
}

/// Replayable implication from one universal instance plus checked ground facts
/// to a detached equality/disequality literal (ADR-0117/0118).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierClausePropagationCertificate {
    /// The untouched original universal assertion.
    pub assertion: TermId,
    /// Ground terms substituted for the universal prefix, outermost first.
    pub bindings: Vec<TermId>,
    /// The exact complete source instance reconstructed from `assertion`.
    pub source_instance: TermId,
    /// The sole non-false equality/disequality literal propagated to QF search.
    pub propagated_literal: TermId,
    /// Every other source-instance literal, in clause order.
    pub false_siblings: Vec<QuantifierFalseSiblingJustification>,
    /// Sorted derivations for every named false-sibling reason that is not an
    /// original assertion. Source-only ADR-0117 certificates leave this empty.
    pub derived_reasons: Vec<QuantifierGroundDerivation>,
}

/// Independently checks a detached quantifier-clause propagation.
///
/// The checker reconstructs the complete universal instance and evaluates every
/// false sibling in a fresh e-graph containing only its named source or checked
/// derived reasons. It does not consult retained matching/search state.
#[must_use]
pub fn check_quantifier_clause_propagation(
    arena: &mut TermArena,
    assertions: &[TermId],
    certificate: &QuantifierClausePropagationCertificate,
) -> bool {
    check_quantifier_clause_propagations(arena, assertions, std::slice::from_ref(certificate))
}

/// Independently checks a batch of detached propagations under one shared
/// recursive replay budget.
#[must_use]
pub fn check_quantifier_clause_propagations(
    arena: &mut TermArena,
    assertions: &[TermId],
    certificates: &[QuantifierClausePropagationCertificate],
) -> bool {
    if certificates.is_empty() {
        return true;
    }
    let mut checker = QuantifierProvenanceChecker {
        assertions: assertions.iter().copied().collect(),
        remaining_nodes: MAX_QUANTIFIER_PROVENANCE_NODES,
    };
    certificates
        .iter()
        .all(|certificate| checker.check_propagation(arena, certificate, 0))
}

/// Independently checks one generated ground derivation against the untouched
/// assertion set. This is the admission gate for retained online clauses.
#[must_use]
pub fn check_quantifier_ground_derivation(
    arena: &mut TermArena,
    assertions: &[TermId],
    derivation: &QuantifierGroundDerivation,
) -> bool {
    let mut checker = QuantifierProvenanceChecker {
        assertions: assertions.iter().copied().collect(),
        remaining_nodes: MAX_QUANTIFIER_PROVENANCE_NODES,
    };
    checker.check_derivation(arena, derivation, 0)
}

const MAX_QUANTIFIER_PROVENANCE_DEPTH: usize = 16;
const MAX_QUANTIFIER_PROVENANCE_NODES: usize = 4096;

struct QuantifierProvenanceChecker {
    assertions: HashSet<TermId>,
    remaining_nodes: usize,
}

impl QuantifierProvenanceChecker {
    fn check_propagation(
        &mut self,
        arena: &mut TermArena,
        certificate: &QuantifierClausePropagationCertificate,
        depth: usize,
    ) -> bool {
        if depth > MAX_QUANTIFIER_PROVENANCE_DEPTH || !self.take_node() {
            return false;
        }
        let instance = QuantifierInstanceCertificate {
            assertion: certificate.assertion,
            bindings: certificate.bindings.clone(),
            instance: certificate.source_instance,
        };
        if equality_literal(arena, certificate.propagated_literal).is_none()
            || !self.check_instance(arena, &instance)
            || !Self::derivation_table_is_canonical(certificate)
        {
            return false;
        }

        let mut literals = Vec::new();
        collect_clause_literals(arena, certificate.source_instance, &mut literals);
        let Some(propagated_index) = literals
            .iter()
            .position(|&literal| literal == certificate.propagated_literal)
        else {
            return false;
        };
        if literals
            .iter()
            .skip(propagated_index + 1)
            .any(|&literal| literal == certificate.propagated_literal)
            || literals.len() != certificate.false_siblings.len() + 1
        {
            return false;
        }

        let required_derived: BTreeSet<TermId> = certificate
            .false_siblings
            .iter()
            .flat_map(|sibling| sibling.reasons.iter().copied())
            .filter(|reason| !self.assertions.contains(reason))
            .collect();
        let supplied_derived: BTreeSet<TermId> = certificate
            .derived_reasons
            .iter()
            .map(QuantifierGroundDerivation::conclusion)
            .collect();
        if required_derived != supplied_derived {
            return false;
        }
        for derivation in &certificate.derived_reasons {
            if !self.check_derivation(arena, derivation, depth + 1) {
                return false;
            }
        }

        let expected_siblings = literals
            .into_iter()
            .enumerate()
            .filter_map(|(index, literal)| (index != propagated_index).then_some(literal));
        let mut all_reasons = BTreeSet::new();
        for (expected, sibling) in expected_siblings.zip(&certificate.false_siblings) {
            if sibling.literal != expected
                || sibling
                    .reasons
                    .windows(2)
                    .any(|pair| pair[0].index() >= pair[1].index())
                || sibling
                    .reasons
                    .iter()
                    .any(|reason| !self.reason_is_available(certificate, *reason))
            {
                return false;
            }
            if matches!(arena.node(sibling.literal), TermNode::BoolConst(false)) {
                if !sibling.reasons.is_empty() {
                    return false;
                }
            } else {
                let mut facts = GroundEqualityContext::new(arena, &sibling.reasons);
                if evaluate_equality_clause(arena, sibling.literal, &mut facts)
                    != Some(ClauseValue::False)
                {
                    return false;
                }
            }
            all_reasons.extend(sibling.reasons.iter().copied());
        }
        let mut facts =
            GroundEqualityContext::new(arena, &all_reasons.into_iter().collect::<Vec<_>>());
        evaluate_equality_clause(arena, certificate.source_instance, &mut facts)
            == Some(ClauseValue::Unit)
    }

    fn check_derivation(
        &mut self,
        arena: &mut TermArena,
        derivation: &QuantifierGroundDerivation,
        depth: usize,
    ) -> bool {
        if depth > MAX_QUANTIFIER_PROVENANCE_DEPTH {
            return false;
        }
        match derivation {
            QuantifierGroundDerivation::Instance(certificate) => {
                self.take_node() && self.check_instance(arena, certificate)
            }
            QuantifierGroundDerivation::Propagation(certificate) => {
                self.check_propagation(arena, certificate, depth)
            }
        }
    }

    fn check_instance(
        &self,
        arena: &mut TermArena,
        certificate: &QuantifierInstanceCertificate,
    ) -> bool {
        if !self.assertions.contains(&certificate.assertion) {
            return false;
        }
        let (vars, body) = peel_foralls(arena, certificate.assertion);
        if vars.is_empty() || vars.len() != certificate.bindings.len() {
            return false;
        }
        let bound: HashSet<SymbolId> = vars.iter().copied().collect();
        if vars
            .iter()
            .zip(&certificate.bindings)
            .any(|(&var, &binding)| {
                arena.symbol(var).1 != arena.sort_of(binding)
                    || contains_any_symbol(arena, binding, &bound)
            })
        {
            return false;
        }
        let replacements: HashMap<TermId, TermId> = vars
            .iter()
            .map(|&var| arena.var(var))
            .zip(certificate.bindings.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        replace_subterms(arena, body, &replacements, &mut memo)
            .is_ok_and(|instance| instance == certificate.instance)
    }

    fn derivation_table_is_canonical(certificate: &QuantifierClausePropagationCertificate) -> bool {
        certificate
            .derived_reasons
            .windows(2)
            .all(|pair| pair[0].conclusion().index() < pair[1].conclusion().index())
    }

    fn reason_is_available(
        &self,
        certificate: &QuantifierClausePropagationCertificate,
        reason: TermId,
    ) -> bool {
        equality_literal_reason_shape(reason, &self.assertions, certificate)
    }

    fn take_node(&mut self) -> bool {
        let Some(remaining) = self.remaining_nodes.checked_sub(1) else {
            return false;
        };
        self.remaining_nodes = remaining;
        true
    }
}

fn equality_literal_reason_shape(
    reason: TermId,
    assertions: &HashSet<TermId>,
    certificate: &QuantifierClausePropagationCertificate,
) -> bool {
    assertions.contains(&reason)
        || certificate
            .derived_reasons
            .binary_search_by_key(&reason.index(), |derivation| {
                derivation.conclusion().index()
            })
            .is_ok()
}

#[derive(Debug, Default)]
struct PatternPathNode {
    children: BTreeMap<PatternPathStep, usize>,
    terminals: Vec<PatternPathTerminal>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct GroundArgumentFilter {
    argument_index: usize,
    declaration: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PatternPathStep {
    declaration: u32,
    argument_index: usize,
    ground_argument: Option<GroundArgumentFilter>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PatternPathTerminal {
    pattern_index: usize,
    start_declaration: Option<u32>,
}

#[derive(Debug, Clone, Copy)]
enum PatternFilterMode {
    ClassAndGround,
    #[cfg(test)]
    Unfiltered,
    #[cfg(test)]
    ClassOnly,
    #[cfg(test)]
    GroundOnly,
}

impl PatternFilterMode {
    fn use_class_labels(self) -> bool {
        match self {
            Self::ClassAndGround => true,
            #[cfg(test)]
            Self::ClassOnly => true,
            #[cfg(test)]
            Self::Unfiltered | Self::GroundOnly => false,
        }
    }

    fn use_ground_arguments(self) -> bool {
        match self {
            Self::ClassAndGround => true,
            #[cfg(test)]
            Self::GroundOnly => true,
            #[cfg(test)]
            Self::Unfiltered | Self::ClassOnly => false,
        }
    }
}

/// Shared child-to-root `(declaration, argument-index)` paths (ADR-0114).
#[derive(Debug)]
struct PatternPathIndex {
    nodes: Vec<PatternPathNode>,
}

impl Default for PatternPathIndex {
    fn default() -> Self {
        Self {
            nodes: vec![PatternPathNode::default()],
        }
    }
}

impl PatternPathIndex {
    fn add_pattern(&mut self, pattern: &Pattern, pattern_index: usize) {
        self.add_subpattern_paths(pattern, &[], pattern_index);
    }

    fn add_subpattern_paths(
        &mut self,
        pattern: &Pattern,
        outer_path: &[PatternPathStep],
        pattern_index: usize,
    ) {
        let Pattern::App(declaration, arguments) = pattern else {
            return;
        };
        let ground_argument =
            arguments
                .iter()
                .enumerate()
                .find_map(|(argument_index, argument)| match argument {
                    Pattern::App(declaration, children) if children.is_empty() => {
                        Some(GroundArgumentFilter {
                            argument_index,
                            declaration: *declaration,
                        })
                    }
                    Pattern::Var(_) | Pattern::App(_, _) => None,
                });
        for (argument_index, child) in arguments.iter().enumerate() {
            let mut path = Vec::with_capacity(outer_path.len() + 1);
            path.push(PatternPathStep {
                declaration: *declaration,
                argument_index,
                ground_argument,
            });
            path.extend_from_slice(outer_path);
            let start_declaration = match child {
                Pattern::App(declaration, _) => Some(*declaration),
                Pattern::Var(_) => None,
            };
            self.insert(
                &path,
                PatternPathTerminal {
                    pattern_index,
                    start_declaration,
                },
            );
            self.add_subpattern_paths(child, &path, pattern_index);
        }
    }

    fn insert(&mut self, path: &[PatternPathStep], terminal: PatternPathTerminal) {
        let mut node_index = 0;
        for &step in path {
            let next = if let Some(&next) = self.nodes[node_index].children.get(&step) {
                next
            } else {
                let next = self.nodes.len();
                self.nodes.push(PatternPathNode::default());
                self.nodes[node_index].children.insert(step, next);
                next
            };
            node_index = next;
        }
        self.nodes[node_index].terminals.push(terminal);
    }

    fn finish(&mut self) {
        for node in &mut self.nodes {
            node.terminals.sort_unstable();
            node.terminals.dedup();
        }
    }

    #[cfg(test)]
    fn affected_patterns(&self, egraph: &EGraph, starts: &[ENodeId]) -> BTreeSet<usize> {
        self.affected_patterns_with_filters(egraph, starts, PatternFilterMode::ClassAndGround)
    }

    fn affected_candidates(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
    ) -> BTreeMap<usize, BTreeSet<ENodeId>> {
        self.affected_candidates_with_filters(egraph, starts, PatternFilterMode::ClassAndGround)
    }

    #[cfg(test)]
    fn affected_patterns_with_filters(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
        filters: PatternFilterMode,
    ) -> BTreeSet<usize> {
        self.affected_candidates_with_filters(egraph, starts, filters)
            .into_keys()
            .collect()
    }

    fn affected_candidates_with_filters(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
        filters: PatternFilterMode,
    ) -> BTreeMap<usize, BTreeSet<ENodeId>> {
        let mut pending = Vec::new();
        let mut seen = HashSet::new();
        for &start in starts {
            let start = egraph.root(start);
            let state = (start, 0, start);
            if seen.insert(state) {
                pending.push(state);
            }
        }

        let mut candidates: BTreeMap<usize, BTreeSet<ENodeId>> = BTreeMap::new();
        while let Some((class, path_node, start_class)) = pending.pop() {
            for &parent in egraph.parents(class) {
                let declaration = egraph.decl(parent);
                for (argument_index, &argument) in egraph.args(parent).iter().enumerate() {
                    if egraph.root(argument) != class {
                        continue;
                    }
                    for (step, &next_path_node) in &self.nodes[path_node].children {
                        if step.declaration != declaration
                            || step.argument_index != argument_index
                            || (filters.use_ground_arguments()
                                && !Self::ground_argument_matches(egraph, parent, *step))
                        {
                            continue;
                        }
                        for terminal in &self.nodes[next_path_node].terminals {
                            if !filters.use_class_labels()
                                || terminal.start_declaration.is_none_or(|required| {
                                    egraph.class_has_declaration(start_class, required)
                                })
                            {
                                candidates
                                    .entry(terminal.pattern_index)
                                    .or_default()
                                    .insert(parent);
                            }
                        }
                        let state = (egraph.root(parent), next_path_node, start_class);
                        if seen.insert(state) {
                            pending.push(state);
                        }
                    }
                }
            }
        }
        candidates
    }

    fn ground_argument_matches(egraph: &EGraph, parent: ENodeId, step: PatternPathStep) -> bool {
        let Some(filter) = step.ground_argument else {
            return true;
        };
        egraph
            .args(parent)
            .get(filter.argument_index)
            .is_some_and(|&argument| egraph.class_has_declaration(argument, filter.declaration))
    }
}

#[derive(Debug, Clone, Copy)]
enum MergeInvalidationMode {
    ExactPaths,
    #[cfg(test)]
    ExactPathsFullPatterns,
    #[cfg(test)]
    ExactPathsUnfiltered,
    #[cfg(test)]
    ExactPathsClassOnly,
    #[cfg(test)]
    ExactPathsGroundOnly,
    #[cfg(test)]
    Declarations,
    #[cfg(test)]
    All,
}

/// Retained matching state for one quantified refutation attempt (ADR-0111/0112).
///
/// Patterns and bridge declaration ids are stable for the complete attempt.
/// Ground terms and equalities grow monotonically between rounds. Add-only
/// rounds extend a revision-checked e-graph index and rematch only patterns whose
/// root declaration gained an application. Merge rounds additionally rematch
/// roots reached through transitive e-graph parent paths. Generated top-level
/// terms retain exact-instance or checked-propagation derivations for later
/// false-sibling explanations.
/// `(assertion, binder prefix, body, admissible, positive-replacement context)`
/// — the per-universal input [`IncrementalEmatchSession::new_with_nested`]
/// compiles, before triggers are selected.
type CompiledUniversalSpec = (TermId, Vec<SymbolId>, TermId, bool, Option<PositiveContext>);

struct IncrementalEmatchSession {
    bridge: InstBridge,
    patterns: Vec<Pattern>,
    /// Source trigger per pattern index (the first universal that compiled the
    /// pattern), for term invention. `None` only if a pattern was registered
    /// without a source trigger.
    pattern_triggers: Vec<Option<PatternTrigger>>,
    patterns_by_root: HashMap<u32, Vec<usize>>,
    quantifiers_by_pattern: HashMap<usize, Vec<usize>>,
    merge_paths: PatternPathIndex,
    /// Patterns requiring a complete root-declaration scan (initialization and
    /// test-only conservative baselines).
    dirty_patterns: BTreeSet<usize>,
    /// Exact top applications added or reached since each pattern's last scan.
    candidate_patterns: BTreeMap<usize, BTreeSet<ENodeId>>,
    pattern_matches: Vec<Vec<Substitution>>,
    match_index: EMatchIndex,
    quantifiers: Vec<CompiledUniversal>,
    processed_ground: HashSet<TermId>,
    source_ground: HashSet<TermId>,
    ground_derivations: HashMap<TermId, QuantifierGroundDerivation>,
    equality_reason_terms: HashMap<u32, TermId>,
    disequality_nodes: Vec<(TermId, ENodeId, ENodeId)>,
    disequalities: HashSet<(ENodeId, ENodeId)>,
    match_rounds: usize,
    pattern_executions: usize,
    candidate_applications_scanned: usize,
    merge_invalidations: usize,
    merge_affected_patterns: usize,
    extensions: usize,
    /// Per-universal `(emitted joined tuples, starved joins)` — diagnostics
    /// for the `AXEYUM_QPROBE` fixpoint report only.
    join_stats: Vec<(usize, usize)>,
    /// Slice 3: `(quantifier index, witness tuple)` for every registration whose
    /// triggers fired this round. The driver drains these and turns each into the
    /// entailed positive replacement of the owner formula; the matcher itself
    /// never asserts anything for a registration.
    pending_positive: Vec<(usize, Vec<TermId>)>,
}

impl IncrementalEmatchSession {
    #[allow(
        dead_code,
        reason = "the no-registration shorthand; the loop now always passes a \
                  (usually empty) registration slice, the unit tests use this"
    )]
    fn new(arena: &mut TermArena, foralls: &[TermId]) -> Self {
        Self::new_with_nested(arena, foralls, &[])
    }

    /// [`Self::new`] plus first-class registration of universals that occur in
    /// non-entailed positions. Each registration is compiled exactly like an
    /// asserted universal — own binder prefix, own body, triggers selected from
    /// that body — but carries `active: false`, so no instance of it is ever
    /// admitted or certified. With an empty `nested` slice this is byte-identical
    /// to the historical constructor.
    #[allow(
        clippy::too_many_lines,
        reason = "one constructor: compile universals, intern patterns, build indices"
    )]
    fn new_with_nested(
        arena: &mut TermArena,
        foralls: &[TermId],
        nested: &[NestedRegistration],
    ) -> Self {
        let mut bridge = InstBridge::new();
        let mut patterns = Vec::new();
        let mut pattern_triggers: Vec<Option<PatternTrigger>> = Vec::new();
        let mut pattern_ids: HashMap<Pattern, usize> = HashMap::new();
        let mut quantifiers = Vec::with_capacity(foralls.len() + nested.len());

        let compiled: Vec<CompiledUniversalSpec> = foralls
            .iter()
            .map(|&forall_term| {
                let (vars, body) = peel_foralls(arena, forall_term);
                (forall_term, vars, body, true, None)
            })
            .chain(nested.iter().map(|registration| {
                (
                    registration.quantifier,
                    registration.vars.clone(),
                    registration.body,
                    false,
                    registration.context.clone(),
                )
            }))
            .collect();

        for (assertion, vars, body, active, context) in compiled {
            let var_terms = vars.iter().map(|&var| arena.var(var)).collect();
            let var_index: HashMap<SymbolId, u32> = vars
                .iter()
                .enumerate()
                .map(|(index, &var)| (var, u32::try_from(index).expect("variable count fits u32")))
                .collect();
            let mut pattern_indices = Vec::new();
            if !vars.is_empty() {
                for trigger in select_triggers(arena, body, &var_index) {
                    let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
                    let index = if let Some(&index) = pattern_ids.get(&pattern) {
                        index
                    } else {
                        let index = patterns.len();
                        patterns.push(pattern.clone());
                        let mut trigger_vars = std::collections::HashSet::new();
                        collect_vars(arena, trigger, &var_index, &mut trigger_vars);
                        let mut ordered: Vec<SymbolId> = trigger_vars.into_iter().collect();
                        ordered.sort_by_key(|symbol| var_index[symbol]);
                        pattern_triggers.push(Some(PatternTrigger {
                            trigger,
                            var_terms: ordered.iter().map(|&var| arena.var(var)).collect(),
                        }));
                        pattern_ids.insert(pattern, index);
                        index
                    };
                    pattern_indices.push(index);
                }
            }
            quantifiers.push(CompiledUniversal {
                assertion,
                vars,
                var_terms,
                body,
                pattern_indices,
                active,
                context,
            });
        }

        let mut patterns_by_root: HashMap<u32, Vec<usize>> = HashMap::new();
        for (index, pattern) in patterns.iter().enumerate() {
            if let Pattern::App(decl, _) = pattern {
                patterns_by_root.entry(*decl).or_default().push(index);
            }
        }
        let dirty_patterns = (0..patterns.len()).collect();
        let mut quantifiers_by_pattern: HashMap<usize, Vec<usize>> = HashMap::new();
        for (quantifier_index, quantifier) in quantifiers.iter().enumerate() {
            let unique_patterns: BTreeSet<usize> =
                quantifier.pattern_indices.iter().copied().collect();
            for pattern in unique_patterns {
                quantifiers_by_pattern
                    .entry(pattern)
                    .or_default()
                    .push(quantifier_index);
            }
        }
        let pattern_matches = vec![Vec::new(); patterns.len()];
        let match_index = bridge.egraph.new_match_index();
        let mut merge_paths = PatternPathIndex::default();
        for (index, pattern) in patterns.iter().enumerate() {
            merge_paths.add_pattern(pattern, index);
        }
        merge_paths.finish();

        Self {
            bridge,
            patterns,
            pattern_triggers,
            patterns_by_root,
            quantifiers_by_pattern,
            merge_paths,
            dirty_patterns,
            candidate_patterns: BTreeMap::new(),
            pattern_matches,
            match_index,
            quantifiers,
            processed_ground: HashSet::new(),
            source_ground: HashSet::new(),
            ground_derivations: HashMap::new(),
            equality_reason_terms: HashMap::new(),
            disequality_nodes: Vec::new(),
            disequalities: HashSet::new(),
            match_rounds: 0,
            pattern_executions: 0,
            candidate_applications_scanned: 0,
            merge_invalidations: 0,
            merge_affected_patterns: 0,
            extensions: 0,
            join_stats: Vec::new(),
            pending_positive: Vec::new(),
        }
    }

    /// Registers only top-level ground terms not seen in an earlier round. All
    /// term nodes are added before positive equalities are merged, matching the
    /// monotone add-node/merge notification order used by a retained MAM.
    #[cfg(test)]
    fn extend_ground(&mut self, arena: &TermArena, ground: &[TermId]) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::ExactPaths,
        );
    }

    fn extend_ground_with_derivations(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            derivations,
            MergeInvalidationMode::ExactPaths,
        );
    }

    #[cfg(test)]
    fn extend_ground_with_full_merge_invalidation(&mut self, arena: &TermArena, ground: &[TermId]) {
        self.extend_ground_impl(arena, ground, &HashMap::new(), MergeInvalidationMode::All);
    }

    #[cfg(test)]
    fn extend_ground_with_declaration_merge_invalidation(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::Declarations,
        );
    }

    #[cfg(test)]
    fn extend_ground_with_path_filters(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        filters: PatternFilterMode,
    ) {
        let mode = match filters {
            PatternFilterMode::ClassAndGround => MergeInvalidationMode::ExactPaths,
            PatternFilterMode::Unfiltered => MergeInvalidationMode::ExactPathsUnfiltered,
            PatternFilterMode::ClassOnly => MergeInvalidationMode::ExactPathsClassOnly,
            PatternFilterMode::GroundOnly => MergeInvalidationMode::ExactPathsGroundOnly,
        };
        self.extend_ground_impl(arena, ground, &HashMap::new(), mode);
    }

    #[cfg(test)]
    fn extend_ground_with_full_pattern_path_invalidation(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::ExactPathsFullPatterns,
        );
    }

    fn extend_ground_impl(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
        merge_invalidation: MergeInvalidationMode,
    ) {
        let new_terms: Vec<TermId> = ground
            .iter()
            .copied()
            .filter(|term| self.processed_ground.insert(*term))
            .collect();
        if new_terms.is_empty() {
            return;
        }
        if self.extensions == 0 {
            self.source_ground.extend(new_terms.iter().copied());
        } else {
            for &term in &new_terms {
                if let Some(derivation) = derivations.get(&term) {
                    self.ground_derivations.insert(term, derivation.clone());
                }
            }
        }
        self.extensions += 1;
        let node_start = self.bridge.egraph.len();

        for &term in &new_terms {
            self.bridge.add_term(arena, term);
        }
        let added_applications = self.bridge.egraph.application_nodes_since(node_start);
        let mut merge_starts = Vec::new();
        for &term in &new_terms {
            if let Some((true, lhs, rhs)) = equality_literal(arena, term) {
                self.equality_reason_terms
                    .insert(u32::try_from(term.index()).unwrap_or(u32::MAX), term);
                let lhs = self.bridge.add_term(arena, lhs);
                let rhs = self.bridge.add_term(arena, rhs);
                if !self.bridge.egraph.equal(lhs, rhs) {
                    merge_starts.extend([lhs, rhs]);
                }
                self.bridge
                    .egraph
                    .merge(lhs, rhs, u32::try_from(term.index()).unwrap_or(u32::MAX));
            }
        }

        for application in added_applications {
            if let Some(patterns) = self
                .patterns_by_root
                .get(&self.bridge.egraph.decl(application))
            {
                for &pattern in patterns {
                    self.candidate_patterns
                        .entry(pattern)
                        .or_default()
                        .insert(application);
                }
            }
        }
        if !merge_starts.is_empty() {
            let affected_count = self.queue_merge_invalidation(&merge_starts, merge_invalidation);
            self.merge_invalidations += 1;
            self.merge_affected_patterns += affected_count;
        }
        for &term in &new_terms {
            if let Some((false, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = self.bridge.add_term(arena, lhs);
                let rhs = self.bridge.add_term(arena, rhs);
                self.disequality_nodes.push((term, lhs, rhs));
            }
        }
        self.refresh_disequalities();
    }

    fn queue_merge_invalidation(
        &mut self,
        merge_starts: &[ENodeId],
        mode: MergeInvalidationMode,
    ) -> usize {
        match mode {
            MergeInvalidationMode::ExactPaths => {
                let affected = self
                    .merge_paths
                    .affected_candidates(&self.bridge.egraph, merge_starts);
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsFullPatterns => {
                let affected = self
                    .merge_paths
                    .affected_patterns(&self.bridge.egraph, merge_starts);
                let count = affected.len();
                self.dirty_patterns.extend(affected);
                count
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsUnfiltered => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::Unfiltered,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsClassOnly => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::ClassOnly,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsGroundOnly => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::GroundOnly,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::Declarations => {
                let mut affected = BTreeSet::new();
                for declaration in self
                    .bridge
                    .egraph
                    .inverted_parent_declarations(merge_starts)
                {
                    if let Some(patterns) = self.patterns_by_root.get(&declaration) {
                        affected.extend(patterns.iter().copied());
                    }
                }
                let count = affected.len();
                self.dirty_patterns.extend(affected);
                count
            }
            #[cfg(test)]
            MergeInvalidationMode::All => {
                self.dirty_patterns.extend(0..self.patterns.len());
                self.patterns.len()
            }
        }
    }

    fn queue_candidate_map(&mut self, affected: BTreeMap<usize, BTreeSet<ENodeId>>) -> usize {
        let count = affected.len();
        for (pattern, candidates) in affected {
            self.candidate_patterns
                .entry(pattern)
                .or_default()
                .extend(candidates);
        }
        count
    }

    fn refresh_disequalities(&mut self) {
        self.disequalities.clear();
        for &(_, lhs, rhs) in &self.disequality_nodes {
            let lhs = self.bridge.egraph.root(lhs);
            let rhs = self.bridge.egraph.root(rhs);
            self.disequalities.insert(ordered_node_pair(lhs, rhs));
        }
    }

    /// Finds source instances enabled only modulo the retained SAT candidate's
    /// true equalities (ADR-0120). Candidate merges live in one e-graph scope;
    /// concrete tuples are materialized before pop, and only complete exact
    /// instances leave this method. Candidate facts never enter explanation maps.
    fn scoped_candidate_instances(
        &mut self,
        arena: &mut TermArena,
        equality_terms: &[TermId],
        deadline: Option<Instant>,
    ) -> Option<ScopedCandidateBatch> {
        self.scoped_candidate_instances_with_limits(
            arena,
            equality_terms,
            MAX_CANDIDATE_EQUALITIES,
            MAX_CANDIDATE_APPLICATIONS,
            deadline,
        )
    }

    fn scoped_candidate_instances_with_limits(
        &mut self,
        arena: &mut TermArena,
        equality_terms: &[TermId],
        equality_limit: usize,
        application_limit: usize,
        deadline: Option<Instant>,
    ) -> Option<ScopedCandidateBatch> {
        if equality_terms.len() > equality_limit {
            return None;
        }
        let mut endpoints = Vec::new();
        for &term in equality_terms {
            let (true, lhs, rhs) = equality_literal(arena, term)? else {
                return None;
            };
            let (&lhs, &rhs) = (
                self.bridge.term_to_node.get(&lhs)?,
                self.bridge.term_to_node.get(&rhs)?,
            );
            if !self.bridge.egraph.equal(lhs, rhs) {
                endpoints.push((lhs, rhs));
            }
        }
        if endpoints.is_empty() {
            return Some(ScopedCandidateBatch {
                batch: GeneratedGroundBatch {
                    urgent: Vec::new(),
                    units: Vec::new(),
                    deferred: Vec::new(),
                    derivations: HashMap::new(),
                },
                pattern_executions: 0,
                applications_scanned: 0,
            });
        }

        self.bridge.egraph.push();
        let mut merge_starts = Vec::with_capacity(endpoints.len() * 2);
        for (lhs, rhs) in endpoints {
            merge_starts.extend([lhs, rhs]);
            self.bridge.egraph.merge(lhs, rhs, u32::MAX);
        }
        let affected = self
            .merge_paths
            .affected_candidates(&self.bridge.egraph, &merge_starts);
        let applications_scanned = affected.values().map(BTreeSet::len).sum::<usize>();
        if applications_scanned > application_limit {
            self.bridge.egraph.pop();
            return None;
        }

        let dirty: Vec<usize> = affected.keys().copied().collect();
        let patterns: Vec<Pattern> = dirty
            .iter()
            .map(|&index| self.patterns[index].clone())
            .collect();
        let candidates: Vec<Vec<ENodeId>> = affected
            .into_values()
            .map(|nodes| nodes.into_iter().collect())
            .collect();
        let mut scoped_matches: BTreeMap<usize, Vec<Substitution>> = BTreeMap::new();
        let mut impacted_quantifiers = BTreeSet::new();
        if !dirty.is_empty() {
            let mut scoped_index = self.bridge.egraph.new_match_index();
            let matches = self.bridge.egraph.ematch_many_candidates_indexed(
                &patterns,
                &candidates,
                &mut scoped_index,
            );
            for (index, matches) in dirty.iter().copied().zip(matches) {
                let mut combined = self.pattern_matches[index].clone();
                combined.extend(matches);
                combined.sort_unstable();
                combined.dedup();
                scoped_matches.insert(index, combined);
                if let Some(quantifiers) = self.quantifiers_by_pattern.get(&index) {
                    impacted_quantifiers.extend(quantifiers.iter().copied());
                }
            }
        }
        let mut remaining = MAX_JOINED_SUBSTITUTIONS_PER_ROUND;
        let mut tuple_batches = Vec::with_capacity(impacted_quantifiers.len());
        for index in impacted_quantifiers {
            let joined = self.witness_tuples_with_overrides(
                &self.quantifiers[index],
                &self.pattern_matches,
                Some(&scoped_matches),
                remaining,
                deadline,
            );
            let tuples = joined.map(|(tuples, consumed)| {
                remaining = remaining.saturating_sub(consumed);
                tuples
            });
            tuple_batches.push((index, tuples));
        }
        self.bridge.egraph.pop();
        Some(ScopedCandidateBatch {
            batch: self.materialize_candidate_instances(arena, tuple_batches),
            pattern_executions: dirty.len(),
            applications_scanned,
        })
    }

    fn materialize_candidate_instances(
        &self,
        arena: &mut TermArena,
        tuple_batches: Vec<(usize, Option<Vec<Vec<TermId>>>)>,
    ) -> GeneratedGroundBatch {
        let mut urgent = Vec::new();
        let mut derivations = HashMap::new();
        for (quantifier_index, tuples) in tuple_batches {
            let Some(tuples) = tuples else {
                continue;
            };
            let quantifier = &self.quantifiers[quantifier_index];
            // Registrations are matched, never asserted (see `active`).
            if !quantifier.active {
                continue;
            }
            for tuple in tuples {
                let replacements: HashMap<TermId, TermId> = quantifier
                    .var_terms
                    .iter()
                    .copied()
                    .zip(tuple.iter().copied())
                    .collect();
                let mut memo = HashMap::new();
                let Ok(instance) =
                    replace_subterms(arena, quantifier.body, &replacements, &mut memo)
                else {
                    continue;
                };
                derivations.entry(instance).or_insert_with(|| {
                    QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                        assertion: quantifier.assertion,
                        bindings: tuple,
                        instance,
                    })
                });
                urgent.push(instance);
            }
        }
        urgent.sort_by_key(|term| term.index());
        urgent.dedup();
        GeneratedGroundBatch {
            urgent,
            units: Vec::new(),
            deferred: Vec::new(),
            derivations,
        }
    }

    fn lazy_clause_batches(
        &mut self,
        arena: &mut TermArena,
        deadline: Option<Instant>,
    ) -> Vec<LazyClauseBatch> {
        let tuple_batches = self.match_witness_tuples(deadline);
        // Deadline discipline: instance materialization below is O(tuples ×
        // body size), so consult the clock at coarse tuple granularity. An
        // expired clock truncates to the batches built so far — instances are
        // monotone hints (never a verdict by themselves), so truncation is
        // sound, and the caller's round-top deadline check exits cleanly.
        let mut tuples_since_clock_check = 0usize;
        let mut expired = deadline.is_some_and(|deadline| Instant::now() >= deadline);
        let mut batches = Vec::with_capacity(self.quantifiers.len());
        let mut pending_positive: Vec<(usize, Vec<TermId>)> = Vec::new();
        for (index, (quantifier, tuples)) in self.quantifiers.iter().zip(tuple_batches).enumerate()
        {
            let (Some(tuples), false) = (tuples, expired) else {
                batches.push(LazyClauseBatch::default());
                continue;
            };
            // Registrations are matched, never asserted (see `active`). The
            // tuples were still joined, and `join_stats` recorded them, so the
            // trace shows the nested trigger firing. Slice 3: a registration
            // with a positive-replacement context hands its tuples to the
            // driver, which admits the *owner with the universal replaced* —
            // entailed — rather than the bare instance, which is not.
            if !quantifier.active {
                if quantifier.context.is_some() {
                    for tuple in tuples {
                        if pending_positive.len() >= MAX_POSITIVE_TUPLES_PER_ROUND {
                            break;
                        }
                        pending_positive.push((index, tuple));
                    }
                }
                batches.push(LazyClauseBatch::default());
                continue;
            }
            {
                let mut batch = LazyClauseBatch::default();
                for tuple in &tuples {
                    tuples_since_clock_check += 1;
                    if tuples_since_clock_check >= 64 {
                        tuples_since_clock_check = 0;
                        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                            expired = true;
                            break;
                        }
                    }
                    let replacements: HashMap<TermId, TermId> = quantifier
                        .var_terms
                        .iter()
                        .copied()
                        .zip(tuple.iter().copied())
                        .collect();
                    let mut memo = HashMap::new();
                    let Ok(instance) =
                        replace_subterms(arena, quantifier.body, &replacements, &mut memo)
                    else {
                        continue;
                    };
                    batch
                        .instance_certificates
                        .entry(instance)
                        .or_insert_with(|| QuantifierInstanceCertificate {
                            assertion: quantifier.assertion,
                            bindings: tuple.clone(),
                            instance,
                        });
                    match evaluate_equality_clause_with(arena, instance, &mut |lhs, rhs| {
                        self.equality(lhs, rhs)
                    }) {
                        Some(ClauseValue::True) => batch.redundant += 1,
                        Some(ClauseValue::False) => batch.urgent.push(instance),
                        Some(ClauseValue::Unit) => {
                            match self.detached_propagation(arena, quantifier, tuple, instance) {
                                Some(propagation) => batch.propagations.push(propagation),
                                None => batch.units.push(instance),
                            }
                        }
                        Some(ClauseValue::Undetermined) | None => batch.deferred.push(instance),
                    }
                }
                batch.urgent.sort_by_key(|term| term.index());
                batch.urgent.dedup();
                batch.units.sort_by_key(|term| term.index());
                batch.units.dedup();
                batch.propagations.sort_by_key(|propagation| {
                    (
                        propagation.propagated_literal.index(),
                        propagation.source_instance.index(),
                    )
                });
                batch.propagations.dedup_by_key(|propagation| {
                    (propagation.propagated_literal, propagation.source_instance)
                });
                batch.deferred.sort_by_key(|term| term.index());
                batch.deferred.dedup();
                batches.push(batch);
            }
        }
        self.pending_positive.extend(pending_positive);
        batches
    }

    fn detached_propagation(
        &self,
        arena: &TermArena,
        quantifier: &CompiledUniversal,
        tuple: &[TermId],
        source_instance: TermId,
    ) -> Option<QuantifierClausePropagationCertificate> {
        let mut literals = Vec::new();
        collect_clause_literals(arena, source_instance, &mut literals);
        let mut propagated_literal = None;
        let mut false_siblings = Vec::new();
        for literal in literals {
            match self.literal_value(arena, literal)? {
                LiteralValue::True => return None,
                LiteralValue::Undetermined => {
                    if propagated_literal.replace(literal).is_some() {
                        return None;
                    }
                }
                LiteralValue::False => {
                    false_siblings.push(self.false_sibling_justification(arena, literal)?);
                }
            }
        }
        let propagated_literal = propagated_literal?;
        if false_siblings.is_empty() {
            return None;
        }
        equality_literal(arena, propagated_literal)?;
        let mut derived_reason_terms: Vec<TermId> = false_siblings
            .iter()
            .flat_map(|sibling| sibling.reasons.iter().copied())
            .filter(|reason| !self.source_ground.contains(reason))
            .collect();
        derived_reason_terms.sort_by_key(|term| term.index());
        derived_reason_terms.dedup();
        let derived_reasons = derived_reason_terms
            .into_iter()
            .map(|reason| self.ground_derivations.get(&reason).cloned())
            .collect::<Option<Vec<_>>>()?;
        Some(QuantifierClausePropagationCertificate {
            assertion: quantifier.assertion,
            bindings: tuple.to_vec(),
            source_instance,
            propagated_literal,
            false_siblings,
            derived_reasons,
        })
    }

    fn literal_value(&self, arena: &TermArena, literal: TermId) -> Option<LiteralValue> {
        if let TermNode::BoolConst(value) = arena.node(literal) {
            return Some(if *value {
                LiteralValue::True
            } else {
                LiteralValue::False
            });
        }
        let (positive, lhs, rhs) = equality_literal(arena, literal)?;
        let value = self.equality(lhs, rhs);
        Some(if positive { value } else { value.negate() })
    }

    fn false_sibling_justification(
        &self,
        arena: &TermArena,
        literal: TermId,
    ) -> Option<QuantifierFalseSiblingJustification> {
        if matches!(arena.node(literal), TermNode::BoolConst(false)) {
            return Some(QuantifierFalseSiblingJustification {
                literal,
                reasons: Vec::new(),
            });
        }
        let (positive, lhs, rhs) = equality_literal(arena, literal)?;
        let reasons = if positive {
            self.disequality_reasons(lhs, rhs)?
        } else {
            self.equality_reasons(lhs, rhs)?
        };
        Some(QuantifierFalseSiblingJustification { literal, reasons })
    }

    fn equality_reasons(&self, lhs: TermId, rhs: TermId) -> Option<Vec<TermId>> {
        let (&lhs, &rhs) = (
            self.bridge.term_to_node.get(&lhs)?,
            self.bridge.term_to_node.get(&rhs)?,
        );
        if !self.bridge.egraph.equal(lhs, rhs) {
            return None;
        }
        self.explanation_terms(lhs, rhs)
    }

    fn disequality_reasons(&self, lhs: TermId, rhs: TermId) -> Option<Vec<TermId>> {
        let (&lhs, &rhs) = (
            self.bridge.term_to_node.get(&lhs)?,
            self.bridge.term_to_node.get(&rhs)?,
        );
        let pair = ordered_node_pair(self.bridge.egraph.root(lhs), self.bridge.egraph.root(rhs));
        for &(reason, disequal_lhs, disequal_rhs) in &self.disequality_nodes {
            if !self.reason_has_provenance(reason)
                || ordered_node_pair(
                    self.bridge.egraph.root(disequal_lhs),
                    self.bridge.egraph.root(disequal_rhs),
                ) != pair
            {
                continue;
            }
            for (left, right) in [(disequal_lhs, disequal_rhs), (disequal_rhs, disequal_lhs)] {
                let (Some(mut lhs_reasons), Some(rhs_reasons)) = (
                    self.explanation_terms(lhs, left),
                    self.explanation_terms(rhs, right),
                ) else {
                    continue;
                };
                lhs_reasons.extend(rhs_reasons);
                lhs_reasons.push(reason);
                lhs_reasons.sort_by_key(|term| term.index());
                lhs_reasons.dedup();
                return Some(lhs_reasons);
            }
        }
        None
    }

    fn explanation_terms(&self, lhs: ENodeId, rhs: ENodeId) -> Option<Vec<TermId>> {
        if !self.bridge.egraph.equal(lhs, rhs) {
            return None;
        }
        let mut terms = Vec::new();
        for reason in self.bridge.egraph.explain(lhs, rhs) {
            let &term = self.equality_reason_terms.get(&reason)?;
            if !self.reason_has_provenance(term) {
                return None;
            }
            terms.push(term);
        }
        terms.sort_by_key(|term| term.index());
        terms.dedup();
        Some(terms)
    }

    fn reason_has_provenance(&self, term: TermId) -> bool {
        self.source_ground.contains(&term) || self.ground_derivations.contains_key(&term)
    }

    fn match_witness_tuples(&mut self, deadline: Option<Instant>) -> Vec<Option<Vec<Vec<TermId>>>> {
        // Deadline discipline: pattern execution and substitution joining are
        // the dominant per-round costs (measured: one deadline-blind matching
        // round overran a 500 ms budget by more than a minute), so the clock
        // is consulted between the two batched match phases, per quantifier in
        // the join loop, and — via `witness_tuples_with_overrides` — between
        // bounded merge-attempt blocks. The batched `ematch_many_*` calls are
        // kept intact deliberately: a per-pattern split measurably perturbed
        // the loop's admission schedule and cost a scored refutation, so the
        // batch itself stays a single unit and the growth-forecast round gate
        // bounds it. An expired clock skips the candidate phase and the
        // remaining joins; the truncation only defers instances, which are
        // monotone hints, never a verdict by themselves.
        let expired = |deadline: Option<Instant>| -> bool {
            deadline.is_some_and(|deadline| Instant::now() >= deadline)
        };
        if !self.dirty_patterns.is_empty() {
            let seg = Instant::now();
            let dirty: Vec<usize> = self.dirty_patterns.iter().copied().collect();
            let patterns: Vec<Pattern> = dirty
                .iter()
                .map(|&index| self.patterns[index].clone())
                .collect();
            let matches = self
                .bridge
                .egraph
                .ematch_many_indexed(&patterns, &mut self.match_index);
            for (index, matches) in dirty.iter().copied().zip(matches) {
                self.pattern_matches[index] = matches;
            }
            self.pattern_executions += dirty.len();
            for index in &dirty {
                self.candidate_patterns.remove(index);
            }
            self.dirty_patterns.clear();
            crate::auto::qtrace("match-seg", seg, &format!("dirty n={}", dirty.len()));
        }
        if !self.candidate_patterns.is_empty() && !expired(deadline) {
            let seg = Instant::now();
            let pending = std::mem::take(&mut self.candidate_patterns);
            let dirty: Vec<usize> = pending.keys().copied().collect();
            let patterns: Vec<Pattern> = dirty
                .iter()
                .map(|&index| self.patterns[index].clone())
                .collect();
            let candidates: Vec<Vec<ENodeId>> = pending
                .into_values()
                .map(|candidates| candidates.into_iter().collect())
                .collect();
            let matches = self.bridge.egraph.ematch_many_candidates_indexed(
                &patterns,
                &candidates,
                &mut self.match_index,
            );
            for (index, matches) in dirty.iter().copied().zip(matches) {
                self.pattern_matches[index].extend(matches);
                self.pattern_matches[index].sort_unstable();
                self.pattern_matches[index].dedup();
            }
            self.pattern_executions += dirty.len();
            self.candidate_applications_scanned += candidates.iter().map(Vec::len).sum::<usize>();
            crate::auto::qtrace("match-seg", seg, &format!("candidates n={}", dirty.len()));
        }
        self.match_rounds += 1;
        let join_seg = Instant::now();
        let mut remaining = MAX_JOINED_SUBSTITUTIONS_PER_ROUND;
        let mut batches = Vec::with_capacity(self.quantifiers.len());
        if self.join_stats.is_empty() {
            self.join_stats = vec![(0usize, 0usize); self.quantifiers.len()];
        }
        for (index, quantifier) in self.quantifiers.iter().enumerate() {
            if expired(deadline) {
                batches.push(None);
                continue;
            }
            let before = remaining;
            let joined = self.witness_tuples_with_overrides(
                quantifier,
                &self.pattern_matches,
                None,
                remaining,
                deadline,
            );
            let tuples = joined.map(|(tuples, consumed)| {
                remaining = remaining.saturating_sub(consumed);
                tuples
            });
            let matchable = !quantifier.pattern_indices.is_empty()
                && quantifier.pattern_indices.iter().all(|&pattern| {
                    self.pattern_matches
                        .get(pattern)
                        .is_some_and(|matches| !matches.is_empty())
                });
            if let Some(stats) = self.join_stats.get_mut(index) {
                match &tuples {
                    Some(emitted) => stats.0 += emitted.len(),
                    // Every pattern has matches yet the join produced nothing:
                    // the shared per-round budget (or a merge conflict wipe)
                    // starved this universal. `before` disambiguates the
                    // fully-starved case.
                    None if matchable || before == 0 => stats.1 += 1,
                    None => {}
                }
            }
            batches.push(tuples);
        }
        crate::auto::qtrace("match-seg", join_seg, "join done");
        batches
    }

    #[cfg(test)]
    fn witness_tuples(
        &self,
        quantifier: &CompiledUniversal,
        pattern_matches: &[Vec<Vec<Option<ENodeId>>>],
    ) -> Option<Vec<Vec<TermId>>> {
        self.witness_tuples_with_overrides(
            quantifier,
            pattern_matches,
            None,
            MAX_JOINED_SUBSTITUTIONS_PER_ROUND,
            None,
        )
        .map(|(tuples, _)| tuples)
    }

    fn witness_tuples_with_overrides(
        &self,
        quantifier: &CompiledUniversal,
        pattern_matches: &[Vec<Substitution>],
        overrides: Option<&BTreeMap<usize, Vec<Substitution>>>,
        join_budget: usize,
        deadline: Option<Instant>,
    ) -> Option<(Vec<Vec<TermId>>, usize)> {
        if join_budget == 0 || quantifier.vars.is_empty() || quantifier.pattern_indices.is_empty() {
            return None;
        }
        let nvars = quantifier.vars.len();
        let mut joined: Vec<Vec<Option<ENodeId>>> = vec![vec![None; nvars]];
        let mut remaining = join_budget;
        // The `join_budget` counts only *successful* merges, so a sparse join
        // can scan |joined| × |matches| pairs without consuming it. Count
        // attempts and consult the wall clock at a coarse block size so this
        // loop cannot silently overrun the shared query deadline.
        let mut attempts_since_clock_check = 0usize;
        for &pattern_index in &quantifier.pattern_indices {
            let matches = overrides
                .and_then(|matches| matches.get(&pattern_index))
                .or_else(|| pattern_matches.get(pattern_index))?;
            let mut next = Vec::new();
            for partial in &joined {
                for matched in matches {
                    attempts_since_clock_check += 1;
                    if attempts_since_clock_check >= 8192 {
                        attempts_since_clock_check = 0;
                        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                            return None;
                        }
                    }
                    if let Some(merged) =
                        merge_substitutions_modulo(&self.bridge.egraph, partial, matched)
                    {
                        let updated = remaining.checked_sub(1)?;
                        remaining = updated;
                        next.push(merged);
                    }
                }
            }
            joined = next;
            if joined.is_empty() {
                return None;
            }
        }

        let mut tuples = Vec::new();
        for substitution in joined {
            let mut tuple = Vec::with_capacity(nvars);
            let complete = (0..nvars).all(|index| {
                if let Some(term) = substitution
                    .get(index)
                    .copied()
                    .flatten()
                    .map(|class| self.bridge.egraph.root(class))
                    .and_then(|root| self.bridge.repr_term.get(&root).copied())
                {
                    tuple.push(term);
                    true
                } else {
                    false
                }
            });
            if complete {
                tuples.push(tuple);
            }
        }
        tuples.sort_by(|left, right| {
            left.iter()
                .map(|term| term.index())
                .cmp(right.iter().map(|term| term.index()))
        });
        tuples.dedup();
        Some((tuples, join_budget - remaining))
    }

    /// Per-sort seed lists for term invention: the prepared constant seeds
    /// (Skolem-first) extended with ground application terms the e-graph
    /// already holds (admitted-instance subterms and earlier inventions), in
    /// deterministic term order, capped per sort.
    fn build_invention_seed_lists(
        &self,
        arena: &TermArena,
        state: &mut TermInventionState,
        needed: &HashSet<Sort>,
    ) -> HashMap<Sort, Vec<TermId>> {
        let mut known_terms: Vec<TermId> = self.bridge.term_to_node.keys().copied().collect();
        known_terms.sort_by_key(|term| term.index());
        let mut seed_lists: HashMap<Sort, Vec<TermId>> = HashMap::new();
        for sort in needed {
            let mut seeds = state.constant_seeds.get(sort).cloned().unwrap_or_default();
            for &term in &known_terms {
                if seeds.len() >= MAX_INVENTION_SEEDS_PER_SORT {
                    break;
                }
                if matches!(
                    arena.node(term),
                    TermNode::App {
                        op: Op::Apply(_),
                        ..
                    }
                ) && arena.sort_of(term) == *sort
                    && !seeds.contains(&term)
                    && state.is_binder_free(arena, term)
                {
                    seeds.push(term);
                }
            }
            seeds.truncate(MAX_INVENTION_SEEDS_PER_SORT);
            seed_lists.insert(*sort, seeds);
        }
        seed_lists
    }

    /// Direct staged instances for universals the matching/join schedules have
    /// starved completely (no admitted instance at this fixpoint): enumerates
    /// binder tuples over the invention seed lists by digit sum, builds each
    /// instance, and admits it through the standard
    /// [`QuantifierInstanceCertificate`] gate — the same checked, entailed
    /// instances matching would have produced had the joins reached them.
    /// Returns the admitted instance terms.
    #[allow(clippy::too_many_arguments)]
    #[allow(
        clippy::too_many_lines,
        reason = "one staged enumeration with its eligibility gate"
    )]
    #[allow(clippy::too_many_arguments)]
    fn invent_starved_universal_instances(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        state: &mut TermInventionState,
        seen: &mut HashSet<TermId>,
        ground: &mut Vec<TermId>,
        retained: &mut HashMap<TermId, QuantifierGroundDerivation>,
        generations: &mut TermGenerations,
    ) -> Vec<TermId> {
        if state.direct_total >= MAX_DIRECT_INSTANCES_TOTAL {
            return Vec::new();
        }
        // Universals whose retained instances exceed what this route fed them
        // are being served by the ordinary matching schedules; only starved
        // ones (matching has produced nothing of their own) get direct tuples.
        let mut retained_counts = vec![0usize; self.quantifiers.len()];
        for derivation in retained.values() {
            if let QuantifierGroundDerivation::Instance(certificate) = derivation
                && let Some(index) = self
                    .quantifiers
                    .iter()
                    .position(|q| q.assertion == certificate.assertion)
            {
                retained_counts[index] += 1;
            }
        }
        let served: Vec<bool> = self
            .quantifiers
            .iter()
            .enumerate()
            .map(|(index, quantifier)| {
                // Registrations never receive direct instances either: an
                // instance of one is not a consequence of the assertions.
                if !quantifier.active {
                    return true;
                }
                let direct = state
                    .direct_per_universal
                    .get(&quantifier.assertion)
                    .copied()
                    .unwrap_or(0);
                retained_counts[index] > direct
            })
            .collect();
        let mut needed: HashSet<Sort> = HashSet::new();
        for (index, quantifier) in self.quantifiers.iter().enumerate() {
            if served[index] || quantifier.vars.is_empty() {
                continue;
            }
            for &var in &quantifier.var_terms {
                needed.insert(arena.sort_of(var));
            }
        }
        if needed.is_empty() {
            return Vec::new();
        }
        let seed_lists = self.build_invention_seed_lists(arena, state, &needed);
        let universals: Vec<(TermId, Vec<TermId>, TermId)> = self
            .quantifiers
            .iter()
            .enumerate()
            .filter(|(index, quantifier)| !served[*index] && !quantifier.vars.is_empty())
            .map(|(_, quantifier)| {
                (
                    quantifier.assertion,
                    quantifier.var_terms.clone(),
                    quantifier.body,
                )
            })
            .collect();

        let mut order: Vec<TermId> = Vec::new();
        let mut candidates: HashMap<TermId, QuantifierGroundDerivation> = HashMap::new();
        for (assertion, var_terms, body) in universals {
            if state.direct_total >= MAX_DIRECT_INSTANCES_TOTAL {
                break;
            }
            let lists: Vec<Vec<TermId>> = var_terms
                .iter()
                .map(|&var| {
                    seed_lists
                        .get(&arena.sort_of(var))
                        .cloned()
                        .unwrap_or_default()
                })
                .collect();
            if lists.iter().any(Vec::is_empty) {
                continue;
            }
            let lens: Vec<usize> = lists.iter().map(Vec::len).collect();
            let max_sum: usize = lens.iter().map(|&len| len - 1).sum();
            let mut visits = 0usize;
            let mut created = 0usize;
            'stages: for stage in 0..=max_sum {
                let mut done = false;
                for_each_tuple_with_sum(&lens, stage, &mut Vec::new(), &mut |digits| {
                    visits += 1;
                    let bindings: Vec<TermId> = digits
                        .iter()
                        .enumerate()
                        .map(|(slot, &digit)| lists[slot][digit])
                        .collect();
                    let replacements: HashMap<TermId, TermId> = var_terms
                        .iter()
                        .copied()
                        .zip(bindings.iter().copied())
                        .collect();
                    let mut memo = HashMap::new();
                    if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo)
                        && !seen.contains(&instance)
                        && !candidates.contains_key(&instance)
                    {
                        candidates.insert(
                            instance,
                            QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                                assertion,
                                bindings,
                                instance,
                            }),
                        );
                        order.push(instance);
                        created += 1;
                        state.direct_total += 1;
                        *state.direct_per_universal.entry(assertion).or_default() += 1;
                    }
                    let stop = visits >= MAX_DIRECT_TUPLE_VISITS_PER_UNIVERSAL_STEP
                        || created >= MAX_DIRECT_INSTANCES_PER_UNIVERSAL_STEP
                        || state.direct_total >= MAX_DIRECT_INSTANCES_TOTAL;
                    done = stop;
                    !stop
                });
                if done {
                    break 'stages;
                }
            }
        }
        admit_generated_ground(
            arena,
            assertions,
            order,
            seen,
            ground,
            retained,
            &candidates,
            generations,
        )
    }

    /// Adds one invented ground term to the matcher's e-graph (nodes only —
    /// no assertion, no merge) and registers its new applications as match
    /// candidates for the affected patterns. Returns `false` when the term is
    /// already known to the e-graph.
    fn seed_invented_term(&mut self, arena: &TermArena, term: TermId) -> bool {
        if self.bridge.term_to_node.contains_key(&term) {
            return false;
        }
        let node_start = self.bridge.egraph.len();
        self.bridge.add_term(arena, term);
        for application in self.bridge.egraph.application_nodes_since(node_start) {
            if let Some(patterns) = self
                .patterns_by_root
                .get(&self.bridge.egraph.decl(application))
            {
                for &pattern in patterns {
                    self.candidate_patterns
                        .entry(pattern)
                        .or_default()
                        .insert(application);
                }
            }
        }
        true
    }

    /// One term-invention step for the starved fixpoint (see the
    /// `MAX_INVENTED_TERMS_*` constants): substitutes per-sort seed terms into
    /// each usable compiled trigger, staged by digit-sum over the seed
    /// indices, and seeds every NEW ground trigger instance into the matcher's
    /// e-graph so the next matching round can produce certified universal
    /// instances over it. Returns the number of freshly seeded terms; `0`
    /// means the route is exhausted and the caller should stop.
    fn invent_starved_trigger_terms(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        state: &mut TermInventionState,
    ) -> usize {
        if !state.prepared {
            state.prepare(arena, assertions, &self.pattern_triggers);
        }
        if state.invented_total >= MAX_INVENTED_TERMS_TOTAL {
            return 0;
        }
        // Sorts any usable pattern actually binds; nothing else needs seeds.
        let mut needed: HashSet<Sort> = HashSet::new();
        for (index, usable) in state.pattern_usable.iter().enumerate() {
            if !usable {
                continue;
            }
            if let Some(trigger) = &self.pattern_triggers[index] {
                for &var in &trigger.var_terms {
                    needed.insert(arena.sort_of(var));
                }
            }
        }
        if needed.is_empty() {
            return 0;
        }
        let seed_lists = self.build_invention_seed_lists(arena, state, &needed);

        let mut invented_this_step = 0usize;
        for pattern_index in 0..self.patterns.len() {
            if invented_this_step >= MAX_INVENTED_TERMS_PER_STEP
                || state.invented_total >= MAX_INVENTED_TERMS_TOTAL
            {
                break;
            }
            if !state
                .pattern_usable
                .get(pattern_index)
                .copied()
                .unwrap_or(false)
            {
                continue;
            }
            let Some(trigger) = self.pattern_triggers[pattern_index].clone() else {
                continue;
            };
            if trigger.var_terms.is_empty() {
                continue;
            }
            let lists: Vec<Vec<TermId>> = trigger
                .var_terms
                .iter()
                .map(|&var| {
                    seed_lists
                        .get(&arena.sort_of(var))
                        .cloned()
                        .unwrap_or_default()
                })
                .collect();
            if lists.iter().any(Vec::is_empty) {
                continue;
            }
            let lens: Vec<usize> = lists.iter().map(Vec::len).collect();
            let max_sum: usize = lens.iter().map(|&len| len - 1).sum();
            let mut visits = 0usize;
            let mut created = 0usize;
            'stages: for stage in 0..=max_sum {
                let mut done = false;
                for_each_tuple_with_sum(&lens, stage, &mut Vec::new(), &mut |digits| {
                    visits += 1;
                    let replacements: HashMap<TermId, TermId> = trigger
                        .var_terms
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(slot, var)| (var, lists[slot][digits[slot]]))
                        .collect();
                    let mut memo = HashMap::new();
                    if let Ok(instance) =
                        replace_subterms(arena, trigger.trigger, &replacements, &mut memo)
                        && self.seed_invented_term(arena, instance)
                    {
                        created += 1;
                        invented_this_step += 1;
                        state.invented_total += 1;
                    }
                    let stop = visits >= MAX_INVENTION_TUPLE_VISITS_PER_PATTERN_STEP
                        || created >= MAX_INVENTED_TERMS_PER_PATTERN_STEP
                        || invented_this_step >= MAX_INVENTED_TERMS_PER_STEP
                        || state.invented_total >= MAX_INVENTED_TERMS_TOTAL;
                    done = stop;
                    !stop
                });
                if done {
                    break 'stages;
                }
            }
        }
        invented_this_step
    }

    /// Conservative equality lookup over terms already registered from the
    /// active ground context. Missing body terms remain undetermined instead of
    /// mutating retained matching state before their source instance is asserted.
    fn equality(&self, lhs: TermId, rhs: TermId) -> LiteralValue {
        if lhs == rhs {
            return LiteralValue::True;
        }
        let (Some(&lhs), Some(&rhs)) = (
            self.bridge.term_to_node.get(&lhs),
            self.bridge.term_to_node.get(&rhs),
        ) else {
            return LiteralValue::Undetermined;
        };
        if self.bridge.egraph.equal(lhs, rhs) {
            return LiteralValue::True;
        }
        let pair = ordered_node_pair(self.bridge.egraph.root(lhs), self.bridge.egraph.root(rhs));
        if self.disequalities.contains(&pair) {
            LiteralValue::False
        } else {
            LiteralValue::Undetermined
        }
    }
}

#[cfg(test)]
fn lazy_clause_instances(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> LazyClauseBatch {
    let Some(matches) = witness_matches_via_egraph(arena, ground, forall_term) else {
        return LazyClauseBatch::default();
    };
    let WitnessMatches {
        vars,
        body,
        tuples,
        bridge,
    } = matches;
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut facts = GroundEqualityContext::from_matching_bridge(arena, ground, bridge);
    let mut batch = LazyClauseBatch::default();
    for tuple in &tuples {
        let replacements: HashMap<TermId, TermId> = var_terms
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) else {
            continue;
        };
        match evaluate_equality_clause(arena, instance, &mut facts) {
            Some(ClauseValue::True) => batch.redundant += 1,
            Some(ClauseValue::False | ClauseValue::Unit) => batch.urgent.push(instance),
            Some(ClauseValue::Undetermined) | None => batch.deferred.push(instance),
        }
    }
    batch.urgent.sort_by_key(|t| t.index());
    batch.urgent.dedup();
    batch.deferred.sort_by_key(|t| t.index());
    batch.deferred.dedup();
    batch
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseValue {
    True,
    False,
    Unit,
    Undetermined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LiteralValue {
    True,
    False,
    Undetermined,
}

impl LiteralValue {
    fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Undetermined => Self::Undetermined,
        }
    }
}

/// Equality/disequality unit facts used to justify clause classification.
///
/// This deliberately ignores non-unit Boolean structure. Missing information is
/// `Undetermined`, so classification can lose pruning but cannot invent truth.
struct GroundEqualityContext {
    bridge: InstBridge,
    disequalities: HashSet<(ENodeId, ENodeId)>,
}

impl GroundEqualityContext {
    fn new(arena: &TermArena, ground: &[TermId]) -> Self {
        let mut bridge = InstBridge::new();
        for &term in ground {
            bridge.add_term(arena, term);
        }
        Self::from_bridge(arena, ground, bridge)
    }

    fn from_bridge(arena: &TermArena, ground: &[TermId], mut bridge: InstBridge) -> Self {
        for &term in ground {
            if let Some((true, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = bridge.add_term(arena, lhs);
                let rhs = bridge.add_term(arena, rhs);
                bridge
                    .egraph
                    .merge(lhs, rhs, u32::try_from(term.index()).unwrap_or(u32::MAX));
            }
        }
        Self::from_matching_bridge(arena, ground, bridge)
    }

    /// Reuses the bridge built by `witness_matches_via_egraph`, which has already
    /// merged every positive top-level equality for congruence-aware matching.
    fn from_matching_bridge(arena: &TermArena, ground: &[TermId], mut bridge: InstBridge) -> Self {
        let mut disequalities = HashSet::new();
        for &term in ground {
            if let Some((false, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = bridge.add_term(arena, lhs);
                let rhs = bridge.add_term(arena, rhs);
                let lhs = bridge.egraph.root(lhs);
                let rhs = bridge.egraph.root(rhs);
                disequalities.insert(ordered_node_pair(lhs, rhs));
            }
        }
        Self {
            bridge,
            disequalities,
        }
    }

    fn equality(&mut self, arena: &TermArena, lhs: TermId, rhs: TermId) -> LiteralValue {
        let lhs = self.bridge.add_term(arena, lhs);
        let rhs = self.bridge.add_term(arena, rhs);
        if self.bridge.egraph.equal(lhs, rhs) {
            return LiteralValue::True;
        }
        let lhs_root = self.bridge.egraph.root(lhs);
        let rhs_root = self.bridge.egraph.root(rhs);
        if self
            .disequalities
            .contains(&ordered_node_pair(lhs_root, rhs_root))
        {
            LiteralValue::False
        } else {
            LiteralValue::Undetermined
        }
    }
}

fn ordered_node_pair(a: ENodeId, b: ENodeId) -> (ENodeId, ENodeId) {
    if a <= b { (a, b) } else { (b, a) }
}

fn equality_literal(arena: &TermArena, term: TermId) -> Option<(bool, TermId, TermId)> {
    match arena.node(term) {
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => Some((true, args[0], args[1])),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => match arena.node(args[0]) {
            TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
                Some((false, args[0], args[1]))
            }
            _ => None,
        },
        _ => None,
    }
}

fn evaluate_equality_clause(
    arena: &TermArena,
    clause: TermId,
    facts: &mut GroundEqualityContext,
) -> Option<ClauseValue> {
    evaluate_equality_clause_with(arena, clause, &mut |lhs, rhs| {
        facts.equality(arena, lhs, rhs)
    })
}

fn evaluate_equality_clause_with(
    arena: &TermArena,
    clause: TermId,
    equality: &mut impl FnMut(TermId, TermId) -> LiteralValue,
) -> Option<ClauseValue> {
    let mut literals = Vec::new();
    collect_clause_literals(arena, clause, &mut literals);
    let mut undetermined = 0usize;
    for literal in literals {
        let value = if let TermNode::BoolConst(value) = arena.node(literal) {
            if *value {
                LiteralValue::True
            } else {
                LiteralValue::False
            }
        } else {
            let (positive, lhs, rhs) = equality_literal(arena, literal)?;
            let value = equality(lhs, rhs);
            if positive { value } else { value.negate() }
        };
        match value {
            LiteralValue::True => return Some(ClauseValue::True),
            LiteralValue::False => {}
            LiteralValue::Undetermined => undetermined += 1,
        }
    }
    Some(match undetermined {
        0 => ClauseValue::False,
        1 => ClauseValue::Unit,
        _ => ClauseValue::Undetermined,
    })
}

fn collect_clause_literals(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if args.len() == 2 => {
            collect_clause_literals(arena, args[0], out);
            collect_clause_literals(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

/// E-matches the universal `forall_term`'s trigger(s) against the `ground` terms
/// and returns, in addition to the bound variables and quantifier-free body, the
/// **witness tuples** — one ground term per bound variable, in binder order
/// (outermost first) — that the e-matching selects. Tuples are deterministically
/// ordered and de-duplicated.
///
/// This is the witness-tuple source the Alethe quantifier emitter
/// ([`crate::prove_quant_unsat_alethe`]) consumes when the brute-force cartesian
/// search would blow its candidate cap: e-matching is trigger-driven, so it scales
/// to many ground terms / multiple binders where the cartesian product does not.
/// The returned tuples are *candidates* — the caller validates that some subset
/// actually refutes the ground set before emitting a proof, so an unhelpful match
/// set is rejected cleanly, never turned into a bad proof.
///
/// Returns `None` when `forall_term` is not a universal, has no trigger covering
/// all bound variables, or no complete witness tuple is found (the trigger's
/// symbols do not occur in the ground terms).
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn witness_tuples_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Option<(Vec<SymbolId>, TermId, Vec<Vec<TermId>>)> {
    let matches = witness_matches_via_egraph(arena, ground, forall_term)?;
    Some((matches.vars, matches.body, matches.tuples))
}

struct WitnessMatches {
    vars: Vec<SymbolId>,
    body: TermId,
    tuples: Vec<Vec<TermId>>,
    #[cfg(test)]
    bridge: InstBridge,
}

fn witness_matches_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Option<WitnessMatches> {
    // Peel the (possibly nested) universal prefix `∀x. ∀y. … body`.
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return None;
    }
    let var_index: HashMap<SymbolId, u32> = vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, u32::try_from(i).expect("variable count fits u32")))
        .collect();

    // Infer a (possibly multi-pattern) trigger: a set of function-application
    // subterms whose bound variables together cover all of them. A single term is
    // used when one covers all variables; otherwise a greedy set cover (matched
    // and joined below) handles patterns like `∀x,y. f(x) = g(y)`.
    let triggers = select_triggers(arena, body, &var_index);
    if triggers.is_empty() {
        return None;
    }

    let mut bridge = InstBridge::new();
    for &g in ground {
        bridge.add_term(arena, g);
        // A top-level ground equality `(= s t)` asserts s = t — merge it so matching
        // is genuinely modulo the ground congruence.
        if let TermNode::App { op, args } = arena.node(g)
            && matches!(op, Op::Eq)
            && args.len() == 2
        {
            let (s, t) = (args[0], args[1]);
            let ns = bridge.add_term(arena, s);
            let nt = bridge.add_term(arena, t);
            bridge.egraph.merge(ns, nt, 0);
        }
    }

    // Match each trigger and join the per-trigger substitutions into full
    // substitutions consistent on shared variables.
    let nvars = vars.len();
    let mut joined: Vec<Vec<Option<ENodeId>>> = vec![vec![None; nvars]];
    for trigger in triggers {
        let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
        let matches = bridge.egraph.ematch(&pattern);
        let mut next = Vec::new();
        for partial in &joined {
            for m in &matches {
                if let Some(merged) = merge_substitutions(partial, m) {
                    next.push(merged);
                }
            }
        }
        joined = next;
        if joined.is_empty() {
            return None;
        }
    }

    let mut tuples: Vec<Vec<TermId>> = Vec::new();
    for subst in joined {
        // Build the witness tuple from every bound variable's matched class
        // representative; skip incomplete matches.
        let mut tuple: Vec<TermId> = Vec::with_capacity(nvars);
        let complete = (0..nvars).all(|i| {
            if let Some(repr) = subst
                .get(i)
                .copied()
                .flatten()
                .and_then(|class| bridge.repr_term.get(&class).copied())
            {
                tuple.push(repr);
                true
            } else {
                false
            }
        });
        if complete {
            tuples.push(tuple);
        }
    }
    // Deterministic order and de-dup (tuples compare lexicographically by index).
    tuples.sort_by(|x, y| x.iter().map(|t| t.index()).cmp(y.iter().map(|t| t.index())));
    tuples.dedup();
    Some(WitnessMatches {
        vars,
        body,
        tuples,
        #[cfg(test)]
        bridge,
    })
}

/// Peels the universal prefix `∀v1. ∀v2. … body`, returning the bound variables
/// (outer first) and the innermost non-quantified body.
fn peel_foralls(arena: &TermArena, mut term: TermId) -> (Vec<SymbolId>, TermId) {
    let mut vars = Vec::new();
    while let Some((var, body)) = as_forall(arena, term) {
        vars.push(var);
        term = body;
    }
    (vars, term)
}

/// Decomposes a `(forall x body)` term into its bound variable and body.
fn as_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    match arena.node(term) {
        TermNode::App { op, args } if matches!(op, Op::Forall(_)) && args.len() == 1 => {
            let Op::Forall(var) = op else {
                unreachable!("matched Forall above")
            };
            Some((*var, args[0]))
        }
        _ => None,
    }
}

/// Refutes a **closed** top-level universal `∀x⃗. body` by falsifying its body.
///
/// Returns `Ok(Some(Unsat))` when `forall_term` is a closed universal (a
/// quantifier-free body mentioning no symbol outside its own bound variables) and
/// `¬body[x⃗ := c⃗]` is satisfiable for fresh constants `c⃗` — a witness that the
/// closed sentence `∀x⃗. body` is *false*, hence the whole query is `unsat`.
/// Returns `Ok(None)` when the shape does not apply (not a universal, an open or
/// still-quantified body) or the falsification sub-check is not a definite `Sat`
/// (`unsat` ⇒ the universal is valid, already handled upstream; `unknown` ⇒ decline
/// so the e-matching loop still runs). Never returns a non-`Unsat` `CheckResult`.
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground [`check_auto`] sub-check.
fn refute_closed_universal(
    arena: &mut TermArena,
    forall_term: TermId,
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return Ok(None);
    }
    let bound: HashSet<SymbolId> = vars.iter().copied().collect();
    // Only a *closed* quantifier-free body is a sentence we can falsify exactly.
    if !body_is_closed_qf(arena, body, &bound) {
        return Ok(None);
    }
    // Substitute each bound variable with a fresh Herbrand constant of its sort, so
    // the ground solver is free to pick the falsifying witness.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    for &v in &vars {
        let sort = arena.symbol(v).1;
        let fresh = arena
            .declare_internal(&format!("!cu_{}", v.index()), sort)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let var = arena.var(v);
        let fresh_term = arena.var(fresh);
        map.insert(var, fresh_term);
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let instance = replace_subterms(arena, body, &map, &mut memo)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let negated = arena
        .not(instance)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    // `¬body[c⃗]` satisfiable ⇒ `∃x⃗. ¬body` ⇒ `∀x⃗. body` is false ⇒ query unsat.
    match check_auto(arena, &[negated], config)? {
        CheckResult::Sat(_) => Ok(Some(CheckResult::Unsat)),
        _ => Ok(None),
    }
}

/// Whether `term` is quantifier-free and every symbol it mentions is in `bound`
/// (so the universal it bodies is a closed sentence over exactly `bound`).
fn body_is_closed_qf(arena: &TermArena, term: TermId, bound: &HashSet<SymbolId>) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if !bound.contains(s) => {
                return false; // a free symbol: not a closed sentence
            }
            TermNode::App { op, args } => {
                // Reject anything carrying a *free* symbol the substitution cannot
                // reach: an inner quantifier (not quantifier-free) or an
                // uninterpreted-function application (its `FuncId` is a free symbol
                // — `∀x. f(x)=c` is satisfiable, not a refutable closed sentence).
                if matches!(op, Op::Forall(_) | Op::Exists(_) | Op::Apply(_)) {
                    return false;
                }
                for &a in args {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    true
}

#[derive(Clone, Copy)]
struct EuclideanResiduePattern {
    remainder: SymbolId,
    quotient: SymbolId,
    dividend: TermId,
    modulus: i128,
}

#[derive(Clone, Copy)]
struct AffineGrowthPattern {
    variable: SymbolId,
    coefficient: i128,
    else_value: TermId,
    threshold: TermId,
}

#[derive(Clone, Copy)]
struct NestedXorSearchPattern {
    outer_bindings: [(SymbolId, i128); 2],
    nested: SymbolId,
    nested_pivot: i128,
    nested_body: TermId,
}

/// Builds the final hierarchical universal instance from ADR-0099.
///
/// This search matcher is intentionally separate from the original-IR evidence
/// checker in `quant_nested_xor_cert`.
fn nested_xor_discriminator_instance(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<TermId>, SolverError> {
    let (outer, body) = peel_foralls(arena, forall_term);
    if outer.len() != 2
        || outer[0] == outer[1]
        || outer.iter().any(|&var| arena.symbol(var).1 != Sort::Int)
    {
        return Ok(None);
    }
    let Some(pattern) = search_nested_xor_pattern(arena, body, &outer) else {
        return Ok(None);
    };
    let nested_witness = pattern
        .nested_pivot
        .checked_add(1)
        .or_else(|| pattern.nested_pivot.checked_sub(1))
        .expect("every i128 value has an adjacent representable integer");

    let mut replacements = HashMap::new();
    for (var, value) in pattern.outer_bindings {
        let value = arena.int_const(value);
        replacements.insert(arena.var(var), value);
    }
    let nested_value = arena.int_const(nested_witness);
    replacements.insert(arena.var(pattern.nested), nested_value);
    let mut memo = HashMap::new();
    replace_subterms(arena, pattern.nested_body, &replacements, &mut memo)
        .map(Some)
        .map_err(|error| SolverError::Backend(error.to_string()))
}

fn search_nested_xor_pattern(
    arena: &TermArena,
    body: TermId,
    outer: &[SymbolId],
) -> Option<NestedXorSearchPattern> {
    let (selector, nested_quantifier) = search_outer_xor_children(arena, body)?;
    let outer_bindings = search_selector_bindings(arena, selector, outer)?;
    let (nested, nested_body) = as_forall(arena, nested_quantifier)?;
    if outer.contains(&nested) || arena.symbol(nested).1 != Sort::Int {
        return None;
    }
    let (active, active_pivot, nested_pivot) =
        search_nested_discriminator(arena, nested_body, outer, nested)?;
    if !outer_bindings
        .iter()
        .any(|&(var, pivot)| var == active && pivot == active_pivot)
    {
        return None;
    }
    Some(NestedXorSearchPattern {
        outer_bindings,
        nested,
        nested_pivot,
        nested_body,
    })
}

fn search_outer_xor_children(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (as_forall(arena, *left), as_forall(arena, *right)) {
        (None, Some(_)) => Some((*left, *right)),
        (Some(_), None) => Some((*right, *left)),
        _ => None,
    }
}

fn search_selector_bindings(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
) -> Option<[(SymbolId, i128); 2]> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let first = search_symbol_constant_equality(arena, *left)?;
    let second = search_symbol_constant_equality(arena, *right)?;
    if first.0 == second.0 || !outer.contains(&first.0) || !outer.contains(&second.0) {
        return None;
    }
    Some([first, second])
}

fn search_nested_discriminator(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<(SymbolId, i128, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    search_discriminator_ites(arena, *left, *right, outer, nested)
        .or_else(|| search_discriminator_ites(arena, *right, *left, outer, nested))
}

fn search_discriminator_ites(
    arena: &TermArena,
    active_ite: TermId,
    nested_ite: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<(SymbolId, i128, i128)> {
    let (active_guard, active_then, active_else) = search_ite(arena, active_ite)?;
    let (nested_guard, nested_then, nested_else) = search_ite(arena, nested_ite)?;
    let (active, active_pivot) = search_symbol_constant_equality(arena, active_guard)?;
    let (found_nested, nested_pivot) = search_symbol_constant_equality(arena, nested_guard)?;
    if !outer.contains(&active) || found_nested != nested {
        return None;
    }
    let then_value = search_int_constant(arena, active_then)?;
    let else_value = search_int_constant(arena, active_else)?;
    if then_value == else_value
        || search_int_constant(arena, nested_then) != Some(then_value)
        || search_int_constant(arena, nested_else) != Some(else_value)
    {
        return None;
    }
    Some((active, active_pivot, nested_pivot))
}

fn search_symbol_constant_equality(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(symbol), _) => Some((*symbol, search_int_constant(arena, *right)?)),
        (_, TermNode::Symbol(symbol)) => Some((*symbol, search_int_constant(arena, *left)?)),
        _ => None,
    }
}

fn search_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    Some((*condition, *then_value, *else_value))
}

fn search_int_constant(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => {
            let [inner] = &**args else {
                return None;
            };
            match arena.node(*inner) {
                TermNode::IntConst(value) => value.checked_neg(),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Builds the two consecutive symbolic counterexample instances from
/// ADR-0097. A non-matching universal declines.
fn affine_growth_instances(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<Vec<TermId>>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    let bound: HashSet<_> = vars.iter().copied().collect();
    if vars.is_empty()
        || bound.len() != vars.len()
        || vars.iter().any(|&var| arena.symbol(var).1 != Sort::Int)
    {
        return Ok(None);
    }
    let Some(pattern) = match_affine_growth_body(arena, body, &bound) else {
        return Ok(None);
    };

    let coefficient = arena.int_const(pattern.coefficient);
    let numerator = arena
        .int_add(pattern.else_value, pattern.threshold)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let quotient = arena
        .int_div(numerator, coefficient)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let one = arena.int_const(1);
    let first = arena
        .int_add(quotient, one)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let second = arena
        .int_add(first, one)
        .map_err(|error| SolverError::Backend(error.to_string()))?;

    let variable = arena.var(pattern.variable);
    let mut instances = Vec::with_capacity(2);
    for candidate in [first, second] {
        let replacements = HashMap::from([(variable, candidate)]);
        let mut memo = HashMap::new();
        instances.push(
            replace_subterms(arena, body, &replacements, &mut memo)
                .map_err(|error| SolverError::Backend(error.to_string()))?,
        );
    }
    Ok(Some(instances))
}

fn match_affine_growth_body(
    arena: &TermArena,
    body: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<AffineGrowthPattern> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [comparison] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(*comparison)
    else {
        return None;
    };
    let [difference, threshold] = &**args else {
        return None;
    };
    if contains_any_symbol(arena, *threshold, bound) {
        return None;
    }

    let (variable, coefficient, piecewise) = match_growth_difference(arena, *difference)?;
    if coefficient <= 0 || !bound.contains(&variable) {
        return None;
    }
    let (pivot, then_value, else_value) = match_growth_piecewise(arena, piecewise, variable)?;
    if [pivot, then_value, else_value]
        .into_iter()
        .any(|term| contains_any_symbol(arena, term, bound))
    {
        return None;
    }

    Some(AffineGrowthPattern {
        variable,
        coefficient,
        else_value,
        threshold: *threshold,
    })
}

fn match_growth_difference(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128, TermId)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let [scaled, piecewise] = &**args else {
                return None;
            };
            let (variable, coefficient) = match_growth_scaled(arena, *scaled)?;
            Some((variable, coefficient, *piecewise))
        }
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => {
            let [left, right] = &**args else {
                return None;
            };
            match_growth_scaled_plus_negated(arena, *left, *right)
                .or_else(|| match_growth_scaled_plus_negated(arena, *right, *left))
        }
        _ => None,
    }
}

fn match_growth_scaled_plus_negated(
    arena: &TermArena,
    scaled: TermId,
    negated: TermId,
) -> Option<(SymbolId, i128, TermId)> {
    let (variable, coefficient) = match_growth_scaled(arena, scaled)?;
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(negated)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let piecewise = if growth_is_minus_one(arena, *left) {
        *right
    } else if growth_is_minus_one(arena, *right) {
        *left
    } else {
        return None;
    };
    Some((variable, coefficient, piecewise))
}

fn match_growth_scaled(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::IntConst(coefficient), TermNode::Symbol(variable))
        | (TermNode::Symbol(variable), TermNode::IntConst(coefficient)) => {
            Some((*variable, *coefficient))
        }
        _ => None,
    }
}

fn growth_is_minus_one(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::IntConst(-1) => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => matches!(&**args, [one] if matches!(arena.node(*one), TermNode::IntConst(1))),
        _ => false,
    }
}

fn match_growth_piecewise(
    arena: &TermArena,
    term: TermId,
    variable: SymbolId,
) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*condition) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let pivot = match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(found), _) if *found == variable => *right,
        (_, TermNode::Symbol(found)) if *found == variable => *left,
        _ => return None,
    };
    Some((pivot, *then_value, *else_value))
}

/// Builds the symbolic counterexample instance for the exact Euclidean residue
/// partition described at the call site. A non-matching universal declines.
fn euclidean_residue_instance(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<TermId>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.len() != 2 || vars.iter().any(|&v| arena.symbol(v).1 != Sort::Int) {
        return Ok(None);
    }
    let bound: HashSet<SymbolId> = vars.iter().copied().collect();
    let Some(pattern) = match_euclidean_residue_body(arena, body, &bound) else {
        return Ok(None);
    };
    if !bound.contains(&pattern.remainder)
        || !bound.contains(&pattern.quotient)
        || pattern.remainder == pattern.quotient
    {
        return Ok(None);
    }

    let modulus = arena.int_const(pattern.modulus);
    let quotient = arena
        .int_div(pattern.dividend, modulus)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let remainder = arena
        .int_mod(pattern.dividend, modulus)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let mut replacements = HashMap::new();
    replacements.insert(arena.var(pattern.remainder), remainder);
    replacements.insert(arena.var(pattern.quotient), quotient);
    let mut memo = HashMap::new();
    replace_subterms(arena, body, &replacements, &mut memo)
        .map(Some)
        .map_err(|e| SolverError::Backend(e.to_string()))
}

fn match_euclidean_residue_body(
    arena: &TermArena,
    body: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    let mut disjuncts = Vec::new();
    flatten_or(arena, body, &mut disjuncts);
    if disjuncts.len() != 3 {
        return None;
    }

    let pattern = disjuncts
        .iter()
        .find_map(|&d| match_negated_recomposition(arena, d, bound))?;
    let mut lower = false;
    let mut upper = false;
    for &d in &disjuncts {
        if match_negated_recomposition(arena, d, bound).is_some() {
            continue;
        }
        if is_remainder_lower_guard(arena, d, pattern.remainder) {
            if lower {
                return None;
            }
            lower = true;
        } else if is_remainder_upper_guard(arena, d, pattern.remainder, pattern.modulus) {
            if upper {
                return None;
            }
            upper = true;
        } else {
            return None;
        }
    }
    (lower && upper).then_some(pattern)
}

fn flatten_or(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    {
        let args = args.clone();
        for arg in args {
            flatten_or(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn match_negated_recomposition(
    arena: &TermArena,
    term: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(args[0]) else {
        return None;
    };
    match_recomposition_equality(arena, args[0], args[1], bound)
        .or_else(|| match_recomposition_equality(arena, args[1], args[0], bound))
}

fn match_recomposition_equality(
    arena: &TermArena,
    sum: TermId,
    dividend: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    if contains_any_symbol(arena, dividend, bound) {
        return None;
    }
    let TermNode::App {
        op: Op::IntAdd,
        args,
    } = arena.node(sum)
    else {
        return None;
    };
    let (quotient, modulus, remainder) = match_scaled_plus_remainder(arena, args[0], args[1])
        .or_else(|| match_scaled_plus_remainder(arena, args[1], args[0]))?;
    if modulus <= 0 || !bound.contains(&quotient) || !bound.contains(&remainder) {
        return None;
    }
    Some(EuclideanResiduePattern {
        remainder,
        quotient,
        dividend,
        modulus,
    })
}

fn match_scaled_plus_remainder(
    arena: &TermArena,
    scaled: TermId,
    remainder: TermId,
) -> Option<(SymbolId, i128, SymbolId)> {
    let TermNode::Symbol(remainder) = arena.node(remainder) else {
        return None;
    };
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(scaled)
    else {
        return None;
    };
    let (modulus, quotient) = match (arena.node(args[0]), arena.node(args[1])) {
        (TermNode::IntConst(k), TermNode::Symbol(q))
        | (TermNode::Symbol(q), TermNode::IntConst(k)) => (*k, *q),
        _ => return None,
    };
    Some((quotient, modulus, *remainder))
}

fn is_remainder_lower_guard(arena: &TermArena, term: TermId, remainder: SymbolId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::IntLt, args }
            if matches!(arena.node(args[0]), TermNode::Symbol(s) if *s == remainder)
                && matches!(arena.node(args[1]), TermNode::IntConst(0))
    )
}

fn is_remainder_upper_guard(
    arena: &TermArena,
    term: TermId,
    remainder: SymbolId,
    modulus: i128,
) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::IntGe, args }
            if matches!(arena.node(args[0]), TermNode::Symbol(s) if *s == remainder)
                && matches!(arena.node(args[1]), TermNode::IntConst(k) if *k == modulus)
    )
}

fn contains_any_symbol(arena: &TermArena, term: TermId, symbols: &HashSet<SymbolId>) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if symbols.contains(s) => return true,
            TermNode::App { op, args } => {
                if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    false
}

/// Infers a trigger: a set of function-application subterms whose bound variables
/// together cover all of them. Prefers a single term that covers everything (e.g.
/// `f(x)`, `g(x, y)`); otherwise a greedy set cover yields a multi-pattern (e.g.
/// `{f(x), g(y)}` for `∀x,y. f(x) = g(y)`). Returns empty when the variables cannot
/// be covered by function applications.
fn select_triggers(arena: &TermArena, body: TermId, vars: &HashMap<SymbolId, u32>) -> Vec<TermId> {
    // Candidate function-application subterms with the variable-index set each one
    // covers.
    let mut candidates: Vec<(TermId, HashSet<u32>)> = Vec::new();
    collect_app_candidates(arena, body, vars, &mut candidates);

    let all: HashSet<u32> = (0..u32::try_from(vars.len()).expect("var count fits u32")).collect();
    // A single covering term is the best trigger.
    if let Some((t, _)) = candidates.iter().find(|(_, c)| *c == all) {
        return vec![*t];
    }
    // Greedy set cover otherwise.
    let mut uncovered = all;
    let mut chosen = Vec::new();
    while !uncovered.is_empty() {
        let best = candidates
            .iter()
            .max_by_key(|(_, c)| c.intersection(&uncovered).count());
        match best {
            Some((t, c)) if c.intersection(&uncovered).next().is_some() => {
                for v in c {
                    uncovered.remove(v);
                }
                chosen.push(*t);
            }
            _ => return Vec::new(), // some variable is in no function application
        }
    }
    chosen
}

/// Collects every function-application subterm of `body`, with the set of bound
/// variable indices it mentions (only those covering ≥1 bound variable are kept).
fn collect_app_candidates(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    out: &mut Vec<(TermId, HashSet<u32>)>,
) {
    if let TermNode::App { op, args } = arena.node(term) {
        // With the nesting-preserving layout a body can still contain binders.
        // An application under one mentions variables this universal does not
        // bind, so compiling it as a trigger would freeze those into ground
        // constants that never match — a trigger that covers a variable on paper
        // and matches nothing in practice, which starves the universal entirely.
        // Each nested binder is registered separately with its own triggers.
        if matches!(op, Op::Forall(_) | Op::Exists(_))
            && crate::quant_skolemize::nested_quantifiers_enabled()
        {
            return;
        }
        if matches!(op, Op::Apply(_)) {
            let mut seen = HashSet::new();
            collect_vars(arena, term, vars, &mut seen);
            if !seen.is_empty() {
                let indices: HashSet<u32> = seen.iter().map(|s| vars[s]).collect();
                out.push((term, indices));
            }
        }
        let args = args.clone();
        for a in args {
            collect_app_candidates(arena, a, vars, out);
        }
    }
}

/// Merges two partial substitutions, returning `None` on a variable conflict.
fn merge_substitutions(
    a: &[Option<ENodeId>],
    b: &[Option<ENodeId>],
) -> Option<Vec<Option<ENodeId>>> {
    let mut out = a.to_vec();
    for (slot, &bi) in out.iter_mut().zip(b) {
        if let Some(bv) = bi {
            match *slot {
                Some(av) if av != bv => return None,
                _ => *slot = Some(bv),
            }
        }
    }
    Some(out)
}

/// Combines retained substitutions against the e-graph's current roots.
/// Cached class ids may predate one or more ADR-0113 merge notifications.
fn merge_substitutions_modulo(
    egraph: &EGraph,
    a: &[Option<ENodeId>],
    b: &[Option<ENodeId>],
) -> Option<Vec<Option<ENodeId>>> {
    let mut out: Vec<Option<ENodeId>> = a
        .iter()
        .map(|value| value.map(|node| egraph.root(node)))
        .collect();
    for (slot, &bi) in out.iter_mut().zip(b) {
        if let Some(bv) = bi.map(|node| egraph.root(node)) {
            match *slot {
                Some(av) if av != bv => return None,
                _ => *slot = Some(bv),
            }
        }
    }
    Some(out)
}

/// Records which `vars` occur in `term`.
fn collect_vars(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    seen: &mut std::collections::HashSet<SymbolId>,
) {
    match arena.node(term) {
        TermNode::Symbol(s) if vars.contains_key(s) => {
            seen.insert(*s);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for a in args {
                collect_vars(arena, a, vars, seen);
            }
        }
        _ => {}
    }
}

/// Retained term-invention state for one e-graph refutation attempt. Prepared
/// lazily at the first starved fixpoint; all fields are bookkeeping for a
/// bounded, deterministic enumeration — none of them carries proof content.
#[derive(Default)]
struct TermInventionState {
    prepared: bool,
    /// Every symbol bound by a `forall`/`exists` anywhere in the assertions.
    /// An occurrence of one of these is not ground and never usable as a seed.
    binders: HashSet<SymbolId>,
    /// Free constant symbols per sort, in symbol order — deliberately
    /// collected from the WHOLE assertion DAG including universal bodies, so
    /// Skolem constants that occur only under a binder become seeds.
    constant_seeds: HashMap<Sort, Vec<TermId>>,
    /// Whether each pattern's source trigger is usable for invention:
    /// quantifier-free and mentioning no binder symbol beyond its own
    /// variables (a foreign bound variable would make the "ground" instance
    /// spurious).
    pattern_usable: Vec<bool>,
    /// Total terms this attempt has invented, against
    /// [`MAX_INVENTED_TERMS_TOTAL`].
    invented_total: usize,
    /// Total direct instances generated for starved universals, against
    /// [`MAX_DIRECT_INSTANCES_TOTAL`].
    direct_total: usize,
    /// Direct instances generated per universal assertion, so a universal fed
    /// only by this route stays eligible (its retained count never exceeding
    /// its direct count means matching has produced nothing for it).
    direct_per_universal: HashMap<TermId, usize>,
    /// Memoized binder-free / quantifier-free classification per term.
    ground_cache: HashMap<TermId, bool>,
}

impl TermInventionState {
    fn prepare(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        pattern_triggers: &[Option<PatternTrigger>],
    ) {
        self.prepared = true;
        // One DFS over the assertion DAG: binder symbols and symbol
        // occurrences (first-visit order; the sort grouping below re-sorts by
        // symbol index for determinism).
        let mut seen: HashSet<TermId> = HashSet::new();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut symbols: Vec<SymbolId> = Vec::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match arena.node(term) {
                TermNode::Symbol(symbol) => symbols.push(*symbol),
                TermNode::App { op, args } => {
                    if let Op::Forall(binder) | Op::Exists(binder) = op {
                        self.binders.insert(*binder);
                    }
                    stack.extend(args.iter().copied());
                }
                _ => {}
            }
        }
        // Skolem/internal witnesses (reserved `!…` names) FIRST: the
        // refutations this class needs bind mostly to the negated-conclusion
        // Skolem constants, and the digit-sum staging reaches early seeds
        // exponentially sooner than late ones.
        symbols.sort_by_key(|symbol| (!arena.symbol(*symbol).0.starts_with('!'), symbol.index()));
        symbols.dedup();
        for symbol in symbols {
            if self.binders.contains(&symbol) {
                continue;
            }
            let sort = arena.symbol(symbol).1;
            let seeds = self.constant_seeds.entry(sort).or_default();
            if seeds.len() < MAX_INVENTION_SEEDS_PER_SORT {
                seeds.push(arena.var(symbol));
            }
        }
        self.pattern_usable = pattern_triggers
            .iter()
            .map(|entry| {
                entry.as_ref().is_some_and(|trigger| {
                    let own: HashSet<TermId> = trigger.var_terms.iter().copied().collect();
                    self.trigger_usable(arena, trigger.trigger, &own)
                })
            })
            .collect();
    }

    /// A trigger is usable when it contains no quantifier and every symbol in
    /// it is either one of its own bound variables or not a binder at all.
    fn trigger_usable(
        &self,
        arena: &TermArena,
        trigger: TermId,
        own_vars: &HashSet<TermId>,
    ) -> bool {
        let mut seen: HashSet<TermId> = HashSet::new();
        let mut stack = vec![trigger];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match arena.node(term) {
                TermNode::Symbol(symbol)
                    if self.binders.contains(symbol) && !own_vars.contains(&term) =>
                {
                    return false;
                }
                TermNode::App { op, args } => {
                    if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                        return false;
                    }
                    stack.extend(args.iter().copied());
                }
                _ => {}
            }
        }
        true
    }

    /// Memoized: `term` mentions no binder symbol and no quantifier, so it is
    /// a genuinely ground seed candidate.
    fn is_binder_free(&mut self, arena: &TermArena, term: TermId) -> bool {
        if let Some(&known) = self.ground_cache.get(&term) {
            return known;
        }
        let free = match arena.node(term) {
            TermNode::Symbol(symbol) => !self.binders.contains(symbol),
            TermNode::App { op, args } => {
                if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                    false
                } else {
                    let args = args.clone();
                    args.iter().all(|&arg| self.is_binder_free(arena, arg))
                }
            }
            _ => true,
        };
        self.ground_cache.insert(term, free);
        free
    }
}

/// Enumerates every index tuple over `lens` whose digit sum equals
/// `remaining`, in lexicographic order; the visitor returns `false` to stop
/// the whole enumeration. Staging tuples by digit sum yields the
/// smallest-seed combinations first (all-zeros, then single steps, …), the
/// same cheap relevance order cvc5's enumerative modes use.
fn for_each_tuple_with_sum(
    lens: &[usize],
    remaining: usize,
    prefix: &mut Vec<usize>,
    visit: &mut impl FnMut(&[usize]) -> bool,
) -> bool {
    let position = prefix.len();
    if position == lens.len() {
        if remaining == 0 {
            return visit(prefix);
        }
        return true;
    }
    let suffix_capacity: usize = lens[position..]
        .iter()
        .map(|&len| len.saturating_sub(1))
        .sum();
    if remaining > suffix_capacity {
        return true;
    }
    let max_digit = lens[position].saturating_sub(1).min(remaining);
    for digit in 0..=max_digit {
        prefix.push(digit);
        let keep_going = for_each_tuple_with_sum(lens, remaining - digit, prefix, visit);
        prefix.pop();
        if !keep_going {
            return false;
        }
    }
    true
}

/// Bridges ground IR terms to the e-graph for instantiation: it builds e-nodes,
/// assigns each symbol/function/constant a `decl`, and remembers a representative
/// ground term per class (to substitute back on a match).
struct InstBridge {
    egraph: EGraph,
    term_to_node: HashMap<TermId, ENodeId>,
    func_decls: HashMap<FuncId, u32>,
    symbol_decls: HashMap<usize, u32>,
    op_decls: HashMap<String, u32>,
    /// First ground term seen per class root — the instantiation witness.
    repr_term: HashMap<ENodeId, TermId>,
    next_decl: u32,
}

impl InstBridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_to_node: HashMap::new(),
            func_decls: HashMap::new(),
            symbol_decls: HashMap::new(),
            op_decls: HashMap::new(),
            repr_term: HashMap::new(),
            next_decl: 0,
        }
    }

    fn fresh_decl(&mut self) -> u32 {
        let d = self.next_decl;
        self.next_decl += 1;
        d
    }

    fn add_term(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.term_to_node.get(&term) {
            return n;
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.symbol_decl(s.index());
                self.egraph.add(decl, &[])
            }
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.func_decl(func);
                self.egraph.add(decl, &children)
            }
            TermNode::App { op, args } => {
                // Other interpreted operators are treated as uninterpreted for the
                // purposes of matching (sound: matching only fires on real terms).
                let op = format!("{op:?}");
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.op_decl(&op);
                self.egraph.add(decl, &children)
            }
            _ => {
                // A literal constant: each distinct value is its own leaf.
                let key = format!("c:{:?}", arena.node(term));
                let decl = self.op_decl(&key);
                self.egraph.add(decl, &[])
            }
        };
        let root = self.egraph.root(node);
        self.repr_term.entry(root).or_insert(term);
        self.term_to_node.insert(term, node);
        node
    }

    fn symbol_decl(&mut self, sym: usize) -> u32 {
        if let Some(&d) = self.symbol_decls.get(&sym) {
            return d;
        }
        let d = self.fresh_decl();
        self.symbol_decls.insert(sym, d);
        d
    }

    fn func_decl(&mut self, func: FuncId) -> u32 {
        if let Some(&d) = self.func_decls.get(&func) {
            return d;
        }
        let d = self.fresh_decl();
        self.func_decls.insert(func, d);
        d
    }

    fn op_decl(&mut self, key: &str) -> u32 {
        if let Some(&d) = self.op_decls.get(key) {
            return d;
        }
        let d = self.fresh_decl();
        self.op_decls.insert(key.to_owned(), d);
        d
    }

    /// Converts a trigger term to an e-matching [`Pattern`] under this bridge's
    /// decl assignment: the bound `var` becomes `Var(0)`, and every other subterm
    /// (symbols, applications, constants, interpreted ops) becomes an application
    /// keyed by the same decl the ground terms use — so a ground subterm in the
    /// trigger matches its own class, while only `var` is free.
    fn trigger_to_pattern(
        &mut self,
        arena: &TermArena,
        term: TermId,
        vars: &HashMap<SymbolId, u32>,
    ) -> Pattern {
        match arena.node(term) {
            TermNode::Symbol(s) if vars.contains_key(s) => Pattern::Var(vars[s]),
            TermNode::Symbol(s) => Pattern::App(self.symbol_decl(s.index()), Vec::new()),
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.func_decl(func), subs)
            }
            TermNode::App { op, args } => {
                let key = format!("{op:?}");
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.op_decl(&key), subs)
            }
            _ => Pattern::App(
                self.op_decl(&format!("c:{:?}", arena.node(term))),
                Vec::new(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;
    use axeyum_ir::Sort;

    /// The term-starved class in miniature: `∀x:S. p(f(x))` against
    /// `∀y:T. ¬p(y)` with the only S-sorted constants living in a ground
    /// disequality. No application term exists anywhere in the ground set, so
    /// matching alone reaches an immediate fixpoint; term invention must
    /// build `f(d)` (and the trigger instance over it) for the refutation.
    #[test]
    fn term_invention_refutes_a_term_starved_contradiction() {
        let mut arena = TermArena::new();
        let carrier_s = arena.declare_uninterpreted_sort("TiS");
        let carrier_t = arena.declare_uninterpreted_sort("TiT");
        let sort_s = Sort::Uninterpreted(carrier_s);
        let sort_t = Sort::Uninterpreted(carrier_t);
        let image_fn = arena.declare_fun("ti_f", &[sort_s], sort_t).unwrap();
        let predicate = arena.declare_fun("ti_p", &[sort_t], Sort::Bool).unwrap();
        let left_const = arena.declare("ti_d", sort_s).unwrap();
        let right_const = arena.declare("ti_e", sort_s).unwrap();

        let binder_x = arena.declare("ti_x", sort_s).unwrap();
        let xv = arena.var(binder_x);
        let f_x = arena.apply(image_fn, &[xv]).unwrap();
        let p_f_x = arena.apply(predicate, &[f_x]).unwrap();
        let all_imaged = arena.forall(binder_x, p_f_x).unwrap();

        let binder_y = arena.declare("ti_y", sort_t).unwrap();
        let yv = arena.var(binder_y);
        let p_y = arena.apply(predicate, &[yv]).unwrap();
        let not_p_y = arena.not(p_y).unwrap();
        let none_p = arena.forall(binder_y, not_p_y).unwrap();

        let dv = arena.var(left_const);
        let ev = arena.var(right_const);
        let d_eq_e = arena.eq(dv, ev).unwrap();
        let ground = arena.not(d_eq_e).unwrap();

        let assertions = vec![all_imaged, none_p, ground];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        assert!(matches!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &config).unwrap(),
            CheckResult::Unsat
        ));
    }

    /// Skolem-seeded variant: the only constant of the binder sort occurs
    /// INSIDE a universal body (the position a Skolem constant lands in after
    /// skolemization), never in any ground assertion. Invention must collect
    /// it from the body and still build the refuting terms.
    #[test]
    fn term_invention_seeds_constants_from_universal_bodies() {
        let mut arena = TermArena::new();
        let carrier_s = arena.declare_uninterpreted_sort("TiBodyS");
        let carrier_t = arena.declare_uninterpreted_sort("TiBodyT");
        let sort_s = Sort::Uninterpreted(carrier_s);
        let sort_t = Sort::Uninterpreted(carrier_t);
        let image_fn = arena.declare_fun("tib_f", &[sort_s], sort_t).unwrap();
        let predicate = arena.declare_fun("tib_p", &[sort_t], Sort::Bool).unwrap();
        let skolem = arena.declare("tib_sk", sort_s).unwrap();

        let binder_x = arena.declare("tib_x", sort_s).unwrap();
        let xv = arena.var(binder_x);
        let f_x = arena.apply(image_fn, &[xv]).unwrap();
        let p_f_x = arena.apply(predicate, &[f_x]).unwrap();
        let all_imaged = arena.forall(binder_x, p_f_x).unwrap();

        // `∀y:T. ¬p(y) ∨ ¬(y = f(sk))` — unsat against the first universal at
        // y := f(sk); the constant `sk` occurs only here, under the binder.
        let binder_y = arena.declare("tib_y", sort_t).unwrap();
        let yv = arena.var(binder_y);
        let p_y = arena.apply(predicate, &[yv]).unwrap();
        let not_p_y = arena.not(p_y).unwrap();
        let sk = arena.var(skolem);
        let f_sk = arena.apply(image_fn, &[sk]).unwrap();
        let y_is_witness = arena.eq(yv, f_sk).unwrap();
        let y_not_witness = arena.not(y_is_witness).unwrap();
        let clause = arena.or(not_p_y, y_not_witness).unwrap();
        let none_witnessed = arena.forall(binder_y, clause).unwrap();

        let assertions = vec![all_imaged, none_witnessed];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        assert!(matches!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &config).unwrap(),
            CheckResult::Unsat
        ));
    }

    /// Soundness control: invention on a satisfiable query must never
    /// manufacture a refutation — the invented terms are nodes, not facts.
    #[test]
    fn term_invention_never_refutes_a_satisfiable_query() {
        let mut arena = TermArena::new();
        let carrier_s = arena.declare_uninterpreted_sort("TiSatS");
        let carrier_t = arena.declare_uninterpreted_sort("TiSatT");
        let sort_s = Sort::Uninterpreted(carrier_s);
        let sort_t = Sort::Uninterpreted(carrier_t);
        let image_fn = arena.declare_fun("tis_f", &[sort_s], sort_t).unwrap();
        let predicate = arena.declare_fun("tis_p", &[sort_t], Sort::Bool).unwrap();
        let control_pred = arena.declare_fun("tis_q", &[sort_s], Sort::Bool).unwrap();
        let left_const = arena.declare("tis_d", sort_s).unwrap();

        let binder_x = arena.declare("tis_x", sort_s).unwrap();
        let xv = arena.var(binder_x);
        let f_x = arena.apply(image_fn, &[xv]).unwrap();
        let p_f_x = arena.apply(predicate, &[f_x]).unwrap();
        let all_imaged = arena.forall(binder_x, p_f_x).unwrap();

        let dv = arena.var(left_const);
        let q_d = arena.apply(control_pred, &[dv]).unwrap();
        let ground = arena.not(q_d).unwrap();

        let assertions = vec![all_imaged, ground];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        assert!(!matches!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &config).unwrap(),
            CheckResult::Unsat
        ));
    }

    #[test]
    fn chained_integer_recurrence_reaches_its_ground_base() {
        let mut arena = TermArena::new();
        let function = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let twenty = arena.int_const(20);
        let minus_thousand = arena.int_const(-1000);

        let f_zero = arena.apply(function, &[zero]).unwrap();
        let base = arena.eq(f_zero, one).unwrap();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let positive = arena.int_gt(xv, zero).unwrap();
        let predecessor = arena.int_sub(xv, one).unwrap();
        let f_predecessor = arena.apply(function, &[predecessor]).unwrap();
        let recurrence_value = arena.int_mul(minus_thousand, f_predecessor).unwrap();
        let f_x = arena.apply(function, &[xv]).unwrap();
        let recurrence = arena.eq(f_x, recurrence_value).unwrap();
        let guarded = arena.implies(positive, recurrence).unwrap();
        let universal = arena.forall(x, guarded).unwrap();
        let f_twenty = arena.apply(function, &[twenty]).unwrap();
        let negative_twentieth = arena.int_lt(f_twenty, zero).unwrap();

        assert!(predecessor_recurrence_sign_refutation(
            &arena,
            &[base, negative_twentieth],
            universal,
        ));
        let positive_twentieth = arena.int_gt(f_twenty, zero).unwrap();
        assert!(
            !predecessor_recurrence_sign_refutation(&arena, &[base, positive_twentieth], universal,),
            "the expected positive sign is satisfiable and must not be refuted"
        );
        let nineteen = arena.int_const(19);
        let f_nineteen = arena.apply(function, &[nineteen]).unwrap();
        let negative_nineteenth = arena.int_lt(f_nineteen, zero).unwrap();
        assert!(
            !predecessor_recurrence_sign_refutation(
                &arena,
                &[base, negative_nineteenth],
                universal,
            ),
            "the expected negative sign at an odd index must remain satisfiable"
        );
        let sixty_five = arena.int_const(65);
        let f_sixty_five = arena.apply(function, &[sixty_five]).unwrap();
        let positive_sixty_fifth = arena.int_gt(f_sixty_five, zero).unwrap();
        assert!(
            !predecessor_recurrence_sign_refutation(
                &arena,
                &[base, positive_sixty_fifth],
                universal,
            ),
            "indices beyond the deterministic checker cap must decline"
        );
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[base, universal, negative_twentieth],
            &config,
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "twenty deterministic predecessor instances reach f(0) and refute the sign"
        );
    }

    #[test]
    fn expired_online_deadline_declines_before_encoding() {
        let mut arena = TermArena::new();
        let value = arena.int_var("expired_online_value").unwrap();
        let zero = arena.int_const(0);
        let equality = arena.eq(value, zero).unwrap();
        let deadline = Instant::now()
            .checked_sub(std::time::Duration::from_millis(1))
            .unwrap();

        assert!(OnlineQuantifierClauseSession::new(&arena, &[equality], Some(deadline)).is_none());
    }

    /// Builds `∀x. (= (f x) c)` and ground terms mentioning `f(a)`, `f(b)`.
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn setup() -> (
        TermArena,
        TermId,
        [TermId; 2],
        TermId,
        TermId,
        FuncId,
        SymbolId,
    ) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        // A ground assertion that contains f(a) and f(b).
        let sum = arena.bv_add(fa, fb).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        // Body referencing the bound variable: (= (f x) c).
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        (arena, forall, [a, b], c, ground0, f, x)
    }

    fn shared_match_stress(
        ground_terms: usize,
        quantifier_count: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let function = arena.declare_fun("shared_f", &[sort], sort).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(ground_terms);
        for index in 0..ground_terms {
            let argument = arena.bv_var(&format!("shared_a_{index}"), 16).unwrap();
            let application = arena.apply(function, &[argument]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
        }

        let mut foralls = Vec::with_capacity(quantifier_count);
        for index in 0..quantifier_count {
            let variable = arena.declare(&format!("shared_x_{index}"), sort).unwrap();
            let variable_term = arena.var(variable);
            let application = arena.apply(function, &[variable_term]).unwrap();
            let value = arena.bv_const(16, index as u128).unwrap();
            let body = arena.eq(application, value).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }
        (arena, ground, foralls)
    }

    fn unrelated_root_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut appended = None;

        for pattern_index in 0..pattern_count {
            let function = arena
                .declare_fun(&format!("queued_f_{pattern_index}"), &[sort], sort)
                .unwrap();
            for term_index in 0..=terms_per_pattern {
                let argument = arena
                    .bv_var(&format!("queued_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let application = arena.apply(function, &[argument]).unwrap();
                let equality = arena.eq(application, zero).unwrap();
                let disequality = arena.not(equality).unwrap();
                if pattern_index == 0 && term_index == terms_per_pattern {
                    appended = Some(disequality);
                } else if term_index < terms_per_pattern {
                    ground.push(disequality);
                }
            }

            let variable = arena
                .declare(&format!("queued_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let application = arena.apply(function, &[variable_term]).unwrap();
            let body = arena.eq(application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            appended.expect("the first root has one append-only term"),
        )
    }

    fn merge_root_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut merge_equality = None;

        for pattern_index in 0..pattern_count {
            let function = arena
                .declare_fun(&format!("merge_f_{pattern_index}"), &[sort, sort], sort)
                .unwrap();
            for term_index in 0..terms_per_pattern {
                let left = arena
                    .bv_var(&format!("merge_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let right = arena
                    .bv_var(&format!("merge_b_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let application = arena.apply(function, &[left, right]).unwrap();
                let equality = arena.eq(application, zero).unwrap();
                ground.push(arena.not(equality).unwrap());
                if pattern_index == 0 && term_index == 0 {
                    merge_equality = Some(arena.eq(left, right).unwrap());
                }
            }

            let variable = arena
                .declare(&format!("merge_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let application = arena
                .apply(function, &[variable_term, variable_term])
                .unwrap();
            let body = arena.eq(application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            merge_equality.expect("the first root has one merge equality"),
        )
    }

    fn shared_root_path_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let outer = arena.declare_fun("path_outer", &[sort], sort).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut merge_equality = None;

        for pattern_index in 0..pattern_count {
            let inner = arena
                .declare_fun(&format!("path_inner_{pattern_index}"), &[sort, sort], sort)
                .unwrap();
            for term_index in 0..terms_per_pattern {
                let left = arena
                    .bv_var(&format!("path_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let right = arena
                    .bv_var(&format!("path_b_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let inner_application = arena.apply(inner, &[left, right]).unwrap();
                let outer_application = arena.apply(outer, &[inner_application]).unwrap();
                let equality = arena.eq(outer_application, zero).unwrap();
                ground.push(arena.not(equality).unwrap());
                if pattern_index == 0 && term_index == 0 {
                    merge_equality = Some(arena.eq(left, right).unwrap());
                }
            }

            let variable = arena
                .declare(&format!("path_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let inner_application = arena.apply(inner, &[variable_term, variable_term]).unwrap();
            let outer_application = arena.apply(outer, &[inner_application]).unwrap();
            let body = arena.eq(outer_application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            merge_equality.expect("the first nested path has one merge equality"),
        )
    }

    fn path_filter_matrix_stress(
        label_count: usize,
        constant_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let outer = arena
            .declare_fun("filter_outer", &[sort, sort], sort)
            .unwrap();
        let constants: Vec<TermId> = (0..constant_count)
            .map(|index| arena.bv_var(&format!("filter_c_{index}"), 16).unwrap())
            .collect();
        let inner_functions: Vec<FuncId> = (0..label_count)
            .map(|index| {
                arena
                    .declare_fun(&format!("filter_inner_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();

        let pattern_count = label_count * constant_count;
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern + label_count);
        let mut merge_left = None;
        for label_index in 0..label_count {
            for (constant_index, &constant) in constants.iter().enumerate() {
                for term_index in 0..terms_per_pattern {
                    let argument = arena
                        .bv_var(
                            &format!("filter_b_{label_index}_{constant_index}_{term_index}"),
                            16,
                        )
                        .unwrap();
                    let application = arena.apply(outer, &[argument, constant]).unwrap();
                    let equality = arena.eq(application, zero).unwrap();
                    ground.push(arena.not(equality).unwrap());
                    if label_index == 0 && constant_index == 0 && term_index == 0 {
                        merge_left = Some(argument);
                    }
                }
            }
        }

        let mut merge_right = None;
        for (label_index, &inner) in inner_functions.iter().enumerate() {
            let argument = arena
                .bv_var(&format!("filter_anchor_{label_index}"), 16)
                .unwrap();
            let application = arena.apply(inner, &[argument]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
            if label_index == 0 {
                merge_right = Some(application);
            }
        }

        let mut foralls = Vec::with_capacity(pattern_count);
        for (label_index, &inner) in inner_functions.iter().enumerate() {
            for (constant_index, &constant) in constants.iter().enumerate() {
                let variable = arena
                    .declare(&format!("filter_x_{label_index}_{constant_index}"), sort)
                    .unwrap();
                let variable_term = arena.var(variable);
                let inner_application = arena.apply(inner, &[variable_term]).unwrap();
                let outer_application = arena.apply(outer, &[inner_application, constant]).unwrap();
                let body = arena.eq(outer_application, zero).unwrap();
                foralls.push(arena.forall(variable, body).unwrap());
            }
        }

        let merge_equality = arena
            .eq(
                merge_left.expect("matrix has one outer argument"),
                merge_right.expect("matrix has one nested anchor"),
            )
            .unwrap();
        (arena, ground, foralls, merge_equality)
    }

    fn generation_delta_stress(applications: usize) -> (TermArena, Vec<TermId>, TermId, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let constant = arena.bv_var("delta_constant", 16).unwrap();
        let inner = arena.declare_fun("delta_inner", &[sort], sort).unwrap();
        let outer = arena
            .declare_fun("delta_outer", &[sort, sort], sort)
            .unwrap();

        let mut ground = Vec::with_capacity(applications + 1);
        let mut merge_left = None;
        for index in 0..applications {
            let argument = arena
                .bv_var(&format!("delta_argument_{index}"), 16)
                .unwrap();
            let application = arena.apply(outer, &[argument, constant]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
            if index == 0 {
                merge_left = Some(argument);
            }
        }
        let anchor = arena.bv_var("delta_anchor", 16).unwrap();
        let inner_anchor = arena.apply(inner, &[anchor]).unwrap();
        let inner_equality = arena.eq(inner_anchor, zero).unwrap();
        ground.push(arena.not(inner_equality).unwrap());

        let variable = arena.declare("delta_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let inner_application = arena.apply(inner, &[variable_term]).unwrap();
        let outer_application = arena.apply(outer, &[inner_application, constant]).unwrap();
        let body = arena.eq(outer_application, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();
        let merge_equality = arena
            .eq(
                merge_left.expect("stress target has one outer argument"),
                inner_anchor,
            )
            .unwrap();
        (arena, ground, forall, merge_equality)
    }

    #[test]
    fn shared_session_interns_patterns_and_matches_complete_legacy_tuples() {
        const GROUND_TERMS: usize = 256;
        const QUANTIFIERS: usize = 32;

        let (mut legacy_arena, legacy_ground, legacy_foralls) =
            shared_match_stress(GROUND_TERMS, QUANTIFIERS);
        let legacy_started = Instant::now();
        let legacy_tuples: Vec<Vec<Vec<TermId>>> = legacy_foralls
            .iter()
            .map(|&quantifier| {
                witness_tuples_via_egraph(&mut legacy_arena, &legacy_ground, quantifier)
                    .expect("every shared pattern matches")
                    .2
            })
            .collect();
        let legacy_elapsed = legacy_started.elapsed();
        assert!(
            legacy_tuples
                .iter()
                .all(|tuples| tuples.len() == GROUND_TERMS)
        );

        let (mut shared_arena, shared_ground, shared_foralls) =
            shared_match_stress(GROUND_TERMS, QUANTIFIERS);
        let shared_started = Instant::now();
        let mut session = IncrementalEmatchSession::new(&mut shared_arena, &shared_foralls);
        assert_eq!(
            session.patterns.len(),
            1,
            "identical triggers across quantifiers must share one compiled pattern"
        );
        session.extend_ground(&shared_arena, &shared_ground);
        let shared_tuples: Vec<Vec<Vec<TermId>>> = session
            .match_witness_tuples(None)
            .into_iter()
            .map(|tuples| tuples.expect("every shared pattern matches"))
            .collect();
        let shared_elapsed = shared_started.elapsed();

        assert_eq!(shared_tuples, legacy_tuples);
        assert_eq!(session.extensions, 1);
        assert_eq!(session.match_rounds, 1);
        assert_eq!(session.processed_ground.len(), GROUND_TERMS);
        eprintln!(
            "shared MAM target: ground_terms={GROUND_TERMS} quantifiers={QUANTIFIERS} unique_patterns=1 legacy_match_us={} shared_match_us={}",
            legacy_elapsed.as_micros(),
            shared_elapsed.as_micros()
        );
    }

    #[test]
    fn internal_session_declines_tuple_join_above_ground_budget() {
        let matches = MAX_JOINED_SUBSTITUTIONS_PER_ROUND + 1;
        let (mut arena, ground, foralls) = shared_match_stress(matches, 1);
        assert_eq!(
            witness_tuples_via_egraph(&mut arena, &ground, foralls[0])
                .expect("the public complete matcher must still return its witnesses")
                .2
                .len(),
            matches
        );

        let mut session = IncrementalEmatchSession::new(&mut arena, &foralls);
        session.extend_ground(&arena, &ground);
        assert_eq!(session.match_witness_tuples(None), vec![None]);
    }

    #[test]
    fn add_only_candidate_queue_matches_full_rebuild_and_executes_one_root() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, appended) =
            unrelated_root_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut queued = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut full = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(queued.patterns.len(), PATTERNS);
        assert_eq!(full.patterns, queued.patterns);

        queued.extend_ground(&arena, &ground);
        full.extend_ground(&arena, &ground);
        assert_eq!(
            queued.match_witness_tuples(None),
            full.match_witness_tuples(None)
        );
        assert_eq!(queued.pattern_executions, PATTERNS);

        let mut extended_ground = ground;
        extended_ground.push(appended);
        queued.extend_ground(&arena, &extended_ground);
        full.extend_ground(&arena, &extended_ground);

        let queued_before = queued.pattern_executions;
        let queued_candidates_before = queued.candidate_applications_scanned;
        let queued_started = Instant::now();
        let queued_tuples = queued.match_witness_tuples(None);
        let queued_elapsed = queued_started.elapsed();
        assert_eq!(queued.pattern_executions - queued_before, 1);
        assert_eq!(
            queued.candidate_applications_scanned - queued_candidates_before,
            1
        );
        assert_eq!(queued.dirty_patterns.len(), 0);

        // Recreate ADR-0111's complete per-round index construction and pattern
        // execution while retaining the same bridge and complete tuple join.
        full.match_index = full.bridge.egraph.new_match_index();
        full.dirty_patterns.extend(0..full.patterns.len());
        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        let full_tuples = full.match_witness_tuples(None);
        let full_elapsed = full_started.elapsed();

        assert_eq!(full.pattern_executions - full_before, PATTERNS);
        assert_eq!(queued_tuples, full_tuples);
        assert!(queued_tuples.iter().all(Option::is_some));
        assert_eq!(
            queued_tuples[0].as_ref().unwrap().len(),
            TERMS_PER_PATTERN + 1
        );
        assert!(
            queued_tuples[1..]
                .iter()
                .all(|tuples| tuples.as_ref().unwrap().len() == TERMS_PER_PATTERN)
        );
        eprintln!(
            "candidate queue target: patterns={PATTERNS} retained_terms={} appended_roots=1 full_rematch_us={} queued_update_us={} full_pattern_executions={PATTERNS} queued_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            full_elapsed.as_micros(),
            queued_elapsed.as_micros()
        );
    }

    #[test]
    fn merge_candidate_queue_matches_full_rebuild_and_executes_one_root() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, merge_equality) =
            merge_root_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut queued = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut full = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(queued.patterns.len(), PATTERNS);
        assert_eq!(full.patterns, queued.patterns);

        queued.extend_ground(&arena, &ground);
        full.extend_ground(&arena, &ground);
        assert_eq!(
            queued.match_witness_tuples(None),
            full.match_witness_tuples(None)
        );
        assert_eq!(queued.pattern_executions, PATTERNS);

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);
        let queued_before = queued.pattern_executions;
        let queued_candidates_before = queued.candidate_applications_scanned;
        let queued_started = Instant::now();
        queued.extend_ground(&arena, &extended_ground);
        let queued_tuples = queued.match_witness_tuples(None);
        let queued_elapsed = queued_started.elapsed();
        assert_eq!(queued.merge_invalidations, 1);
        assert_eq!(queued.merge_affected_patterns, 1);
        assert_eq!(queued.pattern_executions - queued_before, 1);
        assert_eq!(
            queued.candidate_applications_scanned - queued_candidates_before,
            1
        );

        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        full.extend_ground_with_full_merge_invalidation(&arena, &extended_ground);
        // ADR-0112 rebuilt its root-keyed index after every merge.
        full.match_index = full.bridge.egraph.new_match_index();
        let full_tuples = full.match_witness_tuples(None);
        let full_elapsed = full_started.elapsed();

        assert_eq!(full.pattern_executions - full_before, PATTERNS);
        assert_eq!(queued_tuples, full_tuples);
        assert_eq!(queued_tuples[0].as_ref().unwrap().len(), 1);
        assert!(queued_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "merge queue target: patterns={PATTERNS} retained_terms={} affected_roots=1 full_round_us={} queued_round_us={} full_pattern_executions={PATTERNS} queued_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            full_elapsed.as_micros(),
            queued_elapsed.as_micros()
        );
    }

    #[test]
    fn compiled_parent_paths_beat_shared_root_declaration_invalidation() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, merge_equality) =
            shared_root_path_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut exact = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut declarations = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(exact.patterns.len(), PATTERNS);
        assert_eq!(declarations.patterns, exact.patterns);
        let root_declarations: BTreeSet<u32> = exact
            .patterns
            .iter()
            .filter_map(|pattern| match pattern {
                Pattern::App(declaration, _) => Some(*declaration),
                Pattern::Var(_) => None,
            })
            .collect();
        assert_eq!(root_declarations.len(), 1, "every trigger shares one root");

        exact.extend_ground(&arena, &ground);
        declarations.extend_ground(&arena, &ground);
        assert_eq!(
            exact.match_witness_tuples(None),
            declarations.match_witness_tuples(None)
        );

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);
        let exact_before = exact.pattern_executions;
        let exact_started = Instant::now();
        exact.extend_ground(&arena, &extended_ground);
        let exact_tuples = exact.match_witness_tuples(None);
        let exact_elapsed = exact_started.elapsed();

        let declaration_before = declarations.pattern_executions;
        let declaration_started = Instant::now();
        declarations.extend_ground_with_declaration_merge_invalidation(&arena, &extended_ground);
        let declaration_tuples = declarations.match_witness_tuples(None);
        let declaration_elapsed = declaration_started.elapsed();

        assert_eq!(exact.pattern_executions - exact_before, 1);
        assert_eq!(
            declarations.pattern_executions - declaration_before,
            PATTERNS
        );
        assert_eq!(exact.merge_affected_patterns, 1);
        assert_eq!(declarations.merge_affected_patterns, PATTERNS);
        assert_eq!(exact_tuples, declaration_tuples);
        assert_eq!(exact_tuples[0].as_ref().unwrap().len(), 1);
        assert!(exact_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "parent path target: patterns={PATTERNS} shared_roots=1 retained_terms={} affected_paths=1 declaration_round_us={} exact_path_round_us={} declaration_pattern_executions={PATTERNS} exact_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            declaration_elapsed.as_micros(),
            exact_elapsed.as_micros()
        );
    }

    #[test]
    fn compiled_parent_paths_distinguish_declarations_and_terminate_on_cycles() {
        let pattern_g = Pattern::App(30, vec![Pattern::App(20, vec![Pattern::Var(0)])]);
        let pattern_h = Pattern::App(30, vec![Pattern::App(21, vec![Pattern::Var(0)])]);
        let cyclic = Pattern::App(40, vec![Pattern::App(40, vec![Pattern::Var(0)])]);
        let mut paths = PatternPathIndex::default();
        paths.add_pattern(&pattern_g, 0);
        paths.add_pattern(&pattern_h, 1);
        paths.add_pattern(&cyclic, 2);
        paths.add_pattern(&pattern_g, 0);
        paths.finish();

        let mut egraph = EGraph::new();
        let left = egraph.add(0, &[]);
        let right = egraph.add(1, &[]);
        let unrelated = egraph.add(2, &[]);
        let g_left = egraph.add(20, &[left]);
        egraph.add(20, &[right]);
        egraph.add(30, &[g_left]);
        let h_unrelated = egraph.add(21, &[unrelated]);
        egraph.add(30, &[h_unrelated]);
        egraph.merge(left, right, 1);
        assert_eq!(paths.affected_patterns(&egraph, &[left, right]), [0].into());

        let recursive = egraph.add(40, &[unrelated]);
        egraph.merge(unrelated, recursive, 2);
        assert_eq!(
            paths.affected_patterns(&egraph, &[unrelated]),
            [1, 2].into()
        );
    }

    #[test]
    fn compiled_parent_paths_distinguish_argument_positions_after_shared_prefix() {
        let left_path = Pattern::App(
            30,
            vec![Pattern::App(20, vec![Pattern::Var(0)]), Pattern::Var(1)],
        );
        let right_path = Pattern::App(
            30,
            vec![Pattern::Var(1), Pattern::App(20, vec![Pattern::Var(0)])],
        );
        let mut paths = PatternPathIndex::default();
        paths.add_pattern(&left_path, 0);
        paths.add_pattern(&right_path, 1);
        paths.finish();

        let mut egraph = EGraph::new();
        let left = egraph.add(0, &[]);
        let right = egraph.add(1, &[]);
        let other = egraph.add(2, &[]);
        let g_left = egraph.add(20, &[left]);
        egraph.add(20, &[right]);
        egraph.add(30, &[g_left, other]);
        egraph.merge(left, right, 1);

        assert_eq!(paths.affected_patterns(&egraph, &[left, right]), [0].into());
    }

    #[test]
    fn class_and_ground_filters_reduce_same_shape_path_terminals_independently() {
        const LABELS: usize = 8;
        const CONSTANTS: usize = 8;
        const TERMS_PER_PATTERN: usize = 64;
        const PATTERNS: usize = LABELS * CONSTANTS;

        let (mut arena, ground, foralls, merge_equality) =
            path_filter_matrix_stress(LABELS, CONSTANTS, TERMS_PER_PATTERN);
        let mut unfiltered = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut class_only = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut ground_only = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut combined = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(combined.patterns.len(), PATTERNS);

        for session in [
            &mut unfiltered,
            &mut class_only,
            &mut ground_only,
            &mut combined,
        ] {
            session.extend_ground(&arena, &ground);
            assert!(
                session
                    .match_witness_tuples(None)
                    .into_iter()
                    .all(|tuples| tuples.is_none())
            );
        }

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);

        let unfiltered_before = unfiltered.pattern_executions;
        let unfiltered_started = Instant::now();
        unfiltered.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::Unfiltered,
        );
        let unfiltered_tuples = unfiltered.match_witness_tuples(None);
        let unfiltered_elapsed = unfiltered_started.elapsed();

        let class_before = class_only.pattern_executions;
        let class_started = Instant::now();
        class_only.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::ClassOnly,
        );
        let class_tuples = class_only.match_witness_tuples(None);
        let class_elapsed = class_started.elapsed();

        let ground_before = ground_only.pattern_executions;
        let ground_started = Instant::now();
        ground_only.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::GroundOnly,
        );
        let ground_tuples = ground_only.match_witness_tuples(None);
        let ground_elapsed = ground_started.elapsed();

        let combined_before = combined.pattern_executions;
        let combined_started = Instant::now();
        combined.extend_ground(&arena, &extended_ground);
        let combined_tuples = combined.match_witness_tuples(None);
        let combined_elapsed = combined_started.elapsed();

        assert_eq!(unfiltered.pattern_executions - unfiltered_before, PATTERNS);
        assert_eq!(class_only.pattern_executions - class_before, CONSTANTS);
        assert_eq!(ground_only.pattern_executions - ground_before, LABELS);
        assert_eq!(combined.pattern_executions - combined_before, 1);
        assert_eq!(unfiltered.merge_affected_patterns, PATTERNS);
        assert_eq!(class_only.merge_affected_patterns, CONSTANTS);
        assert_eq!(ground_only.merge_affected_patterns, LABELS);
        assert_eq!(combined.merge_affected_patterns, 1);
        assert_eq!(combined_tuples, unfiltered_tuples);
        assert_eq!(combined_tuples, class_tuples);
        assert_eq!(combined_tuples, ground_tuples);
        assert_eq!(combined_tuples[0].as_ref().unwrap().len(), 1);
        assert!(combined_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "path filter target: patterns={PATTERNS} labels={LABELS} constants={CONSTANTS} retained_terms={} affected_unfiltered={PATTERNS} affected_class={CONSTANTS} affected_ground={LABELS} affected_combined=1 unfiltered_round_us={} class_round_us={} ground_round_us={} combined_round_us={}",
            PATTERNS * TERMS_PER_PATTERN + LABELS,
            unfiltered_elapsed.as_micros(),
            class_elapsed.as_micros(),
            ground_elapsed.as_micros(),
            combined_elapsed.as_micros()
        );
    }

    #[test]
    fn generation_delta_candidates_avoid_full_affected_pattern_rescan() {
        const APPLICATIONS: usize = 4096;

        let (mut arena, ground, forall, merge_equality) = generation_delta_stress(APPLICATIONS);
        let mut full = IncrementalEmatchSession::new(&mut arena, &[forall]);
        let mut delta = IncrementalEmatchSession::new(&mut arena, &[forall]);
        full.extend_ground(&arena, &ground);
        delta.extend_ground(&arena, &ground);
        assert_eq!(
            full.match_witness_tuples(None),
            delta.match_witness_tuples(None)
        );

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);

        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        full.extend_ground_with_full_pattern_path_invalidation(&arena, &extended_ground);
        let full_tuples = full.match_witness_tuples(None);
        let full_elapsed = full_started.elapsed();

        let delta_before = delta.pattern_executions;
        let candidate_before = delta.candidate_applications_scanned;
        let delta_started = Instant::now();
        delta.extend_ground(&arena, &extended_ground);
        let delta_tuples = delta.match_witness_tuples(None);
        let delta_elapsed = delta_started.elapsed();

        assert_eq!(full_tuples, delta_tuples);
        assert_eq!(full.pattern_executions - full_before, 1);
        assert_eq!(delta.pattern_executions - delta_before, 1);
        assert_eq!(delta.candidate_applications_scanned - candidate_before, 1);
        assert_eq!(delta_tuples[0].as_ref().unwrap().len(), 1);
        eprintln!(
            "generation delta target: retained_outer_apps={APPLICATIONS} full_pattern_executions=1 delta_pattern_executions=1 full_top_applications_scanned={APPLICATIONS} delta_top_applications_scanned=1 full_round_us={} delta_round_us={}",
            full_elapsed.as_micros(),
            delta_elapsed.as_micros()
        );
    }

    #[test]
    fn selective_merge_queue_enables_nested_trigger_match() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let argument = arena.bv_var("nested_merge_a", 8).unwrap();
        let outer_argument = arena.bv_var("nested_merge_b", 8).unwrap();
        let inner_function = arena.declare_fun("nested_merge_g", &[sort], sort).unwrap();
        let outer_function = arena.declare_fun("nested_merge_f", &[sort], sort).unwrap();
        let ga = arena.apply(inner_function, &[argument]).unwrap();
        let fb = arena.apply(outer_function, &[outer_argument]).unwrap();
        let ga_eq_zero = arena.eq(ga, zero).unwrap();
        let fb_eq_zero = arena.eq(fb, zero).unwrap();
        let mut ground = vec![
            arena.not(ga_eq_zero).unwrap(),
            arena.not(fb_eq_zero).unwrap(),
        ];

        let variable = arena.declare("nested_merge_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let gx = arena.apply(inner_function, &[variable_term]).unwrap();
        let fgx = arena.apply(outer_function, &[gx]).unwrap();
        let body = arena.eq(fgx, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        assert_eq!(session.match_witness_tuples(None), vec![None]);
        ground.push(arena.eq(outer_argument, ga).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 1);
        assert_eq!(session.candidate_patterns.values().next().unwrap().len(), 1);
        assert_eq!(session.merge_affected_patterns, 1);
        let tuples = session.match_witness_tuples(None);
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("the merge enables the nested trigger")
            .2;
        assert_eq!(tuples, vec![Some(fresh)]);
    }

    #[test]
    fn selective_merge_queue_enables_ground_subpattern_match() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let argument = arena.bv_var("ground_merge_a", 8).unwrap();
        let pattern_constant = arena.bv_var("ground_merge_c", 8).unwrap();
        let ground_constant = arena.bv_var("ground_merge_d", 8).unwrap();
        let function = arena
            .declare_fun("ground_merge_h", &[sort, sort], sort)
            .unwrap();
        let had = arena.apply(function, &[argument, ground_constant]).unwrap();
        let had_eq_zero = arena.eq(had, zero).unwrap();
        let mut ground = vec![arena.not(had_eq_zero).unwrap()];

        let variable = arena.declare("ground_merge_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let hxc = arena
            .apply(function, &[variable_term, pattern_constant])
            .unwrap();
        let body = arena.eq(hxc, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        assert_eq!(session.match_witness_tuples(None), vec![None]);
        ground.push(arena.eq(pattern_constant, ground_constant).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 1);
        assert_eq!(session.candidate_patterns.values().next().unwrap().len(), 1);
        let tuples = session.match_witness_tuples(None);
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("the merge enables the ground subpattern")
            .2;
        assert_eq!(tuples, vec![Some(fresh)]);
    }

    #[test]
    fn add_and_merge_round_dirties_the_union_of_affected_roots() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let merge_left = arena.bv_var("union_round_a", 8).unwrap();
        let merge_right = arena.bv_var("union_round_b", 8).unwrap();
        let added_argument = arena.bv_var("union_round_c", 8).unwrap();
        let merge_function = arena
            .declare_fun("union_round_f", &[sort, sort], sort)
            .unwrap();
        let added_function = arena.declare_fun("union_round_u", &[sort], sort).unwrap();
        let fab = arena
            .apply(merge_function, &[merge_left, merge_right])
            .unwrap();
        let fab_eq_zero = arena.eq(fab, zero).unwrap();
        let mut ground = vec![arena.not(fab_eq_zero).unwrap()];

        let variable = arena.declare("union_round_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let fxx = arena
            .apply(merge_function, &[variable_term, variable_term])
            .unwrap();
        let fbody = arena.eq(fxx, zero).unwrap();
        let forall_f = arena.forall(variable, fbody).unwrap();
        let ux = arena.apply(added_function, &[variable_term]).unwrap();
        let ubody = arena.eq(ux, zero).unwrap();
        let forall_u = arena.forall(variable, ubody).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall_f, forall_u]);
        session.extend_ground(&arena, &ground);
        session.match_witness_tuples(None);

        let uc = arena.apply(added_function, &[added_argument]).unwrap();
        let uc_eq_zero = arena.eq(uc, zero).unwrap();
        ground.push(arena.not(uc_eq_zero).unwrap());
        ground.push(arena.eq(merge_left, merge_right).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 2);
        assert!(
            session
                .candidate_patterns
                .values()
                .all(|candidates| candidates.len() == 1)
        );
        assert_eq!(session.merge_affected_patterns, 1);
        let tuples = session.match_witness_tuples(None);
        assert_eq!(tuples[0].as_ref().unwrap().len(), 1);
        assert_eq!(tuples[1].as_ref().unwrap().len(), 1);
    }

    #[test]
    fn retained_substitution_join_uses_current_eclass_roots() {
        let mut egraph = EGraph::new();
        let a = egraph.add(0, &[]);
        let b = egraph.add(1, &[]);
        let left = vec![Some(a)];
        let right = vec![Some(b)];
        assert!(merge_substitutions(&left, &right).is_none());

        egraph.merge(a, b, 1);
        assert_eq!(
            merge_substitutions_modulo(&egraph, &left, &right),
            Some(vec![Some(egraph.root(a))])
        );
    }

    #[test]
    fn equal_top_applications_preserve_cached_distinct_bindings_without_rematch() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let left = arena.bv_var("equal_apps_left", 8).unwrap();
        let right = arena.bv_var("equal_apps_right", 8).unwrap();
        let function = arena.declare_fun("equal_apps_f", &[sort], sort).unwrap();
        let left_app = arena.apply(function, &[left]).unwrap();
        let right_app = arena.apply(function, &[right]).unwrap();
        let left_eq_zero = arena.eq(left_app, zero).unwrap();
        let right_eq_zero = arena.eq(right_app, zero).unwrap();
        let mut ground = vec![
            arena.not(left_eq_zero).unwrap(),
            arena.not(right_eq_zero).unwrap(),
        ];

        let variable = arena.declare("equal_apps_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let pattern_app = arena.apply(function, &[variable_term]).unwrap();
        let body = arena.eq(pattern_app, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let before = session.match_witness_tuples(None);
        assert_eq!(before[0].as_ref().unwrap().len(), 2);
        let executions = session.pattern_executions;

        ground.push(arena.eq(left_app, right_app).unwrap());
        session.extend_ground(&arena, &ground);
        assert!(session.dirty_patterns.is_empty());
        let cached = session.match_witness_tuples(None);
        assert_eq!(session.pattern_executions, executions);
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("both unequal arguments remain valid trigger bindings")
            .2;
        assert_eq!(cached, vec![Some(fresh)]);
        assert_eq!(cached[0].as_ref().unwrap().len(), 2);
    }

    #[test]
    fn lazy_clause_batch_prioritizes_one_conflict_among_256_matches() {
        const MATCHES: usize = 256;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let one = arena.bv_const(16, 1).unwrap();
        let mut ground = Vec::with_capacity(MATCHES * 2);
        let mut conflict_instance = None;
        for i in 0..MATCHES {
            let a = arena.bv_var(&format!("a{i}"), 16).unwrap();
            let fa = arena.apply(f, &[a]).unwrap();
            let ga = arena.apply(g, &[a]).unwrap();
            let fa_eq_zero = arena.eq(fa, zero).unwrap();
            ground.push(arena.not(fa_eq_zero).unwrap());
            let ga_eq_one = arena.eq(ga, one).unwrap();
            if i + 1 == MATCHES {
                ground.push(arena.not(ga_eq_one).unwrap());
                conflict_instance = Some(arena.or(fa_eq_zero, ga_eq_one).unwrap());
            } else {
                ground.push(ga_eq_one);
            }
        }

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let gx_eq_one = arena.eq(gx, one).unwrap();
        let body = arena.or(fx_eq_zero, gx_eq_one).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let eager_total_started = Instant::now();
        let eager = instantiate_forall_via_egraph(&mut arena, &ground, forall);
        assert_eq!(eager.len(), MATCHES, "every distinct f(a_i) must match");
        let mut eager_replay = ground.clone();
        eager_replay.extend(eager.iter().copied());
        let eager_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &eager_replay, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let eager_elapsed = eager_started.elapsed();
        let eager_total_elapsed = eager_total_started.elapsed();

        let lazy_total_started = Instant::now();
        let batch = lazy_clause_instances(&mut arena, &ground, forall);
        assert_eq!(batch.redundant, MATCHES - 1);
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.urgent, vec![conflict_instance.unwrap()]);
        assert!(
            eager.contains(&batch.urgent[0]),
            "the scheduler must retain a genuine complete source instance"
        );
        let mut retained = IncrementalEmatchSession::new(&mut arena, &[forall]);
        retained.extend_ground(&arena, &ground);
        let retained_batch = retained.lazy_clause_batches(&mut arena, None).remove(0);
        assert_eq!(retained_batch.redundant, batch.redundant);
        assert_eq!(retained_batch.urgent, batch.urgent);
        assert_eq!(retained_batch.deferred, batch.deferred);

        let mut replay = ground.clone();
        replay.extend(batch.urgent);
        let lazy_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &replay, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the original ground context plus the selected source instance refutes"
        );
        let lazy_elapsed = lazy_started.elapsed();
        let lazy_total_elapsed = lazy_total_started.elapsed();
        eprintln!(
            "lazy quantifier clause target: eager_instances={MATCHES} eager_qf_us={} eager_total_us={} lazy_instances=1 lazy_qf_us={} lazy_total_us={}",
            eager_elapsed.as_micros(),
            eager_total_elapsed.as_micros(),
            lazy_elapsed.as_micros(),
            lazy_total_elapsed.as_micros()
        );
        let mut assertions = ground;
        assertions.push(forall);
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(
        clippy::many_single_char_names,
        clippy::similar_names,
        clippy::too_many_lines
    )]
    fn detached_clause_certificate_replays_and_rejects_tampering() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("detach_a", 8).unwrap();
        let b = arena.bv_var("detach_b", 8).unwrap();
        let f = arena.declare_fun("detach_f", &[sort], sort).unwrap();
        let h = arena.declare_fun("detach_h", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();

        let x = arena.declare("detach_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let false_sibling = arena.not(fx_eq_zero).unwrap();
        let propagated = arena.eq(hx, one).unwrap();
        let body = arena.or(false_sibling, propagated).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let ground = vec![fa_eq_zero, ha_ne_zero];
        let assertions = vec![fa_eq_zero, ha_ne_zero, forall];

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena, None).remove(0);
        assert!(batch.urgent.is_empty());
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.propagations.len(), 1);
        let certificate = batch.propagations[0].clone();
        assert_eq!(certificate.bindings, vec![a]);
        assert_eq!(certificate.false_siblings.len(), 1);
        assert_eq!(certificate.false_siblings[0].reasons, vec![fa_eq_zero]);
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &certificate
        ));

        let wrong_var = arena.declare("detach_wrong_x", sort).unwrap();
        let wrong_forall = arena.forall(wrong_var, body).unwrap();
        let mut tampered = certificate.clone();
        tampered.assertion = wrong_forall;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.bindings[0] = b;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.source_instance = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.propagated_literal = certificate.false_siblings[0].literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].literal = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered
            .false_siblings
            .push(certificate.false_siblings[0].clone());
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons.clear();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons = vec![ha_ne_zero];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let generated_reason = arena.eq(a, a).unwrap();
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons = vec![generated_reason];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate;
        tampered.false_siblings[0].reasons = vec![fa_eq_zero, fa_eq_zero];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn detached_clause_reasons_cover_congruence_and_transported_disequality() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let a = arena.bv_var("detach_transport_a", 8).unwrap();
        let b = arena.bv_var("detach_transport_b", 8).unwrap();
        let f = arena
            .declare_fun("detach_transport_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("detach_transport_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let fa_ne_zero = arena.not(fa_eq_zero).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let fb_eq_two = arena.eq(fb, two).unwrap();
        let fb_ne_two = arena.not(fb_eq_two).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();
        let ground = vec![fa_ne_zero, a_eq_b, fb_ne_two, ha_ne_zero];

        let x = arena.declare("detach_transport_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let positive_false = arena.eq(fx, two).unwrap();
        let hx_eq_one = arena.eq(hx, one).unwrap();
        let body = arena.or(positive_false, hx_eq_one).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let mut assertions = ground.clone();
        assertions.push(forall);

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena, None).remove(0);
        assert_eq!(batch.propagations.len(), 1);
        let certificate = &batch.propagations[0];
        assert!(certificate.false_siblings[0].reasons.contains(&a_eq_b));
        assert!(certificate.false_siblings[0].reasons.contains(&fb_ne_two));
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            certificate
        ));

        let fx_eq_fb = arena.eq(fx, fb).unwrap();
        let negative_false = arena.not(fx_eq_fb).unwrap();
        let body = arena.or(negative_false, hx_eq_one).unwrap();
        let congruent_forall = arena.forall(x, body).unwrap();
        let mut congruent_assertions = ground.clone();
        congruent_assertions.push(congruent_forall);
        let mut congruent = IncrementalEmatchSession::new(&mut arena, &[congruent_forall]);
        congruent.extend_ground(&arena, &ground);
        let batch = congruent.lazy_clause_batches(&mut arena, None).remove(0);
        assert_eq!(batch.propagations.len(), 1);
        assert_eq!(
            batch.propagations[0].false_siblings[0].reasons,
            vec![a_eq_b]
        );
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &congruent_assertions,
            &batch.propagations[0]
        ));
    }

    #[test]
    fn detached_clause_checker_accepts_reflexive_and_false_constant_siblings() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("detach_reflexive_a", 8).unwrap();
        let f = arena
            .declare_fun("detach_reflexive_f", &[sort], sort)
            .unwrap();
        let x = arena.declare("detach_reflexive_x", sort).unwrap();
        let xv = arena.var(x);
        let reflexive = arena.eq(xv, xv).unwrap();
        let false_reflexive = arena.not(reflexive).unwrap();
        let fx = arena.apply(f, &[xv]).unwrap();
        let target = arena.eq(fx, zero).unwrap();
        let body = arena.or(false_reflexive, target).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let a_eq_a = arena.eq(a, a).unwrap();
        let false_a_eq_a = arena.not(a_eq_a).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let propagated = arena.eq(fa, zero).unwrap();
        let source_instance = arena.or(false_a_eq_a, propagated).unwrap();
        let certificate = QuantifierClausePropagationCertificate {
            assertion: forall,
            bindings: vec![a],
            source_instance,
            propagated_literal: propagated,
            false_siblings: vec![QuantifierFalseSiblingJustification {
                literal: false_a_eq_a,
                reasons: Vec::new(),
            }],
            derived_reasons: Vec::new(),
        };
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &[forall],
            &certificate
        ));

        let false_term = arena.bool_const(false);
        let body = arena.or(false_term, target).unwrap();
        let forall_false = arena.forall(x, body).unwrap();
        let source_instance = arena.or(false_term, propagated).unwrap();
        let false_certificate = QuantifierClausePropagationCertificate {
            assertion: forall_false,
            bindings: vec![a],
            source_instance,
            propagated_literal: propagated,
            false_siblings: vec![QuantifierFalseSiblingJustification {
                literal: false_term,
                reasons: Vec::new(),
            }],
            derived_reasons: Vec::new(),
        };
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &[forall_false],
            &false_certificate
        ));
    }

    #[test]
    fn generated_equality_reason_falls_back_to_complete_source_instance() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("detach_generated_a", 8).unwrap();
        let f = arena
            .declare_fun("detach_generated_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("detach_generated_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let fa_ne_zero = arena.not(fa_eq_zero).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();
        let mut ground = vec![fa_ne_zero, ha_ne_zero];

        let x = arena.declare("detach_generated_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_body = arena.eq(fx, one).unwrap();
        let generator = arena.forall(x, generated_body).unwrap();
        let false_sibling = arena.not(generated_body).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let consumer_body = arena.or(false_sibling, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[generator, consumer]);
        session.extend_ground(&arena, &ground);
        let first = session.lazy_clause_batches(&mut arena, None);
        assert_eq!(first[0].units.len(), 1);
        assert!(first[1].propagations.is_empty());
        assert_eq!(first[1].deferred.len(), 1);
        ground.push(first[0].units[0]);

        session.extend_ground(&arena, &ground);
        let second = session.lazy_clause_batches(&mut arena, None);
        assert!(second[1].propagations.is_empty());
        assert_eq!(second[1].units.len(), 1);
        let fa_eq_one = arena.eq(fa, one).unwrap();
        let fa_ne_one = arena.not(fa_eq_one).unwrap();
        let ha_eq_one = arena.eq(ha, one).unwrap();
        let expected = arena.or(fa_ne_one, ha_eq_one).unwrap();
        assert_eq!(second[1].units[0], expected);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn exact_instance_provenance_justifies_later_detached_literal() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("instance_provenance_a", 8).unwrap();
        let f = arena
            .declare_fun("instance_provenance_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("instance_provenance_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let source_f_disequality = arena.not(fa_eq_zero).unwrap();
        let ha_eq_one = arena.eq(ha, one).unwrap();
        let p = arena.bool_var("instance_provenance_p").unwrap();
        let not_ha_eq_one = arena.not(ha_eq_one).unwrap();
        let target_implies_p = arena.or(not_ha_eq_one, p).unwrap();
        let not_p = arena.not(p).unwrap();

        let x = arena.declare("instance_provenance_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_body = arena.eq(fx, one).unwrap();
        let generator = arena.forall(x, generated_body).unwrap();
        let false_sibling = arena.not(generated_body).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let consumer_body = arena.or(false_sibling, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();
        let assertions = vec![
            source_f_disequality,
            target_implies_p,
            not_p,
            generator,
            consumer,
        ];

        let source_ground = vec![source_f_disequality, target_implies_p, not_p];
        let mut ground = source_ground.clone();
        let mut session = IncrementalEmatchSession::new(&mut arena, &[generator, consumer]);
        let derivations = HashMap::new();
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let first = session.lazy_clause_batches(&mut arena, None);
        let instance = first[0].units[0];
        let instance_certificate = first[0].instance_certificates[&instance].clone();
        assert_eq!(
            instance_certificate,
            QuantifierInstanceCertificate {
                assertion: generator,
                bindings: vec![a],
                instance,
            }
        );

        ground.push(instance);
        let mut derivations = HashMap::new();
        derivations.insert(
            instance,
            QuantifierGroundDerivation::Instance(instance_certificate.clone()),
        );
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let second = session.lazy_clause_batches(&mut arena, None);
        assert_eq!(second[1].propagations.len(), 1);
        let propagation = &second[1].propagations[0];
        assert_eq!(
            propagation.derived_reasons,
            vec![QuantifierGroundDerivation::Instance(
                instance_certificate.clone()
            )]
        );
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            propagation
        ));

        let mut online = OnlineQuantifierClauseSession::new(&arena, &source_ground, None).unwrap();
        assert_eq!(
            online.add_checked_batch(&mut arena, &assertions, &[instance], &derivations),
            Some(CdcltOutcome::Sat)
        );
        let propagated = propagation.propagated_literal;
        let propagation_derivation =
            QuantifierGroundDerivation::Propagation(Box::new(propagation.clone()));
        assert!(check_quantifier_ground_derivation(
            &mut arena,
            &assertions,
            &propagation_derivation
        ));
        let propagation_derivations = HashMap::from([(propagated, propagation_derivation)]);
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[propagated],
                &propagation_derivations,
            ),
            Some(CdcltOutcome::Unsat)
        );
        assert_eq!(online.inserted_clauses, 2);
        assert_eq!(online.solve_calls, 2);
        ground.push(propagated);
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the retained refutation candidate must independently replay in QF"
        );

        let mut wrong = instance_certificate;
        wrong.bindings[0] = one;
        let wrong_derivations =
            HashMap::from([(instance, QuantifierGroundDerivation::Instance(wrong))]);
        let mut rejecting =
            OnlineQuantifierClauseSession::new(&arena, &source_ground, None).unwrap();
        assert_eq!(
            rejecting.add_checked_batch(&mut arena, &assertions, &[instance], &wrong_derivations,),
            None
        );
        assert_eq!(rejecting.inserted_clauses, 0);
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn generated_ground_admission_requires_checked_source_provenance() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let x = arena.declare("checked_admission_x", sort).unwrap();
        let x_term = arena.var(x);
        let body = arena.eq(x_term, zero).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let assertions = vec![forall];

        let instance_one = arena.eq(one, zero).unwrap();
        let instance_two = arena.eq(two, zero).unwrap();
        let instance_three = arena.eq(three, zero).unwrap();
        let valid = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: forall,
            bindings: vec![one],
            instance: instance_one,
        });
        let tampered = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: forall,
            bindings: vec![two],
            instance: instance_one,
        });
        let candidates = HashMap::from([(instance_one, valid), (instance_two, tampered)]);
        let mut seen = HashSet::new();
        let mut ground = Vec::new();
        let mut retained = HashMap::new();
        let mut generations = TermGenerations::seed_sources(&arena, &assertions);

        assert_eq!(
            admit_generated_ground(
                &mut arena,
                &assertions,
                vec![instance_one, instance_two, instance_three],
                &mut seen,
                &mut ground,
                &mut retained,
                &candidates,
                &mut generations,
            ),
            vec![instance_one]
        );
        assert_eq!(ground, vec![instance_one]);
        assert_eq!(seen, HashSet::from([instance_one]));
        assert_eq!(retained.len(), 1);
        assert!(retained.contains_key(&instance_one));
    }

    /// Z3-style instantiation generations (T2.6.4, `qi_queue.cpp` cost
    /// `(+ weight generation)`): source-assertion subterms are generation 0 —
    /// including constants that only occur under a binder — an instance bound
    /// over source terms is generation 1, and an instance bound over a term
    /// first introduced by a generation-1 instance is generation 2. This is
    /// the ordering key that keeps flood-regime deferred admission
    /// shallow-first (see [`FLOOD_ROUND_ADMISSION_CAP`]).
    #[test]
    fn term_generations_stage_derived_instances_behind_source_instances() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("GenS");
        let sort = Sort::Uninterpreted(carrier);
        let map_fn = arena.declare_fun("gen_f", &[sort], sort).unwrap();
        let left = arena.declare("gen_c", sort).unwrap();
        let right = arena.declare("gen_d", sort).unwrap();
        let binder = arena.declare("gen_x", sort).unwrap();
        let xv = arena.var(binder);
        let f_x = arena.apply(map_fn, &[xv]).unwrap();
        let body = arena.eq(f_x, xv).unwrap();
        let forall = arena.forall(binder, body).unwrap();
        let cv = arena.var(left);
        let dv = arena.var(right);
        let c_eq_d = arena.eq(cv, dv).unwrap();
        let ground = arena.not(c_eq_d).unwrap();

        let assertions = vec![forall, ground];
        let mut generations = TermGenerations::seed_sources(&arena, &assertions);
        assert_eq!(generations.generation(cv), 0);
        // A constant living only under the binder is still source vocabulary.
        assert_eq!(generations.generation(f_x), 0);

        let f_c = arena.apply(map_fn, &[cv]).unwrap();
        let instance_one = arena.eq(f_c, cv).unwrap();
        let first = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: forall,
            bindings: vec![cv],
            instance: instance_one,
        });
        assert_eq!(generations.derivation_generation(&first), 1);
        generations.record_admitted(&arena, instance_one, 1);
        assert_eq!(generations.generation(f_c), 1);
        // Source subterms keep their shallower generation on re-encounter.
        assert_eq!(generations.generation(cv), 0);

        let f_f_c = arena.apply(map_fn, &[f_c]).unwrap();
        let instance_two = arena.eq(f_f_c, f_c).unwrap();
        let second = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: forall,
            bindings: vec![f_c],
            instance: instance_two,
        });
        assert_eq!(generations.derivation_generation(&second), 2);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn online_quantifier_session_mixes_full_clause_and_dynamic_disequality() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("online_clause_a", 8).unwrap();
        let b = arena.bv_var("online_clause_b", 8).unwrap();
        let f = arena.declare_fun("online_clause_f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();

        let x = arena.declare("online_clause_x", sort).unwrap();
        let xv = arena.var(x);
        let x_eq_a = arena.eq(xv, a).unwrap();
        let not_x_eq_a = arena.not(x_eq_a).unwrap();
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_fa = arena.eq(fx, fa).unwrap();
        let congruence_body = arena.or(not_x_eq_a, fx_eq_fa).unwrap();
        let congruence_universal = arena.forall(x, congruence_body).unwrap();
        let disequality_body = arena.not(fx_eq_fa).unwrap();
        let disequality_universal = arena.forall(x, disequality_body).unwrap();
        let b_eq_a = arena.eq(b, a).unwrap();
        let not_b_eq_a = arena.not(b_eq_a).unwrap();
        let fb_eq_fa = arena.eq(fb, fa).unwrap();
        let full_instance = arena.or(not_b_eq_a, fb_eq_fa).unwrap();
        let disequality_instance = arena.not(fb_eq_fa).unwrap();
        let assertions = vec![a_eq_b, congruence_universal, disequality_universal];
        let full_derivation = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: congruence_universal,
            bindings: vec![b],
            instance: full_instance,
        });
        let disequality_derivation =
            QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                assertion: disequality_universal,
                bindings: vec![b],
                instance: disequality_instance,
            });
        let mut online = OnlineQuantifierClauseSession::new(&arena, &[a_eq_b], None).unwrap();
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[full_instance],
                &HashMap::from([(full_instance, full_derivation.clone())]),
            ),
            Some(CdcltOutcome::Sat)
        );
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[disequality_instance],
                &HashMap::from([(disequality_instance, disequality_derivation)]),
            ),
            Some(CdcltOutcome::Unsat)
        );
        assert_eq!(online.inserted_clauses, 2);
        assert_eq!(online.atom_variables.len(), 3);

        let mut limited = OnlineQuantifierClauseSession::new(&arena, &[a_eq_b], None).unwrap();
        limited.limits.variables = limited.solver.variable_count();
        assert_eq!(
            limited.add_checked_batch(
                &mut arena,
                &assertions,
                &[full_instance],
                &HashMap::from([(full_instance, full_derivation)]),
            ),
            None
        );
        assert_eq!(limited.inserted_clauses, 0);

        let ground = [a_eq_b, full_instance, disequality_instance];
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let mut replay_stats = QuantifierLoopStats::default();
        let mut replay_cache = QuantifierTermCache::default();
        assert!(
            replay_online_refutation(
                &mut arena,
                &ground,
                &SolverConfig::default(),
                None,
                &mut replay_stats,
                &mut replay_cache,
            )
            .unwrap()
        );
        assert!(
            !replay_online_refutation(
                &mut arena,
                &[a_eq_b],
                &SolverConfig::default(),
                None,
                &mut replay_stats,
                &mut replay_cache,
            )
            .unwrap(),
            "an online outcome cannot bypass a non-refuting final QF query"
        );
    }

    #[test]
    fn online_quantifier_session_declines_unsupported_boolean_skeleton() {
        let mut arena = TermArena::new();
        let left = arena.bv_var("online_decline_left", 8).unwrap();
        let right = arena.bv_var("online_decline_right", 8).unwrap();
        let comparison = arena.bv_ult(left, right).unwrap();
        assert!(OnlineQuantifierClauseSession::new(&arena, &[comparison], None).is_none());
        assert_ne!(
            check_auto(&mut arena, &[comparison], &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "declining the accelerator must leave the ordinary QF result intact"
        );

        let equality = arena.eq(left, right).unwrap();
        for limits in [
            OnlineQuantifierLimits {
                variables: 0,
                clauses: usize::MAX,
                literals: usize::MAX,
            },
            OnlineQuantifierLimits {
                variables: usize::MAX,
                clauses: 0,
                literals: usize::MAX,
            },
            OnlineQuantifierLimits {
                variables: usize::MAX,
                clauses: usize::MAX,
                literals: 0,
            },
        ] {
            assert!(
                OnlineQuantifierClauseSession::new_with_limits(&arena, &[equality], None, limits,)
                    .is_none()
            );
        }
    }

    #[test]
    fn ground_count_limit_replays_an_available_qf_refutation() {
        let mut arena = TermArena::new();
        let false_term = arena.bool_const(false);
        let sort = Sort::BitVec(8);
        let function = arena.declare_fun("ground_limit_f", &[sort], sort).unwrap();
        let x = arena.declare("ground_limit_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(function, &[xv]).unwrap();
        let reflexive = arena.eq(fx, fx).unwrap();
        let universal = arena.forall(x, reflexive).unwrap();
        let mut assertions = vec![false_term; MAX_GROUND_TERMS + 1];
        assertions.push(universal);

        let mut stats = QuantifierLoopStats::default();
        assert_eq!(
            prove_quantified_unsat_via_egraph_impl(
                &mut arena,
                &assertions,
                &[],
                &SolverConfig::default(),
                true,
                true,
                &mut stats,
            )
            .unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(stats.qf_checks, 1);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn scoped_sat_candidate_equality_unlocks_nested_trigger_and_then_pops() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("candidate_match_a", 8).unwrap();
        let b = arena.bv_var("candidate_match_b", 8).unwrap();
        let c = arena.bv_var("candidate_match_c", 8).unwrap();
        let p = arena.bool_var("candidate_match_p").unwrap();
        let f = arena
            .declare_fun("candidate_match_f", &[sort], sort)
            .unwrap();
        let g = arena
            .declare_fun("candidate_match_g", &[sort], sort)
            .unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let a_eq_gb = arena.eq(a, gb).unwrap();
        let branch = arena.or(a_eq_gb, p).unwrap();
        let not_p = arena.not(p).unwrap();
        let fa_eq_c = arena.eq(fa, c).unwrap();

        let x = arena.declare("candidate_match_x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let fgx_eq_c = arena.eq(fgx, c).unwrap();
        let body = arena.not(fgx_eq_c).unwrap();
        let universal = arena.forall(x, body).unwrap();
        let assertions = vec![branch, not_p, fa_eq_c, universal];

        let mut baseline_arena = arena.clone();
        let mut baseline_stats = QuantifierLoopStats::default();
        let baseline_started = Instant::now();
        let baseline = prove_quantified_unsat_via_egraph_impl(
            &mut baseline_arena,
            &assertions,
            &[],
            &SolverConfig::default(),
            true,
            false,
            &mut baseline_stats,
        )
        .unwrap();
        let baseline_elapsed = baseline_started.elapsed();
        // Historically the baseline (scoped candidate equalities disabled)
        // stayed `Unknown`: the nested trigger `f(g(x))` had no ground
        // application to match. Term invention now seeds `f(g(b))` from the
        // free constants at the fixpoint, so the baseline refutes too — the
        // candidate arm below still verifies the scoped-candidate machinery
        // (its stats prove the candidate schedule ran and admitted the
        // instance before invention was ever consulted).
        assert_eq!(baseline, CheckResult::Unsat);

        let mut candidate_arena = arena.clone();
        let mut candidate_stats = QuantifierLoopStats::default();
        let candidate_started = Instant::now();
        let candidate = prove_quantified_unsat_via_egraph_impl(
            &mut candidate_arena,
            &assertions,
            &[],
            &SolverConfig::default(),
            true,
            true,
            &mut candidate_stats,
        )
        .unwrap();
        let candidate_elapsed = candidate_started.elapsed();
        assert_eq!(candidate, CheckResult::Unsat);
        assert_eq!(candidate_stats.candidate_checks, 1);
        assert!(candidate_stats.candidate_equalities >= 2);
        assert_eq!(candidate_stats.candidate_instances, 1);
        assert_eq!(candidate_stats.candidate_pattern_executions, 1);
        assert_eq!(candidate_stats.candidate_applications_scanned, 1);
        eprintln!(
            "SAT-candidate decision target: baseline={baseline:?} candidate={candidate:?} baseline_qf_checks={} candidate_qf_checks={} online_solves={} candidate_checks={} candidate_instances={} baseline_us={} candidate_us={}",
            baseline_stats.qf_checks,
            candidate_stats.qf_checks,
            candidate_stats.online_solves,
            candidate_stats.candidate_checks,
            candidate_stats.candidate_instances,
            baseline_elapsed.as_micros(),
            candidate_elapsed.as_micros(),
        );

        let ground = [branch, not_p, fa_eq_c];
        let mut matcher = IncrementalEmatchSession::new(&mut arena, &[universal]);
        matcher.extend_ground(&arena, &ground);
        assert!(
            matcher.lazy_clause_batches(&mut arena, None)[0]
                .instance_certificates
                .is_empty()
        );
        let scoped = matcher
            .scoped_candidate_instances(&mut arena, &[a_eq_gb, fa_eq_c], None)
            .unwrap();
        assert_eq!(scoped.batch.urgent.len(), 1);
        let a_node = matcher.bridge.term_to_node[&a];
        let gb_node = matcher.bridge.term_to_node[&gb];
        assert!(
            !matcher.bridge.egraph.equal(a_node, gb_node),
            "candidate equality must be popped before an instance leaves the matcher"
        );
        assert!(
            matcher.lazy_clause_batches(&mut arena, None)[0]
                .instance_certificates
                .is_empty()
        );
        assert!(
            matcher
                .scoped_candidate_instances_with_limits(
                    &mut arena,
                    &[a_eq_gb],
                    MAX_CANDIDATE_EQUALITIES,
                    0,
                    None,
                )
                .is_none()
        );
        assert!(
            matcher
                .scoped_candidate_instances_with_limits(
                    &mut arena,
                    &[a_eq_gb],
                    0,
                    MAX_CANDIDATE_APPLICATIONS,
                    None,
                )
                .is_none()
        );

        let optional_branch_assertions = [branch, fa_eq_c, universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &optional_branch_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "a candidate from one optional equality branch cannot refute another branch"
        );
        let not_a_eq_gb = arena.not(a_eq_gb).unwrap();
        let disequality_branch = arena.or(not_a_eq_gb, p).unwrap();
        let disequality_assertions = [disequality_branch, not_p, fa_eq_c, universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &disequality_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "a false equality atom must not appear in the true-candidate snapshot"
        );
        let positive_universal = arena.forall(x, fgx_eq_c).unwrap();
        let positive_assertions = [branch, not_p, fa_eq_c, positive_universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &positive_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "candidate matching a satisfiable positive universal must remain non-UNSAT"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn scoped_candidate_paths_match_full_scan_with_one_of_many_patterns() {
        const PATTERNS: usize = 64;
        const REPEATS: usize = 128;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let c = arena.bv_var("candidate_paths_c", 16).unwrap();
        let mut ground = Vec::new();
        let mut universals = Vec::new();
        let mut candidate_equality = None;
        let mut candidate_binding = None;

        for index in 0..PATTERNS {
            let a = arena
                .bv_var(&format!("candidate_paths_a_{index}"), 16)
                .unwrap();
            let b = arena
                .bv_var(&format!("candidate_paths_b_{index}"), 16)
                .unwrap();
            let p = arena
                .bool_var(&format!("candidate_paths_p_{index}"))
                .unwrap();
            let f = arena
                .declare_fun(&format!("candidate_paths_f_{index}"), &[sort], sort)
                .unwrap();
            let g = arena
                .declare_fun(&format!("candidate_paths_g_{index}"), &[sort], sort)
                .unwrap();
            let gb = arena.apply(g, &[b]).unwrap();
            let fa = arena.apply(f, &[a]).unwrap();
            let equality = arena.eq(a, gb).unwrap();
            ground.push(arena.or(equality, p).unwrap());
            ground.push(arena.eq(fa, c).unwrap());

            let x = arena
                .declare(&format!("candidate_paths_x_{index}"), sort)
                .unwrap();
            let xv = arena.var(x);
            let gx = arena.apply(g, &[xv]).unwrap();
            let fgx = arena.apply(f, &[gx]).unwrap();
            let body_equality = arena.eq(fgx, c).unwrap();
            let body = arena.not(body_equality).unwrap();
            universals.push(arena.forall(x, body).unwrap());
            if index == 0 {
                candidate_equality = Some(equality);
                candidate_binding = Some(b);
            }
        }

        let candidate_equality = candidate_equality.unwrap();
        let candidate_binding = candidate_binding.unwrap();
        let mut matcher = IncrementalEmatchSession::new(&mut arena, &universals);
        matcher.extend_ground(&arena, &ground);
        let initial = matcher.lazy_clause_batches(&mut arena, None);
        assert!(
            initial
                .iter()
                .all(|batch| batch.instance_certificates.is_empty())
        );

        let scoped = matcher
            .scoped_candidate_instances(&mut arena, &[candidate_equality], None)
            .unwrap();
        assert_eq!(scoped.pattern_executions, 1);
        assert_eq!(scoped.applications_scanned, 1);
        assert_eq!(scoped.batch.urgent.len(), 1);
        let instance = scoped.batch.urgent[0];
        let QuantifierGroundDerivation::Instance(certificate) =
            &scoped.batch.derivations[&instance]
        else {
            unreachable!();
        };
        assert_eq!(certificate.bindings, vec![candidate_binding]);

        let (_, lhs, rhs) = equality_literal(&arena, candidate_equality).unwrap();
        let lhs = matcher.bridge.term_to_node[&lhs];
        let rhs = matcher.bridge.term_to_node[&rhs];
        matcher.bridge.egraph.push();
        matcher.bridge.egraph.merge(lhs, rhs, u32::MAX);
        let patterns = matcher.patterns.clone();
        let mut full_index = matcher.bridge.egraph.new_match_index();
        let full_matches = matcher
            .bridge
            .egraph
            .ematch_many_indexed(&patterns, &mut full_index);
        let full_tuples: Vec<Option<Vec<Vec<TermId>>>> = matcher
            .quantifiers
            .iter()
            .map(|quantifier| matcher.witness_tuples(quantifier, &full_matches))
            .collect();
        matcher.bridge.egraph.pop();
        let nonempty: Vec<&Vec<Vec<TermId>>> = full_tuples.iter().flatten().collect();
        assert_eq!(nonempty.len(), 1);
        assert_eq!(nonempty[0], &vec![vec![candidate_binding]]);
        assert!(scoped.pattern_executions < PATTERNS);

        let exact_started = Instant::now();
        for _ in 0..REPEATS {
            let result = matcher
                .scoped_candidate_instances(&mut arena, &[candidate_equality], None)
                .unwrap();
            std::hint::black_box(result.batch.urgent.len());
        }
        let exact_elapsed = exact_started.elapsed();
        let full_started = Instant::now();
        for _ in 0..REPEATS {
            matcher.bridge.egraph.push();
            matcher.bridge.egraph.merge(lhs, rhs, u32::MAX);
            let mut full_index = matcher.bridge.egraph.new_match_index();
            let full_matches = matcher
                .bridge
                .egraph
                .ematch_many_indexed(&patterns, &mut full_index);
            let tuple_count = matcher
                .quantifiers
                .iter()
                .filter_map(|quantifier| matcher.witness_tuples(quantifier, &full_matches))
                .map(|tuples| tuples.len())
                .sum::<usize>();
            std::hint::black_box(tuple_count);
            matcher.bridge.egraph.pop();
        }
        let full_elapsed = full_started.elapsed();
        eprintln!(
            "SAT-candidate path target: patterns={PATTERNS} repeats={REPEATS} exact_pattern_executions={} exact_applications={} full_pattern_executions={PATTERNS} exact_us={} full_us={}",
            scoped.pattern_executions,
            scoped.applications_scanned,
            exact_elapsed.as_micros(),
            full_elapsed.as_micros(),
        );
    }

    #[test]
    #[allow(
        clippy::many_single_char_names,
        clippy::similar_names,
        clippy::too_many_lines
    )]
    fn recursive_provenance_table_is_exact_and_canonical() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("provenance_table_a", 8).unwrap();
        let f = arena
            .declare_fun("provenance_table_f", &[sort], sort)
            .unwrap();
        let g = arena
            .declare_fun("provenance_table_g", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("provenance_table_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let source_f_disequality = arena.not(fa_eq_zero).unwrap();
        let ga_eq_zero = arena.eq(ga, zero).unwrap();
        let q = arena.bool_var("provenance_table_q").unwrap();
        let source_g_trigger = arena.or(ga_eq_zero, q).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let p = arena.bool_var("provenance_table_p").unwrap();
        let source_h_trigger = arena.or(ha_eq_zero, p).unwrap();

        let x = arena.declare("provenance_table_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_equality = arena.eq(fx, one).unwrap();
        let equality_generator = arena.forall(x, generated_equality).unwrap();
        let gx_eq_one = arena.eq(gx, one).unwrap();
        let generated_disequality = arena.not(gx_eq_one).unwrap();
        let disequality_generator = arena.forall(x, generated_disequality).unwrap();
        let first_false_sibling = arena.not(generated_equality).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let partial_clause = arena.or(first_false_sibling, gx_eq_one).unwrap();
        let consumer_body = arena.or(partial_clause, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();
        let universals = [equality_generator, disequality_generator, consumer];
        let mut assertions = vec![source_f_disequality, source_g_trigger, source_h_trigger];
        assertions.extend(universals);

        let mut ground = vec![source_f_disequality, source_g_trigger, source_h_trigger];
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        let no_derivations = HashMap::new();
        session.extend_ground_with_derivations(&arena, &ground, &no_derivations);
        let first = session.lazy_clause_batches(&mut arena, None);
        let equality_instance = first[0].units[0];
        let disequality_instance = first[1].units[0];
        let equality_certificate = first[0].instance_certificates[&equality_instance].clone();
        let disequality_certificate = first[1].instance_certificates[&disequality_instance].clone();
        let mut derivations = HashMap::new();
        derivations.insert(
            equality_instance,
            QuantifierGroundDerivation::Instance(equality_certificate),
        );
        derivations.insert(
            disequality_instance,
            QuantifierGroundDerivation::Instance(disequality_certificate),
        );
        ground.extend([equality_instance, disequality_instance]);
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let second = session.lazy_clause_batches(&mut arena, None);
        let certificate = second[2].propagations[0].clone();
        assert_eq!(certificate.derived_reasons.len(), 2);
        assert!(matches!(
            certificate.derived_reasons.as_slice(),
            [
                QuantifierGroundDerivation::Instance(_),
                QuantifierGroundDerivation::Instance(_)
            ]
        ));
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &certificate
        ));

        let mut reordered = certificate.clone();
        reordered.derived_reasons.reverse();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &reordered
        ));

        let mut missing = certificate.clone();
        missing.derived_reasons.pop();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &missing
        ));

        let mut duplicate = certificate.clone();
        duplicate
            .derived_reasons
            .push(duplicate.derived_reasons[1].clone());
        duplicate
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &duplicate
        ));

        let mut unused = certificate.clone();
        unused
            .derived_reasons
            .push(QuantifierGroundDerivation::Instance(
                QuantifierInstanceCertificate {
                    assertion: consumer,
                    bindings: vec![a],
                    instance: certificate.source_instance,
                },
            ));
        unused
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &unused
        ));

        let mut wrong_conclusion = certificate.clone();
        let QuantifierGroundDerivation::Instance(instance) =
            &mut wrong_conclusion.derived_reasons[0]
        else {
            unreachable!();
        };
        instance.instance = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &wrong_conclusion
        ));

        let mut wrong_variant = certificate.clone();
        wrong_variant.derived_reasons[0] =
            QuantifierGroundDerivation::Propagation(Box::new(certificate.clone()));
        wrong_variant
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &wrong_variant
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn recursive_generated_provenance_checks_three_stage_propagation() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("recursive_provenance_a", 8).unwrap();
        let b = arena.bv_var("recursive_provenance_b", 8).unwrap();
        let functions: Vec<FuncId> = (0..=3)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_provenance_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let applications: Vec<TermId> = functions
            .iter()
            .map(|&function| arena.apply(function, &[a]).unwrap())
            .collect();
        let equalities: Vec<TermId> = applications
            .iter()
            .map(|&application| arena.eq(application, zero).unwrap())
            .collect();
        let final_disequality = arena.not(equalities[3]).unwrap();

        let x = arena.declare("recursive_provenance_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let false_sibling = arena.not(current_equality).unwrap();
            let propagated = arena.eq(next, zero).unwrap();
            let body = arena.or(false_sibling, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let mut assertions = vec![equalities[0], final_disequality];
        assertions.extend(universals.iter().copied());

        let mut ground = vec![equalities[0]];
        let mut derivations = HashMap::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        let mut certificates = Vec::new();
        for stage in 0..3 {
            session.extend_ground_with_derivations(&arena, &ground, &derivations);
            let batches = session.lazy_clause_batches(&mut arena, None);
            let certificate = batches[stage].propagations[0].clone();
            assert_eq!(certificate.propagated_literal, equalities[stage + 1]);
            assert_eq!(certificate.derived_reasons.len(), usize::from(stage > 0));
            assert!(check_quantifier_clause_propagation(
                &mut arena,
                &assertions,
                &certificate
            ));
            let propagated = certificate.propagated_literal;
            derivations.insert(
                propagated,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            ground.push(propagated);
            certificates.push(certificate);
        }

        let second = &certificates[1];
        assert!(matches!(
            second.derived_reasons.as_slice(),
            [QuantifierGroundDerivation::Propagation(_)]
        ));
        let third = &certificates[2];
        let QuantifierGroundDerivation::Propagation(second_derivation) = &third.derived_reasons[0]
        else {
            panic!("the third stage must retain the checked second-stage implication");
        };
        assert!(matches!(
            second_derivation.derived_reasons.as_slice(),
            [QuantifierGroundDerivation::Propagation(_)]
        ));
        let mut node_limited_checker = QuantifierProvenanceChecker {
            assertions: assertions.iter().copied().collect(),
            remaining_nodes: 2,
        };
        assert!(
            !node_limited_checker.check_propagation(&mut arena, third, 0),
            "three propagation nodes must not fit a two-node replay budget"
        );

        let mut tampered = third.clone();
        tampered.derived_reasons.clear();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        let mut tampered = second.clone();
        tampered
            .derived_reasons
            .push(tampered.derived_reasons[0].clone());
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        let mut tampered = third.clone();
        let QuantifierGroundDerivation::Propagation(second_derivation) =
            &mut tampered.derived_reasons[0]
        else {
            unreachable!();
        };
        let QuantifierGroundDerivation::Propagation(first_derivation) =
            &mut second_derivation.derived_reasons[0]
        else {
            unreachable!();
        };
        first_derivation.bindings[0] = b;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        ground.push(final_disequality);
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn recursive_provenance_chain_reduces_complete_instance_volume() {
        const STAGES: usize = 6;
        const FALSE_CONSTANTS: usize = 4;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let false_term = arena.bool_const(false);
        let a = arena.bv_var("recursive_volume_a", 16).unwrap();
        let functions: Vec<FuncId> = (0..=STAGES)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_volume_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let applications: Vec<TermId> = functions
            .iter()
            .map(|&function| arena.apply(function, &[a]).unwrap())
            .collect();
        let equalities: Vec<TermId> = applications
            .iter()
            .map(|&application| arena.eq(application, zero).unwrap())
            .collect();

        let x = arena.declare("recursive_volume_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let mut body = arena.not(current_equality).unwrap();
            for _ in 0..FALSE_CONSTANTS {
                body = arena.or(body, false_term).unwrap();
            }
            let propagated = arena.eq(next, zero).unwrap();
            body = arena.or(body, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let final_disequality = arena.not(equalities[STAGES]).unwrap();
        let mut assertions = vec![equalities[0], final_disequality];
        assertions.extend(universals.iter().copied());

        let mut retained_ground = vec![equalities[0]];
        let mut retained_derivations = HashMap::new();
        let mut complete_instances = Vec::new();
        let mut detached_literals = Vec::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        for stage in 0..STAGES {
            session.extend_ground_with_derivations(&arena, &retained_ground, &retained_derivations);
            let batches = session.lazy_clause_batches(&mut arena, None);
            let certificate = batches[stage].propagations[0].clone();
            assert!(check_quantifier_clause_propagation(
                &mut arena,
                &assertions,
                &certificate
            ));
            complete_instances.push(certificate.source_instance);
            detached_literals.push(certificate.propagated_literal);
            retained_derivations.insert(
                certificate.propagated_literal,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            retained_ground.push(certificate.propagated_literal);
        }

        let mut complete_query = vec![equalities[0], final_disequality];
        complete_query.extend(complete_instances);
        let mut detached_query = vec![equalities[0], final_disequality];
        detached_query.extend(detached_literals);
        assert_eq!(
            check_auto(&mut arena, &complete_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(
            check_auto(&mut arena, &detached_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let complete_stats = axeyum_ir::TermStats::compute(&arena, &complete_query);
        let detached_stats = axeyum_ir::TermStats::compute(&arena, &detached_query);
        assert!(complete_stats.dag_nodes > detached_stats.dag_nodes);
        assert!(complete_stats.tree_nodes > detached_stats.tree_nodes * 2);
        eprintln!(
            "recursive provenance target: stages={STAGES} false_constants={FALSE_CONSTANTS} complete_dag_nodes={} detached_dag_nodes={} complete_tree_nodes={} detached_tree_nodes={}",
            complete_stats.dag_nodes,
            detached_stats.dag_nodes,
            complete_stats.tree_nodes,
            detached_stats.tree_nodes,
        );

        let mut fresh_arena = arena.clone();
        let mut fresh_loop_stats = QuantifierLoopStats::default();
        let fresh_started = Instant::now();
        let fresh_result = prove_quantified_unsat_via_egraph_impl(
            &mut fresh_arena,
            &assertions,
            &[],
            &SolverConfig::default(),
            false,
            false,
            &mut fresh_loop_stats,
        )
        .unwrap();
        let fresh_elapsed = fresh_started.elapsed();
        let mut online_arena = arena.clone();
        let mut online_loop_stats = QuantifierLoopStats::default();
        let online_started = Instant::now();
        let online_result = prove_quantified_unsat_via_egraph_impl(
            &mut online_arena,
            &assertions,
            &[],
            &SolverConfig::default(),
            true,
            true,
            &mut online_loop_stats,
        )
        .unwrap();
        let online_elapsed = online_started.elapsed();
        assert_eq!(fresh_result, CheckResult::Unsat);
        assert_eq!(online_result, fresh_result);
        assert!(online_loop_stats.online_solves > 0);
        assert!(online_loop_stats.online_clauses > 0);
        assert!(
            online_loop_stats.qf_checks < fresh_loop_stats.qf_checks,
            "retained clauses must eliminate at least one complete QF rebuild"
        );
        eprintln!(
            "online quantifier target: fresh_qf_checks={} online_qf_checks={} online_solves={} online_clauses={} fresh_us={} online_us={}",
            fresh_loop_stats.qf_checks,
            online_loop_stats.qf_checks,
            online_loop_stats.online_solves,
            online_loop_stats.online_clauses,
            fresh_elapsed.as_micros(),
            online_elapsed.as_micros(),
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn recursive_provenance_rejects_over_depth_chain() {
        const STAGES: usize = MAX_QUANTIFIER_PROVENANCE_DEPTH + 2;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("recursive_depth_a", 8).unwrap();
        let functions: Vec<FuncId> = (0..=STAGES)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_depth_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let initial_application = arena.apply(functions[0], &[a]).unwrap();
        let initial = arena.eq(initial_application, zero).unwrap();
        let x = arena.declare("recursive_depth_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let false_sibling = arena.not(current_equality).unwrap();
            let propagated = arena.eq(next, zero).unwrap();
            let body = arena.or(false_sibling, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let mut assertions = vec![initial];
        assertions.extend(universals.iter().copied());
        let mut ground = vec![initial];
        let mut derivations = HashMap::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);

        for stage in 0..STAGES {
            session.extend_ground_with_derivations(&arena, &ground, &derivations);
            let batches = session.lazy_clause_batches(&mut arena, None);
            let certificate = batches[stage].propagations[0].clone();
            assert_eq!(
                check_quantifier_clause_propagation(&mut arena, &assertions, &certificate),
                stage <= MAX_QUANTIFIER_PROVENANCE_DEPTH,
                "the first rejected certificate must exceed the documented depth cap"
            );
            derivations.insert(
                certificate.propagated_literal,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            ground.push(certificate.propagated_literal);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn checked_detached_units_reduce_qf_term_volume() {
        const MATCHES: usize = 128;
        const FALSE_SIBLINGS: usize = 6;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let one = arena.bv_const(16, 1).unwrap();
        let f = arena.declare_fun("detach_bench_f", &[sort], sort).unwrap();
        let h = arena.declare_fun("detach_bench_h", &[sort], sort).unwrap();
        let siblings: Vec<FuncId> = (0..FALSE_SIBLINGS)
            .map(|index| {
                arena
                    .declare_fun(&format!("detach_bench_g_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let p = arena.bool_var("detach_bench_p").unwrap();
        let mut ground = Vec::new();
        let mut first_target = None;
        for index in 0..MATCHES {
            let argument = arena
                .bv_var(&format!("detach_bench_a_{index}"), 16)
                .unwrap();
            let fa = arena.apply(f, &[argument]).unwrap();
            let fa_eq_zero = arena.eq(fa, zero).unwrap();
            ground.push(fa_eq_zero);
            for &sibling in &siblings {
                let application = arena.apply(sibling, &[argument]).unwrap();
                ground.push(arena.eq(application, zero).unwrap());
            }
            let ha = arena.apply(h, &[argument]).unwrap();
            let ha_eq_zero = arena.eq(ha, zero).unwrap();
            ground.push(arena.not(ha_eq_zero).unwrap());
            if index == 0 {
                let target = arena.eq(ha, one).unwrap();
                first_target = Some(target);
                let not_target = arena.not(target).unwrap();
                ground.push(arena.or(not_target, p).unwrap());
                ground.push(arena.not(p).unwrap());
            }
        }

        let x = arena.declare("detach_bench_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let mut body = arena.not(fx_eq_zero).unwrap();
        for &sibling in &siblings {
            let application = arena.apply(sibling, &[xv]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            let false_literal = arena.not(equality).unwrap();
            body = arena.or(body, false_literal).unwrap();
        }
        let hx = arena.apply(h, &[xv]).unwrap();
        let target = arena.eq(hx, one).unwrap();
        body = arena.or(body, target).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let mut assertions = ground.clone();
        assertions.push(forall);

        let eager_total_started = Instant::now();
        let eager = instantiate_forall_via_egraph(&mut arena, &ground, forall);
        assert_eq!(eager.len(), MATCHES);
        let mut eager_query = ground.clone();
        eager_query.extend(eager.iter().copied());
        let eager_stats = axeyum_ir::TermStats::compute(&arena, &eager_query);
        let eager_qf_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &eager_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let eager_qf_elapsed = eager_qf_started.elapsed();
        let eager_total_elapsed = eager_total_started.elapsed();

        let detached_total_started = Instant::now();
        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena, None).remove(0);
        assert!(batch.urgent.is_empty());
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.propagations.len(), MATCHES);
        assert!(check_quantifier_clause_propagations(
            &mut arena,
            &assertions,
            &batch.propagations
        ));
        let detached: Vec<TermId> = batch
            .propagations
            .iter()
            .map(|certificate| certificate.propagated_literal)
            .collect();
        assert!(detached.contains(&first_target.unwrap()));
        let mut detached_query = ground;
        detached_query.extend(detached);
        let detached_stats = axeyum_ir::TermStats::compute(&arena, &detached_query);
        let detached_qf_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &detached_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let detached_qf_elapsed = detached_qf_started.elapsed();
        let detached_total_elapsed = detached_total_started.elapsed();

        assert!(eager_stats.tree_nodes > detached_stats.tree_nodes * 2);
        assert!(eager_stats.dag_nodes > detached_stats.dag_nodes);
        eprintln!(
            "detached quantifier target: matches={MATCHES} false_siblings={FALSE_SIBLINGS} eager_dag_nodes={} detached_dag_nodes={} eager_tree_nodes={} detached_tree_nodes={} eager_qf_us={} detached_qf_us={} eager_total_us={} detached_total_us={}",
            eager_stats.dag_nodes,
            detached_stats.dag_nodes,
            eager_stats.tree_nodes,
            detached_stats.tree_nodes,
            eager_qf_elapsed.as_micros(),
            detached_qf_elapsed.as_micros(),
            eager_total_elapsed.as_micros(),
            detached_total_elapsed.as_micros()
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default())
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn lazy_clause_classification_is_conservative() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ground_f_is_zero = arena.eq(fa, zero).unwrap();
        let ground_f_not_zero = arena.not(ground_f_is_zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let quantified_f_is_zero = arena.eq(fx, zero).unwrap();
        let quantified_g_is_one = arena.eq(gx, one).unwrap();
        let clause = arena.or(quantified_f_is_zero, quantified_g_is_one).unwrap();
        let forall_clause = arena.forall(x, clause).unwrap();

        let unit = lazy_clause_instances(&mut arena, &[ground_f_not_zero], forall_clause);
        assert_eq!(unit.urgent.len(), 1, "false or unknown is unit-like");
        assert!(unit.deferred.is_empty());

        let fa_plus_one = arena.bv_add(fa, one).unwrap();
        let mention = arena.eq(fa_plus_one, zero).unwrap();
        let unresolved = lazy_clause_instances(&mut arena, &[mention], forall_clause);
        assert!(unresolved.urgent.is_empty());
        assert_eq!(unresolved.deferred.len(), 1, "two unknown literals defer");

        let conjunction = arena
            .and(quantified_f_is_zero, quantified_g_is_one)
            .unwrap();
        let forall_non_clause = arena.forall(x, conjunction).unwrap();
        let non_clause = lazy_clause_instances(&mut arena, &[mention], forall_non_clause);
        assert!(non_clause.urgent.is_empty());
        assert_eq!(
            non_clause.deferred.len(),
            1,
            "unsupported shapes retain legacy reach"
        );
    }

    #[test]
    fn lazy_clause_truth_uses_ground_congruence() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let asserted_value = arena.eq(fa, zero).unwrap();
        let congruent_value = arena.eq(fb, zero).unwrap();
        let mut facts = GroundEqualityContext::new(&arena, &[a_eq_b, asserted_value]);
        assert_eq!(
            evaluate_equality_clause(&arena, congruent_value, &mut facts),
            Some(ClauseValue::True),
            "f(a)=0 and a=b must justify f(b)=0 by congruence"
        );
    }

    #[test]
    fn instantiates_over_ground_applications() {
        let (mut arena, forall, [a, b], c, ground0, f, _x) = setup();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);

        // Expect (= (f a) c) and (= (f b) c).
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let want_a = arena.eq(fa, c).unwrap();
        let want_b = arena.eq(fb, c).unwrap();
        assert!(instances.contains(&want_a), "instance for a missing");
        assert!(instances.contains(&want_b), "instance for b missing");
        assert_eq!(instances.len(), 2);
    }

    #[test]
    fn witness_tuples_expose_the_matched_witnesses() {
        // The witness-tuple variant returns the binder→ground-term tuples (in
        // binder order) the e-matching selects: here `[a]` and `[b]` for the two
        // f-applications. This is what the Alethe quantifier emitter consumes.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let (vars, _body, tuples) =
            witness_tuples_via_egraph(&mut arena, &[ground0], forall).expect("matches");
        assert_eq!(vars.len(), 1, "one binder");
        assert!(tuples.contains(&vec![a]), "witness a missing: {tuples:?}");
        assert!(tuples.contains(&vec![b]), "witness b missing: {tuples:?}");
        assert_eq!(tuples.len(), 2);
    }

    #[test]
    fn instantiation_is_modulo_congruence() {
        // Add a = b to the ground: f(a) and f(b) become one class, so the trigger
        // fires once and there is a single instance.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let a_eq_b = arena.eq(a, b).unwrap();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0, a_eq_b], forall);
        assert_eq!(
            instances.len(),
            1,
            "congruent f-applications instantiate once, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_nested_trigger() {
        // ∀x. (= (f (g x)) c), ground containing f(g(a)): instance (= (f (g a)) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let fga = arena.apply(f, &[ga]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(fga, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let body = arena.eq(fgx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(fga, c).unwrap();
        assert_eq!(instances, vec![want], "nested trigger f(g(x)) → x = a");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_binary_trigger_with_a_ground_argument() {
        // ∀x. (= (h x a) c), ground containing h(b, a) and h(d, a): two instances;
        // the ground argument `a` in the trigger is matched by its class.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let d = arena.bv_var("d", 8).unwrap();
        let h = arena.declare_fun("h", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let hba = arena.apply(h, &[b, a]).unwrap();
        let hda = arena.apply(h, &[d, a]).unwrap();
        // A decoy h(a, b) whose ground argument is b, not a — must NOT match h(x, a).
        let hab = arena.apply(h, &[a, b]).unwrap();
        let hba_hda = arena.bv_add(hba, hda).unwrap();
        let sum = arena.bv_add(hba_hda, hab).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let hxa = arena.apply(h, &[xv, a]).unwrap();
        let body = arena.eq(hxa, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want_b = arena.eq(hba, c).unwrap();
        let want_d = arena.eq(hda, c).unwrap();
        assert!(instances.contains(&want_b));
        assert!(instances.contains(&want_d));
        assert_eq!(
            instances.len(),
            2,
            "only h(_, a) matches, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn instantiates_a_multi_pattern_trigger() {
        // ∀x. ∀y. (= (f x) (g y)): no single subterm covers both x and y, so the
        // multi-pattern {f(x), g(y)} is inferred and the matches joined.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let g0 = arena.eq(fa, zero).unwrap();
        let g1 = arena.eq(gb, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gy = arena.apply(g, &[yv]).unwrap();
        let inner_body = arena.eq(fx, gy).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[g0, g1], forall);
        let want = arena.eq(fa, gb).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b joined from {{f(x), g(y)}}");
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn nested_trigger_fires_through_congruence_involution() {
        // The canonical congruence-only test: ∀x. f(f(x)) = x with ground
        //   f(a) = b,  f(b) = c,  a ≠ c.
        // The trigger f(f(x)) has NO syntactic match — there is no literal
        // `f(f(·))` ground term. It fires only because f(a)=b puts f(a) inside b's
        // class, so the outer ground f(b) has an inner f-application (f(a)) in its
        // argument class ⇒ x ↦ a. The instance f(f(a)) = a forces c = a ⨯ a ≠ c.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let fb_eq_c = arena.eq(fb, c).unwrap();
        let a_ne_c = {
            let e = arena.eq(a, c).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let ffx = arena.apply(f, &[fx]).unwrap();
        let body = arena.eq(ffx, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_eq_b, fb_eq_c, a_ne_c, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "nested trigger must fire via congruence and refute"
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn instantiation_loop_refutes_a_quantified_contradiction() {
        // f(a) ≠ 0  ∧  ∀x. (= (f x) 0): instantiating x = a gives f(a) = 0,
        // contradicting the ground disequality → UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa_eq_0 = arena.eq(fa, zero).unwrap();
        let fa_ne_0 = arena.not(fa_eq_0).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_0 = arena.eq(fx, zero).unwrap();
        let forall = arena.forall(x, fx_eq_0).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn instantiation_loop_refutes_across_multiple_rounds() {
        // A genuinely multi-round refutation: the g(x) trigger can only fire after
        // the f(x) instantiation has introduced g(a) into the ground set.
        //   ground:    f(a) ≠ 0
        //   ∀x. f(x) = g(x)   → round 1: f(a) = g(a)  (introduces ground g(a))
        //   ∀x. g(x) = 0      → round 2: g(a) = 0     (now g(a) exists to match)
        //   ⇒ f(a) = g(a) = 0 contradicts f(a) ≠ 0   → UNSAT (round 3 check)
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fa_ne_0 = {
            let e = arena.eq(fa, zero).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let fx_eq_gx = arena.eq(fx, gx).unwrap();
        let forall_fg = arena.forall(x, fx_eq_gx).unwrap();
        let gx_eq_0 = arena.eq(gx, zero).unwrap();
        let forall_g0 = arena.forall(x, gx_eq_0).unwrap();

        let mut retained_ground = vec![fa_ne_0];
        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall_fg, forall_g0]);
        session.extend_ground(&arena, &retained_ground);
        let first_round = session.lazy_clause_batches(&mut arena, None);
        assert_eq!(first_round[0].units.len(), 1);
        assert!(first_round[1].urgent.is_empty() && first_round[1].units.is_empty());
        let first_pattern_executions = session.pattern_executions;
        assert_eq!(first_pattern_executions, session.patterns.len());
        let first_instance = first_round[0].units[0];
        retained_ground.push(first_instance);
        let first_node_count = session.bridge.egraph.len();

        session.extend_ground(&arena, &retained_ground);
        assert_eq!(session.merge_invalidations, 1);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(
            session.candidate_patterns.len(),
            1,
            "only the newly added g-root pattern needs delta matching"
        );
        let second_round = session.lazy_clause_batches(&mut arena, None);
        assert_eq!(
            session.pattern_executions - first_pattern_executions,
            1,
            "the unrelated retained f-root cache remains valid modulo roots"
        );
        assert_eq!(second_round[1].urgent.len(), 1);
        let second_instance = second_round[1].urgent[0];
        retained_ground.push(second_instance);
        assert_eq!(
            session.extensions, 2,
            "only appended ground extends the bridge"
        );
        assert_eq!(session.match_rounds, 2);
        assert!(
            session.bridge.egraph.len() > first_node_count,
            "the retained bridge must gain the newly introduced g(a) term"
        );
        assert_eq!(
            check_auto(&mut arena, &retained_ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "retained-round source instances must independently replay"
        );

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall_fg, forall_g0],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "multi-round chaining should refute"
        );
    }

    #[test]
    fn instantiation_loop_passes_through_quantifier_free() {
        // No universals: routes straight to check_auto (here, sat).
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a_eq_1 = arena.eq(a, one).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[a_eq_1], &SolverConfig::default())
                .unwrap();
        assert!(matches!(result, CheckResult::Sat(_)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_a_two_variable_quantifier() {
        // ∀x. ∀y. (= (g x y) c), ground containing g(a, b): instance (= (g a b) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let gab = arena.apply(g, &[a, b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(gab, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let gxy = arena.apply(g, &[xv, yv]).unwrap();
        let inner_body = arena.eq(gxy, c).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(gab, c).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b from the g(x,y) trigger");
    }

    fn euclidean_clock_universal(
        arena: &mut TermArena,
        modulus: i128,
        upper: i128,
        extra_disjunct: bool,
    ) -> TermId {
        let t = arena.int_var("t").unwrap();
        let s = arena.declare("s", Sort::Int).unwrap();
        let m = arena.declare("m", Sort::Int).unwrap();
        let sv = arena.var(s);
        let mv = arena.var(m);
        let k = arena.int_const(modulus);
        let km = arena.int_mul(k, mv).unwrap();
        let sum = arena.int_add(km, sv).unwrap();
        let recomposes = arena.eq(sum, t).unwrap();
        let not_recomposes = arena.not(recomposes).unwrap();
        let zero = arena.int_const(0);
        let below_range = arena.int_lt(sv, zero).unwrap();
        let upper = arena.int_const(upper);
        let above_range = arena.int_ge(sv, upper).unwrap();
        let bounds = arena.or(below_range, above_range).unwrap();
        let mut body = arena.or(not_recomposes, bounds).unwrap();
        if extra_disjunct {
            let truth = arena.bool_const(true);
            body = arena.or(body, truth).unwrap();
        }
        let inner = arena.forall(m, body).unwrap();
        arena.forall(s, inner).unwrap()
    }

    #[test]
    fn euclidean_residue_instantiation_refutes_clock_rows() {
        for modulus in [3, 10] {
            let mut arena = TermArena::new();
            let forall = euclidean_clock_universal(&mut arena, modulus, modulus, false);
            assert!(
                euclidean_residue_instance(&mut arena, forall)
                    .unwrap()
                    .is_some(),
                "the exact modulus-{modulus} residue partition must instantiate"
            );
            let result =
                prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                    .unwrap();
            assert_eq!(
                result,
                CheckResult::Unsat,
                "div/mod symbolic counterexample must refute the modulus-{modulus} row"
            );
        }
    }

    #[test]
    fn euclidean_residue_instantiation_declines_non_partition_shapes() {
        let mut arena = TermArena::new();
        let narrowed = euclidean_clock_universal(&mut arena, 3, 2, false);
        assert!(
            euclidean_residue_instance(&mut arena, narrowed)
                .unwrap()
                .is_none(),
            "a different upper guard is not the exact Euclidean residue partition"
        );
        assert_ne!(
            prove_quantified_unsat_via_egraph(&mut arena, &[narrowed], &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat,
            "a satisfiable narrowed-residue universal must not be refuted"
        );

        let mut arena = TermArena::new();
        let weakened = euclidean_clock_universal(&mut arena, 3, 3, true);
        assert!(
            euclidean_residue_instance(&mut arena, weakened)
                .unwrap()
                .is_none(),
            "an extra disjunct must decline instead of changing the theorem"
        );
        assert_ne!(
            prove_quantified_unsat_via_egraph(&mut arena, &[weakened], &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat,
            "the valid extra-true-disjunct universal must not be refuted"
        );
    }

    #[test]
    fn nested_xor_instantiation_refutes_issue4433() {
        let mut script = axeyum_smtlib::parse_script(include_str!(
            "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__issue4433-nqe.smt2"
        ))
        .unwrap();
        let assertion = script.assertions[0];
        let instance = nested_xor_discriminator_instance(&mut script.arena, assertion)
            .unwrap()
            .expect("exact nested-XOR shape must produce a hierarchical instance");
        assert_eq!(
            check_auto(&mut script.arena, &[instance], &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the derived off-pivot selector equality must be contradictory"
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(
                &mut script.arena,
                &[assertion],
                &SolverConfig::default(),
            )
            .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn nested_xor_instantiation_declines_near_misses() {
        let shapes = [
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 0) (ite (= c 0) 0 0)))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (or (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1)))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (and (= (ite (= a 0) 0 1) (ite (= c 0) 0 1)) true))))) (check-sat)",
        ];
        for text in shapes {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertion = script.assertions[0];
            assert!(
                nested_xor_discriminator_instance(&mut script.arena, assertion)
                    .unwrap()
                    .is_none(),
                "near-miss structure must not use ADR-0099: {text}"
            );
        }

        for text in [
            "(set-logic LIA) (assert (not (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (or true (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
        ] {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertions = script.assertions.clone();
            let result = crate::solve(&mut script.arena, &assertions, &SolverConfig::default());
            assert!(
                !matches!(result, Ok(CheckResult::Unsat)),
                "satisfiable polarity/context near miss must not be refuted: {text}"
            );
        }
    }

    #[test]
    fn affine_growth_instantiation_refutes_repair_const_nterm() {
        let mut script = axeyum_smtlib::parse_script(include_str!(
            "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__repair-const-nterm.smt2"
        ))
        .unwrap();
        let assertion = script.assertions[0];
        let instances = affine_growth_instances(&mut script.arena, assertion)
            .unwrap()
            .expect("exact affine-growth shape must instantiate");
        assert_eq!(instances.len(), 2);
        assert_eq!(
            prove_quantified_unsat_via_egraph(
                &mut script.arena,
                &[assertion],
                &SolverConfig::default(),
            )
            .unwrap(),
            CheckResult::Unsat,
            "two consecutive symbolic counterexamples must refute the target"
        );
    }

    #[test]
    fn affine_growth_instantiation_declines_near_misses() {
        for text in [
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int)) \
             (not (>= (- (* 0 x) (ite (= x p) a b)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (assert (forall ((x Int)) \
             (not (>= (- (* 3 x) (ite (= x p) a x)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int)) \
             (or (not (>= (- (* 3 x) (ite (= x p) a b)) 1)) true))) (check-sat)",
        ] {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertion = script.assertions[0];
            assert!(
                affine_growth_instances(&mut script.arena, assertion)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn closed_universal_with_no_trigger_is_refuted() {
        // The measured qbv-simp shape: ∀A B C D. (A=B ∧ C=D) ∨ (A=C ∧ B=D).
        // status unsat — the universal is *false* (A=0,B=1,C=0,D=0 falsifies it),
        // but its body has no function-application trigger, so the e-matching loop
        // alone returns `unknown`. Closed-universal falsification decides it.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let mk = |arena: &mut TermArena, n: &str| {
            let s = arena.declare(n, sort).unwrap();
            (s, arena.var(s))
        };
        let (a, av) = mk(&mut arena, "A");
        let (b, bv) = mk(&mut arena, "B");
        let (c, cv) = mk(&mut arena, "C");
        let (d, dv) = mk(&mut arena, "D");
        let ab = arena.eq(av, bv).unwrap();
        let cd = arena.eq(cv, dv).unwrap();
        let ac = arena.eq(av, cv).unwrap();
        let bd = arena.eq(bv, dv).unwrap();
        let left = arena.and(ab, cd).unwrap();
        let right = arena.and(ac, bd).unwrap();
        let body = arena.or(left, right).unwrap();
        // Bind innermost-first so the peeled prefix is [A, B, C, D].
        let mut forall = arena.forall(d, body).unwrap();
        forall = arena.forall(c, forall).unwrap();
        forall = arena.forall(b, forall).unwrap();
        forall = arena.forall(a, forall).unwrap();

        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "a false closed universal with no trigger must be refuted"
        );
    }

    #[test]
    fn valid_closed_universal_is_not_refuted() {
        // ∀x. (x = x): valid (true), must NOT be reported unsat. The falsification
        // sub-check `¬(x=x)` is unsat, so the lever declines and the loop reaches
        // its own (non-unsat) verdict.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let body = arena.eq(xv, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_ne!(
            result,
            CheckResult::Unsat,
            "a valid closed universal must never be refuted"
        );
    }

    /// Builds the census `∀A B C D. (A=B ∧ C=D) ∨ (A=C ∧ B=D)` closed universal —
    /// a **false** sentence (A=0,B=1,C=0,D=0 falsifies it) that the closed-universal
    /// lever refutes when it is *positively* asserted. Returns the arena and the
    /// forall term, so the polarity tests can embed it in a Boolean context where
    /// refuting it would be **unsound**.
    #[allow(clippy::many_single_char_names)]
    fn false_closed_universal() -> (TermArena, TermId) {
        let mut arena = TermArena::new();
        // A narrow width so the front door's finite-domain expansion
        // (`check_with_quantifiers`, complete for `BitVec`) decides the nested-
        // polarity shapes end-to-end rather than falling through to the e-matching
        // fallback (which cannot bit-blast a residual quantifier).
        let sort = Sort::BitVec(4);
        let mk = |arena: &mut TermArena, n: &str| {
            let s = arena.declare(n, sort).unwrap();
            (s, arena.var(s))
        };
        let (a, av) = mk(&mut arena, "A");
        let (b, bv) = mk(&mut arena, "B");
        let (c, cv) = mk(&mut arena, "C");
        let (d, dv) = mk(&mut arena, "D");
        let ab = arena.eq(av, bv).unwrap();
        let cd = arena.eq(cv, dv).unwrap();
        let ac = arena.eq(av, cv).unwrap();
        let bd = arena.eq(bv, dv).unwrap();
        let left = arena.and(ab, cd).unwrap();
        let right = arena.and(ac, bd).unwrap();
        let body = arena.or(left, right).unwrap();
        // Innermost-first, so the peeled prefix is [A, B, C, D].
        let mut forall = arena.forall(d, body).unwrap();
        forall = arena.forall(c, forall).unwrap();
        forall = arena.forall(b, forall).unwrap();
        forall = arena.forall(a, forall).unwrap();
        (arena, forall)
    }

    /// DEBT 3 polarity guard — the closed-universal falsification lever must fire
    /// ONLY on a **top-level positively-asserted** universal. Here the lever's owner
    /// [`prove_quantified_unsat_via_egraph`] is handed a false `∀` buried under a
    /// top-level `or` (an `Op::Or` node, never in the `foralls` bucket): it must
    /// never forge an `unsat`, whatever the ground solver makes of the disjunction.
    /// (`(or (false ∀) …)` is TRUE, so an `unsat` would be unsound.)
    fn lever_never_forges_unsat(assertion: TermId, arena: &mut TermArena) {
        // The lever's owner: proves the lever itself never fires on the wrong
        // polarity. A ground solver that declines the embedded quantifier surfaces as
        // `Err(Unsupported)` — which is NOT an `unsat`, so the property holds.
        let via_lever =
            prove_quantified_unsat_via_egraph(arena, &[assertion], &SolverConfig::default());
        assert!(
            !matches!(via_lever, Ok(CheckResult::Unsat)),
            "closed-universal lever forged an unsat on a non-top-level universal: {via_lever:?}",
        );
    }

    #[test]
    fn forall_under_or_with_true_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let tru = arena.bool_const(true);
        let disj = arena.or(forall, tru).unwrap();
        // The lever must not forge an unsat.
        lever_never_forges_unsat(disj, &mut arena);
        // End-to-end: the real front door decides it correctly — `(or ∀ true)` is
        // TRUE, so `sat` (via finite BV expansion), never `unsat`.
        let end_to_end = crate::solve(&mut arena, &[disj], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(or (false ∀) true) is TRUE — solve must return sat, got {end_to_end:?}",
        );
    }

    #[test]
    fn forall_under_or_with_sat_ground_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let p = arena.bool_var("p_free").unwrap(); // a free Boolean: can be true
        let disj = arena.or(forall, p).unwrap();
        lever_never_forges_unsat(disj, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[disj], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(or (false ∀) p) is satisfiable (p=true) — got {end_to_end:?}",
        );
    }

    /// DEBT 3 polarity guard: `¬(∀x⃗. body)` with a **false** body-universal is
    /// `∃x⃗. ¬body`, which is TRUE — so the assertion is satisfiable and must NOT be
    /// `unsat`. Refuting the *inner* positive `∀` (the wrong polarity) would forge an
    /// unsat here; the `not` node is not an `Op::Forall`, so the lever never fires.
    #[test]
    fn negated_false_universal_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let neg = arena.not(forall).unwrap();
        lever_never_forges_unsat(neg, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[neg], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "¬(false ∀) = ∃¬body is TRUE — solve must return sat, got {end_to_end:?}",
        );
    }

    /// DEBT 3 polarity guard: a false closed `∀` in the **then** branch of an `ite`
    /// whose condition can select the (true) **else** branch must NOT be `unsat`.
    #[test]
    fn forall_inside_ite_then_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let cond = arena.bool_var("c_free").unwrap();
        let tru = arena.bool_const(true);
        // (ite c (false ∀) true): choosing c=false yields the true else branch.
        let ite = arena.ite(cond, forall, tru).unwrap();
        lever_never_forges_unsat(ite, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[ite], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(ite c (false ∀) true) is satisfiable (c=false) — got {end_to_end:?}",
        );
    }

    /// Control: the same false closed universal asserted **positively** at top level
    /// IS refuted (by the lever), confirming the polarity tests above are non-vacuous
    /// — the universal really is false, so only its *positive* top-level assertion is
    /// unsat.
    #[test]
    fn positive_false_universal_control_is_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let end_to_end = crate::solve(&mut arena, &[forall], &SolverConfig::default()).unwrap();
        assert_eq!(
            end_to_end,
            CheckResult::Unsat,
            "the positively-asserted false closed universal must be unsat (control)",
        );
    }

    #[test]
    fn open_universal_is_not_treated_as_closed() {
        // ∀x. (f x) = c has a free function symbol `f` — it is NOT a closed
        // sentence, so `body_is_closed_qf` rejects it and the falsification lever
        // does not fire (the e-matching path owns it).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let bound: HashSet<SymbolId> = std::iter::once(x).collect();
        assert!(
            !body_is_closed_qf(&arena, body, &bound),
            "a body mentioning a free function symbol is not closed"
        );
    }

    #[test]
    fn non_forall_or_no_trigger_yields_nothing() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();
        // Not a forall.
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], p).is_empty());
        // A forall whose body has no unary trigger over the bound variable.
        let x = arena.declare("x", Sort::Bool).unwrap();
        let xv = arena.var(x);
        let body = arena.or(xv, p).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], forall).is_empty());
    }

    // --- Nested quantifier registration (slice 2) --------------------------

    #[test]
    fn conjunctive_nesting_is_extracted_into_independent_universals() {
        // `∀x. (p(x) ∧ ∀y. q(x, y))` — the conjunctive skeleton is entailed all
        // the way down, so both universals become assertions with their own
        // (minimized) prefixes and therefore their own body-derived triggers.
        // Nothing lands in the non-entailed registration bucket.
        let mut arena = TermArena::new();
        let p = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let px = arena.apply(p, &[xv]).unwrap();
        let qxy = arena.apply(q, &[xv, yv]).unwrap();
        let inner = arena.forall(y, qxy).unwrap();
        let conjunction = arena.and(px, inner).unwrap();
        let assertion = arena.forall(x, conjunction).unwrap();

        let extraction = extract_nested_universals(&mut arena, &[assertion]);

        assert!(
            extraction.nested.is_empty(),
            "a conjunctive position is entailed, so nothing is merely registered"
        );
        assert_eq!(extraction.assertions.len(), 2);
        let prefixes: Vec<usize> = extraction
            .assertions
            .iter()
            .map(|&term| peel_foralls(&arena, term).0.len())
            .collect();
        assert_eq!(
            prefixes,
            vec![1, 2],
            "`p(x)` keeps one binder; `q(x, y)` gets both -- neither is glued to \
             the other's variables"
        );
    }

    #[test]
    fn a_universal_under_a_disjunction_is_registered_but_not_asserted() {
        // `∀x. (p(x) ∨ ∀y. q(x, y))` — `∀x∀y. q(x, y)` is NOT a consequence, so
        // the inner universal must land in the registration bucket, keeping its
        // own binder prefix and its own body.
        let mut arena = TermArena::new();
        let p = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let px = arena.apply(p, &[xv]).unwrap();
        let qxy = arena.apply(q, &[xv, yv]).unwrap();
        let inner = arena.forall(y, qxy).unwrap();
        let disjunction = arena.or(px, inner).unwrap();
        let assertion = arena.forall(x, disjunction).unwrap();

        let extraction = extract_nested_universals(&mut arena, &[assertion]);

        assert_eq!(extraction.assertions, vec![assertion]);
        assert_eq!(extraction.nested.len(), 1);
        assert_eq!(extraction.nested[0].vars, vec![x, y]);
        assert_eq!(extraction.nested[0].body, qxy);

        // The registration is first class in the driver: it is compiled with a
        // trigger taken from `q(x, y)` -- its own body -- not from the
        // disjunction it sits in.
        let session =
            IncrementalEmatchSession::new_with_nested(&mut arena, &[assertion], &extraction.nested);
        let registered = session
            .quantifiers
            .iter()
            .find(|quantifier| !quantifier.active)
            .expect("the nested universal is registered");
        assert_eq!(registered.body, qxy);
        assert_eq!(
            registered.pattern_indices.len(),
            1,
            "one trigger, `q(x, y)`, covering both of its variables"
        );
    }

    #[test]
    fn a_registered_universal_matches_but_produces_no_instance() {
        // The registration is *triggered* (its pattern joins a tuple over the
        // ground terms) yet contributes nothing to the ground set, which is the
        // exact soundness contract of slice 2.
        let mut arena = TermArena::new();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let b_sym = arena.declare("b", Sort::Int).unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let (av, bv, xv, yv) = (
            arena.var(a_sym),
            arena.var(b_sym),
            arena.var(x_sym),
            arena.var(y_sym),
        );
        let qxy = arena.apply(q_fun, &[xv, yv]).unwrap();
        let qab = arena.apply(q_fun, &[av, bv]).unwrap();
        let registration = NestedRegistration {
            quantifier: {
                let inner = arena.forall(y_sym, qxy).unwrap();
                arena.forall(x_sym, inner).unwrap()
            },
            vars: vec![x_sym, y_sym],
            body: qxy,
            context: None,
        };
        let ground = vec![qab];

        let mut session =
            IncrementalEmatchSession::new_with_nested(&mut arena, &[], &[registration]);
        session.extend_ground(&arena, &ground);
        let tuples = session.match_witness_tuples(None);

        assert_eq!(tuples.len(), 1);
        assert_eq!(
            tuples[0].as_deref(),
            Some([vec![av, bv]].as_slice()),
            "the registration's own trigger fires on the ground application"
        );
        let batches = session.lazy_clause_batches(&mut arena, None);
        assert_eq!(batches.len(), 1);
        assert!(
            batches[0].urgent.is_empty()
                && batches[0].units.is_empty()
                && batches[0].deferred.is_empty()
                && batches[0].instance_certificates.is_empty(),
            "a registration must never yield an instance or a certificate"
        );
    }

    #[test]
    fn registered_instances_must_not_refute_a_satisfiable_query() {
        // SOUNDNESS-NEGATIVE. `f(a) = 1` together with `g = 1 ∨ ∀y. f(y) = 0` is
        // satisfiable (take the left disjunct). Were the registration's instance
        // `f(a) = 0` asserted, the ground set would be `unsat` -- so this returns
        // anything BUT `unsat`.
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let a = arena.declare("a", Sort::Int).unwrap();
        let g = arena.declare("g", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (av, gv, yv) = (arena.var(a), arena.var(g), arena.var(y));
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_is_one = arena.eq(fa, one).unwrap();
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_is_zero = arena.eq(fy, zero).unwrap();
        let inner = arena.forall(y, fy_is_zero).unwrap();
        let g_is_one = arena.eq(gv, one).unwrap();
        let disjunction = arena.or(g_is_one, inner).unwrap();
        let assertions = vec![fa_is_one, disjunction];

        let extraction = extract_nested_universals(&mut arena, &assertions);
        assert_eq!(
            extraction.nested.len(),
            1,
            "the disjunct universal is registered, never asserted"
        );

        let mut stats = QuantifierLoopStats::default();
        let result = prove_quantified_unsat_via_egraph_impl(
            &mut arena,
            &extraction.assertions,
            &extraction.nested,
            &SolverConfig::default(),
            true,
            true,
            &mut stats,
        )
        .unwrap();

        assert!(
            !matches!(result, CheckResult::Unsat),
            "a registration's instances are not consequences; refuting here would \
             be a wrong `unsat`, got {result:?}"
        );
    }

    #[test]
    fn extraction_keeps_a_genuine_top_level_refutation() {
        // The decomposition must not lose reach: `f(a) = 1 ∧ ∀y. f(y) = 0` is
        // still refuted after extraction (the universal is in a conjunctive,
        // hence entailed, position).
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let a = arena.declare("a", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (av, yv) = (arena.var(a), arena.var(y));
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let fa = arena.apply(f, &[av]).unwrap();
        let fa_is_one = arena.eq(fa, one).unwrap();
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_is_zero = arena.eq(fy, zero).unwrap();
        let universal = arena.forall(y, fy_is_zero).unwrap();
        let conjunction = arena.and(fa_is_one, universal).unwrap();

        let extraction = extract_nested_universals(&mut arena, &[conjunction]);
        assert!(extraction.nested.is_empty());

        let mut stats = QuantifierLoopStats::default();
        let result = prove_quantified_unsat_via_egraph_impl(
            &mut arena,
            &extraction.assertions,
            &extraction.nested,
            &SolverConfig::default(),
            true,
            true,
            &mut stats,
        )
        .unwrap();

        assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
    }

    #[test]
    fn nested_layout_and_registration_compose_without_refuting_a_satisfiable_query() {
        // SOUNDNESS-NEGATIVE, slice 1 + slice 2 together.
        //
        //   p(a),  ¬q(a, c),  ∀x. (p(x) ∨ ∃z. ∀y. r(x, z, y) ∧ q(x, y))
        //
        // is satisfiable: interpret `p` as true everywhere and the disjunction
        // never needs its right side. The registered `∀y` is exactly the binder
        // whose instance `q(a, c)` would contradict `¬q(a, c)`, so any leak from
        // registration into the asserted ground set shows up here as a wrong
        // `unsat`. It also exercises the layout's Skolem dependency: `z` becomes
        // a function of `x`, under the preserved nesting.
        let mut arena = TermArena::new();
        let p_fun = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let r_fun = arena
            .declare_fun("r", &[Sort::Int, Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let c_sym = arena.declare("c", Sort::Int).unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let z_sym = arena.declare("z", Sort::Int).unwrap();
        let (av, cv, xv, yv, zv) = (
            arena.var(a_sym),
            arena.var(c_sym),
            arena.var(x_sym),
            arena.var(y_sym),
            arena.var(z_sym),
        );
        let pa = arena.apply(p_fun, &[av]).unwrap();
        let qac = arena.apply(q_fun, &[av, cv]).unwrap();
        let not_qac = arena.not(qac).unwrap();
        let px = arena.apply(p_fun, &[xv]).unwrap();
        let rxzy = arena.apply(r_fun, &[xv, zv, yv]).unwrap();
        let qxy = arena.apply(q_fun, &[xv, yv]).unwrap();
        let inner_body = arena.and(rxzy, qxy).unwrap();
        let all_y = arena.forall(y_sym, inner_body).unwrap();
        let some_z = arena.exists(z_sym, all_y).unwrap();
        let disjunction = arena.or(px, some_z).unwrap();
        let all_x = arena.forall(x_sym, disjunction).unwrap();

        let skolemized = crate::quant_skolemize::skolemize_assertions_with_layout(
            &mut arena,
            &[all_x],
            crate::quant_skolemize::QuantifierLayout::Nested,
        )
        .unwrap();
        assert!(skolemized.changed);

        let mut assertions = vec![pa, not_qac];
        assertions.extend(skolemized.assertions.iter().copied());
        let extraction = extract_nested_universals(&mut arena, &assertions);
        assert_eq!(
            extraction.nested.len(),
            1,
            "the `∀y` under the disjunction is registered, not asserted"
        );

        let mut stats = QuantifierLoopStats::default();
        let result = prove_quantified_unsat_via_egraph_impl(
            &mut arena,
            &extraction.assertions,
            &extraction.nested,
            &SolverConfig::default(),
            true,
            true,
            &mut stats,
        )
        .unwrap();

        assert!(
            !matches!(result, CheckResult::Unsat),
            "the query is satisfiable; got {result:?}"
        );
    }

    /// `(∀x. ¬p(x) ∨ ∀y. q(x, y))`, `p(a)`, `¬q(a, b)` — plus the symbols the
    /// caller asks for. The refutation exists only through the inner `∀y`, which
    /// no top-level prefix reaches: it is exposed by instantiating `x := a`.
    fn staged_nested_shape() -> (TermArena, TermId, TermId, TermId, SymbolId, SymbolId) {
        let mut arena = TermArena::new();
        let p_fun = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let b_sym = arena.declare("b", Sort::Int).unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let (av, bv, xv, yv) = (
            arena.var(a_sym),
            arena.var(b_sym),
            arena.var(x_sym),
            arena.var(y_sym),
        );
        let pa = arena.apply(p_fun, &[av]).unwrap();
        let qab = arena.apply(q_fun, &[av, bv]).unwrap();
        let not_qab = arena.not(qab).unwrap();
        let px = arena.apply(p_fun, &[xv]).unwrap();
        let not_px = arena.not(px).unwrap();
        let qxy = arena.apply(q_fun, &[xv, yv]).unwrap();
        let all_y = arena.forall(y_sym, qxy).unwrap();
        let disjunction = arena.or(not_px, all_y).unwrap();
        let all_x = arena.forall(x_sym, disjunction).unwrap();
        (arena, all_x, pa, not_qab, x_sym, y_sym)
    }

    #[test]
    fn positive_replacement_builds_the_entailed_clause_not_the_bare_instance() {
        // `∀x. (¬p(x) ∨ ∀y. q(x, y))` with `x := a, y := b` yields the clause
        // `¬p(a) ∨ q(a, b)` — entailed. The bare instance `q(a, b)` is NOT, and
        // the constructor must never produce it.
        let (mut arena, owner, _, _, x_sym, y_sym) = staged_nested_shape();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let b_sym = arena.declare("b", Sort::Int).unwrap();
        let (av, bv) = (arena.var(a_sym), arena.var(b_sym));

        let formula =
            positive_instance_formula(&mut arena, owner, &[1], &[x_sym, y_sym], &[av, bv])
                .expect("the disjunctive position is positive");

        let p_fun = arena.find_function("p").unwrap();
        let q_fun = arena.find_function("q").unwrap();
        let pa = arena.apply(p_fun, &[av]).unwrap();
        let not_pa = arena.not(pa).unwrap();
        let qab = arena.apply(q_fun, &[av, bv]).unwrap();
        let expected = arena.or(not_pa, qab).unwrap();
        assert_eq!(formula, expected);
        assert_ne!(formula, qab, "the bare instance is not a consequence");
    }

    #[test]
    fn positive_replacement_keeps_uninstantiated_owner_binders_quantified() {
        // `∀x∀z. (¬p(x) ∨ ¬p(z) ∨ ∀y. q(x, y))` instantiated at `x := a, y := b`
        // must keep `z` universally quantified: dropping it would assert a
        // stronger formula than the owner entails.
        let mut arena = TermArena::new();
        let p_fun = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let b_sym = arena.declare("b", Sort::Int).unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let z_sym = arena.declare("z", Sort::Int).unwrap();
        let (av, bv, xv, yv, zv) = (
            arena.var(a_sym),
            arena.var(b_sym),
            arena.var(x_sym),
            arena.var(y_sym),
            arena.var(z_sym),
        );
        let not_px = {
            let px = arena.apply(p_fun, &[xv]).unwrap();
            arena.not(px).unwrap()
        };
        let z_disjunct = {
            let pz = arena.apply(p_fun, &[zv]).unwrap();
            arena.not(pz).unwrap()
        };
        let qxy = arena.apply(q_fun, &[xv, yv]).unwrap();
        let all_y = arena.forall(y_sym, qxy).unwrap();
        let inner_or = arena.or(z_disjunct, all_y).unwrap();
        let body = arena.or(not_px, inner_or).unwrap();
        let owner = {
            let inner = arena.forall(z_sym, body).unwrap();
            arena.forall(x_sym, inner).unwrap()
        };

        let formula =
            positive_instance_formula(&mut arena, owner, &[1, 1], &[x_sym, y_sym], &[av, bv])
                .expect("the doubly nested disjunction is still positive");
        let (remaining, _) = peel_foralls(&arena, formula);
        assert_eq!(remaining, vec![z_sym], "z must stay universally quantified");
    }

    #[test]
    fn positive_replacement_refuses_a_path_that_crosses_a_binder() {
        // SOUNDNESS-NEGATIVE. `A ∨ ∀u. (¬p(u) ∨ ∀y. q(u, y))` does NOT entail
        // `A ∨ ∀u. (¬p(u) ∨ q(c, d))`: substituting the path binder `u` is only
        // licensed for the `u := c` instance of that disjunct. The walk therefore
        // refuses any step through a `forall`.
        let mut arena = TermArena::new();
        let p_fun = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let flag = arena.declare("flag", Sort::Bool).unwrap();
        let c_sym = arena.declare("c", Sort::Int).unwrap();
        let d_sym = arena.declare("d", Sort::Int).unwrap();
        let u_sym = arena.declare("u", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let (flagv, cv, dv, uv, yv) = (
            arena.var(flag),
            arena.var(c_sym),
            arena.var(d_sym),
            arena.var(u_sym),
            arena.var(y_sym),
        );
        let not_pu = {
            let pu = arena.apply(p_fun, &[uv]).unwrap();
            arena.not(pu).unwrap()
        };
        let quy = arena.apply(q_fun, &[uv, yv]).unwrap();
        let all_y = arena.forall(y_sym, quy).unwrap();
        let inner_or = arena.or(not_pu, all_y).unwrap();
        let all_u = arena.forall(u_sym, inner_or).unwrap();
        let owner = arena.or(flagv, all_u).unwrap();

        // The `∀y` sits at owner argument 1, then *through the `∀u` binder*, then
        // at argument 1 again — a path the constructor must not walk.
        assert!(
            positive_instance_formula(&mut arena, owner, &[1, 0, 1], &[u_sym, y_sym], &[cv, dv])
                .is_none(),
            "a replacement under a path binder is not entailed",
        );
    }

    #[test]
    fn positive_replacement_refuses_partial_and_capturing_substitutions() {
        // SOUNDNESS-NEGATIVE. `∀x∀y. q(x, y)` at a positive position entails an
        // instance only when EVERY inner binder is instantiated (otherwise the
        // remaining name becomes a free symbol, which is not a consequence), and
        // never when a binding mentions a symbol still bound at that position.
        let (mut arena, owner, _, _, x_sym, y_sym) = staged_nested_shape();
        let a_sym = arena.find_symbol("a").unwrap();
        let av = arena.var(a_sym);
        let xv = arena.var(x_sym);

        assert!(
            positive_instance_formula(&mut arena, owner, &[1], &[x_sym], &[av]).is_none(),
            "the inner binder y was left free",
        );
        assert!(
            positive_instance_formula(&mut arena, owner, &[1], &[x_sym, y_sym], &[av, xv])
                .is_none(),
            "binding y to the still-bound x captures",
        );
        assert!(
            positive_instance_formula(&mut arena, owner, &[0], &[x_sym, y_sym], &[av, av])
                .is_none(),
            "argument 0 of the disjunction is not a universal",
        );
        let true_term = arena.bool_const(true);
        assert!(
            positive_instance_formula(&mut arena, owner, &[1], &[x_sym, y_sym], &[av, true_term])
                .is_none(),
            "a Bool binding for an Int binder is a sort violation",
        );
    }

    #[test]
    fn positive_replacement_refuses_a_shadowed_binder() {
        // SOUNDNESS-NEGATIVE. Substitution here is binder-blind, so a name that
        // is re-bound *inside* the region being substituted would capture:
        // `∀x. (¬p(x) ∨ ∀y. (q(x, y) ∧ ∀x. r(x)))` at `x := a` must not rewrite
        // the inner `∀x`'s occurrences. The constructor refuses the shape.
        let mut arena = TermArena::new();
        let p_fun = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let q_fun = arena
            .declare_fun("q", &[Sort::Int, Sort::Int], Sort::Bool)
            .unwrap();
        let r_fun = arena.declare_fun("r", &[Sort::Int], Sort::Bool).unwrap();
        let a_sym = arena.declare("a", Sort::Int).unwrap();
        let b_sym = arena.declare("b", Sort::Int).unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let (av, bv, xv, yv) = (
            arena.var(a_sym),
            arena.var(b_sym),
            arena.var(x_sym),
            arena.var(y_sym),
        );
        let not_px = {
            let px = arena.apply(p_fun, &[xv]).unwrap();
            arena.not(px).unwrap()
        };
        let qxy = arena.apply(q_fun, &[xv, yv]).unwrap();
        let rx = arena.apply(r_fun, &[xv]).unwrap();
        let shadowed = arena.forall(x_sym, rx).unwrap();
        let inner_body = arena.and(qxy, shadowed).unwrap();
        let all_y = arena.forall(y_sym, inner_body).unwrap();
        let disjunction = arena.or(not_px, all_y).unwrap();
        let owner = arena.forall(x_sym, disjunction).unwrap();

        assert!(
            positive_instance_formula(&mut arena, owner, &[1], &[x_sym, y_sym], &[av, bv])
                .is_none(),
            "the inner `∀x` shadows the binder being substituted",
        );
    }

    #[test]
    fn lazy_discovery_refutes_through_a_quantifier_exposed_by_an_instantiation() {
        // The keystone shape. `∀x. (¬p(x) ∨ ∀y. q(x, y))`, `p(a)`, `¬q(a, b)` is
        // unsat, and the only route runs through the inner `∀y` — which is not a
        // consequence on its own and is not reachable until `x := a` is
        // instantiated. Slice 2 registered it and produced nothing; slice 3
        // stages `¬p(a) ∨ q(a, b)` and closes it.
        let (mut arena, all_x, pa, not_qab, _, _) = staged_nested_shape();
        let extraction = extract_nested_universals(&mut arena, &[all_x, pa, not_qab]);
        assert_eq!(extraction.nested.len(), 1);
        assert!(
            extraction.nested[0].context.is_some(),
            "the `∀y` sits under an `or`, a positive position",
        );

        let mut stats = QuantifierLoopStats::default();
        let result = prove_quantified_unsat_via_egraph_impl(
            &mut arena,
            &extraction.assertions,
            &extraction.nested,
            &SolverConfig::default(),
            true,
            true,
            &mut stats,
        )
        .unwrap();
        assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
    }

    #[test]
    fn lazy_discovery_registers_the_universal_an_instantiation_exposes() {
        // The registration `∀y. q(a, y)` does not exist in the assertion set: it
        // appears only inside the instance `¬p(a) ∨ ∀y. q(a, y)`. Scanning that
        // admitted instance is what registers it — the staging a flat prefix
        // cannot express.
        let (mut arena, all_x, pa, not_qab, _, _) = staged_nested_shape();
        let assertions = vec![all_x, pa, not_qab];
        let extraction = extract_nested_universals(&mut arena, &assertions);

        // The instance the active universal produces at `x := a`.
        let instance =
            instantiate_forall_via_egraph(&mut arena, &[pa, not_qab], extraction.assertions[0])
                .into_iter()
                .find(|&term| matches!(arena.node(term), TermNode::App { op: Op::BoolOr, .. }))
                .expect("x := a is matched by p(a)");

        let mut discovery = NestedDiscovery::new(&extraction.assertions);
        let mut retained = HashMap::new();
        retained.insert(
            instance,
            QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                assertion: extraction.assertions[0],
                bindings: vec![arena.var(arena.find_symbol("a").unwrap())],
                instance,
            }),
        );
        let found = discovery.scan(&mut arena, &[instance], &retained);

        assert_eq!(found, 1, "the exposed `∀y. q(a, y)` is registered");
        let registration = &discovery.pending_registrations[0];
        assert_eq!(
            registration.context.as_ref().map(|context| context.owner),
            Some(instance),
            "its owner is the instance that exposed it, not an original assertion",
        );
        assert_eq!(peel_foralls(&arena, registration.quantifier).0.len(), 1);
    }

    #[test]
    fn discovery_never_refutes_a_satisfiable_query_through_a_lazily_found_universal() {
        // SOUNDNESS-NEGATIVE for lazy discovery specifically.
        //
        //   ∀x. (¬p(x) ∨ ∀y. q(x, y)),  ¬p(a),  ¬q(a, b)
        //
        // is satisfiable (nothing forces `q`, because `p` is false at `a`). The
        // lazily discovered `∀y. q(a, y)` sits inside the instance
        // `¬p(a) ∨ ∀y. q(a, y)` and its BARE instance `q(a, b)` would contradict
        // `¬q(a, b)`. Only the clause `¬p(a) ∨ q(a, b)` is entailed, and it is
        // satisfied by `¬p(a)` — so any leak of the bare instance out of
        // discovery shows up right here as a wrong `unsat`.
        let (mut arena, all_x, pa, not_qab, _, _) = staged_nested_shape();
        let not_pa = arena.not(pa).unwrap();
        let extraction = extract_nested_universals(&mut arena, &[all_x, not_pa, not_qab]);

        let mut stats = QuantifierLoopStats::default();
        let result = prove_quantified_unsat_via_egraph_impl(
            &mut arena,
            &extraction.assertions,
            &extraction.nested,
            &SolverConfig::default(),
            true,
            true,
            &mut stats,
        )
        .unwrap();
        assert!(
            !matches!(result, CheckResult::Unsat),
            "the query is satisfiable; got {result:?}"
        );
    }

    #[test]
    fn discovery_refuses_an_owner_outside_the_trusted_set() {
        // SOUNDNESS-NEGATIVE. Staging is only ever licensed from a formula the
        // loop already checked. An owner that is neither an assertion nor a
        // retained derivation must be refused outright — fail-closed, counted.
        let (mut arena, all_x, pa, not_qab, x_sym, y_sym) = staged_nested_shape();
        let extraction = extract_nested_universals(&mut arena, &[all_x, pa, not_qab]);
        let mut matcher =
            IncrementalEmatchSession::new_with_nested(&mut arena, &[], &extraction.nested);
        // A forged tuple attributed to the registration, with the owner removed
        // from every trust source.
        matcher.pending_positive.push((
            0,
            vec![
                arena.var(arena.find_symbol("a").unwrap()),
                arena.var(arena.find_symbol("b").unwrap()),
            ],
        ));
        assert_eq!(matcher.quantifiers[0].vars, vec![x_sym, y_sym]);

        let mut discovery = NestedDiscovery::new(&[]);
        let mut seen = HashSet::new();
        let mut ground = Vec::new();
        let mut generations = TermGenerations::seed_sources(&arena, &[]);
        let (admitted, promoted) = discovery.stage(
            &mut arena,
            &mut matcher,
            &HashMap::new(),
            &mut seen,
            &mut ground,
            &mut generations,
        );
        assert!(admitted.is_empty() && promoted.is_empty());
        assert_eq!(discovery.rejected, 1, "the untrusted owner was refused");
        assert!(ground.is_empty());
    }
}
