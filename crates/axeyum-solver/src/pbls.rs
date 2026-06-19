//! Propositional/word-level local search for bit-vectors (Track 1, P1.7).
//!
//! A stochastic local-search (SLS) engine in the `WalkSAT` family, working at the
//! word level over the typed IR: it keeps a concrete assignment to every Bool /
//! bit-vector variable, scores it by how many top-level assertions the ground
//! evaluator falsifies, and repeatedly nudges a variable in some unsatisfied
//! assertion toward a better score — greedy most of the time, a random walk now
//! and then to escape local minima — restarting from a fresh random assignment
//! when a try stalls.
//!
//! It is a **portfolio member for satisfiable instances**: bit-blasting a hard
//! `sat` query to a million-clause CNF can drown CDCL, while local search often
//! lands on a model quickly. It is **incomplete and one-sided**: it returns
//! [`CheckResult::Sat`] *only* with a model the evaluator confirms satisfies
//! every original assertion (so a `sat` answer is always correct), and otherwise
//! [`CheckResult::Unknown`] — it never reports `unsat` (local search cannot
//! refute). Deterministic: a fixed seed and explicit flip/restart budgets, no
//! clock- or service-derived randomness.
//!
//! Scope: Bool and `BitVec(w)` with `w ≤ 128` (a value fits one `u128`). A query
//! mentioning wider vectors, arrays, uninterpreted functions, or arithmetic
//! sorts — anything the ground evaluator cannot evaluate over a plain variable
//! assignment — yields `Unknown` rather than a wrong answer.

use std::collections::{HashMap, HashSet};
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use axeyum_ir::{
    Assignment, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval, eval_with_memo,
};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
use crate::model::Model;

/// Outcome of a local-search run: the (one-sided) result plus search effort.
#[derive(Debug, Clone)]
pub struct LocalSearchOutcome {
    /// `Sat` (model evaluator-verified against every assertion) or `Unknown`;
    /// never `Unsat`.
    pub result: CheckResult,
    /// Total variable flips performed.
    pub flips: usize,
    /// Random restarts performed.
    pub restarts: usize,
}

/// A searchable variable and its kind.
#[derive(Clone, Copy)]
enum VarKind {
    Bool,
    Bv(u32),
}

struct Var {
    sym: SymbolId,
    kind: VarKind,
}

/// Fixed seed — determinism is a public API promise; randomness is varied only by
/// the search trajectory, never by a clock or service.
const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
/// Per-variable bit-flip candidates considered in a greedy step are capped at
/// this width so a step stays cheap on wide vectors.
const GREEDY_BIT_CAP: u32 = 32;
/// Random-walk probability, in percent (`WalkSAT` noise).
const NOISE_PCT: u64 = 30;

/// Deterministic xorshift PRNG.
fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// A pseudo-random index in `0..n` (the codebase's `try_from`-based idiom; no
/// truncating `as` cast).
fn pick(state: &mut u64, n: usize) -> usize {
    usize::try_from(xorshift(state)).unwrap_or(0) % n
}

/// Diagnostic count to `f64` for [`SolveStats`]; the precision loss is irrelevant
/// for flip/restart counters.
#[allow(clippy::cast_precision_loss)]
fn count_f64(n: usize) -> f64 {
    n as f64
}

/// Low-`width` mask (`width ≤ 128`).
fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Collects the supported searchable variables; returns `None` if any free
/// symbol has a sort this engine cannot search (wide BV, arrays, arithmetic, …).
fn collect_vars(arena: &TermArena, assertions: &[TermId]) -> Option<Vec<Var>> {
    let mut seen: HashSet<SymbolId> = HashSet::new();
    let mut order: Vec<SymbolId> = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut visited: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if seen.insert(*s) => order.push(*s),
            TermNode::App { args, .. } => {
                for &a in &args.clone() {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    let mut vars = Vec::with_capacity(order.len());
    for sym in order {
        let kind = match arena.symbol(sym).1 {
            Sort::Bool => VarKind::Bool,
            Sort::BitVec(w) if w <= 128 => VarKind::Bv(w),
            _ => return None,
        };
        vars.push(Var { sym, kind });
    }
    Some(vars)
}

/// Evaluates `term` to a Boolean under `asg`, or `None` if it does not evaluate
/// to a Bool (e.g. an unsupported construct the evaluator rejects).
fn eval_bool(arena: &TermArena, term: TermId, asg: &Assignment) -> Option<bool> {
    match eval(arena, term, asg) {
        Ok(Value::Bool(b)) => Some(b),
        _ => None,
    }
}

/// Result of one local-search step.
enum Step {
    /// A variable was changed (a flip).
    Moved,
    /// The chosen unsatisfied assertion has no searchable variable — this try
    /// cannot fix it, so the caller should restart.
    Stuck,
}

/// Incremental local-search state: a current assignment, the per-assertion
/// satisfaction cache, the unsatisfied count, and a variable→assertions index so
/// a flip only re-evaluates the assertions that mention the moved variable
/// (rather than the whole formula).
struct Search<'a> {
    arena: &'a TermArena,
    assertions: &'a [TermId],
    vars: &'a [Var],
    /// For each variable (index into `vars`), the assertions that mention it.
    var_assertions: Vec<Vec<usize>>,
    /// For each assertion, the searchable variables (indices into `vars`) in it.
    assertion_vars: Vec<Vec<usize>>,
    /// Per-assertion current satisfaction under `asg`.
    sat: Vec<bool>,
    /// Count of currently-falsified assertions.
    unsat_count: usize,
    asg: Assignment,
    state: u64,
    /// **Incremental evaluation cache**: every assertion subterm's value under the
    /// current `asg`. A flip recomputes only the changed variable's *cone* (the
    /// subterms that transitively depend on it) instead of re-walking whole
    /// assertions — the dominant per-flip cost otherwise. Valid for `asg`; the cone
    /// invalidation below keeps it so.
    memo: HashMap<TermId, Value>,
    /// Child→parent edges over the union assertion DAG, for cone discovery.
    parents: HashMap<TermId, Vec<TermId>>,
    /// The interned symbol `TermId` of each variable (root of its cone).
    var_term: Vec<TermId>,
    /// Lazily-computed cone (the variable's symbol node + all transitive ancestors)
    /// per variable — the exact set of `memo` entries a flip of that variable
    /// invalidates. Computed on first flip of each variable (so setup stays
    /// `O(dag)`, not `O(vars × dag)`).
    var_cone: Vec<Option<Vec<TermId>>>,
}

impl<'a> Search<'a> {
    fn new(arena: &'a TermArena, assertions: &'a [TermId], vars: &'a [Var]) -> Self {
        let assertion_vars: Vec<Vec<usize>> = assertions
            .iter()
            .map(|&t| {
                let mut v = Vec::new();
                collect_clause_vars(arena, t, vars, &mut v);
                v
            })
            .collect();
        let mut var_assertions = vec![Vec::new(); vars.len()];
        for (a, vis) in assertion_vars.iter().enumerate() {
            for &vi in vis {
                var_assertions[vi].push(a);
            }
        }
        // Child→parent edges over the union assertion DAG (one O(dag) pass), so a
        // flip's cone can be discovered by walking up from the variable's node; the
        // same pass records each symbol's (already-interned) `TermId`.
        let mut parents: HashMap<TermId, Vec<TermId>> = HashMap::new();
        let mut sym_term: HashMap<SymbolId, TermId> = HashMap::new();
        {
            let mut visited: HashSet<TermId> = HashSet::new();
            let mut stack: Vec<TermId> = assertions.to_vec();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match arena.node(t) {
                    TermNode::Symbol(s) => {
                        sym_term.insert(*s, t);
                    }
                    TermNode::App { args, .. } => {
                        for &a in &args.clone() {
                            parents.entry(a).or_default().push(t);
                            stack.push(a);
                        }
                    }
                    _ => {}
                }
            }
        }
        let var_term: Vec<TermId> = vars
            .iter()
            .map(|v| sym_term[&v.sym]) // every searchable var occurs in the assertions
            .collect();
        let var_cone = vec![None; vars.len()];
        Self {
            arena,
            assertions,
            vars,
            var_assertions,
            assertion_vars,
            sat: vec![false; assertions.len()],
            unsat_count: 0,
            asg: Assignment::new(),
            state: SEED,
            memo: HashMap::new(),
            parents,
            var_term,
            var_cone,
        }
    }

    /// The cone of variable `vi`: its symbol node plus every subterm that
    /// transitively depends on it (discovered by walking parent edges up from the
    /// variable's node). Computed once per variable and cached. This is exactly the
    /// set of `memo` entries a flip of `vi` invalidates.
    fn cone(&mut self, vi: usize) -> &[TermId] {
        if self.var_cone[vi].is_none() {
            let mut seen: HashSet<TermId> = HashSet::new();
            let mut out: Vec<TermId> = Vec::new();
            let mut stack = vec![self.var_term[vi]];
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                out.push(t);
                if let Some(ps) = self.parents.get(&t) {
                    stack.extend(ps.iter().copied());
                }
            }
            self.var_cone[vi] = Some(out);
        }
        self.var_cone[vi].as_deref().expect("cone just computed")
    }

    /// Recomputes the full satisfaction cache (after a fresh random assignment).
    fn recompute(&mut self) {
        // A fresh assignment invalidates the whole cache; rebuild it in one pass
        // (each assertion root, sharing subterms through the memo).
        self.memo.clear();
        self.unsat_count = 0;
        for a in 0..self.assertions.len() {
            let t = self.assertions[a];
            let s =
                eval_with_memo(self.arena, t, &self.asg, &mut self.memo) == Ok(Value::Bool(true));
            self.sat[a] = s;
            if !s {
                self.unsat_count += 1;
            }
        }
    }

    /// Independent full re-verification (the sound `Sat` gate, robust to any
    /// incremental-cache drift).
    fn all_satisfied(&self) -> bool {
        self.assertions
            .iter()
            .all(|&t| eval_bool(self.arena, t, &self.asg) == Some(true))
    }

    /// A random currently-unsatisfied assertion, or `None` if all are satisfied.
    fn random_unsat(&mut self) -> Option<usize> {
        let unsat: Vec<usize> = (0..self.assertions.len())
            .filter(|&a| !self.sat[a])
            .collect();
        if unsat.is_empty() {
            return None;
        }
        Some(unsat[pick(&mut self.state, unsat.len())])
    }

    /// The unsatisfied count that would result from setting `vars[vi] := cand`,
    /// re-evaluating only the affected assertions (the variable's incidence set).
    fn score(&mut self, vi: usize, cand: &Value) -> usize {
        let sym = self.vars[vi].sym;
        let old = self.asg.get(sym).expect("searched variable is assigned");
        // Save the cone's current cached values, apply the candidate, recompute only
        // the cone (incrementally, through the persistent memo), tally the affected
        // assertions' satisfaction delta, then restore exactly — `score` is a
        // hypothetical, so it must leave `asg`/`memo` untouched.
        let cone: Vec<TermId> = self.cone(vi).to_vec();
        let saved: Vec<(TermId, Option<Value>)> = cone
            .iter()
            .map(|&t| (t, self.memo.get(&t).cloned()))
            .collect();
        for &t in &cone {
            self.memo.remove(&t);
        }
        self.asg.set(sym, cand.clone());
        let mut count = self.unsat_count;
        for &a in &self.var_assertions[vi] {
            let t = self.assertions[a];
            let now =
                eval_with_memo(self.arena, t, &self.asg, &mut self.memo) == Ok(Value::Bool(true));
            if now != self.sat[a] {
                if now {
                    count -= 1;
                } else {
                    count += 1;
                }
            }
        }
        self.asg.set(sym, old);
        for (t, v) in saved {
            match v {
                Some(v) => {
                    self.memo.insert(t, v);
                }
                None => {
                    self.memo.remove(&t);
                }
            }
        }
        count
    }

    /// Commits `vars[vi] := cand`, updating the affected assertions' cache and the
    /// unsatisfied count.
    fn commit(&mut self, vi: usize, cand: Value) {
        let sym = self.vars[vi].sym;
        // Invalidate the variable's cone in the persistent memo, apply the move, and
        // re-evaluate the affected assertions — `eval_with_memo` recomputes only the
        // invalidated cone, reusing every other subterm from the cache.
        let cone: Vec<TermId> = self.cone(vi).to_vec();
        for &t in &cone {
            self.memo.remove(&t);
        }
        self.asg.set(sym, cand);
        let affected = self.var_assertions[vi].clone();
        for a in affected {
            let t = self.assertions[a];
            let now =
                eval_with_memo(self.arena, t, &self.asg, &mut self.memo) == Ok(Value::Bool(true));
            if now != self.sat[a] {
                if now {
                    self.unsat_count -= 1;
                } else {
                    self.unsat_count += 1;
                }
                self.sat[a] = now;
            }
        }
    }

    /// One `WalkSAT` step on a random unsatisfied assertion: a random flip with
    /// [`NOISE_PCT`] probability, otherwise the greedy move (over the in-clause
    /// variables' candidates) minimizing the unsatisfied count, ties broken
    /// randomly. Incremental scoring touches only affected assertions.
    fn step(&mut self) -> Step {
        let Some(a) = self.random_unsat() else {
            return Step::Moved;
        };
        let in_clause = self.assertion_vars[a].clone();
        if in_clause.is_empty() {
            return Step::Stuck;
        }
        if xorshift(&mut self.state) % 100 < NOISE_PCT {
            let vi = in_clause[pick(&mut self.state, in_clause.len())];
            let current = self.asg.get(self.vars[vi].sym).expect("assigned");
            let cands = candidate_values(self.vars[vi].kind, &current, &mut self.state);
            if !cands.is_empty() {
                let c = cands[pick(&mut self.state, cands.len())].clone();
                self.commit(vi, c);
            }
            return Step::Moved;
        }
        let mut best: Option<(usize, usize, Value)> = None; // (score, vi, value)
        for &vi in &in_clause {
            let current = self.asg.get(self.vars[vi].sym).expect("assigned");
            for cand in candidate_values(self.vars[vi].kind, &current, &mut self.state) {
                let sc = self.score(vi, &cand);
                let better = match &best {
                    None => true,
                    Some((bs, _, _)) => {
                        sc < *bs || (sc == *bs && xorshift(&mut self.state) & 1 == 0)
                    }
                };
                if better {
                    best = Some((sc, vi, cand));
                }
            }
        }
        if let Some((_, vi, value)) = best {
            self.commit(vi, value);
        }
        Step::Moved
    }
}

/// Assigns every variable a fresh random value.
fn randomize(asg: &mut Assignment, vars: &[Var], state: &mut u64) {
    for v in vars {
        match v.kind {
            VarKind::Bool => asg.set(v.sym, Value::Bool(xorshift(state) & 1 == 0)),
            VarKind::Bv(w) => {
                let lo = u128::from(xorshift(state));
                let hi = u128::from(xorshift(state));
                let value = ((hi << 64) | lo) & mask(w);
                asg.set(v.sym, Value::Bv { width: w, value });
            }
        }
    }
}

/// Builds the candidate replacement values for a single variable (the moves a
/// greedy or random step may apply).
fn candidate_values(kind: VarKind, current: &Value, state: &mut u64) -> Vec<Value> {
    match (kind, current) {
        (VarKind::Bool, Value::Bool(b)) => vec![Value::Bool(!b)],
        (VarKind::Bv(w), Value::Bv { value, .. }) => {
            let m = mask(w);
            let mut moves = Vec::new();
            for bit in 0..w.min(GREEDY_BIT_CAP) {
                moves.push(Value::Bv {
                    width: w,
                    value: (value ^ (1u128 << bit)) & m,
                });
            }
            // A couple of word-level nudges and a random jump.
            moves.push(Value::Bv {
                width: w,
                value: value.wrapping_add(1) & m,
            });
            moves.push(Value::Bv {
                width: w,
                value: value.wrapping_sub(1) & m,
            });
            let lo = u128::from(xorshift(state));
            let hi = u128::from(xorshift(state));
            moves.push(Value::Bv {
                width: w,
                value: ((hi << 64) | lo) & m,
            });
            moves
        }
        _ => Vec::new(),
    }
}

/// Builds a [`Model`] from the satisfying assignment over the searched variables.
fn model_from(asg: &Assignment, vars: &[Var]) -> Model {
    let mut model = Model::new();
    for v in vars {
        if let Some(value) = asg.get(v.sym) {
            model.set(v.sym, value);
        }
    }
    model
}

#[cfg(not(target_arch = "wasm32"))]
fn past(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}
#[cfg(target_arch = "wasm32")]
fn past(_deadline: Option<()>) -> bool {
    false
}

/// Runs word-level local search on `assertions` (see module docs).
///
/// # Errors
///
/// Does not currently return [`SolverError`]; the signature matches the solver
/// family for uniformity.
pub fn solve_local_search(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<LocalSearchOutcome, SolverError> {
    #[cfg(not(target_arch = "wasm32"))]
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    #[cfg(target_arch = "wasm32")]
    let deadline: Option<()> = None;

    let unknown = |reason: &str, flips, restarts| LocalSearchOutcome {
        result: CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!("local search: {reason}"),
        }),
        flips,
        restarts,
    };

    let Some(vars) = collect_vars(arena, assertions) else {
        return Ok(unknown(
            "query has a sort local search cannot evaluate",
            0,
            0,
        ));
    };
    // An empty conjunction is trivially satisfiable.
    if assertions.is_empty() {
        return Ok(LocalSearchOutcome {
            result: CheckResult::Sat(Model::new()),
            flips: 0,
            restarts: 0,
        });
    }
    // Probe once: an assertion the evaluator cannot reduce to a Bool (arrays,
    // uninterpreted functions, …) is out of scope.
    let mut probe = Assignment::new();
    let mut probe_state = SEED;
    randomize(&mut probe, &vars, &mut probe_state);
    if assertions
        .iter()
        .any(|&t| eval_bool(arena, t, &probe).is_none())
    {
        return Ok(unknown(
            "query has a construct the evaluator cannot reduce",
            0,
            0,
        ));
    }

    // Budgets scale with the problem; bounded so the engine stays a quick portfolio
    // probe rather than an open-ended loop.
    let span = vars.len() + assertions.len();
    let max_tries = 25usize;
    let max_flips = 200 + 40 * span;

    let mut search = Search::new(arena, assertions, &vars);
    let mut flips = 0usize;

    for restart in 0..max_tries {
        randomize(&mut search.asg, &vars, &mut search.state);
        search.recompute();
        for _ in 0..max_flips {
            if past(deadline) {
                return Ok(unknown("timeout", flips, restart));
            }
            if search.unsat_count == 0 && search.all_satisfied() {
                return Ok(LocalSearchOutcome {
                    result: CheckResult::Sat(model_from(&search.asg, &vars)),
                    flips,
                    restarts: restart,
                });
            }
            match search.step() {
                Step::Moved => flips += 1,
                Step::Stuck => break, // ground-false assertion — restart.
            }
        }
    }
    Ok(unknown("flip/restart budget exhausted", flips, max_tries))
}

/// Collects (deduplicated, by membership) the indices into `vars` of the
/// variables occurring in `term`.
fn collect_clause_vars(arena: &TermArena, term: TermId, vars: &[Var], out: &mut Vec<usize>) {
    let index: HashMap<SymbolId, usize> =
        vars.iter().enumerate().map(|(i, v)| (v.sym, i)).collect();
    let mut present = vec![false; vars.len()];
    let mut stack = vec![term];
    let mut visited: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) => {
                if let Some(&i) = index.get(s) {
                    if !present[i] {
                        present[i] = true;
                        out.push(i);
                    }
                }
            }
            TermNode::App { args, .. } => {
                for &a in &args.clone() {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
}

/// Local-search portfolio backend (satisfiable-only; `Unknown` otherwise).
#[derive(Debug, Default)]
pub struct PblsBackend {
    stats: Option<SolveStats>,
}

impl PblsBackend {
    /// Creates a new local-search backend.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl SolverBackend for PblsBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "axeyum-pbls (word-level WalkSAT, sat-only)".to_owned(),
            produces_models: true,
            complete: false,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let outcome = solve_local_search(arena, assertions, config)?;
        let mut stats = SolveStats::default();
        stats
            .backend
            .push(("pbls_flips".to_owned(), count_f64(outcome.flips)));
        stats
            .backend
            .push(("pbls_restarts".to_owned(), count_f64(outcome.restarts)));
        self.stats = Some(stats);
        Ok(outcome.result)
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}
