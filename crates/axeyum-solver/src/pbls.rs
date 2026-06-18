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

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

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

/// Number of assertions currently falsified (a `None` evaluation counts as
/// unsatisfied so the search keeps moving; the final `Sat` gate still requires a
/// genuine all-true model).
fn unsatisfied(arena: &TermArena, assertions: &[TermId], asg: &Assignment) -> Vec<usize> {
    assertions
        .iter()
        .enumerate()
        .filter(|&(_, &t)| eval_bool(arena, t, asg) != Some(true))
        .map(|(i, _)| i)
        .collect()
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

    let mut state = SEED;
    let mut asg = Assignment::new();
    let mut flips = 0usize;

    for restart in 0..max_tries {
        randomize(&mut asg, &vars, &mut state);
        for _ in 0..max_flips {
            if past(deadline) {
                return Ok(unknown("timeout", flips, restart));
            }
            let unsat = unsatisfied(arena, assertions, &asg);
            if unsat.is_empty() {
                return Ok(LocalSearchOutcome {
                    result: CheckResult::Sat(model_from(&asg, &vars)),
                    flips,
                    restarts: restart,
                });
            }
            // Pick a random unsatisfied assertion and the searchable variables in it.
            let chosen = unsat[pick(&mut state, unsat.len())];
            let mut in_clause: Vec<usize> = Vec::new();
            collect_clause_vars(arena, assertions[chosen], &vars, &mut in_clause);
            if in_clause.is_empty() {
                break; // ground-false assertion; this try cannot fix it — restart.
            }
            flips += 1;
            apply_move(arena, assertions, &vars, &in_clause, &mut asg, &mut state);
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

/// Applies one move: with [`NOISE_PCT`] probability a random flip of a random
/// in-clause variable, otherwise the greedy move (over all in-clause variables'
/// candidates) minimizing the total unsatisfied count, ties broken randomly.
fn apply_move(
    arena: &TermArena,
    assertions: &[TermId],
    vars: &[Var],
    in_clause: &[usize],
    asg: &mut Assignment,
    state: &mut u64,
) {
    if xorshift(state) % 100 < NOISE_PCT {
        let vi = in_clause[pick(state, in_clause.len())];
        let var = &vars[vi];
        let current = asg.get(var.sym).expect("searched variable is assigned");
        let cands = candidate_values(var.kind, &current, state);
        if !cands.is_empty() {
            let c = cands[pick(state, cands.len())].clone();
            asg.set(var.sym, c);
        }
        return;
    }
    // Greedy: evaluate every candidate of every in-clause variable.
    let mut best: Option<(usize, SymbolId, Value)> = None; // (score, sym, value)
    for &vi in in_clause {
        let var = &vars[vi];
        let current = asg.get(var.sym).expect("searched variable is assigned");
        for cand in candidate_values(var.kind, &current, state) {
            asg.set(var.sym, cand.clone());
            let score = unsatisfied(arena, assertions, asg).len();
            asg.set(var.sym, current.clone());
            let better = match &best {
                None => true,
                Some((bs, _, _)) => score < *bs || (score == *bs && xorshift(state) & 1 == 0),
            };
            if better {
                best = Some((score, var.sym, cand));
            }
        }
    }
    if let Some((_, sym, value)) = best {
        asg.set(sym, value);
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
