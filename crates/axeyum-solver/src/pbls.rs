//! Propositional/word-level local search for bit-vectors (Track 1, P1.7).
//!
//! A stochastic local-search (SLS) engine in the `WalkSAT` family, working at the
//! word level over the typed IR: it keeps a concrete assignment to every Bool /
//! bit-vector / integer variable, scores it by how many top-level assertions the
//! ground evaluator falsifies, and repeatedly nudges a variable in some unsatisfied
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
//! Scope: Bool, `Int`, and `BitVec(w)` with `w ≤ 128` (a value fits one `u128`).
//! Integer moves are deliberately finite and constant-guided, so this remains a
//! heuristic model finder rather than an arithmetic decision procedure. A query
//! mentioning wider vectors, arrays, uninterpreted functions, or real arithmetic
//! — anything the ground evaluator cannot evaluate over a plain variable
//! assignment — yields `Unknown` rather than a wrong answer.

use std::collections::{HashMap, HashSet};
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use axeyum_ir::{
    Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval, eval_with_memo,
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
    Int,
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
/// Maximum number of integer constants carried into one move's candidate set.
const INT_CONST_CANDIDATE_CAP: usize = 24;
/// Maximum assertion-local repair candidates for one variable in one greedy step.
const LOCAL_REPAIR_CANDIDATE_CAP: usize = 32;
/// Maximum assertion DAG size for structural Boolean scoring. Larger generated
/// formulas use the old root-truth score so a single local-search move cannot
/// spend the whole portfolio budget walking a massive Boolean DAG repeatedly.
const STRUCTURAL_COST_NODE_CAP: usize = 512;
const STRUCTURAL_COST_VAR_CAP: usize = 8;
/// Wider OR-shaped assertions get a one-step structural tie-break only when
/// they are currently selected. This exposes gradients for generated
/// disjunctions of small branches without making every assertion's persistent
/// score expensive.
const FOCUSED_OR_VAR_CAP: usize = 96;
const FOCUSED_OR_BRANCH_CAP: usize = 64;
const FOCUSED_OR_BRANCH_REPAIR_CAP: usize = 32;

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
            Sort::Int => VarKind::Int,
            _ => return None,
        };
        vars.push(Var { sym, kind });
    }
    Some(vars)
}

fn collect_int_constants(arena: &TermArena, assertions: &[TermId]) -> Vec<i128> {
    let mut constants = vec![0, 1, -1];
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut visited: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::IntConst(value) => {
                constants.push(*value);
                if let Some(next) = value.checked_add(1) {
                    constants.push(next);
                }
                if let Some(prev) = value.checked_sub(1) {
                    constants.push(prev);
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
    constants.sort_unstable();
    constants.dedup();
    constants
}

/// Evaluates `term` to a Boolean under `asg`, or `None` if it does not evaluate
/// to a Bool (e.g. an unsupported construct the evaluator rejects).
fn eval_bool(arena: &TermArena, term: TermId, asg: &Assignment) -> Option<bool> {
    match eval(arena, term, asg) {
        Ok(Value::Bool(b)) => Some(b),
        _ => None,
    }
}

fn eval_bool_memo(
    arena: &TermArena,
    term: TermId,
    asg: &Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> Option<bool> {
    match eval_with_memo(arena, term, asg, memo) {
        Ok(Value::Bool(value)) => Some(value),
        _ => None,
    }
}

/// A finite structural cost for making `term` evaluate to `desired`.
///
/// Boolean connectives expose useful local-search gradients inside generated
/// formula DAGs. Theory atoms remain black boxes: if the evaluator says the atom
/// already has the desired truth value its cost is 0, otherwise 1. This is a
/// heuristic score only; returned `sat` models are still independently replayed.
fn bool_cost(
    arena: &TermArena,
    term: TermId,
    desired: bool,
    asg: &Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> usize {
    let TermNode::App { op, args } = arena.node(term) else {
        return atom_bool_cost(arena, term, desired, asg, memo);
    };
    match op {
        Op::BoolNot => bool_cost(arena, args[0], !desired, asg, memo),
        Op::BoolAnd if desired => args
            .iter()
            .map(|&arg| bool_cost(arena, arg, true, asg, memo))
            .sum(),
        Op::BoolAnd => args
            .iter()
            .map(|&arg| bool_cost(arena, arg, false, asg, memo))
            .min()
            .unwrap_or(1),
        Op::BoolOr if desired => args
            .iter()
            .map(|&arg| bool_cost(arena, arg, true, asg, memo))
            .min()
            .unwrap_or(1),
        Op::BoolOr => args
            .iter()
            .map(|&arg| bool_cost(arena, arg, false, asg, memo))
            .sum(),
        Op::BoolImplies if desired => bool_cost(arena, args[0], false, asg, memo)
            .min(bool_cost(arena, args[1], true, asg, memo)),
        Op::BoolImplies => {
            bool_cost(arena, args[0], true, asg, memo) + bool_cost(arena, args[1], false, asg, memo)
        }
        Op::BoolXor => bool_pair_cost(arena, args[0], args[1], !desired, asg, memo),
        Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
            bool_pair_cost(arena, args[0], args[1], desired, asg, memo)
        }
        Op::Ite if arena.sort_of(term) == Sort::Bool => {
            let then_cost = bool_cost(arena, args[0], true, asg, memo)
                + bool_cost(arena, args[1], desired, asg, memo);
            let else_cost = bool_cost(arena, args[0], false, asg, memo)
                + bool_cost(arena, args[2], desired, asg, memo);
            then_cost.min(else_cost)
        }
        _ => atom_bool_cost(arena, term, desired, asg, memo),
    }
}

fn bool_pair_cost(
    arena: &TermArena,
    lhs: TermId,
    rhs: TermId,
    equal: bool,
    asg: &Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> usize {
    let same_true = bool_cost(arena, lhs, true, asg, memo) + bool_cost(arena, rhs, true, asg, memo);
    let same_false =
        bool_cost(arena, lhs, false, asg, memo) + bool_cost(arena, rhs, false, asg, memo);
    let diff_lhs = bool_cost(arena, lhs, true, asg, memo) + bool_cost(arena, rhs, false, asg, memo);
    let diff_rhs = bool_cost(arena, lhs, false, asg, memo) + bool_cost(arena, rhs, true, asg, memo);
    if equal {
        same_true.min(same_false)
    } else {
        diff_lhs.min(diff_rhs)
    }
}

fn atom_bool_cost(
    arena: &TermArena,
    term: TermId,
    desired: bool,
    asg: &Assignment,
    memo: &mut HashMap<TermId, Value>,
) -> usize {
    match eval_bool_memo(arena, term, asg, memo) {
        Some(value) if value == desired => 0,
        _ => 1,
    }
}

fn structural_cost_enabled(arena: &TermArena, term: TermId) -> bool {
    let mut visited = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if visited.len() > STRUCTURAL_COST_NODE_CAP {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn focused_or_cost_enabled(arena: &TermArena, term: TermId, var_count: usize) -> bool {
    if var_count <= STRUCTURAL_COST_VAR_CAP || var_count > FOCUSED_OR_VAR_CAP {
        return false;
    }
    matches!(arena.node(term), TermNode::App { op: Op::BoolOr, .. })
        && structural_cost_enabled(arena, term)
}

fn collect_or_branches(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => {
            collect_or_branches(arena, args[0], out);
            collect_or_branches(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn collect_and_literals(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            collect_and_literals(arena, args[0], out);
            collect_and_literals(arena, args[1], out);
        }
        _ => out.push(term),
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
    /// Whether each assertion is small enough for structural Boolean scoring.
    structural_cost: Vec<bool>,
    /// Whether each assertion is a bounded, wider OR that should get selected
    /// branch-repair tie-breaks.
    focused_or_cost: Vec<bool>,
    int_constants: Vec<i128>,
    /// Per-assertion current structural Boolean cost under `asg`.
    cost: Vec<usize>,
    /// Sum of the current per-assertion costs.
    total_cost: usize,
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
    fn new(
        arena: &'a TermArena,
        assertions: &'a [TermId],
        vars: &'a [Var],
        int_constants: Vec<i128>,
    ) -> Self {
        let assertion_vars: Vec<Vec<usize>> = assertions
            .iter()
            .map(|&t| {
                let mut v = Vec::new();
                collect_clause_vars(arena, t, vars, &mut v);
                v
            })
            .collect();
        let structural_cost = assertions
            .iter()
            .zip(assertion_vars.iter())
            .map(|(&t, vars)| {
                vars.len() <= STRUCTURAL_COST_VAR_CAP && structural_cost_enabled(arena, t)
            })
            .collect();
        let focused_or_cost = assertions
            .iter()
            .zip(assertion_vars.iter())
            .map(|(&t, vars)| focused_or_cost_enabled(arena, t, vars.len()))
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
            structural_cost,
            focused_or_cost,
            int_constants,
            cost: vec![0; assertions.len()],
            total_cost: 0,
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
        self.total_cost = 0;
        for a in 0..self.assertions.len() {
            let cost = self.assertion_cost(a);
            self.cost[a] = cost;
            self.total_cost += cost;
        }
    }

    fn assertion_cost(&mut self, a: usize) -> usize {
        let t = self.assertions[a];
        if self.structural_cost[a] {
            bool_cost(self.arena, t, true, &self.asg, &mut self.memo)
        } else {
            atom_bool_cost(self.arena, t, true, &self.asg, &mut self.memo)
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
            .filter(|&a| self.cost[a] > 0)
            .collect();
        if unsat.is_empty() {
            return None;
        }
        let focused: Vec<usize> = unsat
            .iter()
            .copied()
            .filter(|&a| self.focused_or_cost[a])
            .collect();
        if !focused.is_empty() {
            return Some(focused[pick(&mut self.state, focused.len())]);
        }
        Some(unsat[pick(&mut self.state, unsat.len())])
    }

    /// The structural cost that would result from setting `vars[vi] := cand`,
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
        let mut total = self.total_cost;
        let affected = self.var_assertions[vi].clone();
        for a in affected {
            let now = self.assertion_cost(a);
            total = total - self.cost[a] + now;
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
        total
    }

    /// The selected assertion's structural cost under a hypothetical move.
    ///
    /// This is used only as a tie-break for bounded OR-shaped assertions whose
    /// persistent score is intentionally the cheap root-truth bit. It lets a move
    /// that satisfies one conjunct inside an OR branch beat a completely flat
    /// no-op, while the accepted `sat` path still requires full replay.
    fn focused_score(&mut self, a: usize, vi: usize, cand: &Value) -> usize {
        let sym = self.vars[vi].sym;
        let old = self.asg.get(sym).expect("searched variable is assigned");
        let cone: Vec<TermId> = self.cone(vi).to_vec();
        let saved: Vec<(TermId, Option<Value>)> = cone
            .iter()
            .map(|&t| (t, self.memo.get(&t).cloned()))
            .collect();
        for &t in &cone {
            self.memo.remove(&t);
        }
        self.asg.set(sym, cand.clone());
        let focus = bool_cost(
            self.arena,
            self.assertions[a],
            true,
            &self.asg,
            &mut self.memo,
        );
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
        focus
    }

    /// Commits `vars[vi] := cand`, updating the affected assertions' cost cache.
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
            let now = self.assertion_cost(a);
            self.total_cost = self.total_cost - self.cost[a] + now;
            self.cost[a] = now;
        }
    }

    fn try_commit_focused_or_branch(&mut self, a: usize) -> bool {
        if !self.focused_or_cost[a] {
            return false;
        }
        let mut branches = Vec::new();
        collect_or_branches(self.arena, self.assertions[a], &mut branches);
        if branches.is_empty() || branches.len() > FOCUSED_OR_BRANCH_CAP {
            return false;
        }
        let mut best: Option<Vec<(usize, Value)>> = None;
        for branch in branches {
            let Some(plan) = self.branch_repair_plan(branch) else {
                continue;
            };
            if plan.is_empty() {
                continue;
            }
            let better = best
                .as_ref()
                .is_none_or(|current| plan.len() < current.len());
            if better {
                best = Some(plan);
            }
        }
        let Some(plan) = best else {
            return false;
        };
        for (vi, value) in plan {
            self.commit(vi, value);
        }
        true
    }

    fn branch_repair_plan(&mut self, branch: TermId) -> Option<Vec<(usize, Value)>> {
        let mut literals = Vec::new();
        collect_and_literals(self.arena, branch, &mut literals);
        let mut temp = self.asg.clone();
        let mut repairs: Vec<(usize, Value)> = Vec::new();
        for literal in literals {
            if eval_bool(self.arena, literal, &temp) == Some(true) {
                continue;
            }
            let (vi, value) = self.literal_repair(literal, &temp)?;
            temp.set(self.vars[vi].sym, value.clone());
            if let Some((_, existing)) = repairs.iter_mut().find(|(rvi, _)| *rvi == vi) {
                *existing = value;
            } else {
                repairs.push((vi, value));
                if repairs.len() > FOCUSED_OR_BRANCH_REPAIR_CAP {
                    return None;
                }
            }
            if eval_bool(self.arena, literal, &temp) != Some(true) {
                return None;
            }
        }
        if eval_bool(self.arena, branch, &temp) == Some(true) {
            Some(repairs)
        } else {
            None
        }
    }

    fn literal_repair(&mut self, literal: TermId, temp: &Assignment) -> Option<(usize, Value)> {
        let mut vis = Vec::new();
        collect_clause_vars(self.arena, literal, self.vars, &mut vis);
        for vi in vis {
            let sym = self.vars[vi].sym;
            let current = temp.get(sym)?;
            let mut candidates = local_repair_candidates(self.arena, literal, sym, temp);
            candidates.extend(candidate_values(
                self.vars[vi].kind,
                &current,
                &self.int_constants,
                &mut self.state,
            ));
            dedup_candidates(&mut candidates);
            candidates.retain(|candidate| candidate != &current);
            for candidate in candidates {
                let mut probe = temp.clone();
                probe.set(sym, candidate.clone());
                if eval_bool(self.arena, literal, &probe) == Some(true) {
                    return Some((vi, candidate));
                }
            }
        }
        None
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
        if self.try_commit_focused_or_branch(a) {
            return Step::Moved;
        }
        if xorshift(&mut self.state) % 100 < NOISE_PCT {
            let vi = in_clause[pick(&mut self.state, in_clause.len())];
            let current = self.asg.get(self.vars[vi].sym).expect("assigned");
            let mut cands = candidate_values(
                self.vars[vi].kind,
                &current,
                &self.int_constants,
                &mut self.state,
            );
            cands.retain(|candidate| candidate != &current);
            if !cands.is_empty() {
                let c = cands[pick(&mut self.state, cands.len())].clone();
                self.commit(vi, c);
            }
            return Step::Moved;
        }
        let focused_or = self.focused_or_cost[a];
        let mut best: Option<(usize, usize, usize, Value)> = None; // (score, focus, vi, value)
        for &vi in &in_clause {
            let current = self.asg.get(self.vars[vi].sym).expect("assigned");
            let mut candidates = local_repair_candidates(
                self.arena,
                self.assertions[a],
                self.vars[vi].sym,
                &self.asg,
            );
            candidates.extend(candidate_values(
                self.vars[vi].kind,
                &current,
                &self.int_constants,
                &mut self.state,
            ));
            dedup_candidates(&mut candidates);
            candidates.retain(|candidate| candidate != &current);
            for cand in candidates {
                let sc = self.score(vi, &cand);
                let focus = if focused_or {
                    self.focused_score(a, vi, &cand)
                } else {
                    usize::MAX
                };
                let better = match &best {
                    None => true,
                    Some((bs, bf, _, _)) => {
                        sc < *bs
                            || (sc == *bs && focus < *bf)
                            || (sc == *bs && focus == *bf && xorshift(&mut self.state) & 1 == 0)
                    }
                };
                if better {
                    best = Some((sc, focus, vi, cand));
                }
            }
        }
        if let Some((_, _, vi, value)) = best {
            self.commit(vi, value);
        }
        Step::Moved
    }
}

/// Assigns every variable a fresh random value.
fn randomize(asg: &mut Assignment, vars: &[Var], int_constants: &[i128], state: &mut u64) {
    for v in vars {
        match v.kind {
            VarKind::Bool => asg.set(v.sym, Value::Bool(xorshift(state) & 1 == 0)),
            VarKind::Bv(w) => {
                let lo = u128::from(xorshift(state));
                let hi = u128::from(xorshift(state));
                let value = ((hi << 64) | lo) & mask(w);
                asg.set(v.sym, Value::Bv { width: w, value });
            }
            VarKind::Int => {
                let value = if int_constants.is_empty() {
                    let raw = i128::from(xorshift(state) % 17);
                    raw - 8
                } else {
                    int_constants[pick(state, int_constants.len())]
                };
                asg.set(v.sym, Value::Int(value));
            }
        }
    }
}

/// Builds the candidate replacement values for a single variable (the moves a
/// greedy or random step may apply).
fn candidate_values(
    kind: VarKind,
    current: &Value,
    int_constants: &[i128],
    state: &mut u64,
) -> Vec<Value> {
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
        (VarKind::Int, Value::Int(value)) => {
            let mut moves = Vec::new();
            push_int_candidate(&mut moves, 0);
            push_int_candidate(&mut moves, 1);
            push_int_candidate(&mut moves, -1);
            if let Some(next) = value.checked_add(1) {
                push_int_candidate(&mut moves, next);
            }
            if let Some(prev) = value.checked_sub(1) {
                push_int_candidate(&mut moves, prev);
            }
            if let Some(next) = value.checked_add(2) {
                push_int_candidate(&mut moves, next);
            }
            if let Some(prev) = value.checked_sub(2) {
                push_int_candidate(&mut moves, prev);
            }
            if let Some(negated) = value.checked_neg() {
                push_int_candidate(&mut moves, negated);
            }
            for &constant in int_constants.iter().take(INT_CONST_CANDIDATE_CAP) {
                push_int_candidate(&mut moves, constant);
            }
            if !int_constants.is_empty() {
                push_int_candidate(&mut moves, int_constants[pick(state, int_constants.len())]);
            }
            moves
        }
        _ => Vec::new(),
    }
}

fn local_repair_candidates(
    arena: &TermArena,
    assertion: TermId,
    sym: SymbolId,
    asg: &Assignment,
) -> Vec<Value> {
    if arena.symbol(sym).1 != Sort::Int {
        return Vec::new();
    }
    let mut out = Vec::new();
    collect_local_int_repairs(arena, assertion, true, sym, asg, &mut out);
    out
}

fn collect_local_int_repairs(
    arena: &TermArena,
    term: TermId,
    desired: bool,
    sym: SymbolId,
    asg: &Assignment,
    out: &mut Vec<Value>,
) {
    if out.len() >= LOCAL_REPAIR_CANDIDATE_CAP {
        return;
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    match *op {
        Op::BoolNot => collect_local_int_repairs(arena, args[0], !desired, sym, asg, out),
        Op::BoolAnd | Op::BoolOr => {
            for &arg in args {
                collect_local_int_repairs(arena, arg, desired, sym, asg, out);
                if out.len() >= LOCAL_REPAIR_CANDIDATE_CAP {
                    break;
                }
            }
        }
        Op::BoolImplies => {
            collect_local_int_repairs(arena, args[0], !desired, sym, asg, out);
            collect_local_int_repairs(arena, args[1], desired, sym, asg, out);
        }
        Op::BoolXor | Op::Eq if arena.sort_of(args[0]) == Sort::Bool => {
            collect_local_int_repairs(arena, args[0], true, sym, asg, out);
            collect_local_int_repairs(arena, args[0], false, sym, asg, out);
            collect_local_int_repairs(arena, args[1], true, sym, asg, out);
            collect_local_int_repairs(arena, args[1], false, sym, asg, out);
        }
        Op::Ite if arena.sort_of(term) == Sort::Bool => {
            collect_local_int_repairs(arena, args[0], true, sym, asg, out);
            collect_local_int_repairs(arena, args[0], false, sym, asg, out);
            collect_local_int_repairs(arena, args[1], desired, sym, asg, out);
            collect_local_int_repairs(arena, args[2], desired, sym, asg, out);
        }
        Op::Eq if arena.sort_of(args[0]) == Sort::Int => {
            add_int_equality_repairs(arena, args[0], args[1], desired, sym, asg, out);
        }
        Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe => {
            add_int_order_repairs(arena, *op, [args[0], args[1]], desired, sym, asg, out);
        }
        _ => {}
    }
}

fn add_int_equality_repairs(
    arena: &TermArena,
    lhs: TermId,
    rhs: TermId,
    desired: bool,
    sym: SymbolId,
    asg: &Assignment,
    out: &mut Vec<Value>,
) {
    if let Some(constant) = unit_affine_const(arena, lhs, sym)
        && let Some(value) = eval_int(arena, rhs, asg)
        && let Some(candidate) = value.checked_sub(constant)
    {
        if desired {
            push_local_int_candidate(out, candidate);
        } else {
            push_offset_local_int_candidates(out, candidate);
        }
    }
    if let Some(constant) = unit_affine_const(arena, rhs, sym)
        && let Some(value) = eval_int(arena, lhs, asg)
        && let Some(candidate) = value.checked_sub(constant)
    {
        if desired {
            push_local_int_candidate(out, candidate);
        } else {
            push_offset_local_int_candidates(out, candidate);
        }
    }
}

fn add_int_order_repairs(
    arena: &TermArena,
    op: Op,
    terms: [TermId; 2],
    desired: bool,
    sym: SymbolId,
    asg: &Assignment,
    out: &mut Vec<Value>,
) {
    let [lhs, rhs] = terms;
    let (lhs, rhs, strict) = match op {
        Op::IntLt => (lhs, rhs, true),
        Op::IntLe => (lhs, rhs, false),
        Op::IntGt => (rhs, lhs, true),
        Op::IntGe => (rhs, lhs, false),
        _ => return,
    };
    add_le_like_repairs(arena, [lhs, rhs], strict, desired, sym, asg, out);
}

fn add_le_like_repairs(
    arena: &TermArena,
    terms: [TermId; 2],
    strict: bool,
    desired: bool,
    sym: SymbolId,
    asg: &Assignment,
    out: &mut Vec<Value>,
) {
    let [lhs, rhs] = terms;
    if let Some(constant) = unit_affine_const(arena, lhs, sym)
        && let Some(bound) = eval_int(arena, rhs, asg)
    {
        let target = if desired {
            if strict {
                bound.checked_sub(1)
            } else {
                Some(bound)
            }
        } else if strict {
            Some(bound)
        } else {
            bound.checked_add(1)
        };
        if let Some(target) = target.and_then(|value| value.checked_sub(constant)) {
            push_local_int_candidate(out, target);
        }
    }
    if let Some(constant) = unit_affine_const(arena, rhs, sym)
        && let Some(bound) = eval_int(arena, lhs, asg)
    {
        let target = if desired {
            if strict {
                bound.checked_add(1)
            } else {
                Some(bound)
            }
        } else if strict {
            Some(bound)
        } else {
            bound.checked_sub(1)
        };
        if let Some(target) = target.and_then(|value| value.checked_sub(constant)) {
            push_local_int_candidate(out, target);
        }
    }
}

/// Parses `term` as `sym + c` for small unit-affine repair moves.
fn unit_affine_const(arena: &TermArena, term: TermId, sym: SymbolId) -> Option<i128> {
    match arena.node(term) {
        TermNode::Symbol(s) if *s == sym => Some(0),
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => {
            if let Some(offset) = unit_affine_const(arena, args[0], sym)
                && let Some(constant) = int_const(arena, args[1])
            {
                return offset.checked_add(constant);
            }
            if let Some(offset) = unit_affine_const(arena, args[1], sym)
                && let Some(constant) = int_const(arena, args[0])
            {
                return offset.checked_add(constant);
            }
            None
        }
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let offset = unit_affine_const(arena, args[0], sym)?;
            let constant = int_const(arena, args[1])?;
            offset.checked_sub(constant)
        }
        _ => None,
    }
}

fn int_const(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        _ => None,
    }
}

fn eval_int(arena: &TermArena, term: TermId, asg: &Assignment) -> Option<i128> {
    match eval(arena, term, asg) {
        Ok(Value::Int(value)) => Some(value),
        _ => None,
    }
}

fn push_offset_local_int_candidates(out: &mut Vec<Value>, value: i128) {
    if let Some(prev) = value.checked_sub(1) {
        push_local_int_candidate(out, prev);
    }
    if let Some(next) = value.checked_add(1) {
        push_local_int_candidate(out, next);
    }
}

fn push_local_int_candidate(out: &mut Vec<Value>, value: i128) {
    if out.len() >= LOCAL_REPAIR_CANDIDATE_CAP {
        return;
    }
    push_int_candidate(out, value);
}

fn dedup_candidates(candidates: &mut Vec<Value>) {
    let mut deduped = Vec::with_capacity(candidates.len());
    for candidate in candidates.drain(..) {
        if !deduped.contains(&candidate) {
            deduped.push(candidate);
        }
    }
    *candidates = deduped;
}

fn push_int_candidate(out: &mut Vec<Value>, value: i128) {
    let candidate = Value::Int(value);
    if !out.contains(&candidate) {
        out.push(candidate);
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
    let int_constants = collect_int_constants(arena, assertions);
    // Probe once: an assertion the evaluator cannot reduce to a Bool (arrays,
    // uninterpreted functions, …) is out of scope.
    let mut probe = Assignment::new();
    let mut probe_state = SEED;
    randomize(&mut probe, &vars, &int_constants, &mut probe_state);
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

    let mut search = Search::new(arena, assertions, &vars, int_constants);
    let mut flips = 0usize;

    for restart in 0..max_tries {
        randomize(
            &mut search.asg,
            &vars,
            &search.int_constants,
            &mut search.state,
        );
        search.recompute();
        for _ in 0..max_flips {
            if past(deadline) {
                return Ok(unknown("timeout", flips, restart));
            }
            if search.total_cost == 0 && search.all_satisfied() {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_search_finds_integer_model_from_constants() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let three = arena.int_const(3);
        let five = arena.int_const(5);
        let x_eq_three = arena.eq(xv, three).unwrap();
        let y_eq_five = arena.eq(yv, five).unwrap();

        let outcome =
            solve_local_search(&arena, &[x_eq_three, y_eq_five], &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = outcome.result else {
            panic!("integer local search should find the direct constant model");
        };
        let assignment = model.to_assignment();
        assert_eq!(
            eval(&arena, x_eq_three, &assignment).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&arena, y_eq_five, &assignment).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn local_search_scores_nested_boolean_structure() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let three = arena.int_const(3);
        let five = arena.int_const(5);
        let x_eq_three = arena.eq(xv, three).unwrap();
        let y_eq_five = arena.eq(yv, five).unwrap();
        let assertion = arena.and(x_eq_three, y_eq_five).unwrap();

        let outcome = solve_local_search(&arena, &[assertion], &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = outcome.result else {
            panic!("structural Boolean scoring should find the nested integer model");
        };
        let assignment = model.to_assignment();
        assert_eq!(
            eval(&arena, assertion, &assignment).unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn local_integer_repairs_use_current_affine_values() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let one = arena.int_const(1);
        let y_plus_one = arena.int_add(yv, one).unwrap();
        let assertion = arena.eq(xv, y_plus_one).unwrap();

        let mut assignment = Assignment::new();
        assignment.set(x, Value::Int(0));
        assignment.set(y, Value::Int(41));

        let x_repairs = local_repair_candidates(&arena, assertion, x, &assignment);
        assert!(
            x_repairs.contains(&Value::Int(42)),
            "x should be repairable to the current value of y + 1"
        );

        assignment.set(x, Value::Int(17));
        let y_repairs = local_repair_candidates(&arena, assertion, y, &assignment);
        assert!(
            y_repairs.contains(&Value::Int(16)),
            "y should be repairable to the current value of x - 1"
        );
    }

    #[test]
    fn focused_or_tiebreak_solves_wide_branch_disjunction() {
        let mut arena = TermArena::new();
        let mut branches = Vec::new();
        for i in 0..10 {
            let lhs = arena.declare(&format!("lhs_{i}"), Sort::Int).unwrap();
            let rhs = arena.declare(&format!("rhs_{i}"), Sort::Int).unwrap();
            let target = arena.int_const(i128::from(40 + i));
            let lhs_term = arena.var(lhs);
            let rhs_term = arena.var(rhs);
            let lhs_eq = arena.eq(lhs_term, target).unwrap();
            let rhs_eq = arena.eq(rhs_term, target).unwrap();
            branches.push(arena.and(lhs_eq, rhs_eq).unwrap());
        }
        let mut iter = branches.into_iter();
        let mut assertion = iter.next().expect("at least one branch");
        for branch in iter {
            assertion = arena.or(assertion, branch).unwrap();
        }
        assert!(focused_or_cost_enabled(&arena, assertion, 20));

        let outcome = solve_local_search(&arena, &[assertion], &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = outcome.result else {
            panic!("focused OR tie-break should find one satisfying branch");
        };
        assert_eq!(
            eval(&arena, assertion, &model.to_assignment()).unwrap(),
            Value::Bool(true)
        );
    }
}
