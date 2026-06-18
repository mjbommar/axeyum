//! A proof-producing pure-Rust CDCL SAT core (ADR-0012).
//!
//! Conflict-driven clause learning with **1-UIP** conflict analysis and
//! **two-watched-literal** propagation. Every learned clause is RUP by
//! construction, so the sequence of learned clauses is a valid DRAT proof; on
//! `unsat` the empty clause is derived. The proof is verified by
//! [`crate::check_drat`], so `unsat` is sound regardless of bugs in this
//! (untrusted) search — the project's "untrusted fast search, trusted small
//! checking" identity, realized for `unsat`.
//!
//! A conflict budget bounds the search so it can never hang. This is a
//! proof/correctness reference; the fast default solving path remains the
//! `rustsat-batsat` adapter until the benchmarking gate says otherwise.

use crate::drat::DratStep;
use crate::{CnfAssignment, CnfFormula, CnfLit, CnfVar};

/// Maximum conflicts before the core gives up (safety valve).
const MAX_CONFLICTS: usize = 2_000_000;

/// VSIDS activity decay: each conflict `var_inc` is divided by this, so older
/// activity bumps decay geometrically relative to fresh ones (the `MiniSat`
/// scheme).
const VSIDS_DECAY: f64 = 0.95;
/// Rescale all activities (and `var_inc`) by this when any exceeds the cap, to
/// avoid `f64` overflow without changing their relative order.
const VSIDS_RESCALE: f64 = 1e-100;
/// Activity ceiling that triggers a rescale.
const VSIDS_RESCALE_LIMIT: f64 = 1e100;
/// Conflict-interval unit multiplied by the Luby value to set each restart's
/// length.
const LUBY_UNIT: usize = 100;

/// The `i`-th term (1-indexed) of the Luby sequence `1,1,2,1,1,2,4,1,…`, used to
/// space restarts (Knuth's reluctant-doubling formulation, iterative).
fn luby(mut i: u64) -> u64 {
    let mut k = 1u64;
    loop {
        let pow = 1u64 << k; // 2^k
        if i == pow - 1 {
            return 1u64 << (k - 1); // 2^(k-1)
        }
        let half = 1u64 << (k - 1); // 2^(k-1)
        if half <= i && i < pow - 1 {
            i = i - half + 1;
            k = 1;
        } else {
            k += 1;
        }
    }
}

/// Outcome of [`solve_with_drat_proof`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofSolveOutcome {
    /// Satisfiable, with a model over the formula's variables.
    Sat(CnfAssignment),
    /// Unsatisfiable, with a DRAT proof verifiable by [`crate::check_drat`].
    Unsat(Vec<DratStep>),
    /// The conflict budget was exhausted before a result was reached.
    ResourceOut,
}

/// Solves `formula` with the proof-producing CDCL core.
pub fn solve_with_drat_proof(formula: &CnfFormula) -> ProofSolveOutcome {
    Cdcl::new(formula).solve()
}

fn lit_code(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

struct Cdcl {
    clauses: Vec<Vec<CnfLit>>,
    /// Per-literal watch lists, indexed by [`lit_code`].
    watches: Vec<Vec<usize>>,
    assign: Vec<Option<bool>>,
    level: Vec<usize>,
    reason: Vec<Option<usize>>,
    trail: Vec<usize>,
    trail_lim: Vec<usize>,
    qhead: usize,
    initial_units: Vec<CnfLit>,
    has_empty_clause: bool,
    proof: Vec<DratStep>,
    conflicts: usize,
    /// VSIDS activity per variable (higher ⇒ branched sooner).
    activity: Vec<f64>,
    /// Current activity bump increment (grows each conflict by `1/decay`).
    var_inc: f64,
    /// Saved decision polarity per variable (phase saving).
    phase: Vec<bool>,
    /// Conflicts since the last restart (the Luby restart trigger).
    conflicts_since_restart: usize,
    /// Index into the Luby sequence (1-based; advances on each restart).
    restart_count: u64,
}

impl Cdcl {
    fn new(formula: &CnfFormula) -> Self {
        let n = formula.variable_count();
        let clauses: Vec<Vec<CnfLit>> = formula
            .clauses()
            .iter()
            .map(|clause| clause.lits().to_vec())
            .collect();
        let mut watches = vec![Vec::new(); 2 * n];
        let mut initial_units = Vec::new();
        let mut has_empty_clause = false;
        for (cid, clause) in clauses.iter().enumerate() {
            match clause.len() {
                0 => has_empty_clause = true,
                1 => initial_units.push(clause[0]),
                _ => {
                    watches[lit_code(clause[0])].push(cid);
                    watches[lit_code(clause[1])].push(cid);
                }
            }
        }
        Self {
            clauses,
            watches,
            assign: vec![None; n],
            level: vec![0; n],
            reason: vec![None; n],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            initial_units,
            has_empty_clause,
            proof: Vec::new(),
            conflicts: 0,
            activity: vec![0.0; n],
            var_inc: 1.0,
            phase: vec![false; n],
            conflicts_since_restart: 0,
            restart_count: 1,
        }
    }

    /// Bumps `var`'s VSIDS activity, rescaling all activities if it overflows the
    /// cap (preserving their relative order).
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            for a in &mut self.activity {
                *a *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
        }
    }

    /// Decays activity by growing the bump increment (the `MiniSat` trick).
    fn decay(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// Conflicts allowed before the next restart, per the Luby schedule.
    fn restart_limit(&self) -> usize {
        usize::try_from(luby(self.restart_count)).unwrap_or(usize::MAX) * LUBY_UNIT
    }

    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    fn value(&self, lit: CnfLit) -> Option<bool> {
        self.assign[lit.var().index()].map(|v| v != lit.is_negated())
    }

    fn true_literal(&self, var: usize) -> CnfLit {
        let positive = CnfLit::positive(CnfVar::new(var).expect("variable index in range"));
        if self.assign[var] == Some(true) {
            positive
        } else {
            positive.negated()
        }
    }

    fn enqueue(&mut self, lit: CnfLit, reason: Option<usize>) {
        let var = lit.var().index();
        let value = !lit.is_negated();
        self.assign[var] = Some(value);
        self.phase[var] = value; // phase saving: remember the last polarity
        self.level[var] = self.decision_level();
        self.reason[var] = reason;
        self.trail.push(var);
    }

    fn solve(mut self) -> ProofSolveOutcome {
        if self.has_empty_clause {
            self.proof.push(DratStep::Add(Vec::new()));
            return ProofSolveOutcome::Unsat(self.proof);
        }
        for lit in std::mem::take(&mut self.initial_units) {
            match self.value(lit) {
                Some(false) => {
                    self.proof.push(DratStep::Add(Vec::new()));
                    return ProofSolveOutcome::Unsat(self.proof);
                }
                Some(true) => {}
                None => self.enqueue(lit, None),
            }
        }

        loop {
            if let Some(conflict) = self.propagate() {
                if self.decision_level() == 0 {
                    self.proof.push(DratStep::Add(Vec::new()));
                    return ProofSolveOutcome::Unsat(self.proof);
                }
                self.conflicts += 1;
                if self.conflicts > MAX_CONFLICTS {
                    return ProofSolveOutcome::ResourceOut;
                }
                let (learned, backjump) = self.analyze(conflict);
                self.proof.push(DratStep::Add(learned.clone()));
                if learned.is_empty() {
                    return ProofSolveOutcome::Unsat(self.proof);
                }
                let clause_id = self.clauses.len();
                let asserting = learned[0];
                if learned.len() >= 2 {
                    self.watches[lit_code(learned[0])].push(clause_id);
                    self.watches[lit_code(learned[1])].push(clause_id);
                }
                self.clauses.push(learned);
                self.backtrack_to(backjump);
                self.enqueue(asserting, Some(clause_id));
                self.conflicts_since_restart += 1;
                self.decay();
            } else {
                // No conflict: consider a Luby restart, then make a decision.
                if self.decision_level() > 0 && self.conflicts_since_restart >= self.restart_limit()
                {
                    self.conflicts_since_restart = 0;
                    self.restart_count += 1;
                    self.backtrack_to(0);
                    continue;
                }
                if let Some(var) = self.pick_branch() {
                    self.trail_lim.push(self.trail.len());
                    let positive =
                        CnfLit::positive(CnfVar::new(var).expect("variable index in range"));
                    // Phase saving: decide the variable's last-seen polarity.
                    let decision = if self.phase[var] {
                        positive
                    } else {
                        positive.negated()
                    };
                    self.enqueue(decision, None);
                } else {
                    let values = self.assign.iter().map(|v| v.unwrap_or(false)).collect();
                    return ProofSolveOutcome::Sat(CnfAssignment::new(values));
                }
            }
        }
    }

    /// Two-watched-literal unit propagation; returns a conflicting clause id.
    fn propagate(&mut self) -> Option<usize> {
        while self.qhead < self.trail.len() {
            let var = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = self.true_literal(var).negated();
            let code = lit_code(false_lit);

            let mut watchers = std::mem::take(&mut self.watches[code]);
            let mut i = 0;
            let mut conflict = None;
            while i < watchers.len() {
                let cid = watchers[i];
                // Keep the falsified literal at index 1.
                if self.clauses[cid][0] == false_lit {
                    self.clauses[cid].swap(0, 1);
                }
                let other = self.clauses[cid][0];
                if self.value(other) == Some(true) {
                    i += 1;
                    continue;
                }
                // Look for a non-false literal to watch instead.
                let mut moved = false;
                for k in 2..self.clauses[cid].len() {
                    if self.value(self.clauses[cid][k]) != Some(false) {
                        self.clauses[cid].swap(1, k);
                        let new_code = lit_code(self.clauses[cid][1]);
                        self.watches[new_code].push(cid);
                        watchers.swap_remove(i);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                // No replacement: `other` is unit or the clause is in conflict.
                // Either way the clause keeps watching `false_lit` (stays in
                // `watchers`).
                if self.value(other) == Some(false) {
                    conflict = Some(cid);
                    break;
                }
                self.enqueue(other, Some(cid));
                i += 1;
            }
            self.watches[code] = watchers;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// 1-UIP conflict analysis: returns the learned clause (asserting literal at
    /// index 0, second-watch literal at index 1) and the backjump level. An
    /// empty result means the conflict is implied at level 0 (the empty clause).
    fn analyze(&mut self, conflict: usize) -> (Vec<CnfLit>, usize) {
        let mut seen = vec![false; self.assign.len()];
        let mut lower: Vec<CnfLit> = Vec::new();
        let mut path_count = 0usize;
        let mut pivot_var: Option<usize> = None;
        let mut index = self.trail.len();
        let mut clause_id = conflict;
        let current = self.decision_level();

        loop {
            // Clone the reason clause's literals so we can bump activities while
            // walking it (the borrow checker forbids reading `self.clauses` and
            // mutating `self.activity` at once; reason clauses are short).
            let lits = self.clauses[clause_id].clone();
            for q in lits {
                let v = q.var().index();
                if Some(v) == pivot_var || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                self.bump_var(v); // VSIDS: bump every variable in the conflict side
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(q);
                }
            }

            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index]] {
                    found = true;
                    break;
                }
            }
            if !found {
                return (Vec::new(), 0);
            }

            let var = self.trail[index];
            seen[var] = false;
            path_count -= 1;
            pivot_var = Some(var);

            if path_count == 0 {
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negated());
                learned.extend(lower);
                // Put the highest-level non-asserting literal at index 1 so the
                // clause watches correctly after backjumping.
                let mut backjump = 0;
                if learned.len() >= 2 {
                    let mut best = 1;
                    for k in 2..learned.len() {
                        if self.level[learned[k].var().index()]
                            > self.level[learned[best].var().index()]
                        {
                            best = k;
                        }
                    }
                    learned.swap(1, best);
                    backjump = self.level[learned[1].var().index()];
                }
                return (learned, backjump);
            }

            clause_id = self.reason[var].expect("implied literal has a reason clause");
        }
    }

    fn backtrack_to(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let bound = self.trail_lim[level];
            while self.trail.len() > bound {
                let var = self.trail.pop().expect("trail not empty above bound");
                self.assign[var] = None;
                self.reason[var] = None;
            }
            self.trail_lim.truncate(level);
        }
        self.qhead = self.trail.len();
    }

    fn pick_branch(&self) -> Option<usize> {
        // The unassigned variable of highest VSIDS activity; ties break to the
        // lowest index (only a strictly greater activity replaces the best), so
        // the choice is deterministic.
        let mut best: Option<usize> = None;
        for v in 0..self.assign.len() {
            if self.assign[v].is_some() {
                continue;
            }
            match best {
                None => best = Some(v),
                Some(b) if self.activity[v] > self.activity[b] => best = Some(v),
                _ => {}
            }
        }
        best
    }
}

#[cfg(test)]
mod tests {
    use super::{ProofSolveOutcome, solve_with_drat_proof};
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, SatResult, check_drat, solve_with_rustsat_batsat,
    };

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
                .unwrap();
        }
        f
    }

    fn assert_unsat_with_checked_proof(f: &CnfFormula) {
        match solve_with_drat_proof(f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(f, &proof), Ok(true), "DRAT proof must verify");
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    #[test]
    fn unit_contradiction_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(1, &[&[1], &[-1]]));
    }

    #[test]
    fn full_2x2_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]));
    }

    #[test]
    fn pigeonhole_3_into_2_is_unsat_with_checked_proof() {
        assert_unsat_with_checked_proof(&formula(
            6,
            &[
                &[1, 2],
                &[3, 4],
                &[5, 6],
                &[-1, -3],
                &[-1, -5],
                &[-3, -5],
                &[-2, -4],
                &[-2, -6],
                &[-4, -6],
            ],
        ));
    }

    #[test]
    fn empty_clause_is_immediately_unsat() {
        assert_unsat_with_checked_proof(&formula(1, &[&[]]));
    }

    #[test]
    fn pigeonhole_4_into_3_is_unsat_with_checked_proof() {
        // 4 pigeons, 3 holes: x_{p,h} = var 3*(p-1)+h. Each pigeon in some hole
        // (4 clauses) + no two pigeons share a hole (3 holes × C(4,2)=6 pairs).
        // Enough conflicts to exercise VSIDS branching and a Luby restart.
        let v = |p: i64, h: i64| 3 * (p - 1) + h;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=4 {
            clauses.push(vec![v(p, 1), v(p, 2), v(p, 3)]);
        }
        for h in 1..=3 {
            for p1 in 1..=4 {
                for p2 in (p1 + 1)..=4 {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        assert_unsat_with_checked_proof(&formula(12, &refs));
    }

    #[test]
    fn satisfiable_formula_yields_a_satisfying_model() {
        let f = formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]]);
        match solve_with_drat_proof(&f) {
            ProofSolveOutcome::Sat(model) => assert!(model.satisfies(&f).unwrap()),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    /// Strong validation of the watched-literal core: on many random CNFs, the
    /// CDCL core must agree with the `BatSat` adapter on sat/unsat, every `sat`
    /// model must satisfy, and every `unsat` proof must pass the DRAT checker.
    #[test]
    fn random_cnfs_agree_with_batsat_and_self_check() {
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..400 {
            let vars = 3 + below(&mut next, 5); // 3..=7 variables
            let clause_count = 3 + below(&mut next, 18);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + below(&mut next, 3); // 1..=3 literals
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }

            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(model.satisfies(&f).unwrap(), "cdcl model must satisfy");
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(check_drat(&f, &proof), Ok(true), "cdcl proof must verify");
                }
                (cdcl, other) => {
                    panic!("cdcl/batsat disagreement: cdcl={cdcl:?} batsat={other:?}");
                }
            }
        }
    }
}
