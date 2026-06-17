//! Conflict-driven (CDCL) XOR-aware SAT solver with clause learning.
//!
//! This module is the *competitive integration* slice of the CDCL(XOR) path
//! (ADR-0035; `docs/research/05-algorithms/cdcl-xor-integration-design.md`,
//! path 2). The earlier slices built and brute-force validated the algebraic
//! pieces — the GF(2) Gaussian solver ([`crate::gf2`]), sound XOR-gate recovery
//! ([`crate::extract_xors`]), the in-search Gaussian propagation primitive
//! ([`crate::xor_implications`]) — and a correctness-first *naive*
//! decider ([`crate::solve_with_xor`]) that interleaves clause propagation with
//! a full per-trail Gaussian recompute but **lacks clause learning**. Learning
//! is exactly what makes XOR reasoning *competitive*; this module adds it.
//!
//! [`solve_with_xor_cdcl`] decides a [`CnfFormula`] conjoined with the XOR
//! system [`extract_xors`] recovers from it, using a conflict-driven loop with
//! **1-UIP conflict analysis** and **two-watched-literal** propagation, modeled
//! on the proof-producing core [`crate::solve_with_drat_proof`].
//!
//! # Scope and trust
//!
//! Search only. There is **no DRAT / proof emission**: an XOR-derived reason
//! clause is generally not RUP, so it cannot be certified by the in-tree DRAT
//! checker. Per ADR-0035, XOR-assisted `unsat` is the ledgered `XorGaussian`
//! trust hole, backed by the brute-force-validated soundness of the XOR engine;
//! `sat` carries no trust cost (the model is checked by evaluation). This module
//! produces neither a ledger entry nor a proof — wiring into production dispatch
//! and the trust ledger is the next slice. It is deliberately ISOLATED: it does
//! not touch [`crate::solve_with_drat_proof`] or any dispatch.
//!
//! # The XOR propagator (the key new piece)
//!
//! Conflict analysis needs *antecedent-valid* reasons: the reason for an implied
//! literal must consist only of literals assigned strictly **before** it. The
//! Gaussian primitive [`xor_implications`] does not give that (its reasons are a
//! connected-component over-approximation, not necessarily pre-assigned). So
//! this module uses the standard `CryptoMiniSat` `gausswatched`-style
//! **watched-literal XOR propagation** instead:
//!
//! For each XOR constraint `(x_a ⊕ x_b ⊕ … = p)` we **watch two of its
//! variables**. When a watched variable is assigned, we look for another
//! unassigned variable in the constraint to watch instead.
//!
//! * If a replacement is found, the constraint stays passive.
//! * If exactly **one** unassigned variable remains, the constraint *forces*
//!   it: its value is `p ⊕ (XOR of every other variable's current value)`. The
//!   reason is **exactly the other variables of this constraint** — all of which
//!   are currently assigned, hence all assigned before this implication, so the
//!   reason is minimal and antecedent-valid, precisely what 1-UIP needs.
//! * If **zero** unassigned variables remain and the parity is wrong, the
//!   constraint is in conflict; its conflict set is the constraint's variables.
//!
//! This watched-literal scheme is **sound but incomplete** versus full Gaussian
//! elimination (it misses parities only a row combination would expose); that is
//! expected and fine. A complete Gaussian-on-trail propagator (with
//! row-provenance reasons) for the implications this misses is a later
//! enhancement.
//!
//! # XOR antecedents in 1-UIP analysis
//!
//! Clause and XOR implications share one trail; each trail entry records its
//! antecedent as either a clause index or an XOR-constraint index. During 1-UIP
//! resolution, an XOR antecedent is treated exactly like a clause antecedent: we
//! **synthesize its equivalent reason clause** on demand — for an
//! XOR-implied literal `ℓ` forced by constraint `C`, the reason clause is
//! `(ℓ ∨ ¬(other vars of C at their trail values))`, i.e. the clause that
//! "propagated" `ℓ`. For an XOR *conflict* the synthesized clause is the
//! all-false clause over the constraint's variables at their trail values. These
//! synthesized clauses slot into the same resolution loop the clause antecedents
//! use.
//!
//! # Search heuristics (the competitive core)
//!
//! The search core uses the standard CDCL modernization, made deterministic:
//!
//! * **VSIDS activity branching.** Each variable carries an activity score;
//!   every variable touched during 1-UIP conflict analysis (the resolved
//!   antecedents and the learned-clause literals) is *bumped*, and a per-conflict
//!   exponential decay (`var_inc /= decay`, with rescale-on-overflow) keeps the
//!   most recently active variables on top. The next decision is the unassigned
//!   variable of highest activity; **ties break to the lowest variable index**,
//!   so the search stays fully deterministic.
//! * **Phase saving.** The last value each variable was assigned is remembered
//!   and reused as the decision phase (the initial saved phase is `false`,
//!   matching the historical false-first behavior).
//! * **Luby restarts.** A fixed Luby sequence scaled by a small unit triggers a
//!   backtrack to level 0 (keeping every learned clause, activity score, and
//!   saved phase). The sequence is deterministic, so restarts do not perturb
//!   reproducibility.
//!
//! # Determinism
//!
//! Activity ties break to the lowest variable index, the Luby sequence is fixed,
//! phase saving is a per-variable array, and constraint/watch scans stay
//! index-ordered; no hash-map iteration influences any result or order.
//!
//! # Soundness
//!
//! The recovered XOR gates *are* clauses already in `formula`, so the clause set
//! is the ground truth and XOR propagation is pure acceleration (it can only
//! prune assignments the clauses already forbid). A returned [`XorCdclResult::Sat`]
//! model is asserted (in debug builds) to satisfy **every clause and every XOR
//! constraint** before it is returned.

use crate::{CnfFormula, XorConstraintInput, extract_xors};

/// Maximum conflicts before the solver gives up (safety valve → `Unknown`).
const MAX_CONFLICTS: usize = 2_000_000;

/// VSIDS activity decay: each conflict, `var_inc` is divided by this, so older
/// bumps decay geometrically relative to fresh ones (the `MiniSat` scheme uses
/// `0.95`).
const VSIDS_DECAY: f64 = 0.95;

/// Rescale activities (and `var_inc`) by this when any activity exceeds the cap,
/// to avoid `f64` overflow on very long runs.
const VSIDS_RESCALE: f64 = 1e-100;

/// Activity rescale trigger: when any score exceeds this, divide everything by
/// it (multiply by [`VSIDS_RESCALE`]).
const VSIDS_RESCALE_LIMIT: f64 = 1e100;

/// Luby restart unit: the Luby value is multiplied by this to get the conflict
/// interval before the next restart.
const RESTART_UNIT: usize = 100;

/// Outcome of [`solve_with_xor_cdcl`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XorCdclResult {
    /// The formula and all recovered XOR constraints are jointly satisfiable.
    ///
    /// The carried assignment is a full model (one Boolean per variable, in
    /// index order) satisfying **every clause and every XOR constraint**.
    Sat(Vec<bool>),
    /// The formula (equivalently, the formula plus its XOR system) is
    /// unsatisfiable. Search-only: no proof is emitted (the `XorGaussian` trust
    /// hole, ADR-0035).
    Unsat,
    /// The conflict budget was exhausted before a verdict was reached. The
    /// solver is total: this keeps it non-hanging, never an error.
    Unknown,
}

/// Decides `formula` conjoined with the XOR constraints recovered from it, using
/// a conflict-driven (CDCL) loop with 1-UIP clause learning and watched-literal
/// clause + XOR propagation.
///
/// The XOR system is recovered with [`extract_xors`]. See the module docs for
/// the watched-literal XOR propagator and how XOR antecedents enter conflict
/// analysis.
///
/// # Panics
///
/// Does not panic in release builds. In debug builds it asserts the internal
/// invariant that a returned `Sat` model satisfies every clause and every XOR
/// constraint; that assertion holding is the module's soundness guarantee.
#[must_use]
pub fn solve_with_xor_cdcl(formula: &CnfFormula) -> XorCdclResult {
    let constraints = extract_xors(formula).system.constraints();
    let result = XorCdcl::new(formula, &constraints).solve();
    if let XorCdclResult::Sat(model) = &result {
        debug_assert!(
            model_satisfies_all(formula, &constraints, model),
            "solve_with_xor_cdcl returned a Sat model violating a clause or XOR constraint"
        );
    }
    result
}

/// Test-only variant returning the verdict and the number of conflicts the
/// search resolved (i.e. learned clauses generated). Used to assert that
/// learning actually fires on learning-required instances.
#[cfg(test)]
fn solve_with_xor_cdcl_conflicts(formula: &CnfFormula) -> (XorCdclResult, usize) {
    let constraints = extract_xors(formula).system.constraints();
    let mut solver = XorCdcl::new(formula, &constraints);
    let result = solver.run();
    (result, solver.conflicts)
}

/// Returns `true` iff `model` satisfies every clause of `formula` and every XOR
/// constraint in `constraints`. The public `Sat` guarantee.
fn model_satisfies_all(
    formula: &CnfFormula,
    constraints: &[XorConstraintInput],
    model: &[bool],
) -> bool {
    if model.len() != formula.variable_count() {
        return false;
    }
    let clauses_ok = formula.evaluate(model).unwrap_or(false);
    let xors_ok = constraints.iter().all(|(vars, parity)| {
        let mut acc = false;
        for &v in vars {
            acc ^= model[v];
        }
        acc == *parity
    });
    clauses_ok && xors_ok
}

/// A literal as the two-watched-literal core encodes it: `2*var + negated`.
///
/// `var` is a zero-based variable index; `negated == 1` means the literal is the
/// variable's negation. A literal `lit` is *true* under an assignment when the
/// variable's value differs from `negated`.
type Lit = usize;

#[inline]
fn make_lit(var: usize, negated: bool) -> Lit {
    2 * var + usize::from(negated)
}

#[inline]
fn lit_var(lit: Lit) -> usize {
    lit / 2
}

#[inline]
fn lit_negated(lit: Lit) -> bool {
    lit & 1 == 1
}

#[inline]
fn lit_not(lit: Lit) -> Lit {
    lit ^ 1
}

/// The antecedent that forced a trail literal.
#[derive(Clone, Copy)]
enum Reason {
    /// A decision (no antecedent).
    Decision,
    /// An initial top-level unit clause (an empty antecedent for analysis).
    Unit,
    /// A clause forced this literal; the value is the clause index.
    Clause(usize),
    /// An XOR constraint forced this literal; the value is the constraint index.
    Xor(usize),
}

/// The conflict-driven XOR-aware search state.
struct XorCdcl<'a> {
    /// Clause database (initial clauses followed by learned clauses), as lit
    /// codes. Two-watched-literal invariant on clauses of length ≥ 2.
    clauses: Vec<Vec<Lit>>,
    /// Per-literal clause watch lists, indexed by lit code.
    clause_watches: Vec<Vec<usize>>,
    /// XOR constraints, each as a (sorted, deduped-by-extraction) variable list
    /// plus rhs parity.
    constraints: &'a [XorConstraintInput],
    /// The two watched variables of each constraint (positions into its var
    /// list), or `None` when the constraint has < 2 variables (degenerate).
    xor_watch: Vec<Option<(usize, usize)>>,
    /// Per-variable list of constraint indices watching that variable.
    xor_watches: Vec<Vec<usize>>,
    /// Current partial assignment.
    assign: Vec<Option<bool>>,
    /// Decision level each variable was assigned at.
    level: Vec<usize>,
    /// Antecedent of each variable's assignment.
    reason: Vec<Reason>,
    /// Assignment order (variable indices).
    trail: Vec<usize>,
    /// Trail index where each decision level began.
    trail_lim: Vec<usize>,
    /// Propagation queue head into `trail`.
    qhead: usize,
    /// Initial top-level unit clauses.
    initial_units: Vec<Lit>,
    /// Whether the formula contains an empty clause.
    has_empty_clause: bool,
    /// Conflicts seen so far (the budget counter).
    conflicts: usize,
    /// Whether a top-level contradiction was found during setup.
    top_level_unsat: bool,
    /// VSIDS activity score per variable (higher ⇒ branched sooner).
    activity: Vec<f64>,
    /// Current activity bump increment (grows each conflict by `1/decay`).
    var_inc: f64,
    /// Saved (last-assigned) phase per variable for phase saving; initial
    /// `false` reproduces the historical false-first decision phase.
    saved_phase: Vec<bool>,
    /// Conflicts counted since the last restart (the restart trigger).
    conflicts_since_restart: usize,
    /// Index into the Luby sequence for the next restart interval.
    luby_index: usize,
}

impl<'a> XorCdcl<'a> {
    fn new(formula: &CnfFormula, constraints: &'a [XorConstraintInput]) -> Self {
        let n = formula.variable_count();

        let mut clauses: Vec<Vec<Lit>> = Vec::with_capacity(formula.clauses().len());
        let mut clause_watches = vec![Vec::new(); 2 * n];
        let mut initial_units = Vec::new();
        let mut has_empty_clause = false;
        for clause in formula.clauses() {
            let lits: Vec<Lit> = clause
                .lits()
                .iter()
                .map(|lit| make_lit(lit.var().index(), lit.is_negated()))
                .collect();
            match lits.len() {
                0 => has_empty_clause = true,
                1 => {
                    initial_units.push(lits[0]);
                    clauses.push(lits);
                }
                _ => {
                    let cid = clauses.len();
                    clause_watches[lits[0]].push(cid);
                    clause_watches[lits[1]].push(cid);
                    clauses.push(lits);
                }
            }
        }

        // Watched-literal XOR setup: each constraint watches its first two
        // variables (every extracted variable list is already deduped, so the
        // two are distinct). Constraints with < 2 variables are degenerate.
        let mut xor_watch = Vec::with_capacity(constraints.len());
        let mut xor_watches = vec![Vec::new(); n];
        let mut top_level_unsat = false;
        for (cid, (vars, parity)) in constraints.iter().enumerate() {
            match vars.len() {
                0 => {
                    // Empty XOR: `0 = parity`. `parity == true` is `0 = 1`,
                    // unconditionally UNSAT. (Extraction never emits these, but
                    // be total.)
                    xor_watch.push(None);
                    if *parity {
                        top_level_unsat = true;
                    }
                }
                1 => {
                    // A 1-variable XOR `x = parity`; treat as an initial unit on
                    // that variable.
                    xor_watch.push(None);
                    initial_units.push(make_lit(vars[0], !*parity));
                }
                _ => {
                    xor_watch.push(Some((0, 1)));
                    xor_watches[vars[0]].push(cid);
                    xor_watches[vars[1]].push(cid);
                }
            }
        }

        Self {
            clauses,
            clause_watches,
            constraints,
            xor_watch,
            xor_watches,
            assign: vec![None; n],
            level: vec![0; n],
            reason: vec![Reason::Decision; n],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            initial_units,
            has_empty_clause,
            conflicts: 0,
            top_level_unsat,
            activity: vec![0.0; n],
            var_inc: 1.0,
            saved_phase: vec![false; n],
            conflicts_since_restart: 0,
            luby_index: 0,
        }
    }

    #[inline]
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// The truth value of `lit` under the current assignment, if assigned.
    #[inline]
    fn value(&self, lit: Lit) -> Option<bool> {
        self.assign[lit_var(lit)].map(|v| v != lit_negated(lit))
    }

    /// The literal that is *true* for `var`'s current (assigned) value.
    #[inline]
    fn true_literal(&self, var: usize) -> Lit {
        make_lit(var, self.assign[var] != Some(true))
    }

    /// Assigns the variable of `lit` so `lit` is true, recording its antecedent.
    fn enqueue(&mut self, lit: Lit, reason: Reason) {
        let var = lit_var(lit);
        let value = !lit_negated(lit);
        self.assign[var] = Some(value);
        self.saved_phase[var] = value;
        self.level[var] = self.decision_level();
        self.reason[var] = reason;
        self.trail.push(var);
    }

    fn solve(mut self) -> XorCdclResult {
        self.run()
    }

    fn run(&mut self) -> XorCdclResult {
        if self.has_empty_clause || self.top_level_unsat {
            return XorCdclResult::Unsat;
        }
        // Seed the initial unit clauses (and 1-var XORs); a direct clash is UNSAT.
        for lit in std::mem::take(&mut self.initial_units) {
            match self.value(lit) {
                Some(false) => return XorCdclResult::Unsat,
                Some(true) => {}
                None => self.enqueue(lit, Reason::Unit),
            }
        }

        loop {
            if let Some(conflict) = self.propagate() {
                if self.decision_level() == 0 {
                    return XorCdclResult::Unsat;
                }
                self.conflicts += 1;
                self.conflicts_since_restart += 1;
                if self.conflicts > MAX_CONFLICTS {
                    return XorCdclResult::Unknown;
                }
                let (learned, backjump) = self.analyze(conflict);
                if learned.is_empty() {
                    return XorCdclResult::Unsat;
                }
                // VSIDS: bump every variable that took part in this conflict's
                // resolution (collected in `analyze`), then decay for next time.
                self.decay_activity();
                let asserting = learned[0];
                let cid = self.clauses.len();
                if learned.len() >= 2 {
                    self.clause_watches[learned[0]].push(cid);
                    self.clause_watches[learned[1]].push(cid);
                }
                self.clauses.push(learned);
                self.backtrack_to(backjump);
                self.enqueue(asserting, Reason::Clause(cid));
            } else if self.should_restart() {
                self.restart();
            } else if let Some(var) = self.pick_branch() {
                self.trail_lim.push(self.trail.len());
                // Decide on the saved phase (phase saving; initial phase false).
                self.enqueue(make_lit(var, !self.saved_phase[var]), Reason::Decision);
            } else {
                let model = self.assign.iter().map(|v| v.unwrap_or(false)).collect();
                return XorCdclResult::Sat(model);
            }
        }
    }

    /// Whether enough conflicts have accrued since the last restart to fire the
    /// next Luby restart. A restart only makes sense above level 0.
    fn should_restart(&self) -> bool {
        if self.decision_level() == 0 {
            return false;
        }
        let interval = RESTART_UNIT * luby(self.luby_index);
        self.conflicts_since_restart >= interval
    }

    /// Backjumps to level 0, keeping all learned clauses, activities, and saved
    /// phases, and advances the Luby sequence.
    fn restart(&mut self) {
        self.backtrack_to(0);
        self.conflicts_since_restart = 0;
        self.luby_index += 1;
    }

    /// Bumps `var`'s VSIDS activity by the current increment, rescaling all
    /// activities if any would overflow the `f64` cap.
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            for a in &mut self.activity {
                *a *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
        }
    }

    /// Grows the activity increment for the next conflict (geometric decay of
    /// older bumps relative to newer ones).
    fn decay_activity(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// The conflict produced by propagation: either a conflicting clause id or a
    /// conflicting XOR-constraint id.
    fn propagate(&mut self) -> Option<Conflict> {
        // Interleave clause and XOR propagation off one queue until a fixpoint.
        while self.qhead < self.trail.len() {
            let var = self.trail[self.qhead];
            self.qhead += 1;

            if let Some(conflict) = self.propagate_clauses(var) {
                return Some(conflict);
            }
            if let Some(conflict) = self.propagate_xor(var) {
                return Some(conflict);
            }
        }
        None
    }

    /// Two-watched-literal clause propagation triggered by `var` becoming
    /// assigned. Returns a conflicting clause on an all-false clause.
    fn propagate_clauses(&mut self, var: usize) -> Option<Conflict> {
        let false_lit = lit_not(self.true_literal(var));
        let mut watchers = std::mem::take(&mut self.clause_watches[false_lit]);
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
                    let new_lit = self.clauses[cid][1];
                    self.clause_watches[new_lit].push(cid);
                    watchers.swap_remove(i);
                    moved = true;
                    break;
                }
            }
            if moved {
                continue;
            }
            // No replacement: `other` is unit or the clause is in conflict.
            if self.value(other) == Some(false) {
                conflict = Some(Conflict::Clause(cid));
                break;
            }
            self.enqueue(other, Reason::Clause(cid));
            i += 1;
        }
        self.clause_watches[false_lit] = watchers;
        conflict
    }

    /// Watched-literal XOR propagation triggered by `var` becoming assigned.
    ///
    /// For each constraint watching `var`: try to move the watch to another
    /// unassigned variable; if exactly one unassigned variable remains, force
    /// it; if none remains and the parity is wrong, report an XOR conflict.
    fn propagate_xor(&mut self, var: usize) -> Option<Conflict> {
        let mut watchers = std::mem::take(&mut self.xor_watches[var]);
        let mut i = 0;
        let mut conflict = None;
        while i < watchers.len() {
            let cid = watchers[i];
            match self.visit_xor_watch(cid, var) {
                XorWatchOutcome::Keep => i += 1,
                XorWatchOutcome::Moved(new_var) => {
                    self.xor_watches[new_var].push(cid);
                    watchers.swap_remove(i);
                }
                XorWatchOutcome::Forced(lit) => {
                    self.enqueue(lit, Reason::Xor(cid));
                    i += 1;
                }
                XorWatchOutcome::Conflict => {
                    conflict = Some(Conflict::Xor(cid));
                    break;
                }
            }
        }
        self.xor_watches[var] = watchers;
        conflict
    }

    /// Processes one constraint `cid` whose watched variable `trigger` (now
    /// assigned) just fired.
    ///
    /// Standard two-watched-literal maintenance: try to move the fired watch to
    /// any *unassigned* variable that is not the other watch. If a replacement
    /// is found the constraint stays passive. If none exists, the constraint's
    /// only possibly-free variable is the other watch: if it is still free the
    /// constraint is unit and forces it (the fired watch stays registered,
    /// `Keep`); if it too is assigned the constraint is fully assigned and its
    /// parity decides conflict-or-nothing.
    fn visit_xor_watch(&mut self, cid: usize, trigger: usize) -> XorWatchOutcome {
        let (mut w_keep, mut w_fired) =
            self.xor_watch[cid].expect("watched constraint has two watches");
        let vars = &self.constraints[cid].0;

        // Normalize so `w_fired` is the position of `trigger`.
        if vars[w_keep] == trigger {
            std::mem::swap(&mut w_keep, &mut w_fired);
        }
        debug_assert_eq!(vars[w_fired], trigger, "trigger must be a watched variable");

        // Try to move the fired watch to any unassigned, non-`w_keep` variable.
        // (`w_fired` is assigned now, so it is naturally excluded.)
        if let Some(repl) = vars
            .iter()
            .enumerate()
            .position(|(pos, &v)| pos != w_keep && self.assign[v].is_none())
        {
            self.xor_watch[cid] = Some((w_keep, repl));
            return XorWatchOutcome::Moved(vars[repl]);
        }

        // No replacement: every variable except possibly `w_keep` is assigned.
        // Compute the parity of all assigned variables (rhs ⊕ XOR of trues).
        let mut parity_acc = self.constraints[cid].1;
        for &v in vars {
            if self.assign[v] == Some(true) {
                parity_acc = !parity_acc;
            }
        }

        if self.assign[vars[w_keep]].is_none() {
            // The constraint is unit: force `w_keep`. The single free variable
            // contributes nothing to `parity_acc`, so its forced value is exactly
            // `parity_acc` (what the others leave the rhs needing). Watches stay
            // as they are — the fired (assigned) watch remains registered, which
            // is harmless: it will simply be revisited and kept after backtrack.
            let forced_value = parity_acc;
            XorWatchOutcome::Forced(make_lit(vars[w_keep], !forced_value))
        } else if parity_acc {
            // Fully assigned with the wrong parity ⇒ conflict.
            XorWatchOutcome::Conflict
        } else {
            // Fully assigned, parity holds ⇒ nothing to do; keep the watch.
            XorWatchOutcome::Keep
        }
    }

    /// 1-UIP conflict analysis. Returns the learned clause (asserting literal at
    /// index 0, second-watch literal at index 1) and the backjump level. An
    /// empty learned clause means the conflict is implied at level 0.
    ///
    /// As a side effect it **bumps the VSIDS activity** of every variable that
    /// enters the resolution (each reason clause's literals), which is the set
    /// the learned clause and its resolved antecedents draw from — the standard
    /// `MiniSat`-style bump.
    fn analyze(&mut self, conflict: Conflict) -> (Vec<Lit>, usize) {
        let mut seen = vec![false; self.assign.len()];
        let mut lower: Vec<Lit> = Vec::new();
        let mut path_count = 0usize;
        let mut pivot_var: Option<usize> = None;
        let mut index = self.trail.len();
        let current = self.decision_level();

        // The reason "clause" currently being resolved, materialized as lits.
        let mut clause: Vec<Lit> = self.conflict_clause(conflict);

        loop {
            for &q in &clause {
                let v = lit_var(q);
                // Bump every variable that participates in the resolution, even
                // ones already seen or at level 0 (matching `MiniSat`'s bump on
                // each analyzed reason literal); this keeps recently-active
                // variables hot for branching.
                self.bump_var(v);
                if Some(v) == pivot_var || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
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
                learned.push(lit_not(self.true_literal(var)));
                learned.extend(lower);
                let mut backjump = 0;
                if learned.len() >= 2 {
                    let mut best = 1;
                    for k in 2..learned.len() {
                        if self.level[lit_var(learned[k])] > self.level[lit_var(learned[best])] {
                            best = k;
                        }
                    }
                    learned.swap(1, best);
                    backjump = self.level[lit_var(learned[1])];
                }
                return (learned, backjump);
            }

            // Resolve against the antecedent of `var`, synthesizing the reason
            // clause if the antecedent is an XOR constraint.
            clause = self.reason_clause(var);
        }
    }

    /// Materializes the conflicting clause/constraint as a list of literals.
    fn conflict_clause(&self, conflict: Conflict) -> Vec<Lit> {
        match conflict {
            Conflict::Clause(cid) => self.clauses[cid].clone(),
            // A fully-assigned conflicting XOR: the synthesized reason clause is
            // the all-false clause over its variables at their trail values.
            Conflict::Xor(cid) => self.constraints[cid]
                .0
                .iter()
                .map(|&v| lit_not(self.true_literal(v)))
                .collect(),
        }
    }

    /// The reason clause for the implication that assigned `var`. For a clause
    /// antecedent it is the clause itself; for an XOR antecedent it is the
    /// synthesized clause `(implied_lit ∨ ¬(other vars at their trail values))`.
    fn reason_clause(&self, var: usize) -> Vec<Lit> {
        match self.reason[var] {
            Reason::Clause(cid) => self.clauses[cid].clone(),
            Reason::Xor(cid) => {
                // The implied literal is the one true for `var`; every other
                // variable of the constraint appears negated (at its trail value).
                let implied = self.true_literal(var);
                let mut lits = vec![implied];
                for &v in &self.constraints[cid].0 {
                    if v != var {
                        lits.push(lit_not(self.true_literal(v)));
                    }
                }
                lits
            }
            Reason::Decision | Reason::Unit => {
                // A decision/unit has no contributing antecedent (its literal is
                // already the pivot and was removed from `seen`); an empty reason
                // clause contributes nothing to the resolution.
                Vec::new()
            }
        }
    }

    fn backtrack_to(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let bound = self.trail_lim[level];
            while self.trail.len() > bound {
                let var = self.trail.pop().expect("trail not empty above bound");
                self.assign[var] = None;
                self.reason[var] = Reason::Decision;
            }
            self.trail_lim.truncate(level);
        }
        self.qhead = self.trail.len();
    }

    /// Picks the unassigned variable of highest VSIDS activity, breaking ties to
    /// the lowest variable index (the determinism guarantee). Returns `None` when
    /// every variable is assigned (a full model).
    fn pick_branch(&self) -> Option<usize> {
        let mut best: Option<usize> = None;
        let mut best_act = f64::NEG_INFINITY;
        for (v, slot) in self.assign.iter().enumerate() {
            if slot.is_some() {
                continue;
            }
            // Strictly-greater keeps the lowest index on ties (we scan ascending).
            if self.activity[v] > best_act {
                best_act = self.activity[v];
                best = Some(v);
            }
        }
        best
    }
}

/// The `i`-th term of the Luby sequence (1-indexed by `i+1` internally):
/// `1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, …`. Used to schedule restarts
/// deterministically.
fn luby(i: usize) -> usize {
    // Knuth's closed form. `size` tracks the length of the current power-of-two
    // "super-block" (`2^(seq+1) - 1`); grow until it covers index `i`, then
    // descend into the sub-block containing `i`.
    let mut size = 1usize;
    let mut seq = 0usize;
    let mut i = i;
    while size < i + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size != i + 1 {
        size = (size - 1) / 2;
        seq -= 1;
        i %= size;
    }
    1usize << seq
}

/// The two flavours of conflict the search can hit.
#[derive(Clone, Copy)]
enum Conflict {
    /// An all-false clause (database index).
    Clause(usize),
    /// A fully-assigned XOR constraint with the wrong parity (constraint index).
    Xor(usize),
}

/// What visiting one watched XOR constraint produced.
enum XorWatchOutcome {
    /// The constraint keeps its current watches on this variable.
    Keep,
    /// The watch moved to another variable (carried), so this constraint should
    /// be removed from the current variable's watch list.
    Moved(usize),
    /// The constraint forces a literal (carried).
    Forced(Lit),
    /// The constraint is fully assigned with the wrong parity: a conflict.
    Conflict,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CnfClause, CnfLit, CnfVar, SatResult, XorDpllResult, solve_with_rustsat_batsat_timeout,
        solve_with_xor,
    };
    use std::time::Duration;

    // --- formula construction helpers --------------------------------------

    fn clause(lits: &[(usize, bool)]) -> CnfClause {
        let lits = lits
            .iter()
            .map(|&(v, neg)| {
                let lit = CnfLit::positive(CnfVar::new(v).expect("var fits u32"));
                if neg { lit.negated() } else { lit }
            })
            .collect();
        CnfClause::new(lits)
    }

    fn formula(num_vars: usize, clauses: &[Vec<(usize, bool)>]) -> CnfFormula {
        let mut f = CnfFormula::new(num_vars);
        for c in clauses {
            f.add_clause(clause(c)).expect("valid clause");
        }
        f
    }

    /// Generates the complete clause set encoding `(⊕ of `vars`) = p`, in the
    /// exact form `extract_xors` recognizes.
    fn xor_clauses(vars: &[usize], p: bool) -> Vec<Vec<(usize, bool)>> {
        let k = vars.len();
        let target_parity = !p; // forbidden assignments have parity 1 - p.
        let mut clauses = Vec::new();
        for assign in 0u32..(1u32 << k) {
            let parity = (assign.count_ones() & 1) == 1;
            if parity != target_parity {
                continue;
            }
            let lits: Vec<(usize, bool)> = vars
                .iter()
                .enumerate()
                .map(|(j, &v)| (v, (assign >> j) & 1 == 1))
                .collect();
            clauses.push(lits);
        }
        clauses
    }

    fn assert_sat_model_valid(f: &CnfFormula, model: &[bool]) {
        let constraints = extract_xors(f).system.constraints();
        assert!(
            model_satisfies_all(f, &constraints, model),
            "Sat model {model:?} violates a clause or XOR constraint"
        );
    }

    // --- oracle -------------------------------------------------------------

    /// Brute-force every assignment over `0..n` and collect the models (as
    /// bit-packed `u32`, `var_j` = bit j) satisfying every clause of `f`.
    fn brute_force_models(f: &CnfFormula) -> Vec<u32> {
        let n = f.variable_count();
        assert!(n <= 14, "brute force only intended for small formulas");
        let mut out = Vec::new();
        for assign in 0u32..(1u32 << n) {
            let values: Vec<bool> = (0..n).map(|j| (assign >> j) & 1 == 1).collect();
            if f.evaluate(&values).expect("length matches") {
                out.push(assign);
            }
        }
        out
    }

    fn pack(model: &[bool]) -> u32 {
        let mut bits = 0u32;
        for (j, &b) in model.iter().enumerate() {
            if b {
                bits |= 1u32 << j;
            }
        }
        bits
    }

    // --- hand cases ---------------------------------------------------------

    #[test]
    fn sat_small_formula_with_xor_model_valid() {
        // x0 ⊕ x1 ⊕ x2 = 1 plus a unit forcing x0 = true.
        let mut clauses = xor_clauses(&[0, 1, 2], true);
        clauses.push(vec![(0, false)]);
        let f = formula(3, &clauses);
        match solve_with_xor_cdcl(&f) {
            XorCdclResult::Sat(model) => {
                assert!(model[0], "x0 forced true");
                assert!(model[0] ^ model[1] ^ model[2]);
                assert_sat_model_valid(&f, &model);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn unsat_by_xor_system_alone() {
        // x0 ⊕ x1 = 0, x1 ⊕ x2 = 0, x0 ⊕ x2 = 1 is XOR-contradictory.
        let mut clauses = xor_clauses(&[0, 1], false);
        clauses.extend(xor_clauses(&[1, 2], false));
        clauses.extend(xor_clauses(&[0, 2], true));
        let f = formula(3, &clauses);
        assert_eq!(solve_with_xor_cdcl(&f), XorCdclResult::Unsat);
        assert!(brute_force_models(&f).is_empty());
    }

    #[test]
    fn unsat_by_clauses_alone() {
        // x0 and ¬x0: no XOR gate, contradictory by clauses.
        let f = formula(1, &[vec![(0, false)], vec![(0, true)]]);
        assert_eq!(solve_with_xor_cdcl(&f), XorCdclResult::Unsat);
    }

    #[test]
    fn sat_by_clauses_pruned_by_xor_to_specific_model() {
        // x0 ⊕ x1 = 1 and a unit x1 = false pin x0 = true (the XOR drives it).
        let mut clauses = xor_clauses(&[0, 1], true);
        clauses.push(vec![(1, true)]); // x1 = false
        let f = formula(2, &clauses);
        match solve_with_xor_cdcl(&f) {
            XorCdclResult::Sat(model) => {
                assert!(!model[1], "x1 forced false");
                assert!(model[0], "x0 forced true by the XOR gate");
                assert_sat_model_valid(&f, &model);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn unsat_driven_by_xor_propagation() {
        // x0 ⊕ x1 ⊕ x2 = 0, plus units x0=1, x1=1, x2=1. XOR propagation on the
        // gate variables is what closes it: with x0,x1 set the gate forces x2=0,
        // clashing with the x2=1 unit.
        let mut clauses = xor_clauses(&[0, 1, 2], false);
        clauses.push(vec![(0, false)]);
        clauses.push(vec![(1, false)]);
        clauses.push(vec![(2, false)]);
        let f = formula(3, &clauses);
        assert_eq!(solve_with_xor_cdcl(&f), XorCdclResult::Unsat);
        assert!(brute_force_models(&f).is_empty());
    }

    #[test]
    fn empty_formula_is_sat() {
        let f = CnfFormula::new(0);
        match solve_with_xor_cdcl(&f) {
            XorCdclResult::Sat(model) => assert!(model.is_empty()),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn empty_clause_is_unsat() {
        let f = formula(1, &[vec![]]);
        assert_eq!(solve_with_xor_cdcl(&f), XorCdclResult::Unsat);
    }

    // --- learning-required UNSAT cases --------------------------------------

    /// A parity-chain contradiction that is closed efficiently by learning. The
    /// XOR gates `x_i ⊕ x_{i+1} = 0` chain all variables equal, then
    /// `x0 ⊕ x_last = 1` contradicts; conflict learning records the equalities so the
    /// refutation closes within budget without re-deriving them per branch.
    fn parity_chain_unsat(n: usize) -> CnfFormula {
        assert!(n >= 2);
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
        for i in 0..n - 1 {
            clauses.extend(xor_clauses(&[i, i + 1], false)); // x_i == x_{i+1}
        }
        clauses.extend(xor_clauses(&[0, n - 1], true)); // x0 != x_{n-1}
        formula(n, &clauses)
    }

    #[test]
    fn learning_required_parity_chain_unsat() {
        // The CDCL solver must close these within the conflict budget, and
        // conflict learning must actually fire (≥ 1 resolved conflict) — these
        // instances refute only after the search hits a parity clash, learns
        // the asserting clause, and backjumps.
        for n in [4usize, 8, 12, 16] {
            let f = parity_chain_unsat(n);
            let (result, conflicts) = solve_with_xor_cdcl_conflicts(&f);
            assert_eq!(
                result,
                XorCdclResult::Unsat,
                "parity chain n={n} must be UNSAT within budget"
            );
            assert!(
                conflicts >= 1,
                "parity chain n={n} should drive at least one learned-clause conflict"
            );
        }
    }

    #[test]
    fn learning_required_matches_batsat_on_chain() {
        // Cross-check the learning-required instances against the production
        // solver: same UNSAT verdict.
        for n in [4usize, 8, 12, 16, 20] {
            let f = parity_chain_unsat(n);
            let ours = solve_with_xor_cdcl(&f);
            let theirs = solve_with_rustsat_batsat_timeout(&f, Some(Duration::from_secs(5)))
                .expect("batsat solve");
            assert_eq!(ours, XorCdclResult::Unsat);
            assert!(matches!(theirs, SatResult::Unsat(_)));
        }
    }

    // --- deterministic random generation ------------------------------------

    /// A tiny deterministic LCG (Numerical Recipes constants), no external RNG.
    struct Lcg(u64);

    impl Lcg {
        fn new(seed: u64) -> Self {
            Self(seed)
        }
        fn next_u32(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (self.0 >> 32) as u32
        }
        fn below(&mut self, bound: usize) -> usize {
            (self.next_u32() as usize) % bound
        }
        fn coin(&mut self) -> bool {
            self.next_u32() & 1 == 1
        }
    }

    /// A random small formula: a handful of random short clauses plus a few
    /// planted XOR gates (in the exact form `extract_xors` recognizes).
    fn random_formula(rng: &mut Lcg) -> CnfFormula {
        let num_vars = 3 + rng.below(11); // 3..=13 (<= 14 for brute force)
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();

        let plain = rng.below(5); // 0..=4
        for _ in 0..plain {
            let width = 1 + rng.below(3); // 1..=3
            let mut lits = Vec::new();
            for _ in 0..width {
                let v = rng.below(num_vars);
                lits.push((v, rng.coin()));
            }
            clauses.push(lits);
        }

        let gates = rng.below(3); // 0..=2
        for _ in 0..gates {
            let width = 2 + rng.below(2); // 2..=3
            let mut vars: Vec<usize> = Vec::new();
            let mut guard = 0;
            while vars.len() < width && guard < 64 {
                let v = rng.below(num_vars);
                if !vars.contains(&v) {
                    vars.push(v);
                }
                guard += 1;
            }
            if vars.len() == width {
                vars.sort_unstable();
                clauses.extend(xor_clauses(&vars, rng.coin()));
            }
        }

        formula(num_vars, &clauses)
    }

    // --- brute-force oracle agreement ---------------------------------------

    #[test]
    fn brute_force_agreement_random() {
        let mut rng = Lcg::new(0x5eed_1234_abcd_0001);
        let runs = 500;
        let mut decided = 0;
        for _ in 0..runs {
            let f = random_formula(&mut rng);
            let models = brute_force_models(&f);
            match solve_with_xor_cdcl(&f) {
                XorCdclResult::Sat(model) => {
                    decided += 1;
                    assert_sat_model_valid(&f, &model);
                    assert!(
                        models.contains(&pack(&model)),
                        "Sat model not in the oracle model set"
                    );
                }
                XorCdclResult::Unsat => {
                    decided += 1;
                    assert!(
                        models.is_empty(),
                        "solver says Unsat but the oracle found {} models",
                        models.len()
                    );
                }
                XorCdclResult::Unknown => {}
            }
        }
        assert_eq!(decided, runs, "every small instance must be decided");
    }

    // --- differential vs the production solver ------------------------------

    #[test]
    fn differential_vs_batsat_random() {
        let mut rng = Lcg::new(0xabcd_0099_5eed_2222);
        let runs = 500;
        let timeout = Some(Duration::from_secs(5));
        for _ in 0..runs {
            let f = random_formula(&mut rng);
            let ours = solve_with_xor_cdcl(&f);
            let theirs = solve_with_rustsat_batsat_timeout(&f, timeout)
                .expect("batsat solve must not error on a tiny formula");

            if matches!(ours, XorCdclResult::Unknown) || matches!(theirs, SatResult::Unknown(_)) {
                continue;
            }

            match (&ours, &theirs) {
                (XorCdclResult::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        f.evaluate(model).expect("length matches"),
                        "our Sat model does not satisfy the formula"
                    );
                    assert_sat_model_valid(&f, model);
                }
                (XorCdclResult::Unsat, SatResult::Unsat(_)) => {}
                (ours, theirs) => {
                    panic!("verdict disagreement: ours={ours:?}, batsat={theirs:?}");
                }
            }
        }
    }

    // --- differential vs the naive xor_dpll decider -------------------------

    #[test]
    fn differential_vs_xor_dpll_random() {
        let mut rng = Lcg::new(0x0bad_cafe_1234_5678);
        let runs = 500;
        for _ in 0..runs {
            let f = random_formula(&mut rng);
            let ours = solve_with_xor_cdcl(&f);
            let naive = solve_with_xor(&f);

            // Skip instances either side left undecided.
            if matches!(ours, XorCdclResult::Unknown) || matches!(naive, XorDpllResult::Unknown) {
                continue;
            }

            match (&ours, &naive) {
                (XorCdclResult::Sat(model), XorDpllResult::Sat(_)) => {
                    assert_sat_model_valid(&f, model);
                }
                (XorCdclResult::Unsat, XorDpllResult::Unsat) => {}
                (ours, naive) => {
                    panic!("verdict disagreement vs xor_dpll: ours={ours:?}, naive={naive:?}");
                }
            }
        }
    }

    // --- budget totality ----------------------------------------------------

    #[test]
    fn budget_makes_solver_total() {
        let f = formula(2, &[vec![(0, false)], vec![(1, true)]]);
        assert!(matches!(solve_with_xor_cdcl(&f), XorCdclResult::Sat(_)));
    }

    // --- heuristic unit/regression tests ------------------------------------

    #[test]
    fn luby_sequence_prefix() {
        // The canonical Luby prefix: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
        let expected = [
            1usize, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1,
            2, 4, 8, 16,
        ];
        for (i, &want) in expected.iter().enumerate() {
            assert_eq!(luby(i), want, "luby({i})");
        }
    }

    #[test]
    fn restart_heavy_instance_still_decides() {
        // A small restart unit forces many restarts on the parity chains; the
        // verdict must still be correct (a restart that corrupts state would
        // flip it). We reuse the learning-required chains across a span of n.
        for n in [4usize, 8, 12, 16, 20, 24] {
            let f = parity_chain_unsat(n);
            assert_eq!(
                solve_with_xor_cdcl(&f),
                XorCdclResult::Unsat,
                "restart-heavy parity chain n={n} must stay UNSAT"
            );
        }
    }

    #[test]
    fn vsids_branching_is_deterministic() {
        // Solving the same instance twice must give the identical model (the
        // lowest-index tie-break plus the fixed Luby schedule make the search
        // fully reproducible).
        let mut clauses = xor_clauses(&[0, 1, 2], true);
        clauses.extend(xor_clauses(&[2, 3, 4], false));
        clauses.push(vec![(0, false)]);
        let f = formula(5, &clauses);
        let a = solve_with_xor_cdcl(&f);
        let b = solve_with_xor_cdcl(&f);
        assert_eq!(a, b, "repeated solves must be bit-identical (determinism)");
        assert!(matches!(a, XorCdclResult::Sat(_)));
    }
}
