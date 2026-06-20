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

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::drat::DratStep;
use crate::{CnfAssignment, CnfFormula, CnfLit, CnfVar};

/// Maximum conflicts before the core gives up (safety valve).
const MAX_CONFLICTS: usize = 2_000_000;

/// How many conflicts elapse between wall-clock deadline checks. A fixed
/// conflict cadence (not a per-decision clock read) keeps the deadline test
/// deterministic w.r.t. the search and cheap.
const DEADLINE_CHECK_INTERVAL: usize = 1_024;

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

/// Number of learned clauses tolerated before the first `reduce_db`
/// (MiniSat/Glucose geometric schedule, scaled down for our smaller working
/// instances so reduction actually triggers on real corpora).
const REDUCE_FIRST: usize = 2_000;
/// Additive growth of the learned-clause budget after each `reduce_db`. The
/// budget is `REDUCE_FIRST + REDUCE_INC * reductions`, so reductions become
/// less frequent over time (the standard schedule shape).
const REDUCE_INC: usize = 300;
/// Learned clauses with literal-block distance at or below this are "glue"
/// clauses and are never deleted (the canonical Glucose protection rule).
const GLUE_LBD: usize = 2;
/// Clause-activity decay: each conflict the clause bump increment grows by
/// `1/CLAUSE_DECAY`, so older clause bumps decay relative to fresh ones.
const CLAUSE_DECAY: f64 = 0.999;
/// Rescale all clause activities (and `cla_inc`) when one exceeds this cap, to
/// avoid `f64` overflow without changing their relative order.
const CLAUSE_RESCALE_LIMIT: f64 = 1e20;
/// Multiplier applied on a clause-activity rescale.
const CLAUSE_RESCALE: f64 = 1e-20;

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
    /// The wall-clock deadline passed before a result was reached. Like
    /// [`ProofSolveOutcome::ResourceOut`] this is an *undecided* verdict — the
    /// core never returns `sat`/`unsat` by timeout, so a primary search using
    /// this core can map it to `unknown` without any soundness risk.
    Interrupted,
}

/// Solves `formula` with the proof-producing CDCL core.
pub fn solve_with_drat_proof(formula: &CnfFormula) -> ProofSolveOutcome {
    solve_with_drat_proof_within(formula, None)
}

/// Solves `formula` with the proof-producing CDCL core, stopping early if the
/// optional wall-clock `deadline` passes.
///
/// `deadline` is checked on a deterministic conflict cadence (every
/// `DEADLINE_CHECK_INTERVAL` conflicts), so the search trajectory up to the
/// stopping point is identical to the unbounded run — only *whether* it stops is
/// time-dependent. On expiry the core returns [`ProofSolveOutcome::Interrupted`],
/// an undecided verdict; it never returns `sat`/`unsat` by timeout.
///
/// [`solve_with_drat_proof`] is the `deadline = None` (proof-revalidator) entry.
pub fn solve_with_drat_proof_within(
    formula: &CnfFormula,
    deadline: Option<Instant>,
) -> ProofSolveOutcome {
    Cdcl::new(formula).solve(deadline)
}

fn lit_code(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

/// One entry in a literal's watch list (the `MiniSat`/`BatSat` blocking-literal
/// scheme). `clause` is the watched clause's id; `blocker` is a *cached* literal
/// of that clause OTHER than the watched one. In `propagate`, if `blocker` is
/// already true under the current assignment the clause is satisfied and is
/// skipped *without dereferencing the clause array* — the cache hit that makes
/// BCP fast. The blocker is purely a performance hint: it never changes which
/// propagations or conflicts are derived.
#[derive(Clone, Copy)]
struct Watch {
    clause: CRef,
    blocker: CnfLit,
}

/// A clause reference: a stable index into [`Cdcl::headers`] (and the parallel
/// per-clause metadata vectors). It is the identity used by watches, reasons,
/// and the proof — replacing the old `usize` clause id of the
/// `Vec<Vec<CnfLit>>` layout. [`CRef`]s never move: `headers` only grows
/// (learned clauses are appended) and deletion is by tombstone, so a [`CRef`]
/// stays valid
/// for the whole solve. The clause's literals live in the flat
/// [`Cdcl::arena`] at `[offset .. offset + len]`; that slice never relocates
/// either, since the arena only ever appends.
type CRef = usize;

/// Per-clause index into the packed literal [`Cdcl::arena`]. Mirrors `BatSat`'s
/// `ClauseAllocator`/`ClauseHeader`: all clause literals are stored contiguously
/// in one cache-local arena, and each clause is described by its `(offset, len)`
/// here rather than by a separately-heap-allocated `Vec`. The two watched
/// literals are kept in arena slots `offset+0` and `offset+1` (the slot-0/1
/// convention), exactly as in the prior `Vec<CnfLit>` layout.
#[derive(Clone, Copy)]
struct ClauseHeader {
    offset: usize,
    len: usize,
}

struct Cdcl {
    /// Flat, cache-local arena of all clause literals (problem clauses first,
    /// learned clauses appended). A clause occupies the contiguous slice
    /// `arena[h.offset .. h.offset + h.len]` for its [`ClauseHeader`] `h`. The
    /// arena only grows; existing clause slices never move, so [`CRef`]s and the
    /// `(offset, len)` of already-registered clauses stay valid.
    arena: Vec<CnfLit>,
    /// Per-clause `(offset, len)` headers into [`Cdcl::arena`], indexed by
    /// [`CRef`]. `headers.len()` is the clause count.
    headers: Vec<ClauseHeader>,
    /// Per-literal watch lists, indexed by [`lit_code`]. Each entry carries a
    /// blocking literal (see [`Watch`]).
    watches: Vec<Vec<Watch>>,
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
    /// Number of original (problem) clauses; clause ids `< num_original` are
    /// never deletable. Learned clauses are appended at id `>= num_original`.
    num_original: usize,
    /// Literal-block distance per clause (distinct decision levels among its
    /// literals at learning time). Meaningful for learned clauses only.
    lbd: Vec<usize>,
    /// Clause activity per clause (bumped when the clause participates in a
    /// conflict). Meaningful for learned clauses only.
    cla_activity: Vec<f64>,
    /// Tombstone flag: a deleted learned clause keeps its id (so reasons and
    /// later clause ids stay valid) but is removed from the watch lists and
    /// skipped everywhere. Original clauses are never tombstoned.
    deleted: Vec<bool>,
    /// Current clause-activity bump increment (grows each conflict).
    cla_inc: f64,
    /// Number of `reduce_db` reductions performed so far (drives the budget).
    reductions: usize,
    /// Number of live (non-deleted) learned clauses. Drives the reduce trigger.
    learned_live: usize,
    /// VSIDS order heap: a binary max-heap of variable indices keyed by
    /// `activity` (highest activity at the root), tie-broken by lowest index.
    /// `heap` holds the variables; `heap_pos[v]` is `v`'s position in `heap`,
    /// or [`HEAP_ABSENT`] when `v` is not in the heap. Lazy deletion: assigned
    /// variables are *not* removed on assignment — `pick_branch` pops the root
    /// and skips already-assigned variables, and `backtrack_to` re-inserts a
    /// variable only when it has been popped out (`heap_pos[v] == HEAP_ABSENT`).
    /// All operations are O(log n); the trajectory is identical to the prior
    /// O(n) linear scan because the ordering (`heap_before`) matches its
    /// highest-activity / lowest-index tie-break exactly.
    heap: Vec<usize>,
    heap_pos: Vec<usize>,
}

/// Sentinel in [`Cdcl::heap_pos`] marking a variable that is not currently in
/// the order heap (it has been popped by `pick_branch` and not yet re-inserted).
const HEAP_ABSENT: usize = usize::MAX;

impl Cdcl {
    fn new(formula: &CnfFormula) -> Self {
        let n = formula.variable_count();
        // Pack every clause's literals contiguously into one arena, recording a
        // `(offset, len)` header per clause. This mirrors the prior
        // `Vec<Vec<CnfLit>>` content exactly (same clauses, same order, same
        // intra-clause literal order) — only the storage layout differs.
        let mut arena: Vec<CnfLit> = Vec::new();
        let mut headers: Vec<ClauseHeader> = Vec::with_capacity(formula.clauses().len());
        for clause in formula.clauses() {
            let offset = arena.len();
            arena.extend_from_slice(clause.lits());
            headers.push(ClauseHeader {
                offset,
                len: clause.lits().len(),
            });
        }
        let mut watches = vec![Vec::new(); 2 * n];
        let mut initial_units = Vec::new();
        let mut has_empty_clause = false;
        for (cid, &h) in headers.iter().enumerate() {
            match h.len {
                0 => has_empty_clause = true,
                1 => initial_units.push(arena[h.offset]),
                _ => {
                    // Watch the first two literals; each watch's blocker is the
                    // OTHER watched literal of the same clause.
                    let (l0, l1) = (arena[h.offset], arena[h.offset + 1]);
                    watches[lit_code(l0)].push(Watch {
                        clause: cid,
                        blocker: l1,
                    });
                    watches[lit_code(l1)].push(Watch {
                        clause: cid,
                        blocker: l0,
                    });
                }
            }
        }
        let num_clauses = headers.len();
        let mut cdcl = Self {
            arena,
            headers,
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
            num_original: num_clauses,
            lbd: vec![0; num_clauses],
            cla_activity: vec![0.0; num_clauses],
            deleted: vec![false; num_clauses],
            cla_inc: 1.0,
            reductions: 0,
            learned_live: 0,
            heap: Vec::with_capacity(n),
            heap_pos: vec![HEAP_ABSENT; n],
        };
        // Seed the order heap with every variable. All activities are 0.0, so
        // the heap order is purely by index; inserting in ascending index order
        // builds a valid heap (each insert percolates up against equal-activity
        // parents whose index is smaller, so no swaps occur — O(n) total).
        for v in 0..n {
            cdcl.heap_insert(v);
        }
        cdcl
    }

    /// The literals of clause `cid`, as a cache-local slice into the arena.
    #[inline]
    fn lits(&self, cid: CRef) -> &[CnfLit] {
        let h = self.headers[cid];
        &self.arena[h.offset..h.offset + h.len]
    }

    /// The number of literals in clause `cid`.
    #[inline]
    fn clause_len(&self, cid: CRef) -> usize {
        self.headers[cid].len
    }

    /// The `i`-th literal of clause `cid` (0-based within the clause).
    #[inline]
    fn lit_at(&self, cid: CRef, i: usize) -> CnfLit {
        let h = self.headers[cid];
        self.arena[h.offset + i]
    }

    /// Appends a clause's literals to the arena and pushes its header, returning
    /// the new clause's stable [`CRef`]. The arena only grows here, so no
    /// existing clause slice moves.
    fn alloc_clause(&mut self, lits: &[CnfLit]) -> CRef {
        let offset = self.arena.len();
        self.arena.extend_from_slice(lits);
        let cid = self.headers.len();
        self.headers.push(ClauseHeader {
            offset,
            len: lits.len(),
        });
        cid
    }

    /// Order-heap comparator: returns `true` when variable `a` should sit closer
    /// to the root than `b`, i.e. `a` is the *preferred* branching variable.
    /// Highest activity wins; ties break to the lower index. This mirrors the
    /// prior linear scan exactly, keeping the search trajectory identical.
    fn heap_before(&self, a: usize, b: usize) -> bool {
        let (aa, ab) = (self.activity[a], self.activity[b]);
        // Exact `f64` equality is intentional and load-bearing: it must detect
        // ties *exactly* the way the reference linear scan does (which replaces
        // the best only on a strictly-greater activity, i.e. keeps the lower
        // index on bitwise-equal activity). An epsilon would change the
        // tie-break and so the search trajectory. The two activities are produced
        // by identical arithmetic, so bitwise equality is the correct predicate.
        #[allow(clippy::float_cmp)]
        let tie = aa == ab;
        aa > ab || (tie && a < b)
    }

    /// Restores the heap property by moving the element at `i` toward the root
    /// while it precedes its parent. O(log n).
    fn heap_percolate_up(&mut self, mut i: usize) {
        let x = self.heap[i];
        while i != 0 {
            let parent = (i - 1) / 2;
            let p = self.heap[parent];
            if !self.heap_before(x, p) {
                break;
            }
            self.heap[i] = p;
            self.heap_pos[p] = i;
            i = parent;
        }
        self.heap[i] = x;
        self.heap_pos[x] = i;
    }

    /// Restores the heap property by moving the element at `i` toward the leaves
    /// while a child precedes it. O(log n).
    fn heap_percolate_down(&mut self, mut i: usize) {
        let x = self.heap[i];
        let len = self.heap.len();
        loop {
            let left = 2 * i + 1;
            if left >= len {
                break;
            }
            let right = left + 1;
            let child = if right < len && self.heap_before(self.heap[right], self.heap[left]) {
                right
            } else {
                left
            };
            let c = self.heap[child];
            if !self.heap_before(c, x) {
                break;
            }
            self.heap[i] = c;
            self.heap_pos[c] = i;
            i = child;
        }
        self.heap[i] = x;
        self.heap_pos[x] = i;
    }

    /// True when `var` currently lives in the order heap.
    fn heap_contains(&self, var: usize) -> bool {
        self.heap_pos[var] != HEAP_ABSENT
    }

    /// Inserts `var` into the order heap (no-op if already present). O(log n).
    fn heap_insert(&mut self, var: usize) {
        if self.heap_contains(var) {
            return;
        }
        let i = self.heap.len();
        self.heap.push(var);
        self.heap_pos[var] = i;
        self.heap_percolate_up(i);
    }

    /// Removes and returns the root (preferred) variable. O(log n). The caller
    /// must ensure the heap is non-empty.
    fn heap_remove_min(&mut self) -> usize {
        let root = self.heap[0];
        let last = *self.heap.last().expect("heap not empty");
        self.heap_pos[root] = HEAP_ABSENT;
        if self.heap.len() == 1 {
            self.heap.pop();
            return root;
        }
        self.heap[0] = last;
        self.heap_pos[last] = 0;
        self.heap.pop();
        self.heap_percolate_down(0);
        root
    }

    /// Bumps `var`'s VSIDS activity, rescaling all activities if it overflows the
    /// cap (preserving their relative order).
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            // Rescale every activity (and `var_inc`) by the same positive factor.
            // This preserves the *strict* order of distinct activities, BUT it can
            // collapse two distinct tiny activities to an equal value (rounding /
            // underflow to 0.0). Our comparator's secondary key is the variable
            // index, so a newly-formed tie introduces an ordering constraint the
            // existing heap layout never enforced — silently violating the heap
            // property. Re-heapify from scratch so the heap matches the post-
            // rescale total order exactly. Rescale is rare (activity must exceed
            // 1e100), so this O(n) rebuild does not affect amortized per-decision
            // cost; every other heap operation stays O(log n).
            for a in &mut self.activity {
                *a *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
            self.heap_rebuild();
            return;
        }
        // The variable's activity only ever *increases* here, so it can only move
        // toward the root: a single sift-up restores the heap. O(log n). Variables
        // not currently in the heap (assigned-and-popped) need no update — they
        // are re-inserted at their (now higher) activity when they unassign.
        if self.heap_contains(var) {
            let i = self.heap_pos[var];
            self.heap_percolate_up(i);
        }
    }

    /// Rebuilds the order heap in place over its current membership, restoring
    /// the heap property under the current `activity` values (and the index
    /// tie-break). Floyd's bottom-up heapify: O(n) over the heap's size. Used
    /// after a VSIDS rescale, which can collapse distinct activities into ties
    /// and thereby invalidate the prior layout.
    fn heap_rebuild(&mut self) {
        let len = self.heap.len();
        if len <= 1 {
            return;
        }
        // Percolate down every internal node, highest index first (Floyd build).
        let mut i = len / 2;
        loop {
            i -= 1;
            self.heap_percolate_down(i);
            if i == 0 {
                break;
            }
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

    fn solve(mut self, deadline: Option<Instant>) -> ProofSolveOutcome {
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
                // Deterministic deadline cadence: only read the clock once every
                // `DEADLINE_CHECK_INTERVAL` conflicts. On expiry, abandon the
                // search with an *undecided* verdict (never sat/unsat by timeout).
                if let Some(deadline) = deadline
                    && self.conflicts % DEADLINE_CHECK_INTERVAL == 0
                    && Instant::now() >= deadline
                {
                    return ProofSolveOutcome::Interrupted;
                }
                let (learned, backjump, lbd) = self.analyze(conflict);
                self.proof.push(DratStep::Add(learned.clone()));
                if learned.is_empty() {
                    return ProofSolveOutcome::Unsat(self.proof);
                }
                let asserting = learned[0];
                let clause_id = self.alloc_clause(&learned);
                if learned.len() >= 2 {
                    self.watches[lit_code(learned[0])].push(Watch {
                        clause: clause_id,
                        blocker: learned[1],
                    });
                    self.watches[lit_code(learned[1])].push(Watch {
                        clause: clause_id,
                        blocker: learned[0],
                    });
                }
                // Register the new learned clause's deletion metadata.
                self.lbd.push(lbd);
                self.cla_activity.push(0.0);
                self.deleted.push(false);
                self.learned_live += 1;
                self.bump_clause(clause_id);
                self.backtrack_to(backjump);
                self.enqueue(asserting, Some(clause_id));
                self.conflicts_since_restart += 1;
                self.decay();
                self.decay_clause();
                // Learned-clause-database reduction (Glucose/MiniSat schedule):
                // when the live learned-clause count exceeds the growing budget,
                // delete the worst half (sound: see `reduce_db`). Must run at a
                // point where no decisions are pending so the trail/reasons are
                // consistent; here we are immediately after a backjump+enqueue
                // and before propagation, which is safe (locked-clause check
                // reads the current trail).
                if self.learned_live > self.reduce_budget() {
                    self.reduce_db();
                    self.reductions += 1;
                }
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

    /// Two-watched-literal unit propagation with **blocking literals** (the
    /// `MiniSat`/`BatSat` BCP). Returns a conflicting clause id, or `None` if the
    /// queue drains with no conflict.
    ///
    /// The watch list of the now-false literal is scanned with an in-place `i`
    /// (read) / `j` (write) compaction (mirroring `BatSat`'s `propagate`):
    ///
    /// 1. If a watch's cached `blocker` is already true, the clause is satisfied;
    ///    keep the watch and skip *without touching the clause array* — the fast
    ///    path that most watches take.
    /// 2. Otherwise dereference the clause, put the false literal at index 1, and:
    ///    - if the other watched literal (index 0) is true, keep the watch
    ///      (refreshing its blocker to that literal) and continue;
    ///    - else look for a non-false replacement literal to watch — if found,
    ///      move the watch to that literal's list (blocker = index-0 literal);
    ///    - else the clause is unit/conflicting: keep the watch (blocker = the
    ///      index-0 literal). If index 0 is false → conflict; otherwise enqueue
    ///      index 0 as a unit implication.
    ///
    /// Blocking literals only reduce the *work* to find propagations/conflicts;
    /// the derived implications and conflicts are identical to the plain scheme.
    fn propagate(&mut self) -> Option<usize> {
        let mut conflict = None;
        while self.qhead < self.trail.len() {
            let var = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = self.true_literal(var).negated();
            let code = lit_code(false_lit);

            let mut watchers = std::mem::take(&mut self.watches[code]);
            let end = watchers.len();
            let mut i = 0usize;
            let mut j = 0usize;
            'clauses: while i < end {
                // (1) Fast path: a true blocker means the clause is satisfied;
                // keep the watch and move on without inspecting the clause.
                let blocker = watchers[i].blocker;
                if self.value(blocker) == Some(true) {
                    watchers[j] = watchers[i];
                    j += 1;
                    i += 1;
                    continue;
                }

                let cid = watchers[i].clause;
                // Keep the falsified literal at slot 1 (arena slot offset+1).
                let off = self.headers[cid].offset;
                if self.arena[off] == false_lit {
                    self.arena.swap(off, off + 1);
                }
                i += 1;

                // (2) If the other watched literal is true, the clause is
                // satisfied; keep this watch with its blocker refreshed to it.
                let first = self.arena[off];
                if first != blocker && self.value(first) == Some(true) {
                    watchers[j] = Watch {
                        clause: cid,
                        blocker: first,
                    };
                    j += 1;
                    continue;
                }

                // Look for a non-false literal to watch instead of `false_lit`.
                let len = self.headers[cid].len;
                for k in 2..len {
                    if self.value(self.arena[off + k]) != Some(false) {
                        self.arena.swap(off + 1, off + k);
                        // Move the watch to the new literal's list; its blocker
                        // is the surviving (slot-0) watched literal. This watch
                        // is dropped from the current list (not copied to `j`).
                        let new_code = lit_code(self.arena[off + 1]);
                        self.watches[new_code].push(Watch {
                            clause: cid,
                            blocker: first,
                        });
                        continue 'clauses;
                    }
                }

                // No replacement: the clause is unit or conflicting under the
                // current assignment. Keep this watch (blocker = index-0 lit).
                watchers[j] = Watch {
                    clause: cid,
                    blocker: first,
                };
                j += 1;
                if self.value(first) == Some(false) {
                    // Conflict: stop scanning, but preserve the remaining (not
                    // yet visited) watches by copying them down to `j`.
                    conflict = Some(cid);
                    while i < end {
                        watchers[j] = watchers[i];
                        j += 1;
                        i += 1;
                    }
                    break;
                }
                self.enqueue(first, Some(cid));
            }
            watchers.truncate(j);
            self.watches[code] = watchers;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// 1-UIP conflict analysis: returns the learned clause (asserting literal at
    /// index 0, second-watch literal at index 1), the backjump level, and the
    /// learned clause's literal-block distance (the number of distinct decision
    /// levels among its literals — the LBD/glue measure). An empty result means
    /// the conflict is implied at level 0 (the empty clause).
    fn analyze(&mut self, conflict: usize) -> (Vec<CnfLit>, usize, usize) {
        let mut seen = vec![false; self.assign.len()];
        let mut lower: Vec<CnfLit> = Vec::new();
        let mut path_count = 0usize;
        let mut pivot_var: Option<usize> = None;
        let mut index = self.trail.len();
        let mut clause_id = conflict;
        let current = self.decision_level();

        loop {
            // Bump the activity of any learned clause that participates in this
            // conflict, so frequently-useful learned clauses survive reduceDB.
            self.bump_clause(clause_id);
            // Clone the reason clause's literals so we can bump activities while
            // walking it (the borrow checker forbids reading the arena and
            // mutating `self.activity` at once; reason clauses are short).
            let lits = self.lits(clause_id).to_vec();
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
                return (Vec::new(), 0, 0);
            }

            let var = self.trail[index];
            seen[var] = false;
            path_count -= 1;
            pivot_var = Some(var);

            if path_count == 0 {
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negated());
                learned.extend(lower);
                // Recursive (self-subsuming) minimization: drop literals whose
                // negation is implied — through their reason chains — by the rest
                // of the clause. Shrinks the learned clause more aggressively than
                // one-level subsumption (MiniSat ccmin_mode=2): smaller proof
                // steps, faster propagation, lower backjumps, fewer conflicts.
                //
                // At this point `seen[v]` is true exactly for the non-asserting
                // learned-clause variables (`lower`), and false for the asserting
                // literal's variable — the same precondition BatSat relies on.
                self.minimize(&mut learned, &mut seen);
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
                let lbd = self.compute_lbd(&learned);
                return (learned, backjump, lbd);
            }

            clause_id = self.reason[var].expect("implied literal has a reason clause");
        }
    }

    /// An abstraction of a variable's decision level as a single-bit mask
    /// (`MiniSat`'s `abstractLevel`). The union of these masks over a clause's
    /// literals lets [`Self::lit_redundant`] short-circuit: a reason literal
    /// whose level-bit is absent from the clause's mask comes from a decision
    /// level unrelated to the clause and therefore cannot be resolved away.
    #[inline]
    fn abstract_level(&self, var: usize) -> u32 {
        1u32 << (self.level[var] & 31)
    }

    /// Recursive (self-subsuming) minimization of a learned clause — `MiniSat`
    /// `ccmin_mode = 2`, mirroring `BatSat`'s `minimize_conflict`.
    ///
    /// A non-asserting literal `l` is dropped when its negation is already
    /// entailed by the remaining clause literals through `l`'s reason chain:
    /// every literal in `reason(l)` must be in the clause (`seen`), fixed at
    /// level 0, or itself recursively redundant. Resolving the clause against
    /// those reason chains keeps it entailed, so the minimized clause is still
    /// RUP and the emitted DRAT step stays checkable. Decision literals (no
    /// reason) are never redundant, and the asserting literal (index 0) is
    /// always kept.
    ///
    /// Precondition: `seen[v]` is true exactly for the non-asserting
    /// learned-clause variables (and false for the asserting literal's
    /// variable). `seen` is owned by [`Self::analyze`] (a per-conflict local)
    /// and discarded when that frame returns, so no state leaks across
    /// conflicts; the result depends only on this conflict's `seen` state, the
    /// reason graph, and the input clause order, hence is deterministic
    /// (identical input ⇒ identical clause ⇒ identical proof structure).
    fn minimize(&self, learned: &mut Vec<CnfLit>, seen: &mut [bool]) {
        if learned.len() <= 1 {
            return;
        }
        // Mask of the decision levels present among the non-asserting literals.
        let mut abstract_levels = 0u32;
        for &l in &learned[1..] {
            abstract_levels |= self.abstract_level(l.var().index());
        }
        // Scratch reused across the `lit_redundant` calls in this minimization.
        // `seen` marks set during a *successful* probe are kept (those literals
        // are now known to be in/implied by the clause, which is sound for
        // later probes); a *failed* probe rolls back its own marks. Removed
        // literals stay marked, which is correct and matches BatSat — `seen` is
        // never read again after this conflict.
        let mut stack: Vec<CnfLit> = Vec::new();
        let mut to_clear: Vec<usize> = Vec::new();
        let mut write = 1usize;
        for read in 1..learned.len() {
            let lit = learned[read];
            let v = lit.var().index();
            // Keep `lit` if it is a decision (no reason) or not redundant.
            if self.reason[v].is_none()
                || !self.lit_redundant(lit, abstract_levels, seen, &mut stack, &mut to_clear)
            {
                learned[write] = lit;
                write += 1;
            }
        }
        learned.truncate(write);
    }

    /// Can literal `p` be removed from the learned clause? Iterative
    /// self-subsumption check (no recursion — an explicit `stack` avoids stack
    /// overflow on deep reason chains), mirroring `BatSat`'s `lit_redundant`.
    ///
    /// `p` is redundant iff, walking its reason chain, every encountered
    /// literal is fixed at level 0, already in the clause (`seen`), or has a
    /// reason and a level present in `abstract_levels` (so it can in turn be
    /// resolved away). The first literal that has no reason, or whose level is
    /// outside `abstract_levels`, makes `p` irredundant — and we roll back every
    /// `seen` mark this call set (recorded in `to_clear`) before returning
    /// `false`, so a failed probe leaves no state behind. On success the marks
    /// set during the walk are retained (the literals are now known redundant),
    /// recorded in `to_clear` for the caller to clear once minimization ends.
    fn lit_redundant(
        &self,
        p: CnfLit,
        abstract_levels: u32,
        seen: &mut [bool],
        stack: &mut Vec<CnfLit>,
        to_clear: &mut Vec<usize>,
    ) -> bool {
        stack.clear();
        stack.push(p);
        let top = to_clear.len();
        while let Some(q) = stack.pop() {
            let qv = q.var().index();
            let rid = self.reason[qv].expect("lit_redundant only walks literals with a reason");
            // Skip the propagated literal itself (slot 0 of its reason clause).
            for &l in &self.lits(rid)[1..] {
                let lv = l.var().index();
                if self.level[lv] == 0 || seen[lv] {
                    continue;
                }
                if self.reason[lv].is_some() && (self.abstract_level(lv) & abstract_levels) != 0 {
                    // `l` may itself be redundant: mark it and recurse.
                    seen[lv] = true;
                    stack.push(l);
                    to_clear.push(lv);
                } else {
                    // `l` has no reason or comes from an unrelated decision
                    // level: `p` cannot be removed. Roll back this probe.
                    for &v in &to_clear[top..] {
                        seen[v] = false;
                    }
                    to_clear.truncate(top);
                    return false;
                }
            }
        }
        true
    }

    /// Literal-block distance of a clause: the number of distinct decision
    /// levels among its literals' current assignments. Computed at learning
    /// time (every literal of a freshly learned clause is assigned). LBD = 2
    /// "glue" clauses are the most valuable and are kept permanently.
    fn compute_lbd(&self, clause: &[CnfLit]) -> usize {
        // Small clauses dominate; a stack-free de-dup over a bounded set of
        // levels via a sorted scratch vec keeps this deterministic and cheap.
        let mut levels: Vec<usize> = clause.iter().map(|l| self.level[l.var().index()]).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len()
    }

    /// Bumps a learned clause's activity, rescaling all clause activities (and
    /// `cla_inc`) if it overflows the cap (preserving their relative order).
    fn bump_clause(&mut self, cid: usize) {
        if cid < self.num_original {
            return; // only learned clauses carry activity
        }
        self.cla_activity[cid] += self.cla_inc;
        if self.cla_activity[cid] > CLAUSE_RESCALE_LIMIT {
            for a in &mut self.cla_activity[self.num_original..] {
                *a *= CLAUSE_RESCALE;
            }
            self.cla_inc *= CLAUSE_RESCALE;
        }
    }

    /// Decays clause activity by growing the bump increment (the `MiniSat`
    /// trick, mirrored for clauses).
    fn decay_clause(&mut self) {
        self.cla_inc /= CLAUSE_DECAY;
    }

    /// The learned-clause budget for the current reduction round (geometric
    /// schedule: grows by `REDUCE_INC` after each reduction).
    fn reduce_budget(&self) -> usize {
        REDUCE_FIRST + REDUCE_INC * self.reductions
    }

    /// Is learned clause `cid` currently the reason (antecedent) for an assigned
    /// literal? Such a clause is LOCKED: deleting it would corrupt the
    /// implication graph, so it must be protected.
    fn is_locked(&self, cid: CRef) -> bool {
        if self.clause_len(cid) == 0 {
            return false;
        }
        let v = self.lit_at(cid, 0).var().index();
        self.assign[v].is_some() && self.reason[v] == Some(cid)
    }

    /// Glucose/MiniSat `reduceDB`: delete the worst (low-activity) half of the
    /// deletable learned clauses, protecting originals, locked clauses, and
    /// glue (LBD ≤ [`GLUE_LBD`]) clauses. Each deleted clause emits a DRAT
    /// deletion step so the proof stays checkable, and the watch lists are
    /// rebuilt over the surviving clauses (no dangling ids).
    ///
    /// Soundness/completeness: every learned clause was RUP-derived, so the
    /// formula's models are unchanged by deletion; protecting locked clauses
    /// keeps the implication graph intact; the search can re-derive any deleted
    /// clause, so completeness is preserved.
    fn reduce_db(&mut self) {
        // Candidates for deletion: live, learned, non-glue, non-locked clauses.
        let mut candidates: Vec<CRef> = (self.num_original..self.headers.len())
            .filter(|&cid| {
                !self.deleted[cid]
                    && self.clause_len(cid) > 2
                    && self.lbd[cid] > GLUE_LBD
                    && !self.is_locked(cid)
            })
            .collect();
        if candidates.is_empty() {
            return;
        }
        // Sort worst-first: lower activity is worse. Tie-break by clause id so
        // the order is total and deterministic (no hashmap iteration).
        candidates.sort_by(|&x, &y| {
            self.cla_activity[x]
                .partial_cmp(&self.cla_activity[y])
                .unwrap_or(core::cmp::Ordering::Equal)
                .then(x.cmp(&y))
        });
        // Delete the worst half (the standard fraction).
        let to_delete = candidates.len() / 2;
        for &cid in candidates.iter().take(to_delete) {
            self.deleted[cid] = true;
            self.learned_live -= 1;
            // Emit a DRAT deletion so the proof replays consistently. The
            // checker matches clauses as sets, and this clause was added
            // verbatim, so the stored literals delete it.
            self.proof.push(DratStep::Delete(self.lits(cid).to_vec()));
        }
        if to_delete > 0 {
            self.rebuild_watches();
        }
    }

    /// Rebuilds every watch list from scratch over the live (non-deleted)
    /// clauses, watching the first two literals of each. Called after
    /// `reduce_db` so no watch list references a tombstoned clause id.
    fn rebuild_watches(&mut self) {
        for w in &mut self.watches {
            w.clear();
        }
        for cid in 0..self.headers.len() {
            if self.deleted[cid] {
                continue;
            }
            if self.clause_len(cid) >= 2 {
                let (l0, l1) = (self.lit_at(cid, 0), self.lit_at(cid, 1));
                // Each watch's blocker is the other watched literal.
                self.watches[lit_code(l0)].push(Watch {
                    clause: cid,
                    blocker: l1,
                });
                self.watches[lit_code(l1)].push(Watch {
                    clause: cid,
                    blocker: l0,
                });
            }
        }
    }

    fn backtrack_to(&mut self, level: usize) {
        if level < self.trail_lim.len() {
            let bound = self.trail_lim[level];
            while self.trail.len() > bound {
                let var = self.trail.pop().expect("trail not empty above bound");
                self.assign[var] = None;
                self.reason[var] = None;
                // The variable becomes a branchable candidate again. Re-insert it
                // into the order heap *only* if it was popped out by `pick_branch`
                // (lazy deletion): variables still in the heap stay put, avoiding
                // re-insertion churn. O(log n) per actually-removed variable.
                if !self.heap_contains(var) {
                    self.heap_insert(var);
                }
            }
            self.trail_lim.truncate(level);
        }
        self.qhead = self.trail.len();
    }

    fn pick_branch(&mut self) -> Option<usize> {
        // Pop roots (highest activity, lowest index on ties) until an unassigned
        // variable surfaces — the canonical MiniSat lazy-deletion order heap.
        // Each `heap_remove_min` is O(log n); assigned roots are discarded (their
        // re-insertion is deferred to `backtrack_to`). When the heap empties with
        // every variable assigned, the formula is satisfied → `None`.
        //
        // This yields exactly the variable the prior O(n) linear scan would have
        // chosen (same highest-activity / lowest-index tie-break), so the search
        // trajectory is unchanged.
        while !self.heap.is_empty() {
            let var = self.heap_remove_min();
            if self.assign[var].is_none() {
                return Some(var);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Cdcl, Instant, ProofSolveOutcome, Watch, lit_code, solve_with_drat_proof,
        solve_with_drat_proof_within,
    };
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

    /// A generous (already-passed) deadline does not change the verdict: the
    /// deadline-bounded entry decides the same satisfiable/unsatisfiable formulas
    /// the unbounded entry does.
    #[test]
    fn generous_deadline_does_not_change_verdict() {
        let far = Instant::now().checked_add(std::time::Duration::from_secs(3600));
        // Unsat fixture.
        let unsat = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        assert!(matches!(
            solve_with_drat_proof_within(&unsat, far),
            ProofSolveOutcome::Unsat(_)
        ));
        // Sat fixture.
        let sat = formula(3, &[&[1, 2], &[-1, 3], &[-2, -3]]);
        let ProofSolveOutcome::Sat(model) = solve_with_drat_proof_within(&sat, far) else {
            panic!("expected sat under a far deadline");
        };
        assert!(model.satisfies(&sat).unwrap());
    }

    /// An already-expired deadline yields `Interrupted` — an *undecided* verdict,
    /// never a wrong sat/unsat — on a formula that needs at least one conflict.
    /// (Trivial level-0 unit/empty-clause cases short-circuit before the conflict
    /// loop, so the fixture must force real search past the first conflict.)
    #[test]
    fn expired_deadline_yields_interrupted_never_a_wrong_verdict() {
        // Pigeonhole 4-into-3 forces many conflicts; with a deadline already in
        // the past, the core stops at the first cadence check without deciding.
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
        let f = formula(12, &refs);

        let past = Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("clock far enough from epoch");
        // The cadence is every DEADLINE_CHECK_INTERVAL conflicts, so this larger
        // instance reaches a check before finishing; the verdict is Interrupted.
        match solve_with_drat_proof_within(&f, Some(past)) {
            ProofSolveOutcome::Interrupted => {}
            // The instance is genuinely unsat, so deciding it before the first
            // cadence check is also acceptable (just not a *wrong* verdict).
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(&f, &proof), Ok(true));
            }
            other => panic!("expired deadline must never yield sat: got {other:?}"),
        }
    }

    /// Determinism: the same formula produces byte-identical outcomes across runs
    /// (no hashmap iteration order in the core, no nondeterministic branching).
    #[test]
    fn solve_is_deterministic() {
        let f = formula(
            6,
            &[
                &[1, 2, 3],
                &[-1, 4],
                &[-2, -4, 5],
                &[-3, -5, 6],
                &[-6, 1],
                &[2, -3, -4],
            ],
        );
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "same input must yield same output");
    }

    /// One-level reference for the comparison test below: a literal is dropped
    /// only if *every* literal of its reason is already in the learned clause
    /// (or level 0). This is the pre-recursion behavior; recursive minimization
    /// must remove a (strict) superset of these literals.
    fn minimize_one_level(cdcl: &Cdcl, learned: &mut Vec<CnfLit>) {
        if learned.len() <= 1 {
            return;
        }
        let mut in_learned = vec![false; cdcl.assign.len()];
        for &l in learned.iter() {
            in_learned[l.var().index()] = true;
        }
        let asserting_var = learned[0].var().index();
        learned.retain(|&l| {
            let v = l.var().index();
            if v == asserting_var {
                return true;
            }
            match cdcl.reason[v] {
                None => true,
                Some(rid) => !cdcl.lits(rid).iter().all(|&q| {
                    let qv = q.var().index();
                    qv == v || in_learned[qv] || cdcl.level[qv] == 0
                }),
            }
        });
    }

    /// Recursive minimization must remove *more* literals than one-level
    /// self-subsumption on a clause whose redundancy is only visible through a
    /// two-step reason chain — and the literal it removes must genuinely be
    /// implied (verified by replaying the resulting unsat proof end-to-end in
    /// the companion test). Reason graph (all at level 1, the same decision):
    ///   uip=v0, a=v1, b=v2, c=v3, learned = [~v0, ~v1, ~v2].
    ///   reason(v2) = [~v2, v3]   (so b is implied by ¬c, c ∉ clause)
    ///   reason(v3) = [~v3, v1]   (so c is implied by ¬a, a ∈ clause)
    /// One-level keeps ~v2 (its reason contains c ∉ clause). Recursive sees that
    /// c is itself redundant (its only non-clause reason literal, a, is in the
    /// clause), so ~v2 is redundant too.
    #[test]
    fn recursive_minimization_removes_more_than_one_level() {
        // The clauses double as the reason clauses; literal at slot 0 of each is
        // the propagated literal that `lit_redundant` skips.
        let neg = |v: usize| CnfLit::positive(CnfVar::new(v).unwrap()).negated();
        // clause 0: reason(v2) = [~v2, v3]; clause 1: reason(v3) = [~v3, v1].
        let f = formula(4, &[&[-3, 4], &[-4, 2]]);
        let mut cdcl = Cdcl::new(&f);
        // Hand-build the implication graph at decision level 1 (minimize reads
        // only `level` and `reason`, so leaving `assign` untouched is fine).
        for v in 0..4 {
            cdcl.level[v] = 1;
        }
        cdcl.reason[0] = None; // uip: kept regardless
        cdcl.reason[1] = None; // a: a decision literal — never redundant, always kept
        cdcl.reason[2] = Some(0); // b's reason is clause 0 = [~v2, v3]
        cdcl.reason[3] = Some(1); // c's reason is clause 1 = [~v3, v1]

        let learned_init = vec![neg(0), neg(1), neg(2)];

        // One-level keeps ~v2 (3 literals remain).
        let mut one = learned_init.clone();
        minimize_one_level(&cdcl, &mut one);
        assert_eq!(one.len(), 3, "one-level cannot remove ~v2 here");

        // Recursive removes ~v2 (2 literals remain: ~v0, ~v1).
        let mut rec = learned_init.clone();
        // `seen` precondition: non-asserting learned vars (1,2) marked.
        let mut seen = vec![false; cdcl.assign.len()];
        seen[1] = true;
        seen[2] = true;
        cdcl.minimize(&mut rec, &mut seen);
        assert_eq!(
            rec,
            vec![neg(0), neg(1)],
            "recursive minimization must drop ~v2 via the v3 reason chain"
        );
        assert!(
            rec.len() < one.len(),
            "recursive must remove strictly more than one-level"
        );
    }

    /// End-to-end soundness for recursive minimization: a battery of random
    /// unsat CNFs (where the recursive scheme is exercised) must still produce
    /// DRAT proofs that the independent checker accepts — i.e. recursively
    /// minimized learned clauses stay RUP. Pairs with the disagree-zero
    /// batteries above (which already run the recursive path on every conflict).
    #[test]
    fn recursive_minimization_keeps_proofs_drat_checkable() {
        let mut state = 0x05ee_d5a7_1234_abcdu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut unsat_seen = 0u32;
        for _ in 0..400 {
            let vars = 3 + usize::try_from(next() % 5).unwrap(); // 3..=7
            let clause_count = 6 + usize::try_from(next() % 20).unwrap();
            let mut f = CnfFormula::new(vars);
            let vb = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vb).unwrap() + 1;
                    lits.push(lit(if next() & 1 == 0 { v } else { -v }));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            if let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) {
                assert_eq!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "recursively minimized proof must DRAT-check"
                );
                unsat_seen += 1;
            }
        }
        assert!(unsat_seen > 0, "battery must include unsat instances");
    }

    /// Soundness stress: ≥100 small random 3-CNFs, fixed seed. The native core
    /// and `BatSat` must never disagree (`DISAGREE = 0`), every native `sat` model
    /// must satisfy, every native `unsat` must DRAT-check.
    #[test]
    fn random_3cnf_agreement_stress_disagree_zero() {
        let mut state = 0x0bad_c0de_dead_beefu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..200 {
            let vars = 4 + below(&mut next, 6); // 4..=9 variables
            let clause_count = 5 + below(&mut next, 25);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE: native={native:?} batsat={other:?}");
                }
            }
        }
    }

    /// Blocking-literal BCP is a pure propagation optimization: it must NOT
    /// change any verdict. This battery re-affirms that — over a fresh seed of
    /// many random CNFs the blocking-literal core agrees with `BatSat` on every
    /// instance (`DISAGREE = 0`), every `sat` model satisfies, and every `unsat`
    /// proof (derived via the new `Watch`/blocker propagate) DRAT-checks. A
    /// blocker is a performance hint only; the implications and conflicts derived
    /// are identical to the plain two-watched scheme.
    #[test]
    fn blocking_literal_bcp_preserves_verdicts_disagree_zero() {
        let mut state = 0xb10c_11ad_5a7b_eef0u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..300 {
            let vars = 3 + below(&mut next, 8); // 3..=10 variables
            let clause_count = 4 + below(&mut next, 28);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + below(&mut next, 4); // 1..=4 literals (varied widths)
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
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE (blocking-literal BCP): native={native:?} batsat={other:?}");
                }
            }
        }
    }

    /// Builds an unsatisfiable pigeonhole formula: `pigeons` pigeons into
    /// `pigeons - 1` holes. PHP is exponentially hard for resolution, so larger
    /// instances generate many conflicts/learned clauses — enough to drive
    /// `reduce_db` at least once with the test-scaled budget.
    fn pigeonhole(pigeons: i64) -> CnfFormula {
        let holes = pigeons - 1;
        let v = |p: i64, h: i64| (p - 1) * holes + h; // var id, 1-based
        let nvars = usize::try_from(pigeons * holes).unwrap();
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for p in 1..=pigeons {
            clauses.push((1..=holes).map(|h| v(p, h)).collect());
        }
        for h in 1..=holes {
            for p1 in 1..=pigeons {
                for p2 in (p1 + 1)..=pigeons {
                    clauses.push(vec![-v(p1, h), -v(p2, h)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(nvars, &refs)
    }

    impl Cdcl {
        /// Reference branching rule: the exact O(n) linear scan the order heap
        /// replaces — the unassigned variable of highest activity, ties to the
        /// lowest index. Used only by trajectory-identity tests to confirm the
        /// heap returns the same variable as the scan.
        fn pick_branch_linear(&self) -> Option<usize> {
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

        /// Asserts the order-heap invariants hold: every unassigned variable is in
        /// the heap, `heap_pos` is a consistent inverse of `heap`, and the heap
        /// property (`heap_before(parent, child)`) holds at every node.
        fn assert_heap_invariants(&self) {
            for (i, &v) in self.heap.iter().enumerate() {
                assert_eq!(self.heap_pos[v], i, "heap_pos must invert heap");
                if i > 0 {
                    let parent = self.heap[(i - 1) / 2];
                    assert!(
                        !self.heap_before(v, parent),
                        "heap property violated at {i}: {v} before parent {parent}"
                    );
                }
            }
            for v in 0..self.assign.len() {
                if self.assign[v].is_none() {
                    assert!(
                        self.heap_contains(v),
                        "every unassigned variable must be in the heap: {v}"
                    );
                }
            }
        }
    }

    /// The order heap returns exactly the variable the O(n) linear scan would,
    /// under randomized bump / pop / backtrack stress, and its structural
    /// invariants hold throughout. This is the trajectory-identity guarantee at
    /// the branching-decision level: if the heap ever picked a different variable
    /// than the scan, the search trajectory would diverge.
    #[test]
    fn order_heap_matches_linear_scan_under_stress() {
        let mut state = 0x51ce_d00d_face_0042u64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        // A dummy unit formula gives us a fully-initialized Cdcl with n vars all
        // in the heap; we then drive bump/pick/backtrack by hand.
        let n = 64usize;
        let n_signed = i64::try_from(n).unwrap();
        let n_bound = u64::try_from(n).unwrap();
        let mut clauses: Vec<Vec<i64>> = vec![vec![1]];
        clauses.extend((1..=n_signed).map(|v| vec![v, -v])); // tautologies, harmless
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        let mut cdcl = Cdcl::new(&formula(n, &refs));
        cdcl.assert_heap_invariants();

        for _ in 0..20_000 {
            match next() % 3 {
                // Bump a random variable (raises its activity → sift-up).
                0 => {
                    let v = usize::try_from(next() % n_bound).unwrap();
                    cdcl.bump_var(v);
                    cdcl.decay();
                    cdcl.assert_heap_invariants();
                }
                // Pick the best variable and "decide" it (assign + push a level),
                // first checking the heap agrees with the linear scan.
                1 => {
                    let expected = cdcl.pick_branch_linear();
                    let got = cdcl.pick_branch();
                    assert_eq!(got, expected, "heap pick must match linear scan");
                    if let Some(v) = got {
                        cdcl.trail_lim.push(cdcl.trail.len());
                        let pos = CnfLit::positive(CnfVar::new(v).unwrap());
                        cdcl.enqueue(pos, None);
                    }
                    cdcl.assert_heap_invariants();
                }
                // Backtrack to a random earlier level (unassign → re-insert).
                _ => {
                    if !cdcl.trail_lim.is_empty() {
                        let lvl =
                            usize::try_from(next() % (cdcl.trail_lim.len() as u64 + 1)).unwrap();
                        cdcl.backtrack_to(lvl);
                    }
                    cdcl.assert_heap_invariants();
                }
            }
        }
    }

    /// Determinism of the heap-driven core: the same formula yields a
    /// byte-identical proof across independent runs (the heap is fully
    /// deterministic — fixed insertion order at init, total `heap_before`
    /// ordering, no hashmap iteration). Uses a reducing pigeonhole instance so
    /// the run exercises bump, pop, backtrack, restart, and `reduce_db`.
    #[test]
    fn heap_driven_solve_is_byte_identical_across_runs() {
        let f = pigeonhole(8);
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "heap-driven run must be byte-identical across runs");
        match &a {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(&f, proof), Ok(true), "proof must DRAT-check");
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    /// Counts the clause-deletion (`d`) steps in a proof.
    fn deletion_count(proof: &[crate::DratStep]) -> usize {
        proof
            .iter()
            .filter(|s| matches!(s, crate::DratStep::Delete(_)))
            .count()
    }

    /// A pigeonhole instance large enough to trigger at least one `reduce_db`
    /// produces a proof containing DRAT deletion (`d`) lines, and that proof —
    /// WITH the deletions — still passes the independent checker and derives the
    /// empty clause. This is the core soundness gate for clause-DB reduction.
    #[test]
    fn reduce_db_emits_deletions_and_proof_still_checks() {
        // PHP(8→7): 56 vars, ~196 clauses; resolution-hard, so the core learns
        // far more than REDUCE_FIRST clauses and reduces at least once.
        let f = pigeonhole(8);
        match solve_with_drat_proof(&f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert!(
                    deletion_count(&proof) > 0,
                    "a reducing run must emit DRAT deletions; got none"
                );
                assert_eq!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "proof with deletion lines must DRAT-check and derive the empty clause"
                );
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    /// Determinism with reduction active: the same reducing instance produces a
    /// byte-identical proof (same learned clauses, same deletions, same order)
    /// across runs. The reduce trigger is by deterministic conflict/learned
    /// count, the sort is total (tie-broken by clause id), and no hashmap
    /// iteration leaks into the output.
    #[test]
    fn reduce_db_is_deterministic() {
        let f = pigeonhole(8);
        let a = solve_with_drat_proof(&f);
        let b = solve_with_drat_proof(&f);
        assert_eq!(a, b, "reducing run must be deterministic");
        if let ProofSolveOutcome::Unsat(proof) = &a {
            assert!(deletion_count(proof) > 0, "expected reduction to fire");
        } else {
            panic!("expected unsat");
        }
    }

    /// A clause currently serving as the reason (antecedent) for an assigned
    /// literal is LOCKED and must never be deleted by `reduce_db`. We construct a
    /// state with a learned, non-glue, locked clause and assert `reduce_db`
    /// leaves it live.
    #[test]
    fn reduce_db_never_deletes_a_locked_clause() {
        // Decisions assign a=T, b=T, c=T at three distinct levels; the learned
        // clause (¬a ∨ ¬b ∨ ¬c ∨ d) over those gives LBD 4 (> GLUE_LBD) and is
        // the reason for d, so it is both deletable-by-shape and locked.
        let mut cdcl = Cdcl::new(&formula(4, &[&[1]])); // 4 vars; dummy clause
        // Manually drive three decision levels.
        let dlit = |sign: i64| lit(sign);
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(1), None); // a@1
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(2), None); // b@2
        cdcl.trail_lim.push(cdcl.trail.len());
        cdcl.enqueue(dlit(3), None); // c@3
        // Add a learned clause that implies d, watched on its first two lits.
        let learned = vec![lit(4), lit(-1), lit(-2), lit(-3)]; // d ∨ ¬a ∨ ¬b ∨ ¬c
        let cid = cdcl.alloc_clause(&learned);
        cdcl.watches[lit_code(learned[0])].push(Watch {
            clause: cid,
            blocker: learned[1],
        });
        cdcl.watches[lit_code(learned[1])].push(Watch {
            clause: cid,
            blocker: learned[0],
        });
        cdcl.lbd.push(4); // distinct levels among ¬a,¬b,¬c,d (d will be @3)
        cdcl.cla_activity.push(0.0);
        cdcl.deleted.push(false);
        cdcl.learned_live += 1;
        cdcl.enqueue(dlit(4), Some(cid)); // d@3, reason = cid → cid is LOCKED
        assert!(cdcl.is_locked(cid), "setup: the clause must be locked");
        // Force reduce_db to run regardless of budget.
        cdcl.reduce_db();
        assert!(
            !cdcl.deleted[cid],
            "reduce_db must never delete a locked reason clause"
        );
    }

    /// Reduction stress: many random CNFs solved with reduction active. The
    /// native core and `BatSat` must never disagree, every native `sat` model
    /// must satisfy, and every native `unsat` proof — including its deletion
    /// lines — must DRAT-check. This is the completeness+soundness gate: no UNSAT
    /// is ever reported SAT or vice-versa even as the clause DB churns.
    #[test]
    fn reduce_db_stress_agrees_with_batsat_and_proof_checks() {
        // A spread of resolution-hard pigeonhole instances guarantees several
        // reductions; the random suite guarantees breadth.
        for pigeons in [6, 7, 8] {
            let f = pigeonhole(pigeons);
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "PHP({pigeons}) proof with deletions must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE on PHP({pigeons}): native={native:?} batsat={other:?}");
                }
            }
        }

        let mut state = 0xfeed_face_cafe_b0ddu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        for _ in 0..200 {
            let vars = 5 + below(&mut next, 8); // 5..=12 variables
            let clause_count = 8 + below(&mut next, 30);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let mut lits = Vec::new();
                for _ in 0..3 {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            let batsat = solve_with_rustsat_batsat(&f).unwrap();
            match (solve_with_drat_proof(&f), batsat) {
                (ProofSolveOutcome::Sat(model), SatResult::Sat(_)) => {
                    assert!(
                        model.satisfies(&f).unwrap(),
                        "native sat model must satisfy"
                    );
                }
                (ProofSolveOutcome::Unsat(proof), SatResult::Unsat(_)) => {
                    assert_eq!(
                        check_drat(&f, &proof),
                        Ok(true),
                        "native unsat (with any deletions) must DRAT-check"
                    );
                }
                (native, other) => {
                    panic!("DISAGREE: native={native:?} batsat={other:?}");
                }
            }
        }
    }
}
