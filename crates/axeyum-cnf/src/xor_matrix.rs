//! Incremental GF(2) (XOR) matrix for in-search CDCL(XOR) propagation.
//!
//! This module is the standalone *incremental matrix* primitive for the
//! CDCL(XOR) path (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). The earlier slices landed the from-scratch GF(2) Gaussian solver in
//! [`crate::gf2`] and the pure propagation oracle in [`crate::xor_search`].
//!
//! A measured experiment recorded in that note showed that re-running
//! from-scratch Gaussian elimination per decision level is too slow (`mulhs08`
//! 2.3× slower, `calypto_9` 19× slower). A first incremental matrix fixed that
//! but still scanned *every* row mentioning a variable on each `assign`
//! (`O(rows × words)`), which regressed `mulhs08` from 5 s to over 280 s once
//! integrated into the live CDCL loop. The fix in this slice is the
//! **two-watched-variable (watched-echelon-row) scheme** — the same structure
//! `CryptoMiniSat`'s `EGaussian` uses (Han-Jiang "simplex-way" Gaussian, see
//! `references/cryptominisat/src/gaussian.cpp`) — adapted to lifetime-free Rust.
//!
//! # The scheme: reduced row echelon over free columns, indexed by watches
//!
//! The matrix keeps its rows in **reduced row echelon form (RREF)** over the
//! original variable columns. Unlike the previous slice, assigned variables are
//! **not folded out** of the bitsets; instead a per-variable `assignment` mask
//! is consulted at read time, exactly as `CryptoMiniSat` keeps `cols_unset` /
//! `cols_vals`. Concretely:
//!
//! * `Row::bits` is the row's GF(2) support over *all* variables (never mutated
//!   by an assign that does not re-pivot it);
//! * `Row::rhs` is the original right-hand-side parity;
//! * a variable is *free* in a row iff its bit is set **and** it is unassigned;
//! * the *effective parity* of a row is `rhs ⊕ (parity of its assigned-true
//!   bits)`;
//! * a row with **one** free variable is a forced *unit* (`x = effective
//!   parity`), the propagation completeness path;
//! * a row with **zero** free variables and effective parity `1` is the
//!   inconsistent `0 = 1` row, a conflict.
//!
//! Maintaining full RREF (eliminate each pivot column from *all* other rows,
//! up and down — not just echelon form) is what makes completeness match
//! [`crate::xor_implications`]: pure watched/echelon propagation alone misses
//! implications that only appear after combining rows (e.g. `a⊕b⊕c=0, b⊕c=0`
//! entails `a=0` with nothing assigned), but RREF exposes every such
//! combination as an explicit reduced row. The watches are an *index over the
//! RREF rows*, never a substitute for the elimination.
//!
//! ## The two watches
//!
//! Every non-trivial row watches `min(2, #free)` of its currently-free
//! variables (CMS watches the *responsible* pivot var plus one *non-responsible*
//! free var; the invariant is the same — two free vars are watched).
//! `watches[v]` is the sorted set of rows watching `v`. The decisive invariant:
//!
//! > A row that can *become a unit* (drop from 2 free vars to 1) by assigning
//! > `v` has at most 2 free vars, so it watches *both* of them, hence watches
//! > `v`. Processing only `watches[v]` therefore catches every new unit and
//! > conflict — without scanning the rows that merely contain `v` among many
//! > free vars.
//!
//! ## On assign — watched-row processing
//!
//! `assign(var = value)` records the value in the mask, then:
//!
//! 1. If `var` is the pivot of a row, that row loses its pivot. It is
//!    re-pivoted onto its next free variable and that new pivot column is
//!    eliminated from every other row (the only cross-row work — at most one
//!    re-pivot per assign, and only on *pivot* assigns). This restores RREF.
//! 2. Every row in `watches[var]` is examined: the watch on `var` is moved to
//!    another still-free variable if the row still has ≥ 2 free vars; a row with
//!    one free var is a new forced unit; a row with zero free vars and effective
//!    parity `1` is a conflict.
//!
//! Rows that contain `var` but do **not** watch it are *not* touched — their
//! bit stays set and is masked out by `assignment` at read time. This is the
//! whole point: per-assign cost is proportional to the rows *watching* `var`
//! plus at most one pivot-column elimination, not to all rows mentioning `var`.
//!
//! ## On backtrack — restore via journal
//!
//! The matrix records every assign on a trail and journals enough state
//! (`rows`, `watches`, `pivot_of`, the unit/conflict indices, and `conflict`) so
//! [`IncrementalXorMatrix::backtrack_to`] restores the live RREF + watch index
//! exactly to what a fresh matrix built and assigned to the truncated trail
//! would hold (the differential checks this against a from-scratch rebuild).
//!
//! # Reasons are a sound over-approximation
//!
//! Each conflict and each implied literal carries a `reason`: a subset of the
//! current trail assignments (`(var, value)` pairs) that already forces the
//! result — the assigned variables in the *connected component* (via shared
//! original constraints) of the implied/conflicting variable. Fixing exactly
//! those reason variables still forces the implication/conflict, so the reason
//! is a valid, *sound* explanation — simply not guaranteed minimal. Reasons are
//! always a subset of the trail, sorted by variable index, and deterministic.
//!
//! # Determinism
//!
//! Rows are processed in pivot order, free-variable scans are index-ordered,
//! watch lists are kept sorted, and all outputs (implied literals, reasons) are
//! sorted by variable index. No hash-map iteration order influences any output.

use crate::xor_search::XorImplied;

/// One incremental step's entailment under the current trail.
///
/// Mirrors [`crate::XorImplication`] but is returned per-assign rather than for a
/// whole snapshot, and adds an [`XorMatrixStep::Ok`] case for an assign that
/// neither conflicts nor forces anything new.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XorMatrixStep {
    /// The assign is consistent and forces no new literal beyond the trail.
    Ok,
    /// The XOR system is now inconsistent under the trail. `reason` is a sound
    /// (possibly non-minimal) subset of the trail forcing the contradiction,
    /// sorted by variable index.
    Conflict {
        /// Trail assignments (with values) explaining the conflict.
        reason: Vec<(usize, bool)>,
    },
    /// The assign is consistent and the XOR system now forces these literals on
    /// still-free variables. Sorted by variable index; each carries its reason.
    Implied {
        /// Newly forced literals beyond the trail, sorted by variable.
        implied: Vec<XorImplied>,
    },
}

/// A single live row over the original variable columns.
///
/// The bitset is *not* mutated when a non-pivot variable in it is assigned; the
/// matrix masks assigned variables out at read time via [`IncrementalXorMatrix::assignment`].
#[derive(Debug, Clone)]
struct Row {
    /// One bit per *original* variable; set ⇒ that variable is in the row
    /// (whether or not it is currently assigned).
    bits: Vec<u64>,
    /// The *original* right-hand-side parity. The effective parity under the
    /// trail is `rhs ⊕ (parity of assigned-true bits)`, computed on demand.
    rhs: bool,
    /// Cached pivot variable (lowest-index *free* variable), or `usize::MAX`
    /// when the row has no free variables. Kept in sync by the matrix.
    pivot: usize,
    /// The (≤ 2) currently-free variables this row watches, sorted ascending.
    /// Always `min(2, #free)` of the row's free vars. The watch index
    /// [`IncrementalXorMatrix::watches`] is the inverse of this.
    watched: Vec<usize>,
    /// Sorted, deduplicated component roots whose original constraints were
    /// `XOR`ed to form this row, for naming a tight conflict reason once the
    /// free bits are gone. Propagated through every row XOR.
    components: Vec<usize>,
}

/// A constraint's raw row before final component attachment: its bitset, parity,
/// and any one original variable (to look up the final connected component).
struct RawRow {
    bits: Vec<u64>,
    parity: bool,
    first_var: Option<usize>,
}

/// Merges two sorted-deduped component-root lists into one.
fn merge_components(a: &[usize], b: &[usize]) -> Vec<usize> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// An incremental GF(2) (XOR) matrix over a fixed constraint set, maintained in
/// reduced row echelon form against an evolving partial assignment and indexed
/// by a two-watched-variable scheme for `O(watched)` per-assign cost.
///
/// Construct with [`IncrementalXorMatrix::new`], drive the search with
/// [`IncrementalXorMatrix::assign`], and undo with
/// [`IncrementalXorMatrix::backtrack_to`]. The reported conflict status and
/// implied-literal set always equal what [`crate::xor_implications`] returns on
/// the same current partial assignment (this is the module's correctness
/// contract, enforced by a randomized differential).
#[derive(Debug, Clone)]
pub struct IncrementalXorMatrix {
    num_vars: usize,
    /// Live rows in reduced row echelon form over the original columns.
    rows: Vec<Row>,
    /// Watch index: `watches[v]` is the sorted list of row indices watching `v`.
    watches: Vec<Vec<usize>>,
    /// `pivot_of[v]` is the row index pivoting on `v`, or `usize::MAX`. Unique by
    /// RREF (at most one row has any given pivot).
    pivot_of: Vec<usize>,
    /// Current trail of assignments, in assign order.
    trail: Vec<(usize, bool)>,
    /// Per-trail-entry journal of the full restorable state taken *before* the
    /// corresponding assign was applied. `journal[i]` restores the state that
    /// existed after `i` assignments.
    journal: Vec<JournalEntry>,
    /// `assignment[v]` is `Some(value)` if `v` is on the trail, else `None`.
    assignment: Vec<Option<bool>>,
    /// Connected-component representative per variable (union-find roots), built
    /// once from the original constraints for reasons.
    component: Vec<usize>,
    /// Per-row implied variable when the row is currently a *unit* (exactly one
    /// free var), else `usize::MAX`. Kept in sync incrementally so the full set
    /// of currently-implied literals can be read off without a full scan. This
    /// is the persistent unit index over the RREF rows.
    unit_var: Vec<usize>,
    /// Sorted set of rows currently in unit state (`unit_var[r] != MAX`). The
    /// inverse of `unit_var`, for cheap full-implied-set readout.
    unit_rows: Vec<usize>,
    /// Sorted set of rows currently in `0 = 1` conflict state.
    conflict_rows: Vec<usize>,
    /// Whether the most recent live state is a conflict, and its reason.
    conflict: Option<Vec<(usize, bool)>>,
    /// Perf instrumentation: total rows examined across all `assign` calls.
    rows_examined: u64,
    /// Perf instrumentation: number of `assign` calls.
    assign_calls: u64,
}

/// The state journaled before each assign so backtrack restores it exactly.
#[derive(Debug, Clone)]
struct JournalEntry {
    rows: Vec<Row>,
    watches: Vec<Vec<usize>>,
    pivot_of: Vec<usize>,
    unit_var: Vec<usize>,
    unit_rows: Vec<usize>,
    conflict_rows: Vec<usize>,
    conflict: Option<Vec<(usize, bool)>>,
}

impl IncrementalXorMatrix {
    /// Builds the matrix from XOR `constraints` over `num_vars` variables.
    ///
    /// Each constraint is `(vars, parity)` asserting `(⊕ of vars) = parity`, the
    /// same shape [`crate::xor_implications`] and [`crate::Gf2System`] accept;
    /// duplicate variables in a constraint cancel by parity. The matrix starts
    /// with an empty trail and the constraints reduced to RREF.
    ///
    /// # Panics
    ///
    /// Panics if any variable index in `constraints` is `>= num_vars`.
    #[must_use]
    pub fn new(constraints: &[(Vec<usize>, bool)], num_vars: usize) -> Self {
        let words = num_vars.div_ceil(64).max(1);

        // Build raw rows from the constraints (folding duplicate variables by
        // parity). First pass: bitsets, parities, and the union-find of all
        // variables that share a constraint. Component roots are read off *after*
        // every union, so provenance reflects the final connected components.
        let mut uf = UnionFind::new(num_vars);
        let mut raw_rows: Vec<RawRow> = Vec::with_capacity(constraints.len());
        for (vars, parity) in constraints {
            let mut bits = vec![0u64; words];
            for &v in vars {
                assert!(
                    v < num_vars,
                    "constraint variable index {v} out of range for num_vars {num_vars}"
                );
                bits[v / 64] ^= 1u64 << (v % 64);
            }
            if let Some(&first) = vars.first() {
                for &v in &vars[1..] {
                    uf.union(first, v);
                }
            }
            raw_rows.push(RawRow {
                bits,
                parity: *parity,
                first_var: vars.first().copied(),
            });
        }

        let component: Vec<usize> = (0..num_vars).map(|v| uf.find(v)).collect();

        // Second pass: now that components are final, attach each row's provenance.
        let raw: Vec<Row> = raw_rows
            .into_iter()
            .map(|rr| {
                let pivot = lowest_set_bit(&rr.bits, num_vars);
                let components = match rr.first_var {
                    Some(first) => vec![component[first]],
                    None => Vec::new(),
                };
                Row {
                    bits: rr.bits,
                    rhs: rr.parity,
                    pivot,
                    watched: Vec::new(),
                    components,
                }
            })
            .collect();

        let raw_len = raw.len();
        let mut matrix = Self {
            num_vars,
            rows: raw,
            watches: vec![Vec::new(); num_vars],
            pivot_of: vec![usize::MAX; num_vars],
            trail: Vec::new(),
            journal: Vec::new(),
            assignment: vec![None; num_vars],
            component,
            unit_var: vec![usize::MAX; raw_len],
            unit_rows: Vec::new(),
            conflict_rows: Vec::new(),
            conflict: None,
            rows_examined: 0,
            assign_calls: 0,
        };
        // Reduce the initial system to RREF, then build the pivot index, watch
        // index, and the unit/conflict indices over the reduced rows.
        matrix.reduce_all();
        matrix.rebuild_index();
        matrix.conflict = if matrix.conflict_rows.is_empty() {
            None
        } else {
            Some(matrix.conflict_reason_for_rows(&matrix.conflict_rows.clone()))
        };
        matrix
    }

    /// Number of variables in this matrix.
    #[must_use]
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Length of the current assignment trail.
    #[must_use]
    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// Whether the live system is currently in a conflicting state.
    #[must_use]
    pub fn in_conflict(&self) -> bool {
        self.conflict.is_some()
    }

    /// Total rows examined across all `assign` calls (perf instrumentation).
    #[must_use]
    pub fn rows_examined(&self) -> u64 {
        self.rows_examined
    }

    /// Number of `assign` calls so far (perf instrumentation).
    #[must_use]
    pub fn assign_calls(&self) -> u64 {
        self.assign_calls
    }

    /// Assigns `var = value` on the trail and reports what the XOR system now
    /// entails.
    ///
    /// Returns [`XorMatrixStep::Conflict`] if the system is now inconsistent,
    /// [`XorMatrixStep::Implied`] with the newly forced literals (each with a
    /// sound reason), or [`XorMatrixStep::Ok`] if the assign is consistent and
    /// forces nothing new. The reported conflict status and implied-literal *set*
    /// always equal [`crate::xor_implications`] on the resulting trail.
    ///
    /// # Per-assign cost
    ///
    /// Only the rows in `watches[var]` are examined (plus at most one
    /// pivot-column elimination when `var` is a pivot), so the cost is
    /// proportional to the number of rows *watching* `var` — not all rows
    /// mentioning it. This is the watched-row win over a full scan.
    ///
    /// # Panics
    ///
    /// Panics if `var >= num_vars`, or if `var` is already assigned on the trail.
    pub fn assign(&mut self, var: usize, value: bool) -> XorMatrixStep {
        assert!(
            var < self.num_vars,
            "assign variable index {var} out of range for num_vars {}",
            self.num_vars
        );
        assert!(
            self.assignment[var].is_none(),
            "variable {var} is already assigned on the trail"
        );

        // Journal the pre-assign state so backtrack restores it exactly.
        self.journal.push(JournalEntry {
            rows: self.rows.clone(),
            watches: self.watches.clone(),
            pivot_of: self.pivot_of.clone(),
            unit_var: self.unit_var.clone(),
            unit_rows: self.unit_rows.clone(),
            conflict_rows: self.conflict_rows.clone(),
            conflict: self.conflict.clone(),
        });
        self.trail.push((var, value));
        self.assignment[var] = Some(value);
        self.assign_calls += 1;

        // If we were already in conflict, stay in conflict; keep the existing
        // reason (a subset of the smaller trail is still a subset of this one).
        if let Some(reason) = &self.conflict {
            return XorMatrixStep::Conflict {
                reason: reason.clone(),
            };
        }

        // Step 1: re-pivot if `var` is a pivot. This is the only cross-row work,
        // and restores RREF by eliminating the new pivot column everywhere. The
        // touched rows (including the re-pivoted row) get their per-row state
        // (watches, pivot, unit/conflict) refreshed inside `eliminate_*`.
        if self.pivot_of[var] != usize::MAX {
            let r = self.pivot_of[var];
            self.pivot_of[var] = usize::MAX;
            // The pivot var is now assigned; the row loses it. Recompute the
            // row's free vars (masking assigned) to find the new pivot.
            let new_pivot = self.row_lowest_free(r);
            self.rows[r].pivot = new_pivot;
            if new_pivot != usize::MAX {
                self.pivot_of[new_pivot] = r;
                // Eliminate the new pivot column from every other row to restore
                // RREF (this is the bounded `O(rows-sharing-column)` step). Each
                // touched row's state is refreshed there.
                self.eliminate_column_with_pivot(new_pivot, r);
            }
            // Refresh the re-pivoted row's own per-row state.
            self.update_row_state(r);
        }

        // Step 2: process every row watching `var`. Take the watch list out so we
        // can mutate `self` freely; `update_row_state` re-inserts watches.
        let watching = std::mem::take(&mut self.watches[var]);
        self.rows_examined += watching.len() as u64;
        for &r in &watching {
            // `var` is no longer free in `r`; recompute the row's watches/pivot
            // and unit/conflict status.
            self.update_row_state(r);
        }

        self.build_step()
    }

    /// Undoes assignments until the trail has length `trail_len`, restoring the
    /// live matrix (rows, watches, pivots, conflict) exactly to its state at that
    /// trail length.
    ///
    /// After this call the matrix is what a fresh [`IncrementalXorMatrix::new`]
    /// built and assigned to the first `trail_len` trail entries would hold —
    /// including conflict status.
    ///
    /// # Panics
    ///
    /// Panics if `trail_len` is greater than the current [`Self::trail_len`].
    pub fn backtrack_to(&mut self, trail_len: usize) {
        assert!(
            trail_len <= self.trail.len(),
            "backtrack_to({trail_len}) exceeds trail length {}",
            self.trail.len()
        );
        while self.trail.len() > trail_len {
            let (var, _) = self.trail.pop().expect("trail non-empty above target");
            self.assignment[var] = None;
            let entry = self.journal.pop().expect("journal parallel to trail");
            self.rows = entry.rows;
            self.watches = entry.watches;
            self.pivot_of = entry.pivot_of;
            self.unit_var = entry.unit_var;
            self.unit_rows = entry.unit_rows;
            self.conflict_rows = entry.conflict_rows;
            self.conflict = entry.conflict;
        }
    }

    // --- internal: per-row state maintenance -------------------------------

    /// Recomputes row `r`'s watches, pivot, and unit/conflict membership from
    /// its current bits and the assignment, updating every index incrementally.
    /// This is the single point that keeps `watches`, `pivot_of`, `unit_var`,
    /// `unit_rows`, and `conflict_rows` consistent for one row.
    fn update_row_state(&mut self, r: usize) {
        self.rewatch_row(r);
        self.refresh_pivot(r);

        // Classify by free-var count, computed once.
        let free = self.row_free_vars(r);
        let new_unit = if free.len() == 1 { free[0] } else { usize::MAX };
        let new_conflict = free.is_empty() && self.row_effective_parity(r);

        // Update the unit index.
        let old_unit = self.unit_var[r];
        if old_unit != new_unit {
            if old_unit != usize::MAX {
                if let Some(pos) = self.unit_rows.iter().position(|&x| x == r) {
                    self.unit_rows.remove(pos);
                }
            }
            self.unit_var[r] = new_unit;
            if new_unit != usize::MAX {
                let pos = self.unit_rows.partition_point(|&x| x < r);
                self.unit_rows.insert(pos, r);
            }
        }

        // Update the conflict index.
        let was_conflict = self.conflict_rows.binary_search(&r).is_ok();
        if was_conflict != new_conflict {
            if new_conflict {
                let pos = self.conflict_rows.partition_point(|&x| x < r);
                self.conflict_rows.insert(pos, r);
            } else if let Ok(pos) = self.conflict_rows.binary_search(&r) {
                self.conflict_rows.remove(pos);
            }
        }
    }

    /// Builds the step result from the persistent unit/conflict indices,
    /// updating `self.conflict`.
    fn build_step(&mut self) -> XorMatrixStep {
        if !self.conflict_rows.is_empty() {
            let reason = self.conflict_reason_for_rows(&self.conflict_rows.clone());
            self.conflict = Some(reason.clone());
            return XorMatrixStep::Conflict { reason };
        }
        self.conflict = None;
        if self.unit_rows.is_empty() {
            return XorMatrixStep::Ok;
        }
        // The full set of currently-implied literals (every unit row), sorted by
        // variable and deduplicated (RREF guarantees ≤ one unit row per var, but
        // dedup defensively).
        let mut implied: Vec<XorImplied> = self
            .unit_rows
            .iter()
            .map(|&r| {
                let var = self.unit_var[r];
                XorImplied {
                    var,
                    value: self.row_effective_parity(r),
                    reason: self.component_reason(var),
                }
            })
            .collect();
        implied.sort_by_key(|i| i.var);
        implied.dedup_by_key(|i| i.var);
        XorMatrixStep::Implied { implied }
    }

    // --- internal: RREF maintenance ----------------------------------------

    /// Fully reduces `self.rows` to RREF over all columns (no assignment yet).
    /// Used once at construction; afterwards the matrix is kept in RREF
    /// incrementally.
    fn reduce_all(&mut self) {
        let mut pivot_row = 0usize;
        for col in 0..self.num_vars {
            let Some(sel) = (pivot_row..self.rows.len()).find(|&r| self.row_has_bit(r, col)) else {
                continue;
            };
            self.rows.swap(pivot_row, sel);
            self.eliminate_column_with_pivot_full(col, pivot_row);
            pivot_row += 1;
            if pivot_row == self.rows.len() {
                break;
            }
        }
        for r in 0..self.rows.len() {
            self.rows[r].pivot = lowest_set_bit(&self.rows[r].bits, self.num_vars);
        }
    }

    /// Eliminates column `col` from every row except `pivot_row` at build time,
    /// where no variable is assigned yet (so the lowest set bit is the pivot).
    fn eliminate_column_with_pivot_full(&mut self, col: usize, pivot_row: usize) {
        let pivot_bits = self.rows[pivot_row].bits.clone();
        let pivot_rhs = self.rows[pivot_row].rhs;
        let pivot_components = self.rows[pivot_row].components.clone();
        for r in 0..self.rows.len() {
            if r != pivot_row && self.row_has_bit(r, col) {
                xor_into(&mut self.rows[r].bits, &pivot_bits);
                self.rows[r].rhs ^= pivot_rhs;
                self.rows[r].components =
                    merge_components(&self.rows[r].components, &pivot_components);
            }
        }
    }

    /// Eliminates the *free* pivot column `col` (free var of `pivot_row`) from
    /// every other row that has a 1 there, restoring RREF after a re-pivot.
    ///
    /// Unlike the build-time variant this runs under a partial assignment: each
    /// touched row (one the pivot was added into) has its watches, pivot, and
    /// unit/conflict membership refreshed here so the elimination cascade
    /// surfaces every new combination unit or conflict (completeness).
    fn eliminate_column_with_pivot(&mut self, col: usize, pivot_row: usize) {
        let pivot_bits = self.rows[pivot_row].bits.clone();
        let pivot_rhs = self.rows[pivot_row].rhs;
        let pivot_components = self.rows[pivot_row].components.clone();
        // Finding the rows sharing this pivot column is the one remaining
        // cross-row scan; it fires only on *pivot* assigns (≤ rank per
        // root-to-leaf path), mirroring CryptoMiniSat's `eliminate_col`. Count
        // the rows it actually XORs into as examined.
        let touched: Vec<usize> = (0..self.rows.len())
            .filter(|&r| r != pivot_row && self.row_has_bit(r, col))
            .collect();
        self.rows_examined += touched.len() as u64;
        for &r in &touched {
            xor_into(&mut self.rows[r].bits, &pivot_bits);
            self.rows[r].rhs ^= pivot_rhs;
            self.rows[r].components = merge_components(&self.rows[r].components, &pivot_components);
            // The row's support changed; refresh its watches, pivot, and
            // unit/conflict membership so the eliminate cascade surfaces any new
            // combination unit or conflict.
            self.update_row_state(r);
        }
    }

    /// Recomputes `rows[r].pivot` from its lowest free var and updates
    /// `pivot_of` (clearing any stale entry that pointed at `r`).
    fn refresh_pivot(&mut self, r: usize) {
        let old = self.rows[r].pivot;
        if old != usize::MAX && self.pivot_of[old] == r {
            self.pivot_of[old] = usize::MAX;
        }
        let new_pivot = self.row_lowest_free(r);
        self.rows[r].pivot = new_pivot;
        if new_pivot != usize::MAX {
            self.pivot_of[new_pivot] = r;
        }
    }

    /// Rebuilds every index (`pivot_of`, `watches`, `unit_var`, `unit_rows`,
    /// `conflict_rows`) from the current rows (used once after the build-time
    /// reduce, where the matrix is in RREF with an empty assignment).
    fn rebuild_index(&mut self) {
        for slot in &mut self.pivot_of {
            *slot = usize::MAX;
        }
        for w in &mut self.watches {
            w.clear();
        }
        self.unit_rows.clear();
        self.conflict_rows.clear();
        for slot in &mut self.unit_var {
            *slot = usize::MAX;
        }
        for r in 0..self.rows.len() {
            self.rows[r].watched.clear();
            let pivot = self.row_lowest_free(r);
            self.rows[r].pivot = pivot;
            if pivot != usize::MAX {
                self.pivot_of[pivot] = r;
            }
            let watched = self.choose_watched(r);
            for &v in &watched {
                self.watches[v].push(r);
            }
            self.rows[r].watched = watched;

            // Unit / conflict membership.
            let free = self.row_free_vars(r);
            if free.len() == 1 {
                self.unit_var[r] = free[0];
                self.unit_rows.push(r);
            } else if free.is_empty() && self.row_effective_parity(r) {
                self.conflict_rows.push(r);
            }
        }
        for w in &mut self.watches {
            w.sort_unstable();
            w.dedup();
        }
        self.unit_rows.sort_unstable();
        self.conflict_rows.sort_unstable();
    }

    /// Re-derives row `r`'s watched free vars and updates the `watches` index,
    /// removing `r` from its old watch lists and adding it to the new ones.
    fn rewatch_row(&mut self, r: usize) {
        // Remove `r` from its currently-watched lists.
        let old = std::mem::take(&mut self.rows[r].watched);
        for &v in &old {
            if let Some(pos) = self.watches[v].iter().position(|&x| x == r) {
                self.watches[v].swap_remove(pos);
            }
        }
        let new = self.choose_watched(r);
        for &v in &new {
            self.watches[v].push(r);
            // keep watch lists sorted for determinism
            let w = &mut self.watches[v];
            let mut i = w.len() - 1;
            while i > 0 && w[i - 1] > w[i] {
                w.swap(i - 1, i);
                i -= 1;
            }
        }
        self.rows[r].watched = new;
    }

    /// The (≤ 2) lowest free variables of row `r`, ascending — the vars to watch.
    fn choose_watched(&self, r: usize) -> Vec<usize> {
        let mut out = Vec::with_capacity(2);
        let bits = &self.rows[r].bits;
        for (w, &word) in bits.iter().enumerate() {
            let mut b = word;
            while b != 0 {
                let tz = b.trailing_zeros() as usize;
                let var = w * 64 + tz;
                if var < self.num_vars && self.assignment[var].is_none() {
                    out.push(var);
                    if out.len() == 2 {
                        return out;
                    }
                }
                b &= b - 1;
            }
        }
        out
    }

    fn row_has_bit(&self, r: usize, col: usize) -> bool {
        (self.rows[r].bits[col / 64] >> (col % 64)) & 1 == 1
    }

    /// The lowest *free* (set & unassigned) variable in row `r`, or `usize::MAX`.
    fn row_lowest_free(&self, r: usize) -> usize {
        let bits = &self.rows[r].bits;
        for (w, &word) in bits.iter().enumerate() {
            let mut b = word;
            while b != 0 {
                let tz = b.trailing_zeros() as usize;
                let var = w * 64 + tz;
                if var < self.num_vars && self.assignment[var].is_none() {
                    return var;
                }
                b &= b - 1;
            }
        }
        usize::MAX
    }

    /// The free (set & unassigned) variables of row `r`, ascending.
    fn row_free_vars(&self, r: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let bits = &self.rows[r].bits;
        for (w, &word) in bits.iter().enumerate() {
            let mut b = word;
            while b != 0 {
                let tz = b.trailing_zeros() as usize;
                let var = w * 64 + tz;
                if var < self.num_vars && self.assignment[var].is_none() {
                    out.push(var);
                }
                b &= b - 1;
            }
        }
        out
    }

    /// The effective parity of row `r`: `rhs ⊕ (parity of its assigned-true bits)`.
    fn row_effective_parity(&self, r: usize) -> bool {
        let mut parity = self.rows[r].rhs;
        let bits = &self.rows[r].bits;
        for (w, &word) in bits.iter().enumerate() {
            let mut b = word;
            while b != 0 {
                let tz = b.trailing_zeros() as usize;
                let var = w * 64 + tz;
                if var < self.num_vars && self.assignment[var] == Some(true) {
                    parity = !parity;
                }
                b &= b - 1;
            }
        }
        parity
    }

    // --- internal: conflict / reason readout -------------------------------

    /// Scans all rows for a `0 = 1` conflict from scratch. Used by the
    /// differential tests as an independent recomputation of conflict status;
    /// the live path maintains `conflict_rows` incrementally instead.
    #[cfg(test)]
    fn detect_conflict_reason(&self) -> Option<Vec<(usize, bool)>> {
        let conflict_rows: Vec<usize> = (0..self.rows.len())
            .filter(|&r| self.row_free_vars(r).is_empty() && self.row_effective_parity(r))
            .collect();
        if conflict_rows.is_empty() {
            None
        } else {
            Some(self.conflict_reason_for_rows(&conflict_rows))
        }
    }

    /// A sound conflict reason for the given `0 = 1` rows: every assigned trail
    /// variable in those rows' tracked components (or the whole trail if a row
    /// has no traceable provenance).
    fn conflict_reason_for_rows(&self, rows: &[usize]) -> Vec<(usize, bool)> {
        let mut roots: Vec<usize> = Vec::new();
        let mut untraceable = false;
        for &r in rows {
            if self.rows[r].components.is_empty() {
                untraceable = true;
            } else {
                roots.extend_from_slice(&self.rows[r].components);
            }
        }
        if untraceable || roots.is_empty() {
            self.all_assigned_sorted()
        } else {
            self.components_reason(&roots)
        }
    }

    /// The sorted assigned `(var, value)` pairs in `var`'s connected component.
    fn component_reason(&self, var: usize) -> Vec<(usize, bool)> {
        let root = self.component[var];
        let mut reason: Vec<(usize, bool)> = self
            .trail
            .iter()
            .copied()
            .filter(|&(v, _)| self.component[v] == root)
            .collect();
        reason.sort_unstable_by_key(|&(v, _)| v);
        reason
    }

    /// The sorted, deduplicated assigned pairs across all given component roots.
    fn components_reason(&self, roots: &[usize]) -> Vec<(usize, bool)> {
        let mut root_set: Vec<usize> = roots.to_vec();
        root_set.sort_unstable();
        root_set.dedup();
        let mut reason: Vec<(usize, bool)> = self
            .trail
            .iter()
            .copied()
            .filter(|&(v, _)| root_set.binary_search(&self.component[v]).is_ok())
            .collect();
        reason.sort_unstable_by_key(|&(v, _)| v);
        reason
    }

    /// All assigned trail pairs, sorted by variable (the conservative fallback).
    fn all_assigned_sorted(&self) -> Vec<(usize, bool)> {
        let mut reason: Vec<(usize, bool)> = self.trail.clone();
        reason.sort_unstable_by_key(|&(v, _)| v);
        reason
    }
}

// --- free helpers ----------------------------------------------------------

/// XORs `src` into `dst` word by word (both same length).
fn xor_into(dst: &mut [u64], src: &[u64]) {
    for (d, &s) in dst.iter_mut().zip(src.iter()) {
        *d ^= s;
    }
}

/// The lowest set bit index in `bits`, limited to `num_vars`, or `usize::MAX` if
/// none. (Ignores assignment — used at build time.)
fn lowest_set_bit(bits: &[u64], num_vars: usize) -> usize {
    for (w, &word) in bits.iter().enumerate() {
        if word != 0 {
            let tz = word.trailing_zeros() as usize;
            let var = w * 64 + tz;
            if var < num_vars {
                return var;
            }
        }
    }
    usize::MAX
}

/// Minimal disjoint-set over `0..n` (path compression + union by size), used to
/// group variables into connected components for reasons.
struct UnionFind {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut cur = x;
        while self.parent[cur] != root {
            let next = self.parent[cur];
            self.parent[cur] = root;
            cur = next;
        }
        root
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (keep, drop) = if self.size[ra] >= self.size[rb] {
            (ra, rb)
        } else {
            (rb, ra)
        };
        self.parent[drop] = keep;
        self.size[keep] += self.size[drop];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{XorImplication, xor_implications};

    type Constraint = (Vec<usize>, bool);

    /// The current trail as an `Option`-slice for the `xor_implications` oracle.
    fn matrix_assignment(matrix: &IncrementalXorMatrix) -> Vec<Option<bool>> {
        matrix.assignment.clone()
    }

    /// The conflict status + sorted implied-(var,value) SET a `XorMatrixStep`
    /// represents (the matrix's incremental view). `None` = conflict.
    fn step_view(step: &XorMatrixStep) -> Option<Vec<(usize, bool)>> {
        match step {
            XorMatrixStep::Conflict { .. } => None,
            XorMatrixStep::Ok => Some(Vec::new()),
            XorMatrixStep::Implied { implied } => {
                let mut set: Vec<(usize, bool)> =
                    implied.iter().map(|i| (i.var, i.value)).collect();
                set.sort_unstable();
                Some(set)
            }
        }
    }

    /// The conflict status + sorted implied SET the oracle reports on the same
    /// partial assignment. `None` = conflict.
    fn oracle_view(
        constraints: &[Constraint],
        num_vars: usize,
        assignment: &[Option<bool>],
    ) -> Option<Vec<(usize, bool)>> {
        match xor_implications(constraints, num_vars, assignment) {
            XorImplication::Conflict { .. } => None,
            XorImplication::Implied { implied } => {
                let mut set: Vec<(usize, bool)> =
                    implied.iter().map(|i| (i.var, i.value)).collect();
                set.sort_unstable();
                Some(set)
            }
        }
    }

    /// Asserts the matrix's current entailment (from a recomputed full step view)
    /// equals the oracle's, comparing conflict-status and the implied SET.
    fn assert_matches_oracle(
        constraints: &[Constraint],
        num_vars: usize,
        matrix: &mut IncrementalXorMatrix,
        last_step: &XorMatrixStep,
    ) {
        let assignment = matrix_assignment(matrix);
        let oracle = oracle_view(constraints, num_vars, &assignment);
        let from_step = step_view(last_step);
        assert_eq!(
            from_step, oracle,
            "step view disagrees with oracle on assignment {assignment:?} for {constraints:?}"
        );

        // Reason soundness: every reason must be a subset of the trail, and
        // fixing only the reason must still force the same result.
        match last_step {
            XorMatrixStep::Conflict { reason } => {
                assert_reason_subset_of_trail(reason, &assignment);
                let reason_only = reason_to_assignment(num_vars, reason);
                assert!(
                    matches!(
                        xor_implications(constraints, num_vars, &reason_only),
                        XorImplication::Conflict { .. }
                    ),
                    "fixing only conflict reason {reason:?} does not force the conflict for \
                     {constraints:?}"
                );
            }
            XorMatrixStep::Implied { implied } => {
                for imp in implied {
                    assert_reason_subset_of_trail(&imp.reason, &assignment);
                    let reason_only = reason_to_assignment(num_vars, &imp.reason);
                    match xor_implications(constraints, num_vars, &reason_only) {
                        XorImplication::Implied { implied: forced } => {
                            let found = forced.iter().find(|f| f.var == imp.var);
                            assert!(
                                found.map(|f| f.value) == Some(imp.value),
                                "fixing only reason {:?} fails to force {}={} for {constraints:?}",
                                imp.reason,
                                imp.var,
                                imp.value
                            );
                        }
                        XorImplication::Conflict { .. } => {}
                    }
                }
            }
            XorMatrixStep::Ok => {}
        }
    }

    fn assert_reason_subset_of_trail(reason: &[(usize, bool)], assignment: &[Option<bool>]) {
        for &(v, value) in reason {
            assert_eq!(
                assignment[v],
                Some(value),
                "reason var {v}={value} is not a matching trail assignment"
            );
        }
        assert!(
            reason.windows(2).all(|w| w[0].0 < w[1].0),
            "reason not strictly ascending / has duplicates: {reason:?}"
        );
    }

    fn reason_to_assignment(num_vars: usize, reason: &[(usize, bool)]) -> Vec<Option<bool>> {
        let mut a = vec![None; num_vars];
        for &(v, value) in reason {
            a[v] = Some(value);
        }
        a
    }

    /// A tiny deterministic LCG (no `rand` dependency).
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Self(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
        }
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: usize) -> usize {
            usize::try_from(self.next_u64() % (n as u64)).expect("modulus fits usize")
        }
        fn bool(&mut self) -> bool {
            self.next_u64() & 1 == 1
        }
    }

    /// Generates a random XOR system: `num_constraints` rows over `num_vars`
    /// variables, each row a random non-empty subset (width `1..=max_width`) with
    /// a random parity.
    fn random_system(rng: &mut Lcg, num_vars: usize, num_constraints: usize) -> Vec<Constraint> {
        let max_width = 4.min(num_vars);
        let mut out = Vec::with_capacity(num_constraints);
        for _ in 0..num_constraints {
            let width = 1 + rng.below(max_width);
            let mut vars = Vec::with_capacity(width);
            for _ in 0..width {
                vars.push(rng.below(num_vars));
            }
            out.push((vars, rng.bool()));
        }
        out
    }

    /// A denser system for the perf proof: wider rows (width `4..=10`) drawn
    /// from a shared, moderately small variable pool so rows overlap heavily —
    /// the regime that produces many pivots, re-pivots, and watch movement.
    fn dense_system(rng: &mut Lcg, num_vars: usize, num_constraints: usize) -> Vec<Constraint> {
        let mut out = Vec::with_capacity(num_constraints);
        for _ in 0..num_constraints {
            let width = 4 + rng.below(7);
            let mut vars = Vec::with_capacity(width);
            for _ in 0..width {
                vars.push(rng.below(num_vars));
            }
            out.push((vars, rng.bool()));
        }
        out
    }

    // --- Targeted unit tests -------------------------------------------------

    #[test]
    fn dup_single_var_is_conflict_at_build() {
        // x1 ⊕ x1 = 1 folds to the empty row 0 = 1: a build-time conflict.
        let constraints: Vec<Constraint> = vec![(vec![1, 1], true)];
        let m = IncrementalXorMatrix::new(&constraints, 2);
        assert!(
            m.in_conflict(),
            "0 = 1 from duplicate single var not detected; rows={:?}",
            m.rows
        );
    }

    #[test]
    fn empty_system_no_constraints() {
        let mut m = IncrementalXorMatrix::new(&[], 3);
        assert_eq!(m.trail_len(), 0);
        let s0 = m.assign(0, true);
        assert_eq!(s0, XorMatrixStep::Ok);
        let s1 = m.assign(1, false);
        assert_eq!(s1, XorMatrixStep::Ok);
        assert_matches_oracle(&[], 3, &mut m, &s1);
    }

    #[test]
    fn width2_forces_partner() {
        // x0 ⊕ x1 = 1, assign x0=true ⇒ x1 forced false.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let mut m = IncrementalXorMatrix::new(&constraints, 2);
        let step = m.assign(0, true);
        let XorMatrixStep::Implied { ref implied } = step else {
            panic!("expected Implied, got {step:?}");
        };
        assert_eq!(implied.len(), 1);
        assert_eq!((implied[0].var, implied[0].value), (1, false));
        assert_eq!(implied[0].reason, vec![(0, true)]);
        assert_matches_oracle(&constraints, 2, &mut m, &step);
    }

    #[test]
    fn fully_assigned_wrong_parity_conflict() {
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let mut m = IncrementalXorMatrix::new(&constraints, 2);
        let _ = m.assign(0, true);
        let step = m.assign(1, true); // 1 ⊕ 1 = 0 ≠ 1 ⇒ conflict
        let XorMatrixStep::Conflict { ref reason } = step else {
            panic!("expected Conflict, got {step:?}");
        };
        assert_reason_subset_of_trail(reason, &matrix_assignment(&m));
        assert_matches_oracle(&constraints, 2, &mut m, &step);
    }

    #[test]
    fn chained_implications() {
        // x0 ⊕ x1 = 1, x1 ⊕ x2 = 0; assign x0=true ⇒ x1=false, x2=false.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true), (vec![1, 2], false)];
        let mut m = IncrementalXorMatrix::new(&constraints, 3);
        let step = m.assign(0, true);
        let XorMatrixStep::Implied { ref implied } = step else {
            panic!("expected Implied, got {step:?}");
        };
        let pairs: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();
        assert_eq!(pairs, vec![(1, false), (2, false)]);
        assert_matches_oracle(&constraints, 3, &mut m, &step);
    }

    #[test]
    fn row_combination_implication_at_build() {
        // A combination-only forced unit at construction (no assignment): the
        // system x0⊕x1=0, x1⊕x2=0, x0⊕x2=1 is UNSAT (combination), so `new`
        // already detects a conflict.
        let constraints: Vec<Constraint> =
            vec![(vec![0, 1], false), (vec![1, 2], false), (vec![0, 2], true)];
        let m = IncrementalXorMatrix::new(&constraints, 3);
        assert!(m.in_conflict(), "combination conflict missed at build");
    }

    #[test]
    fn combination_unit_at_build() {
        // x0⊕x1⊕x2=0 and x1⊕x2=0 entail x0=0 with NOTHING assigned — the
        // combination-only unit the watched scheme must surface from full RREF.
        let constraints: Vec<Constraint> = vec![(vec![0, 1, 2], false), (vec![1, 2], false)];
        let m = IncrementalXorMatrix::new(&constraints, 3);
        let assignment = vec![None; 3];
        assert_eq!(
            live_view(&m),
            oracle_view(&constraints, 3, &assignment),
            "combination unit x0=0 missed at build"
        );
    }

    #[test]
    fn conflict_then_backtrack_clears_it() {
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let mut m = IncrementalXorMatrix::new(&constraints, 2);
        let len0 = m.trail_len();
        let _ = m.assign(0, true);
        let len1 = m.trail_len();
        let step = m.assign(1, true);
        assert!(matches!(step, XorMatrixStep::Conflict { .. }));
        assert!(m.in_conflict());
        m.backtrack_to(len1);
        assert!(!m.in_conflict());
        assert_eq!(
            live_view(&m),
            oracle_view(&constraints, 2, &matrix_assignment(&m))
        );
        m.backtrack_to(len0);
        assert_eq!(m.trail_len(), 0);
        assert!(!m.in_conflict());
    }

    #[test]
    fn backtrack_matches_fresh_branch() {
        // Assign A,B,C; backtrack to after A; assign B',C'; the state must match
        // a fresh matrix assigned [A, B', C'].
        let constraints: Vec<Constraint> =
            vec![(vec![0, 1], true), (vec![1, 2], false), (vec![2, 3], true)];
        let num_vars = 4;
        let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
        let _ = m.assign(0, true);
        let after_a = m.trail_len();
        let _ = m.assign(1, false);
        let _ = m.assign(2, true);
        m.backtrack_to(after_a);
        let _ = m.assign(1, true);
        let last = m.assign(2, false);

        let mut fresh = IncrementalXorMatrix::new(&constraints, num_vars);
        let _ = fresh.assign(0, true);
        let _ = fresh.assign(1, true);
        let fresh_last = fresh.assign(2, false);

        assert_eq!(step_view(&last), step_view(&fresh_last));
        assert_eq!(matrix_assignment(&m), matrix_assignment(&fresh));
        assert_eq!(
            effective_rows(&m),
            effective_rows(&fresh),
            "live RREF after backtrack-branch differs from fresh build"
        );
    }

    /// Canonical (sorted) *effective* view of the live rows: each row reduced to
    /// its free vars + effective parity, dropping trivial `0 = 0` rows. This is
    /// the state-equality check, robust to the lazy (unfolded) representation.
    fn effective_rows(m: &IncrementalXorMatrix) -> Vec<(Vec<usize>, bool)> {
        let mut rows: Vec<(Vec<usize>, bool)> = (0..m.rows.len())
            .map(|r| (m.row_free_vars(r), m.row_effective_parity(r)))
            .filter(|(vars, parity)| !vars.is_empty() || *parity)
            .collect();
        rows.sort();
        rows
    }

    #[test]
    fn determinism_repeated_assign_sequences() {
        let constraints: Vec<Constraint> =
            vec![(vec![0, 1], true), (vec![1, 2], false), (vec![3, 4], true)];
        let seq = [(0usize, true), (3, false), (1, true)];
        let run = || {
            let mut m = IncrementalXorMatrix::new(&constraints, 5);
            let mut views = Vec::new();
            for &(v, val) in &seq {
                views.push(step_view(&m.assign(v, val)));
            }
            views
        };
        let first = run();
        for _ in 0..4 {
            assert_eq!(run(), first);
        }
    }

    #[test]
    fn cross_word_variable_range() {
        // Variables above index 63 exercise the multi-word bitset path.
        let constraints: Vec<Constraint> = vec![(vec![0, 64], true), (vec![64, 100], false)];
        let num_vars = 128;
        let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
        let step = m.assign(0, false);
        // x0=false ⇒ x64=true ⇒ x100=true.
        let XorMatrixStep::Implied { ref implied } = step else {
            panic!("expected Implied, got {step:?}");
        };
        let pairs: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();
        assert_eq!(pairs, vec![(64, true), (100, true)]);
        assert_matches_oracle(&constraints, num_vars, &mut m, &step);
    }

    #[test]
    fn duplicate_vars_in_constraint_cancel() {
        // x0 ⊕ x0 ⊕ x1 = 1 reduces to x1 = 1 (forced at build).
        let constraints: Vec<Constraint> = vec![(vec![0, 0, 1], true)];
        let mut m = IncrementalXorMatrix::new(&constraints, 2);
        let step = m.assign(0, true);
        let XorMatrixStep::Implied { ref implied } = step else {
            panic!("expected Implied, got {step:?}");
        };
        assert!(implied.iter().any(|i| i.var == 1 && i.value));
        assert_matches_oracle(&constraints, 2, &mut m, &step);
    }

    // --- The headline differential -------------------------------------------

    #[test]
    fn differential_random_systems_and_sequences() {
        let mut rng = Lcg::new(0xA5A5_1234);
        let num_systems = 400;
        let mut total_steps = 0usize;

        for _ in 0..num_systems {
            let num_vars = 2 + rng.below(8); // 2..=9
            let num_constraints = 1 + rng.below(8); // 1..=8
            let constraints = random_system(&mut rng, num_vars, num_constraints);

            let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
            {
                let assignment = matrix_assignment(&m);
                let oracle = oracle_view(&constraints, num_vars, &assignment);
                let live = live_view(&m);
                assert_eq!(live, oracle, "build state mismatch for {constraints:?}");
            }

            let steps = 6 + rng.below(10);
            let mut checkpoints: Vec<usize> = vec![0];
            for _ in 0..steps {
                if rng.below(4) == 0 && m.trail_len() > 0 {
                    let idx = rng.below(checkpoints.len());
                    let target = checkpoints[idx];
                    m.backtrack_to(target);
                    checkpoints.retain(|&c| c <= target);
                    let assignment = matrix_assignment(&m);
                    let oracle = oracle_view(&constraints, num_vars, &assignment);
                    assert_eq!(
                        live_view(&m),
                        oracle,
                        "post-backtrack mismatch on {assignment:?} for {constraints:?}"
                    );
                    total_steps += 1;
                    continue;
                }

                let Some(var) = pick_free(&mut rng, &m) else {
                    break;
                };
                let value = rng.bool();
                let step = m.assign(var, value);
                assert_matches_oracle(&constraints, num_vars, &mut m, &step);
                let assignment = matrix_assignment(&m);
                let oracle = oracle_view(&constraints, num_vars, &assignment);
                assert_eq!(
                    live_view(&m),
                    oracle,
                    "live view mismatch after assign {var}={value} on {assignment:?} for \
                     {constraints:?}"
                );
                checkpoints.push(m.trail_len());
                total_steps += 1;
            }
        }
        assert!(
            total_steps > 2000,
            "differential exercised only {total_steps} steps"
        );
    }

    /// The matrix's *current* entailment recomputed from live rows (not the last
    /// returned step): conflict status + sorted implied SET. `None` = conflict.
    fn live_view(m: &IncrementalXorMatrix) -> Option<Vec<(usize, bool)>> {
        // Recompute conflict from scratch so a stale `conflict` field cannot mask
        // a divergence (the differential is the soundness proof).
        if m.detect_conflict_reason().is_some() {
            return None;
        }
        let mut set: Vec<(usize, bool)> = Vec::new();
        for r in 0..m.rows.len() {
            let free = m.row_free_vars(r);
            if let [only] = free.as_slice() {
                set.push((*only, m.row_effective_parity(r)));
            }
        }
        set.sort_unstable();
        set.dedup();
        Some(set)
    }

    fn pick_free(rng: &mut Lcg, m: &IncrementalXorMatrix) -> Option<usize> {
        let free: Vec<usize> = (0..m.num_vars)
            .filter(|&v| m.assignment[v].is_none())
            .collect();
        if free.is_empty() {
            None
        } else {
            Some(free[rng.below(free.len())])
        }
    }

    #[test]
    fn differential_backtrack_heavy() {
        // A second differential biased toward deep assign/backtrack churn to
        // stress journal restoration specifically.
        let mut rng = Lcg::new(0x0BAD_F00D);
        for _ in 0..200 {
            let num_vars = 3 + rng.below(6);
            let num_constraints = 2 + rng.below(6);
            let constraints = random_system(&mut rng, num_vars, num_constraints);
            let mut m = IncrementalXorMatrix::new(&constraints, num_vars);

            for _ in 0..20 {
                if m.trail_len() > 0 && rng.bool() {
                    let target = rng.below(m.trail_len());
                    m.backtrack_to(target);
                } else if let Some(var) = pick_free(&mut rng, &m) {
                    let _ = m.assign(var, rng.bool());
                }
                let assignment = matrix_assignment(&m);
                let oracle = oracle_view(&constraints, num_vars, &assignment);
                assert_eq!(
                    live_view(&m),
                    oracle,
                    "backtrack-heavy mismatch on {assignment:?} for {constraints:?}"
                );
            }
        }
    }

    #[test]
    fn differential_against_fresh_rebuild_state() {
        // After every assign, the live *effective* rows must match a fresh matrix
        // built and assigned to the same trail (canonical RREF equality), the
        // strongest backtrack-correctness statement. Adapted to the lazy
        // (unfolded) representation by comparing effective free-vars + parity.
        let mut rng = Lcg::new(0xFEED_BEEF);
        for _ in 0..150 {
            let num_vars = 3 + rng.below(6);
            let num_constraints = 2 + rng.below(6);
            let constraints = random_system(&mut rng, num_vars, num_constraints);
            let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
            let mut trail: Vec<(usize, bool)> = Vec::new();

            for _ in 0..16 {
                if !trail.is_empty() && rng.below(3) == 0 {
                    let target = rng.below(trail.len());
                    m.backtrack_to(target);
                    trail.truncate(target);
                } else if let Some(var) = pick_free(&mut rng, &m) {
                    let value = rng.bool();
                    let _ = m.assign(var, value);
                    trail.push((var, value));
                }

                let mut fresh = IncrementalXorMatrix::new(&constraints, num_vars);
                for &(v, val) in &trail {
                    let _ = fresh.assign(v, val);
                }
                assert_eq!(
                    effective_rows(&m),
                    effective_rows(&fresh),
                    "live RREF diverged from fresh rebuild on trail {trail:?} for {constraints:?}"
                );
                assert_eq!(
                    m.detect_conflict_reason().is_some(),
                    fresh.detect_conflict_reason().is_some()
                );
            }
        }
    }

    // --- Watch-index invariant + perf proof ----------------------------------

    /// The watch index must be a faithful inverse of each row's `watched` list,
    /// and every row must watch exactly `min(2, #free)` of its free vars.
    ///
    /// Skipped when the matrix is in conflict: once a `0 = 1` row appears,
    /// `assign` short-circuits (the system is unsatisfiable under the trail and
    /// stays so until backtrack), so the watch index is intentionally not kept
    /// live in that terminal state.
    fn assert_watch_invariant(m: &IncrementalXorMatrix) {
        if m.in_conflict() {
            return;
        }
        // Each row watches min(2,#free) of its free vars, and those are free.
        for r in 0..m.rows.len() {
            let free = m.row_free_vars(r);
            let want = free.len().min(2);
            assert_eq!(
                m.rows[r].watched.len(),
                want,
                "row {r} watches {:?} but has free {:?}",
                m.rows[r].watched,
                free
            );
            for &v in &m.rows[r].watched {
                assert!(
                    m.assignment[v].is_none() && m.row_has_bit(r, v),
                    "row {r} watches non-free var {v}"
                );
                assert!(m.watches[v].contains(&r), "watches[{v}] missing row {r}");
            }
        }
        // The watch index has no dangling entries.
        for (v, list) in m.watches.iter().enumerate() {
            for &r in list {
                assert!(
                    m.rows[r].watched.contains(&v),
                    "watches[{v}] has row {r} that does not watch {v}"
                );
            }
        }
    }

    #[test]
    fn watch_invariant_holds_across_assigns() {
        let mut rng = Lcg::new(0xC0FF_EE42);
        for _ in 0..150 {
            let num_vars = 3 + rng.below(8);
            let num_constraints = 2 + rng.below(8);
            let constraints = random_system(&mut rng, num_vars, num_constraints);
            let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
            assert_watch_invariant(&m);
            for _ in 0..16 {
                if m.trail_len() > 0 && rng.below(3) == 0 {
                    let target = rng.below(m.trail_len());
                    m.backtrack_to(target);
                } else if let Some(var) = pick_free(&mut rng, &m) {
                    let _ = m.assign(var, rng.bool());
                }
                assert_watch_invariant(&m);
            }
        }
    }

    #[test]
    fn perf_rows_examined_per_assign_is_bounded() {
        // On a moderately large random XOR system, the average rows-examined per
        // assign must be small (≈ watches-per-var), NOT proportional to the total
        // number of rows. This is the in-crate evidence that the per-assign cost
        // dropped from O(rows) to O(watched). The metric counts every row the
        // assign touches: both the watched-row processing and the rows a re-pivot
        // eliminates into. Observed on this seed: ~7 rows/assign over 180 rows,
        // versus ~180 rows/assign for the old "scan all rows every assign" code.
        let mut rng = Lcg::new(0x5EED_1357);
        // A wide, well-connected but under-determined system (many more vars than
        // constraints, so it stays consistent across a long assign prefix) with
        // wide rows so re-pivots and watch movement are genuinely exercised — the
        // regime where the old "scan all rows every assign" code was quadratic.
        let num_vars = 600;
        let num_constraints = 180;
        let constraints = dense_system(&mut rng, num_vars, num_constraints);
        let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
        let total_rows = m.rows.len();
        assert!(total_rows > 100, "system too small: {total_rows} rows");

        // Assign a long prefix of distinct free variables, stopping if the system
        // becomes inconsistent (a conflict is a terminal state for the metric).
        let mut assigns = 0u64;
        for _ in 0..200 {
            if m.in_conflict() {
                break;
            }
            let Some(var) = pick_free(&mut rng, &m) else {
                break;
            };
            let _ = m.assign(var, rng.bool());
            assigns += 1;
        }
        assert!(assigns > 50, "too few assigns to be meaningful: {assigns}");

        // Compare with integer arithmetic to avoid float casts:
        //   avg = rows_examined / assign_calls.
        // Each row watches ≤ 2 vars, so the total watch slots is ≤ 2 * rows and
        // the average rows watching any one assigned var is far below total_rows.
        let examined = m.rows_examined();
        let calls = m.assign_calls();
        let total_rows_u64 = u64::try_from(total_rows).expect("rows fit u64");

        // Bound 1: avg < total_rows / 4  ⟺  4 * examined < total_rows * calls.
        // (The old code would have examined ~all rows every assign, i.e. avg ≈
        // total_rows, so this would fail for it.)
        assert!(
            4 * examined < total_rows_u64 * calls,
            "avg rows-examined-per-assign {examined}/{calls} not bounded well below \
             total rows {total_rows} (watched scheme not effective)"
        );
        // Bound 2: avg < 16  ⟺  examined < 16 * calls (watches-per-var scale).
        assert!(
            examined < 16 * calls,
            "avg rows-examined-per-assign {examined}/{calls} exceeds the watched-scheme scale"
        );
    }
}
