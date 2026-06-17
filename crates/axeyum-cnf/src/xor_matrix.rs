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
//! 2.3× slower, `calypto_9` 19× slower). The fix is a *true incremental matrix*:
//! maintain the XOR system under an evolving partial assignment with cheap
//! per-assignment updates and restore-on-backtrack, instead of rebuilding a
//! fresh [`crate::Gf2System`] every level.
//!
//! Scope: this slice is the *standalone primitive plus its correctness
//! differential* only. It is **not** wired into [`crate::xor_cdcl`] or any solver
//! path — that integration is a deliberately deferred later slice. Likewise the
//! reasons here are sound over-approximations (see below), and minimizing them is
//! a separate refinement.
//!
//! # The scheme: reduced row echelon over free columns, maintained on the trail
//!
//! The matrix keeps its rows in **reduced row echelon form (RREF) over the
//! still-free (unassigned) variables**, with every assigned variable's value
//! already folded into the right-hand-side parity. Concretely, the live state is
//! a set of rows, each a GF(2) bitset over the *free* columns plus a parity bit,
//! such that:
//!
//! * each non-trivial row has a distinct *pivot* (its lowest-index free
//!   variable), no two rows share a pivot, and no other row has that pivot
//!   column set — this is exactly RREF, the same normal form
//!   [`crate::Gf2System::solve`] computes from scratch;
//! * a row with **one** free variable is a forced *unit* (`x = parity`), the
//!   propagation completeness path;
//! * a row with **zero** free variables and parity `1` is the inconsistent
//!   `0 = 1` row, a conflict.
//!
//! Maintaining RREF (not just watched rows) is what makes completeness match
//! [`crate::xor_implications`]: watched-variable propagation alone misses
//! implications that only appear after combining rows, but RREF exposes every
//! such combination as an explicit reduced row. The full set of forced units in
//! RREF is exactly the set of implied literals full Gaussian reports.
//!
//! ## On assign — incremental column elimination
//!
//! Assigning `var = value` substitutes that column out of the live RREF:
//!
//! 1. If a row pivots on `var`, that pivot is lost; the row is re-pivoted onto
//!    its next free variable (and, to restore RREF, that new pivot column is
//!    eliminated from the other rows). This is the only step that can touch
//!    other rows.
//! 2. Every row that *contains* `var` (non-pivot occurrences) clears that bit
//!    and toggles its parity by `value`.
//! 3. Rows that become single-free-variable rows are the new forced units; rows
//!    that become empty with parity `1` are conflicts.
//!
//! Because the live matrix is *already* in RREF before the assign, substituting
//! one column touches only the rows that mention that column plus a single
//! re-pivot — it does **not** redo elimination over the whole system. That is the
//! genuine incremental win over [`crate::xor_search::xor_implications`], which
//! rebuilds and fully Gaussian-eliminates a fresh system on every call. (See the
//! per-assign cost note on [`IncrementalXorMatrix::assign`].)
//!
//! ## On backtrack — restore via journal
//!
//! The matrix records every assign on a trail and journals the pre-assign row
//! state so [`IncrementalXorMatrix::backtrack_to`] restores the live RREF
//! exactly to what a fresh matrix built and assigned to the truncated trail would
//! hold. State after backtrack is byte-for-byte the canonical RREF for that
//! prefix (the differential checks this against a from-scratch rebuild).
//!
//! # Reasons are a sound over-approximation
//!
//! Each conflict and each implied literal carries a `reason`: a subset of the
//! current trail assignments (`(var, value)` pairs) that already forces the
//! result. As in [`crate::xor_search`] the reason is the assigned variables in
//! the *connected component* (via shared original constraints) of the
//! implied/conflicting variable. Fixing exactly those reason variables (leaving
//! every other variable free) still forces the implication/conflict, so the
//! reason is a valid, *sound* explanation — it is simply not guaranteed minimal.
//! Reasons are always a subset of the trail, sorted by variable index, and
//! deterministic.
//!
//! # Determinism
//!
//! Rows are processed in pivot order, free-variable scans are index-ordered, and
//! all outputs (implied literals, reasons) are sorted by variable index. No
//! hash-map iteration order influences any output.

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

/// A single live row: the free-variable bitset, its parity, and the original
/// constraint indices that were `XOR`ed together to form it (for reasons).
#[derive(Debug, Clone)]
struct Row {
    /// One bit per *original* variable; set ⇒ that still-free variable is in the
    /// row. Assigned variables never have their bit set here (folded into
    /// `parity`).
    bits: Vec<u64>,
    /// Right-hand-side parity, with all assigned-variable contributions folded
    /// in.
    parity: bool,
    /// The pivot variable (lowest set bit) cached, or `usize::MAX` when the row
    /// has no free variables.
    pivot: usize,
    /// Sorted, deduplicated component roots whose original constraints were
    /// `XOR`ed to form this row. Lets an *empty* `0 = 1` conflict row still name a
    /// tight, sound reason (the assigned variables in these components), since
    /// once a row's free bits are gone its component can no longer be read off
    /// the bitset. Provenance is propagated through every row XOR.
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
/// reduced row echelon form against an evolving partial assignment.
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
    /// Live rows in reduced row echelon form over the free columns.
    rows: Vec<Row>,
    /// Current trail of assignments, in assign order.
    trail: Vec<(usize, bool)>,
    /// Per-trail-entry journal: the entire `rows` snapshot taken *before* the
    /// corresponding assign was applied, so backtrack restores it exactly.
    /// `journal[i]` restores the state that existed after `i` assignments.
    journal: Vec<Vec<Row>>,
    /// `assignment[v]` is `Some(value)` if `v` is on the trail, else `None`.
    assignment: Vec<Option<bool>>,
    /// Connected-component representative per variable (union-find roots), built
    /// once from the original constraints for reasons.
    component: Vec<usize>,
    /// Whether the most recent live state is a conflict, and its reason.
    conflict: Option<Vec<(usize, bool)>>,
}

impl IncrementalXorMatrix {
    /// Builds the matrix from XOR `constraints` over `num_vars` variables.
    ///
    /// Each constraint is `(vars, parity)` asserting `(⊕ of vars) = parity`, the
    /// same shape [`crate::xor_implications`] and [`crate::Gf2System`] accept;
    /// duplicate variables in a constraint cancel by parity. The matrix starts
    /// with an empty trail and the constraints reduced to RREF over all
    /// variables.
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
        // every union, so provenance reflects the final connected components (a
        // root captured mid-loop can be stale as later constraints merge it).
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

        // Second pass: now that components are final, attach each row's provenance
        // component (the component of any one of its original variables).
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
                    parity: rr.parity,
                    pivot,
                    components,
                }
            })
            .collect();

        let mut matrix = Self {
            num_vars,
            rows: raw,
            trail: Vec::new(),
            journal: Vec::new(),
            assignment: vec![None; num_vars],
            component,
            conflict: None,
        };
        // Reduce the initial system to RREF so the live invariant holds from the
        // start (and so unit/empty rows are exposed immediately).
        matrix.reduce_all();
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
    /// The live matrix is already in RREF, so substituting one column touches
    /// only (a) the single row pivoting on `var`, which is re-pivoted, and (b)
    /// the rows that mention `var`, which clear one bit and toggle parity. A
    /// re-pivot eliminates one new pivot column from the other rows. Worst case
    /// this is `O(rows × words)` (one column elimination), versus
    /// [`crate::xor_implications`]'s full `O(num_vars × rows × words)` rebuild +
    /// Gaussian. In practice each assign touches only the rows containing `var`,
    /// so it is genuinely incremental, not a from-scratch resolve.
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

        // Journal the pre-assign row state so backtrack restores it exactly, then
        // record the trail entry.
        self.journal.push(self.rows.clone());
        self.trail.push((var, value));
        self.assignment[var] = Some(value);

        // If we were already in conflict, the system stays in conflict; keep the
        // existing reason (sound: a subset of the smaller trail is still a subset
        // of this larger trail). xor_implications would also report a conflict.
        if let Some(reason) = &self.conflict {
            return XorMatrixStep::Conflict {
                reason: reason.clone(),
            };
        }

        // Substitute `var` out of every row, re-pivoting and re-reducing only the
        // affected rows.
        self.substitute_column(var, value);

        self.collect_step()
    }

    /// Undoes assignments until the trail has length `trail_len`, restoring the
    /// live matrix exactly to its state at that trail length.
    ///
    /// After this call the matrix is byte-for-byte what a fresh
    /// [`IncrementalXorMatrix::new`] built and assigned to the first `trail_len`
    /// trail entries would hold — including conflict status. A conflict
    /// discovered deeper on the trail and then backtracked away is no longer
    /// reported.
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
            // Restore the rows snapshot taken before this assignment.
            self.rows = self.journal.pop().expect("journal parallel to trail");
        }
        // Recompute conflict status from the restored rows (cheap: scan rows).
        self.conflict = self.detect_conflict_reason();
    }

    // --- internal: RREF maintenance ----------------------------------------

    /// Fully reduces `self.rows` to RREF over all free columns. Used once at
    /// construction; afterwards the matrix is kept in RREF incrementally.
    fn reduce_all(&mut self) {
        let mut pivot_row = 0usize;
        for col in 0..self.num_vars {
            let Some(sel) = (pivot_row..self.rows.len()).find(|&r| self.row_has_bit(r, col)) else {
                continue;
            };
            self.rows.swap(pivot_row, sel);
            self.eliminate_column_with_pivot(col, pivot_row);
            pivot_row += 1;
            if pivot_row == self.rows.len() {
                break;
            }
        }
        // Drop all-zero rows with parity 0 is unnecessary (they are harmless),
        // but recompute pivots and conflict.
        for r in 0..self.rows.len() {
            self.rows[r].pivot = lowest_set_bit(&self.rows[r].bits, self.num_vars);
        }
        self.conflict = self.detect_conflict_reason();
    }

    /// Substitutes assigned `var = value` out of the live RREF, keeping RREF.
    fn substitute_column(&mut self, var: usize, value: bool) {
        // Step 1: any row that *pivots* on `var` loses its pivot. Fold the value
        // and re-pivot onto its next free variable, eliminating that new pivot
        // from the other rows to restore RREF.
        //
        // Step 2: rows where `var` is a non-pivot occurrence simply clear the bit
        // and toggle parity (RREF among the remaining pivots is preserved, since
        // those pivots are untouched).
        //
        // We scan all rows once. Because the matrix was RREF, at most one row had
        // `var` as a pivot; every other occurrence of `var` is a non-pivot bit.
        let word = var / 64;
        let mask = 1u64 << (var % 64);

        // First, fold the value into every row containing `var` and clear the
        // bit. Track rows that lost their pivot so we can re-pivot them.
        let mut lost_pivot_rows: Vec<usize> = Vec::new();
        for r in 0..self.rows.len() {
            if self.rows[r].bits[word] & mask != 0 {
                self.rows[r].bits[word] &= !mask;
                if value {
                    self.rows[r].parity = !self.rows[r].parity;
                }
                if self.rows[r].pivot == var {
                    lost_pivot_rows.push(r);
                }
            }
        }

        // Re-pivot each row that lost its pivot, restoring RREF. There is at most
        // one such row in a true RREF, but handle the general case defensively.
        for &r in &lost_pivot_rows {
            let new_pivot = lowest_set_bit(&self.rows[r].bits, self.num_vars);
            self.rows[r].pivot = new_pivot;
            if new_pivot != usize::MAX {
                // Eliminate the new pivot column from all other rows so it stays
                // a unique pivot (restores RREF).
                self.eliminate_column_with_pivot(new_pivot, r);
            }
        }
    }

    /// Eliminates column `col` from every row except `pivot_row`, using
    /// `rows[pivot_row]` as the pivot. Recomputes affected pivots.
    fn eliminate_column_with_pivot(&mut self, col: usize, pivot_row: usize) {
        let pivot_bits = self.rows[pivot_row].bits.clone();
        let pivot_parity = self.rows[pivot_row].parity;
        let pivot_components = self.rows[pivot_row].components.clone();
        self.rows[pivot_row].pivot = lowest_set_bit(&pivot_bits, self.num_vars);
        for r in 0..self.rows.len() {
            if r != pivot_row && self.row_has_bit(r, col) {
                for (dst, &src) in self.rows[r].bits.iter_mut().zip(pivot_bits.iter()) {
                    *dst ^= src;
                }
                self.rows[r].parity ^= pivot_parity;
                self.rows[r].components =
                    merge_components(&self.rows[r].components, &pivot_components);
                self.rows[r].pivot = lowest_set_bit(&self.rows[r].bits, self.num_vars);
            }
        }
    }

    fn row_has_bit(&self, r: usize, col: usize) -> bool {
        (self.rows[r].bits[col / 64] >> (col % 64)) & 1 == 1
    }

    // --- internal: entailment readout --------------------------------------

    /// Reads the live RREF for the current step: conflict (if any), else the set
    /// of newly implied units.
    fn collect_step(&mut self) -> XorMatrixStep {
        if let Some(reason) = self.detect_conflict_reason() {
            self.conflict = Some(reason.clone());
            return XorMatrixStep::Conflict { reason };
        }
        self.conflict = None;

        // Forced units: rows with exactly one free variable. In RREF these are
        // exactly the implied literals full Gaussian reports.
        let mut implied: Vec<XorImplied> = Vec::new();
        for row in &self.rows {
            let free = row_free_vars(&row.bits, self.num_vars);
            if let [only] = free.as_slice() {
                // Guard: an implied variable must be genuinely free on the trail.
                debug_assert!(
                    self.assignment[*only].is_none(),
                    "implied variable {only} was already assigned"
                );
                if self.assignment[*only].is_none() {
                    let reason = self.component_reason(*only);
                    implied.push(XorImplied {
                        var: *only,
                        value: row.parity,
                        reason,
                    });
                }
            }
        }
        implied.sort_by_key(|i| i.var);
        // RREF guarantees at most one unit row per variable, but dedup defensively
        // in case multiple rows reduce to the same single variable.
        implied.dedup_by_key(|i| i.var);

        if implied.is_empty() {
            XorMatrixStep::Ok
        } else {
            XorMatrixStep::Implied { implied }
        }
    }

    /// Detects a conflict in the live rows: any empty row with parity `1`
    /// (`0 = 1`). Returns a sound, tight reason if so.
    ///
    /// A `0 = 1` row has no free bits left, so its component is read from the
    /// row's tracked provenance (`Row::components`) — the components whose
    /// original constraints were `XOR`ed to form it. The reason is every assigned
    /// trail variable in those components; fixing only those still forces the
    /// `0 = 1` row, so it is sound. If provenance is somehow empty (a constraint
    /// with no variables, e.g. an explicit `() = 1`), fall back to the whole
    /// trail — still a sound subset.
    fn detect_conflict_reason(&self) -> Option<Vec<(usize, bool)>> {
        let mut conflict_roots: Vec<usize> = Vec::new();
        let mut any_conflict = false;
        let mut untraceable = false;
        for row in &self.rows {
            if row_is_zero(&row.bits) && row.parity {
                any_conflict = true;
                if row.components.is_empty() {
                    untraceable = true;
                } else {
                    conflict_roots.extend_from_slice(&row.components);
                }
            }
        }
        if !any_conflict {
            return None;
        }
        let reason = if untraceable || conflict_roots.is_empty() {
            self.all_assigned_sorted()
        } else {
            self.components_reason(&conflict_roots)
        };
        Some(reason)
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

/// The lowest set bit index in `bits`, limited to `num_vars`, or `usize::MAX` if
/// none.
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

/// Whether no bit is set.
fn row_is_zero(bits: &[u64]) -> bool {
    bits.iter().all(|&w| w == 0)
}

/// The free variable indices set in `bits`, ascending, limited to `num_vars`.
fn row_free_vars(bits: &[u64], num_vars: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for (w, &word) in bits.iter().enumerate() {
        let mut b = word;
        while b != 0 {
            let tz = b.trailing_zeros() as usize;
            let var = w * 64 + tz;
            if var < num_vars {
                out.push(var);
            }
            b &= b - 1;
        }
    }
    out
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
    ///
    /// `last_step` is the step the matrix just returned; we cross-check it with a
    /// freshly recomputed view of the current state to also catch stale results.
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
                    // Fixing only the reason still forces this literal (the oracle
                    // must imply it, and to the same value).
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
                        XorImplication::Conflict { .. } => {
                            // A conflict still forces every literal vacuously; the
                            // reason being a conflict is also sound.
                        }
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
            // xorshift* — deterministic, decent spread.
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
    fn conflict_then_backtrack_clears_it() {
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let mut m = IncrementalXorMatrix::new(&constraints, 2);
        let len0 = m.trail_len();
        let _ = m.assign(0, true);
        let len1 = m.trail_len();
        let step = m.assign(1, true);
        assert!(matches!(step, XorMatrixStep::Conflict { .. }));
        assert!(m.in_conflict());
        // Backtrack one level: conflict gone (state implies x1=false).
        m.backtrack_to(len1);
        assert!(!m.in_conflict());
        assert_eq!(
            live_view(&m),
            oracle_view(&constraints, 2, &matrix_assignment(&m))
        );
        // Backtrack to start.
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

        // Fresh matrix on the same prefix.
        let mut fresh = IncrementalXorMatrix::new(&constraints, num_vars);
        let _ = fresh.assign(0, true);
        let _ = fresh.assign(1, true);
        let fresh_last = fresh.assign(2, false);

        assert_eq!(step_view(&last), step_view(&fresh_last));
        assert_eq!(matrix_assignment(&m), matrix_assignment(&fresh));
        // The reduced live rows must match exactly (canonical RREF for the prefix).
        assert_eq!(
            normalized_rows(&m),
            normalized_rows(&fresh),
            "live RREF after backtrack-branch differs from fresh build"
        );
    }

    /// Canonical (sorted) view of the live rows for state-equality checks.
    fn normalized_rows(m: &IncrementalXorMatrix) -> Vec<(Vec<usize>, bool)> {
        let mut rows: Vec<(Vec<usize>, bool)> = m
            .rows
            .iter()
            .map(|r| (row_free_vars(&r.bits, m.num_vars), r.parity))
            // Drop trivial 0 = 0 rows: they carry no information and their count
            // can differ between equivalent reductions.
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
        // At build, x1 is already a forced unit; an assign of x0 keeps it.
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
            // Vary the shape across systems, including cross-word ranges.
            let num_vars = 2 + rng.below(8); // 2..=9
            let num_constraints = 1 + rng.below(8); // 1..=8
            let constraints = random_system(&mut rng, num_vars, num_constraints);

            let mut m = IncrementalXorMatrix::new(&constraints, num_vars);
            // Cross-check the build state (all-None) live view against the oracle.
            {
                let assignment = matrix_assignment(&m);
                let oracle = oracle_view(&constraints, num_vars, &assignment);
                let live = live_view(&m);
                assert_eq!(live, oracle, "build state mismatch for {constraints:?}");
            }

            // A random assignment sequence with occasional backtracks.
            let steps = 6 + rng.below(10);
            let mut checkpoints: Vec<usize> = vec![0];
            for _ in 0..steps {
                // Occasionally backtrack to a recorded checkpoint.
                if rng.below(4) == 0 && m.trail_len() > 0 {
                    let idx = rng.below(checkpoints.len());
                    let target = checkpoints[idx];
                    m.backtrack_to(target);
                    checkpoints.retain(|&c| c <= target);
                    // After backtrack, recompute the live view vs oracle.
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

                // Pick a currently-free variable to assign.
                let Some(var) = pick_free(&mut rng, &m) else {
                    break;
                };
                let value = rng.bool();
                let step = m.assign(var, value);
                assert_matches_oracle(&constraints, num_vars, &mut m, &step);
                // Also cross-check the recomputed live view (catches stale results
                // where `assign` returns Ok but the state actually implies more).
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
        // Sanity: the differential actually exercised many steps.
        assert!(
            total_steps > 2000,
            "differential exercised only {total_steps} steps"
        );
    }

    /// The matrix's *current* entailment recomputed from live rows (not the last
    /// returned step): conflict status + sorted implied SET. `None` = conflict.
    fn live_view(m: &IncrementalXorMatrix) -> Option<Vec<(usize, bool)>> {
        if m.in_conflict() {
            return None;
        }
        let mut set: Vec<(usize, bool)> = Vec::new();
        for row in &m.rows {
            let free = row_free_vars(&row.bits, m.num_vars);
            if let [only] = free.as_slice()
                && m.assignment[*only].is_none()
            {
                set.push((*only, row.parity));
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
        // After every assign, the live reduced rows must match a fresh matrix
        // built and assigned to the same trail (canonical RREF equality), which
        // is the strongest backtrack-correctness statement.
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

                // Rebuild a fresh matrix on the identical trail.
                let mut fresh = IncrementalXorMatrix::new(&constraints, num_vars);
                for &(v, val) in &trail {
                    let _ = fresh.assign(v, val);
                }
                assert_eq!(
                    normalized_rows(&m),
                    normalized_rows(&fresh),
                    "live RREF diverged from fresh rebuild on trail {trail:?} for {constraints:?}"
                );
                assert_eq!(m.in_conflict(), fresh.in_conflict());
            }
        }
    }
}
