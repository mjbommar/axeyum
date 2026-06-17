//! In-search XOR (GF(2)) propagation primitive for CDCL(XOR).
//!
//! This module is the sixth slice of the CDCL(XOR) path (see
//! `docs/research/05-algorithms/multiplier-sat-wall-and-algebraic-paths.md`,
//! path 2). The earlier slices landed the GF(2) Gaussian solver in
//! [`crate::gf2`], XOR-gate extraction in [`crate::xor_extract`], and the
//! whole-formula XOR preprocessing pass in [`crate::xor_propagate`].
//!
//! This slice is the *pure propagation primitive* the eventual CDCL(XOR) loop
//! will call. Given a set of XOR constraints and a **partial** assignment (a
//! snapshot of the current trail), [`xor_implications`] computes everything the
//! XOR theory entails on that trail: either a conflict (some fully-assigned
//! constraint has the wrong parity, or the reduced system is inconsistent) or
//! the list of literals the XOR theory forces beyond the given assignment.
//!
//! Scope: this is the *propagation* primitive only. It does **not** touch any
//! CDCL search loop, watched literals, incremental matrix maintenance,
//! backtracking, or learned-clause generation — wiring this into a live search
//! (including an incremental Gaussian matrix and minimal conflict/propagation
//! reasons) is a deliberately deferred later slice.
//!
//! # How it works
//!
//! The partial assignment is *substituted* into the constraint system and the
//! existing [`Gf2System`] solver is reused, rather than re-implementing
//! Gaussian elimination:
//!
//! * For each constraint `(vars, parity)`, the assigned variables are dropped
//!   and folded into the right-hand side — an assigned `var = true` toggles the
//!   parity (`x ⊕ rest = p` becomes `rest = p ⊕ 1`), an assigned `var = false`
//!   is a no-op. Duplicate variables in a constraint cancel by parity, exactly
//!   as [`Gf2System::add_constraint`] handles them.
//! * A constraint whose free-variable set becomes **empty** is fully decided by
//!   the assignment: if its folded parity is `true` it is the inconsistent row
//!   `0 = 1`, a [`XorImplication::Conflict`]; if `false` it is trivially
//!   satisfied and contributes nothing.
//! * The remaining reduced constraints (those with at least one free variable)
//!   are fed into a fresh [`Gf2System`] sized to `num_vars`. If that system is
//!   [`Gf2Outcome::Unsat`] the trail already forces a contradiction
//!   ([`XorImplication::Conflict`]); otherwise its
//!   [`Gf2Solution::implied_units`](crate::Gf2Solution::implied_units) are
//!   exactly the literals the XOR theory now forces on still-free variables
//!   ([`XorImplication::Implied`]).
//!
//! # Reasons are a sound over-approximation
//!
//! Every implication and every conflict carries a `reason`: the assigned
//! variables (with their trail values) that a CDCL(T) loop would turn into a
//! learned clause. For this first slice the reason is a **sound but
//! non-minimal over-approximation**: it is the set of all assigned variables
//! that share at least one constraint (transitively, within the connected
//! component of constraints) with the implied/conflicting variable. Fixing
//! exactly those reason variables (leaving every other variable free) still
//! forces the implication/conflict, so the reason is a valid explanation — it
//! is simply not guaranteed minimal. Computing a minimal reason is a later
//! refinement. The reason is always a subset of the assigned variables, sorted
//! by variable index, and deterministic.
//!
//! # Determinism
//!
//! All outputs are sorted by variable index and derive only from the (index-
//! ordered) [`Gf2System`] solve and index-ordered constraint scans; no
//! hash-map iteration order influences any output.

use crate::{Gf2Outcome, Gf2System};

/// A single XOR constraint over a variable set with a right-hand-side parity.
///
/// This is the same shape [`crate::extract_xors`] and
/// [`Gf2System::add_constraint`] use: the constraint asserts
/// `(⊕ of `variables`) = parity`. A variable listed an even number of times
/// cancels (`x ⊕ x = 0`).
pub type XorConstraintInput = (Vec<usize>, bool);

/// A literal the XOR theory forces beyond the partial assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorImplied {
    /// The forced variable (free in the input assignment).
    pub var: usize,
    /// The value it is forced to.
    pub value: bool,
    /// A sound (possibly non-minimal) explanation: the assigned variables, with
    /// their trail values, that force this literal. Sorted by variable index.
    pub reason: Vec<(usize, bool)>,
}

/// What the XOR theory entails under a partial assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XorImplication {
    /// The XOR constraints are inconsistent under this partial assignment: no
    /// completion of the free variables satisfies all constraints. `reason` is
    /// the assigned variables (with their trail values) that participate in the
    /// violated constraint(s) — the conflict explanation a CDCL(T) loop turns
    /// into a learned clause. Sound but possibly non-minimal; sorted by
    /// variable index.
    Conflict {
        /// The assigned variables (with values) explaining the conflict.
        reason: Vec<(usize, bool)>,
    },
    /// The constraints are consistent under this partial assignment. `implied`
    /// lists every literal the XOR theory forces on a still-free variable, each
    /// with its propagation reason. Deterministic and sorted by variable index.
    Implied {
        /// Forced literals beyond the given assignment, sorted by variable.
        implied: Vec<XorImplied>,
    },
}

/// Converts a [`crate::ExtractedXors`]-style constraint list into the
/// [`XorConstraintInput`] shape `xor_implications` accepts.
///
/// This is a convenience for callers that already hold `(vars, parity)` pairs
/// from [`crate::extract_xors`]; it simply clones each pair. It does not change
/// extraction.
#[must_use]
pub fn constraints_from_pairs(pairs: &[(Vec<usize>, bool)]) -> Vec<XorConstraintInput> {
    pairs.to_vec()
}

/// Computes everything the XOR theory entails under a partial assignment.
///
/// `constraints` is the set of XOR constraints (`(vars, parity)` per
/// constraint, the [`Gf2System::add_constraint`] shape). `num_vars` is the
/// variable-namespace size; every variable index in `constraints` and the
/// length of `assignment` must be `< num_vars` / `== num_vars` respectively.
/// `assignment[v]` is `Some(value)` if the trail has fixed variable `v` and
/// `None` if it is still free.
///
/// Returns [`XorImplication::Conflict`] when no completion of the free
/// variables satisfies all constraints, otherwise [`XorImplication::Implied`]
/// with every literal forced on a still-free variable. See the module docs for
/// the reduction, and note that `reason`s are sound but possibly non-minimal
/// over-approximations.
///
/// # Panics
///
/// Panics if `assignment.len() != num_vars`, or if any variable index in
/// `constraints` is `>= num_vars`.
#[must_use]
pub fn xor_implications(
    constraints: &[XorConstraintInput],
    num_vars: usize,
    assignment: &[Option<bool>],
) -> XorImplication {
    assert_eq!(
        assignment.len(),
        num_vars,
        "assignment length {} must equal num_vars {num_vars}",
        assignment.len()
    );

    // Build the reason over-approximation by union-find over variables: any two
    // variables sharing a constraint are unioned, so the reason for an
    // implication/conflict is every *assigned* variable in the same connected
    // component as the implied/conflicting (free or empty-row) variable.
    let mut uf = UnionFind::new(num_vars);

    // Reduce every constraint: fold assigned values into the parity, keep the
    // free variables. Empty-with-true rows are immediate conflicts.
    let mut reduced: Vec<(Vec<usize>, bool)> = Vec::with_capacity(constraints.len());
    // For an empty (fully-assigned) conflicting row, remember its component
    // representative so we can gather the reason.
    let mut empty_conflict_rep: Option<usize> = None;

    for (vars, parity) in constraints {
        let mut folded_parity = *parity;
        let mut free: Vec<usize> = Vec::with_capacity(vars.len());
        for &v in vars {
            assert!(
                v < num_vars,
                "constraint variable index {v} out of range for num_vars {num_vars}"
            );
            match assignment[v] {
                Some(true) => folded_parity = !folded_parity,
                Some(false) => {}
                None => free.push(v),
            }
        }
        // Cancel duplicate free variables by parity (x ⊕ x = 0), matching
        // `Gf2System::add_constraint`'s folding. Sort then drop even runs.
        free.sort_unstable();
        let mut deduped: Vec<usize> = Vec::with_capacity(free.len());
        let mut i = 0;
        while i < free.len() {
            let mut count = 1;
            while i + count < free.len() && free[i + count] == free[i] {
                count += 1;
            }
            if count % 2 == 1 {
                deduped.push(free[i]);
            }
            i += count;
        }
        let free = deduped;

        // Union every variable in this *original* constraint so the reason
        // component captures all assigned participants, not just free ones.
        if let Some(&first) = vars.first() {
            for &v in &vars[1..] {
                uf.union(first, v);
            }
        }

        if free.is_empty() {
            if folded_parity {
                // 0 = 1 under the assignment: an immediate conflict. Record a
                // representative variable of this constraint for the reason.
                if empty_conflict_rep.is_none() {
                    empty_conflict_rep = vars.first().copied();
                }
            }
            // folded_parity == false ⇒ 0 = 0, trivially satisfied; drop it.
        } else {
            reduced.push((free, folded_parity));
        }
    }

    // Collect the assigned variables grouped by union-find component so reasons
    // can be assembled deterministically. `assigned[root]` is the sorted list
    // of (var, value) assigned variables in that component.
    let assigned_by_component = assigned_by_component(num_vars, assignment, &mut uf);

    // An empty-row conflict short-circuits: the reason is every assigned
    // variable in that constraint's component.
    if let Some(rep) = empty_conflict_rep {
        let reason = component_reason(&assigned_by_component, &mut uf, rep);
        return XorImplication::Conflict { reason };
    }

    // Feed the reduced free-variable constraints into a fresh GF(2) system and
    // solve. Unsat ⇒ conflict; otherwise the implied units are the forced
    // literals.
    let mut system = Gf2System::new(num_vars);
    for (free, parity) in &reduced {
        system.add_constraint(free, *parity);
    }

    match system.solve() {
        Gf2Outcome::Unsat => {
            // The reduced system is inconsistent. Its variables all live in one
            // or more components; gather the reason from every assigned variable
            // in the components touched by the reduced constraints.
            let mut reps: Vec<usize> = Vec::new();
            for (free, _) in &reduced {
                if let Some(&v) = free.first() {
                    reps.push(v);
                }
            }
            let reason = components_reason(&assigned_by_component, &mut uf, &reps);
            XorImplication::Conflict { reason }
        }
        Gf2Outcome::Sat(sol) => {
            let mut implied: Vec<XorImplied> = Vec::new();
            for &(var, value) in sol.implied_units() {
                // A guard the contract requires: the implied variable must have
                // been genuinely free in the input assignment.
                debug_assert!(
                    assignment[var].is_none(),
                    "implied variable {var} was already assigned"
                );
                if assignment[var].is_some() {
                    continue;
                }
                let reason = component_reason(&assigned_by_component, &mut uf, var);
                implied.push(XorImplied { var, value, reason });
            }
            // `implied_units` is already sorted by variable, but sort defensively
            // so the public contract holds regardless of upstream changes.
            implied.sort_by_key(|a| a.var);
            XorImplication::Implied { implied }
        }
    }
}

/// Builds, per union-find component root, the sorted list of assigned
/// `(var, value)` pairs in that component.
fn assigned_by_component(
    num_vars: usize,
    assignment: &[Option<bool>],
    uf: &mut UnionFind,
) -> Vec<Vec<(usize, bool)>> {
    let mut out: Vec<Vec<(usize, bool)>> = vec![Vec::new(); num_vars];
    for (v, slot) in assignment.iter().enumerate().take(num_vars) {
        if let Some(value) = *slot {
            let root = uf.find(v);
            out[root].push((v, value));
        }
    }
    // Each component bucket is already in ascending `v` order (we iterate `v`
    // ascending), so no per-bucket sort is needed.
    out
}

/// The reason for a single variable `var`: every assigned variable in `var`'s
/// component, sorted by variable index.
fn component_reason(
    assigned_by_component: &[Vec<(usize, bool)>],
    uf: &mut UnionFind,
    var: usize,
) -> Vec<(usize, bool)> {
    let root = uf.find(var);
    assigned_by_component[root].clone()
}

/// The reason for a set of variables: the deduplicated union of every assigned
/// variable across all of their components, sorted by variable index.
fn components_reason(
    assigned_by_component: &[Vec<(usize, bool)>],
    uf: &mut UnionFind,
    vars: &[usize],
) -> Vec<(usize, bool)> {
    let mut roots: Vec<usize> = vars.iter().map(|&v| uf.find(v)).collect();
    roots.sort_unstable();
    roots.dedup();
    let mut reason: Vec<(usize, bool)> = Vec::new();
    for &root in &roots {
        reason.extend_from_slice(&assigned_by_component[root]);
    }
    reason.sort_unstable_by_key(|&(v, _)| v);
    reason.dedup();
    reason
}

/// A minimal disjoint-set (union-find) over `0..n` with path compression and
/// union by size. Used only to group variables into connected components for
/// the reason over-approximation.
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
        // Path compression.
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
        // Union by size; on a tie attach the larger index under the smaller for
        // determinism (the chosen root never appears in output, so this only
        // affects internal tree shape).
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

    /// A constraint as a variable set plus its rhs parity bit.
    type Constraint = (Vec<usize>, bool);

    /// Evaluates one constraint under a *full* boolean assignment: the XOR of
    /// the listed variable values must equal `parity` (folding by parity so
    /// duplicates cancel, matching `add_constraint`).
    fn constraint_holds(vars: &[usize], parity: bool, full: &[bool]) -> bool {
        let mut acc = false;
        for &v in vars {
            acc ^= full[v];
        }
        acc == parity
    }

    fn all_constraints_hold(constraints: &[Constraint], full: &[bool]) -> bool {
        constraints
            .iter()
            .all(|(vars, parity)| constraint_holds(vars, *parity, full))
    }

    /// The free variables of an assignment, in ascending order.
    fn free_vars(assignment: &[Option<bool>]) -> Vec<usize> {
        assignment
            .iter()
            .enumerate()
            .filter_map(|(v, slot)| if slot.is_none() { Some(v) } else { None })
            .collect()
    }

    /// Brute-force every completion of the free variables of `assignment` and
    /// return the full boolean vectors that satisfy all `constraints`.
    fn satisfying_completions(
        constraints: &[Constraint],
        num_vars: usize,
        assignment: &[Option<bool>],
    ) -> Vec<Vec<bool>> {
        let free = free_vars(assignment);
        assert!(
            free.len() <= 20,
            "brute force only intended for small cases"
        );
        let mut out = Vec::new();
        for bits in 0u32..(1u32 << free.len()) {
            let mut full = vec![false; num_vars];
            for (v, slot) in assignment.iter().enumerate() {
                if let Some(value) = *slot {
                    full[v] = value;
                }
            }
            for (i, &v) in free.iter().enumerate() {
                full[v] = (bits >> i) & 1 == 1;
            }
            if all_constraints_hold(constraints, &full) {
                out.push(full);
            }
        }
        out
    }

    /// Whether *any* completion satisfies all constraints.
    fn has_satisfying_completion(
        constraints: &[Constraint],
        num_vars: usize,
        assignment: &[Option<bool>],
    ) -> bool {
        !satisfying_completions(constraints, num_vars, assignment).is_empty()
    }

    /// Builds an assignment from `(var, value)` fixes over `num_vars` vars.
    fn assign(num_vars: usize, fixes: &[(usize, bool)]) -> Vec<Option<bool>> {
        let mut a = vec![None; num_vars];
        for &(v, value) in fixes {
            a[v] = Some(value);
        }
        a
    }

    // --- Conflict soundness -------------------------------------------------

    /// Whenever `xor_implications` returns Conflict, brute force confirms NO
    /// completion satisfies all constraints.
    fn assert_conflict_is_sound(
        constraints: &[Constraint],
        num_vars: usize,
        assignment: &[Option<bool>],
    ) {
        match xor_implications(constraints, num_vars, assignment) {
            XorImplication::Conflict { reason } => {
                assert!(
                    !has_satisfying_completion(constraints, num_vars, assignment),
                    "Conflict reported but a satisfying completion exists"
                );
                assert_reason_well_formed(&reason, assignment);
                // Reason soundness: fixing ONLY the reason variables (others
                // free) already forces the conflict.
                let reason_only = assign(num_vars, &reason);
                assert!(
                    !has_satisfying_completion(constraints, num_vars, &reason_only),
                    "fixing only the reason {reason:?} does not force the conflict"
                );
            }
            XorImplication::Implied { .. } => panic!("expected Conflict"),
        }
    }

    /// A reason is a subset of the assignment (each (var,value) matches a fixed
    /// trail value) and is sorted ascending by variable, with no duplicates.
    fn assert_reason_well_formed(reason: &[(usize, bool)], assignment: &[Option<bool>]) {
        for &(v, value) in reason {
            assert_eq!(
                assignment[v],
                Some(value),
                "reason var {v}={value} not a matching assigned value"
            );
        }
        assert!(
            reason.windows(2).all(|w| w[0].0 < w[1].0),
            "reason not strictly ascending / has duplicates: {reason:?}"
        );
    }

    // --- Implication soundness + completeness --------------------------------

    /// Full check on an Implied result against brute force.
    fn assert_implied_matches_brute_force(
        constraints: &[Constraint],
        num_vars: usize,
        assignment: &[Option<bool>],
    ) {
        let completions = satisfying_completions(constraints, num_vars, assignment);
        // Implied is only returned when consistent.
        assert!(
            !completions.is_empty(),
            "Implied returned but no satisfying completion exists (missed conflict)"
        );

        let result = xor_implications(constraints, num_vars, assignment);
        let XorImplication::Implied { implied } = result else {
            panic!("expected Implied");
        };

        // Output sorted by variable, no duplicates.
        assert!(
            implied.windows(2).all(|w| w[0].var < w[1].var),
            "implied not strictly ascending by var: {implied:?}"
        );

        // Soundness: every implied literal holds in EVERY satisfying completion,
        // and the variable was genuinely free.
        for imp in &implied {
            assert!(
                assignment[imp.var].is_none(),
                "implied var {} was already assigned",
                imp.var
            );
            for full in &completions {
                assert_eq!(
                    full[imp.var], imp.value,
                    "implied {}={} violated by a satisfying completion",
                    imp.var, imp.value
                );
            }
            // Reason well-formed + sound: fixing only the reason forces it.
            assert_reason_well_formed(&imp.reason, assignment);
            let reason_only = assign(num_vars, &imp.reason);
            for full in satisfying_completions(constraints, num_vars, &reason_only) {
                assert_eq!(
                    full[imp.var], imp.value,
                    "fixing only reason {:?} fails to force {}={}",
                    imp.reason, imp.var, imp.value
                );
            }
        }

        // Completeness: every free variable forced to a single value across all
        // satisfying completions must appear in `implied`.
        let implied_vars: std::collections::BTreeSet<usize> =
            implied.iter().map(|i| i.var).collect();
        for &v in &free_vars(assignment) {
            let first = completions[0][v];
            let forced = completions.iter().all(|full| full[v] == first);
            if forced {
                assert!(
                    implied_vars.contains(&v),
                    "var {v} is forced to {first} in all completions but is not in implied"
                );
            }
        }
    }

    // --- Tests ---------------------------------------------------------------

    #[test]
    fn empty_constraints_no_implications() {
        let assignment = assign(3, &[(0, true)]);
        assert_eq!(
            xor_implications(&[], 3, &assignment),
            XorImplication::Implied { implied: vec![] }
        );
    }

    #[test]
    fn empty_assignment_cross_checks_gf2_solve() {
        // With an all-None assignment, `implied` must equal exactly the
        // `implied_units` that `Gf2System::solve` returns on the same system.
        let constraints: Vec<Constraint> = vec![(vec![0, 2], true), (vec![0], true)];
        let num_vars = 3;
        let assignment = vec![None; num_vars];

        let result = xor_implications(&constraints, num_vars, &assignment);
        let XorImplication::Implied { implied } = result else {
            panic!("expected Implied");
        };
        let got: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();

        let mut system = Gf2System::new(num_vars);
        for (vars, parity) in &constraints {
            system.add_constraint(vars, *parity);
        }
        let Gf2Outcome::Sat(sol) = system.solve() else {
            panic!("system should be SAT");
        };
        assert_eq!(got.as_slice(), sol.implied_units());

        // And it lines up with brute force too.
        assert_implied_matches_brute_force(&constraints, num_vars, &assignment);
    }

    #[test]
    fn empty_assignment_cross_check_multiple_systems() {
        let systems: Vec<(usize, Vec<Constraint>)> = vec![
            (4, vec![(vec![0, 1, 2, 3], false), (vec![0, 2], true)]),
            (5, vec![(vec![0, 1, 2], true), (vec![3, 4], false)]),
            (3, vec![(vec![2], true)]),
            (
                6,
                vec![
                    (vec![0, 1], true),
                    (vec![1, 2, 3], false),
                    (vec![4, 5], true),
                ],
            ),
        ];
        for (num_vars, constraints) in &systems {
            let assignment = vec![None; *num_vars];
            let XorImplication::Implied { implied } =
                xor_implications(constraints, *num_vars, &assignment)
            else {
                panic!("expected Implied for {constraints:?}");
            };
            let got: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();

            let mut system = Gf2System::new(*num_vars);
            for (vars, parity) in constraints {
                system.add_constraint(vars, *parity);
            }
            let Gf2Outcome::Sat(sol) = system.solve() else {
                panic!("system should be SAT");
            };
            assert_eq!(got.as_slice(), sol.implied_units(), "for {constraints:?}");
        }
    }

    #[test]
    fn width2_assigned_var_forces_partner() {
        // x0 ⊕ x1 = 1, x0 assigned true ⇒ x1 forced false.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let assignment = assign(2, &[(0, true)]);
        let XorImplication::Implied { implied } = xor_implications(&constraints, 2, &assignment)
        else {
            panic!("expected Implied");
        };
        assert_eq!(implied.len(), 1);
        assert_eq!(implied[0].var, 1);
        assert!(!implied[0].value);
        assert_eq!(implied[0].reason, vec![(0, true)]);
        assert_implied_matches_brute_force(&constraints, 2, &assignment);
    }

    #[test]
    fn width2_other_polarity() {
        // x0 ⊕ x1 = 1, x0 assigned false ⇒ x1 forced true.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let assignment = assign(2, &[(0, false)]);
        let XorImplication::Implied { implied } = xor_implications(&constraints, 2, &assignment)
        else {
            panic!("expected Implied");
        };
        assert_eq!(
            implied,
            vec![XorImplied {
                var: 1,
                value: true,
                reason: vec![(0, false)]
            }]
        );
        assert_implied_matches_brute_force(&constraints, 2, &assignment);
    }

    #[test]
    fn fully_assigned_consistent_no_implication_no_conflict() {
        // x0 ⊕ x1 = 1 with x0=true, x1=false ⇒ holds; nothing implied, no conflict.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let assignment = assign(2, &[(0, true), (1, false)]);
        assert_eq!(
            xor_implications(&constraints, 2, &assignment),
            XorImplication::Implied { implied: vec![] }
        );
    }

    #[test]
    fn fully_assigned_wrong_parity_is_conflict() {
        // x0 ⊕ x1 = 1 with x0=true, x1=true ⇒ parity 0 ≠ 1 ⇒ conflict.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true)];
        let assignment = assign(2, &[(0, true), (1, true)]);
        match xor_implications(&constraints, 2, &assignment) {
            XorImplication::Conflict { reason } => {
                assert_reason_well_formed(&reason, &assignment);
                // Reason must include both assigned vars of the violated row.
                assert!(reason.contains(&(0, true)));
                assert!(reason.contains(&(1, true)));
            }
            XorImplication::Implied { .. } => panic!("expected Conflict"),
        }
        assert_conflict_is_sound(&constraints, 2, &assignment);
    }

    #[test]
    fn reduced_system_conflict() {
        // x0 ⊕ x1 = 0, x1 ⊕ x2 = 0, x0 ⊕ x2 = 1 ⇒ jointly UNSAT even with no
        // assignment (free reduction is the whole system).
        let constraints: Vec<Constraint> =
            vec![(vec![0, 1], false), (vec![1, 2], false), (vec![0, 2], true)];
        let assignment = vec![None; 3];
        assert_conflict_is_sound(&constraints, 3, &assignment);
    }

    #[test]
    fn reduced_system_conflict_under_partial_assignment() {
        // x0 ⊕ x1 = 0 and x0 ⊕ x1 ⊕ x2 = 0 and x2 = 1 (as a 1-var... no, gates
        // are width≥2). Use: x0 ⊕ x1 = 0, x1 ⊕ x2 = 1, x0 ⊕ x2 = 0.
        // Sum: 0 ⊕ 1 ⊕ 0 = 1 on rhs ⇒ UNSAT. Assign x0 to exercise reduction.
        let constraints: Vec<Constraint> =
            vec![(vec![0, 1], false), (vec![1, 2], true), (vec![0, 2], false)];
        for &val in &[false, true] {
            let assignment = assign(3, &[(0, val)]);
            assert_conflict_is_sound(&constraints, 3, &assignment);
        }
    }

    #[test]
    fn chained_implications() {
        // x0 ⊕ x1 = 1, x1 ⊕ x2 = 0, x0 assigned true.
        // ⇒ x1 = false (from c0), x2 = false (from c1). Both implied.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true), (vec![1, 2], false)];
        let assignment = assign(3, &[(0, true)]);
        let XorImplication::Implied { implied } = xor_implications(&constraints, 3, &assignment)
        else {
            panic!("expected Implied");
        };
        let pairs: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();
        assert_eq!(pairs, vec![(1, false), (2, false)]);
        assert_implied_matches_brute_force(&constraints, 3, &assignment);
    }

    #[test]
    fn duplicate_vars_in_constraint_cancel() {
        // x0 ⊕ x0 ⊕ x1 = 1 reduces to x1 = 1. With empty assignment, x1 forced.
        let constraints: Vec<Constraint> = vec![(vec![0, 0, 1], true)];
        let assignment = vec![None; 2];
        let XorImplication::Implied { implied } = xor_implications(&constraints, 2, &assignment)
        else {
            panic!("expected Implied");
        };
        assert_eq!(implied.len(), 1);
        assert_eq!((implied[0].var, implied[0].value), (1, true));
        assert_implied_matches_brute_force(&constraints, 2, &assignment);
    }

    #[test]
    fn assigned_var_cancels_to_trivial_row() {
        // x0 ⊕ x1 = 0 with both assigned equal ⇒ trivially satisfied, no output.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], false)];
        let assignment = assign(2, &[(0, true), (1, true)]);
        assert_eq!(
            xor_implications(&constraints, 2, &assignment),
            XorImplication::Implied { implied: vec![] }
        );
    }

    #[test]
    fn exhaustive_small_systems_brute_force() {
        // Enumerate a handful of fixed small systems crossed with every partial
        // assignment over their variables, and check every result against brute
        // force (conflict soundness, implication soundness + completeness).
        let systems: Vec<(usize, Vec<Constraint>)> = vec![
            (3, vec![(vec![0, 1], true), (vec![1, 2], false)]),
            (3, vec![(vec![0, 1, 2], true)]),
            (
                3,
                vec![(vec![0, 1], false), (vec![1, 2], false), (vec![0, 2], true)],
            ),
            (
                4,
                vec![(vec![0, 1], true), (vec![2, 3], false), (vec![0, 2], true)],
            ),
            (4, vec![(vec![0, 1, 2, 3], false), (vec![0, 1], true)]),
        ];
        for (num_vars, constraints) in &systems {
            // Every partial assignment: each var is None/Some(false)/Some(true).
            let n = *num_vars;
            let total = 3usize.pow(u32::try_from(n).expect("small n"));
            for code in 0..total {
                let mut assignment = vec![None; n];
                let mut c = code;
                for slot in &mut assignment {
                    *slot = match c % 3 {
                        0 => None,
                        1 => Some(false),
                        _ => Some(true),
                    };
                    c /= 3;
                }
                match xor_implications(constraints, n, &assignment) {
                    XorImplication::Conflict { .. } => {
                        assert_conflict_is_sound(constraints, n, &assignment);
                    }
                    XorImplication::Implied { .. } => {
                        assert_implied_matches_brute_force(constraints, n, &assignment);
                    }
                }
            }
        }
    }

    #[test]
    fn determinism_repeated_calls() {
        let constraints: Vec<Constraint> =
            vec![(vec![3, 4], true), (vec![0, 1], false), (vec![1, 2], true)];
        let assignment = assign(5, &[(0, true)]);
        let first = xor_implications(&constraints, 5, &assignment);
        for _ in 0..5 {
            assert_eq!(xor_implications(&constraints, 5, &assignment), first);
        }
    }

    #[test]
    fn reason_is_component_local_not_global() {
        // Two independent gates: x0 ⊕ x1 = 1 (assign x0) and x2 ⊕ x3 = 1
        // (assign x2). The reason for the x1 implication must NOT include x2,
        // since x2 is in a different connected component.
        let constraints: Vec<Constraint> = vec![(vec![0, 1], true), (vec![2, 3], true)];
        let assignment = assign(4, &[(0, true), (2, false)]);
        let XorImplication::Implied { implied } = xor_implications(&constraints, 4, &assignment)
        else {
            panic!("expected Implied");
        };
        let imp1 = implied.iter().find(|i| i.var == 1).expect("x1 implied");
        assert_eq!(
            imp1.reason,
            vec![(0, true)],
            "reason must be component-local"
        );
        let imp3 = implied.iter().find(|i| i.var == 3).expect("x3 implied");
        assert_eq!(
            imp3.reason,
            vec![(2, false)],
            "reason must be component-local"
        );
        assert_implied_matches_brute_force(&constraints, 4, &assignment);
    }

    #[test]
    fn cross_word_variable_range() {
        // Exercise variable indices above 63 to mirror gf2's multi-word path.
        let constraints: Vec<Constraint> = vec![(vec![0, 64], true), (vec![64, 100], false)];
        let mut assignment = vec![None; 128];
        assignment[0] = Some(false);
        let XorImplication::Implied { implied } = xor_implications(&constraints, 128, &assignment)
        else {
            panic!("expected Implied");
        };
        // x0=false, x0⊕x64=1 ⇒ x64=true; x64⊕x100=0 ⇒ x100=true.
        let pairs: Vec<(usize, bool)> = implied.iter().map(|i| (i.var, i.value)).collect();
        assert_eq!(pairs, vec![(64, true), (100, true)]);
    }

    #[test]
    fn constraints_from_pairs_round_trips() {
        let pairs = vec![(vec![0, 1], true), (vec![2], false)];
        assert_eq!(constraints_from_pairs(&pairs), pairs);
    }

    #[test]
    #[should_panic(expected = "assignment length")]
    fn wrong_assignment_length_panics() {
        let _ = xor_implications(&[(vec![0, 1], true)], 3, &[None, None]);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn out_of_range_variable_panics() {
        let _ = xor_implications(&[(vec![0, 5], true)], 3, &[None, None, None]);
    }
}
