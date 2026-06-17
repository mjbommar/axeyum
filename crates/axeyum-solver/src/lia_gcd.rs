//! GCD divisibility test for linear integer equations (Track 2, P2.4 — the first
//! "cut portfolio" rung).
//!
//! A linear Diophantine equation `Σ aᵢ·xᵢ = b` has an integer solution **iff**
//! `gcd(a₁,…,aₙ)` divides `b`. So a top-level integer equation whose coefficient
//! gcd does not divide its constant is *unsatisfiable* — a sound refutation the
//! rational simplex misses (its LP relaxation is feasible) and that
//! branch-and-bound may not even terminate on when the variables are unbounded
//! (e.g. `2x + 4y = 3`). [`prove_lia_unsat_by_gcd`] checks each top-level equation
//! and reports `unsat` on the first divisibility-infeasible one.
//!
//! **Sound, incomplete:** a positive result is a genuine refutation (a single
//! unsatisfiable conjunct makes the conjunction unsatisfiable); it is silent
//! otherwise (the equation may still be unsatisfiable for other reasons — left to
//! the simplex/branch-and-bound).
//!
//! # System-level Diophantine refutation
//!
//! [`prove_lia_unsat_by_diophantine`] strictly generalizes the single-equation
//! test to a *system* of linear integer equalities `A x = b`. A system has an
//! integer solution **iff** integer (fraction-free, GCD-based) row reduction of
//! `[A | b]` never derives an all-zero coefficient row with a nonzero right-hand
//! side, and no surviving row `Σ gᵢ·xᵢ = c` has `gcd(gᵢ) ∤ c`. We reduce with
//! only integer-preserving row operations (computing a Hermite-style echelon
//! form), so any contradiction row we derive is an exact integer consequence of
//! the original equalities — a genuine integer infeasibility. This catches
//! systems the per-equation GCD test misses, e.g. `x + y = 1 ∧ x + y = 2`
//! (combine → `0 = 1`). It subsumes the single-equation case (one equation is a
//! one-row system) and is dispatched in its place.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// Tries to prove `assertions` `unsat` by the GCD test on a top-level integer
/// equation. Returns `true` only on a divisibility-infeasible equation (a sound
/// refutation); `false` otherwise.
#[must_use]
pub fn prove_lia_unsat_by_gcd(arena: &TermArena, assertions: &[TermId]) -> bool {
    for &assertion in assertions {
        if let TermNode::App { op: Op::Eq, args } = arena.node(assertion) {
            if args.len() == 2
                && arena.sort_of(args[0]) == Sort::Int
                && equation_is_infeasible(arena, args[0], args[1])
            {
                return true;
            }
        }
    }
    false
}

/// Tries to prove `assertions` `unsat` by integer (fraction-free) row reduction of
/// the *system* of top-level integer equalities. Returns `true` only when the
/// equality subsystem is integer-infeasible — a derived contradiction row `0 = c`
/// with `c ≠ 0`, or a surviving row `Σ gᵢ·xᵢ = c` with `gcd(gᵢ) ∤ c` (a sound
/// refutation); `false` otherwise.
///
/// This strictly generalizes [`prove_lia_unsat_by_gcd`]: a single equation is a
/// one-row system, and the per-row GCD check reproduces the divisibility test.
/// Inequalities and non-linear / non-integer-equality assertions are ignored —
/// running the test on the equality subset alone is sound (UNSAT of a subset of
/// the conjuncts implies UNSAT of the whole). On any `i128` overflow during the
/// elimination, the test bails out (`false`); it never wraps, panics, or reports a
/// spurious `unsat`.
#[must_use]
pub fn prove_lia_unsat_by_diophantine(arena: &TermArena, assertions: &[TermId]) -> bool {
    // Collect the linear form of every top-level integer equality, normalized to
    // `Σ coeffs·x = rhs` (constants moved to the right). Non-equalities,
    // non-integer, and non-linear assertions are skipped.
    // Two indexings: `pending` holds the eligible integer equalities (term sides);
    // `m` is their count so each row's provenance vector has the right length.
    let pending: Vec<(TermId, TermId)> = assertions
        .iter()
        .filter_map(|&assertion| match arena.node(assertion) {
            TermNode::App { op: Op::Eq, args }
                if args.len() == 2 && arena.sort_of(args[0]) == Sort::Int =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        })
        .collect();
    let m = pending.len();
    let mut rows: Vec<Row> = Vec::new();
    for (idx, &(a, b)) in pending.iter().enumerate() {
        if let Some(row) = equality_row(arena, a, b, idx, m) {
            rows.push(row);
        }
    }
    system_is_infeasible(rows).is_some()
}

/// Like [`prove_lia_unsat_by_diophantine`], but on a genuine refutation returns an
/// **independently-checkable** [`DiophantineCertificate`] — an integer Farkas
/// combination of the original equalities — paired with those original
/// [`Equality`]s. Returns `None` when the system is not refuted, on `i128`
/// overflow during the elimination, or (defensively) if the constructed
/// certificate does not pass [`check_diophantine_certificate`].
///
/// The certificate is emitted **only when its own independent checker accepts it**
/// (mirroring the self-validating Alethe emitters): a construction bug yields no
/// certificate, never a wrong proof.
///
/// # Panics
///
/// Never panics; all arithmetic is `checked_*` and overflow yields `None`.
#[must_use]
pub fn prove_lia_unsat_by_diophantine_certified(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<(Vec<Equality>, DiophantineCertificate)> {
    let pending: Vec<(TermId, TermId)> = assertions
        .iter()
        .filter_map(|&assertion| match arena.node(assertion) {
            TermNode::App { op: Op::Eq, args }
                if args.len() == 2 && arena.sort_of(args[0]) == Sort::Int =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        })
        .collect();
    let m = pending.len();

    // Self-contained originals (for the checker) and provenance-carrying rows (for
    // the elimination) are built from the same normalization. We only proceed when
    // *every* pending equality normalizes, so the certificate's multiplier indices
    // line up one-to-one with `equalities`.
    let mut equalities: Vec<Equality> = Vec::with_capacity(m);
    let mut rows: Vec<Row> = Vec::with_capacity(m);
    for (idx, &(a, b)) in pending.iter().enumerate() {
        let eq = equality_of(arena, a, b)?;
        let row = equality_row(arena, a, b, idx, m)?;
        equalities.push(eq);
        rows.push(row);
    }

    let contradiction = system_is_infeasible(rows)?;
    debug_assert_eq!(contradiction.combo.len(), m);

    let mut combined: Vec<(SymbolId, i128)> =
        contradiction.coeffs.iter().map(|(&s, &c)| (s, c)).collect();
    combined.sort_by_key(|&(s, _)| s); // BTreeMap already sorted; explicit for clarity.
    let cert = DiophantineCertificate {
        multipliers: contradiction.combo,
        combined,
        constant: contradiction.rhs,
    };

    // Self-validate: only bless a certificate the independent checker accepts.
    if check_diophantine_certificate(&equalities, &cert) {
        Some((equalities, cert))
    } else {
        None
    }
}

/// Independently validates a [`DiophantineCertificate`] against the `equalities`
/// it refers to. Re-derives the integer combination `Σ_i multipliers[i]·E_i` from
/// the originals, checks it equals the stated `combined`/`constant` row, and checks
/// `gcd(combined coeffs) ∤ constant` (with `gcd(∅) = 0`, so `0 = d` is infeasible
/// iff `d ≠ 0`). Returns `true` only when all checks pass.
///
/// This shares no code path with the elimination that produced the certificate: it
/// is a self-contained proof of integer infeasibility. Arithmetic is exact `i128`
/// and `checked_*`; any overflow or mismatch conservatively returns `false`.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn check_diophantine_certificate(
    equalities: &[Equality],
    cert: &DiophantineCertificate,
) -> bool {
    // One multiplier per equality.
    if cert.multipliers.len() != equalities.len() {
        return false;
    }
    // Re-derive `Σ_i λ_i · E_i` from the originals using checked arithmetic.
    let mut coeffs: BTreeMap<SymbolId, i128> = BTreeMap::new();
    let mut rhs: i128 = 0;
    for (eq, &lambda) in equalities.iter().zip(&cert.multipliers) {
        for (&sym, &c) in &eq.coeffs {
            let Some(term) = c.checked_mul(lambda) else {
                return false;
            };
            let entry = coeffs.entry(sym).or_insert(0);
            let Some(v) = entry.checked_add(term) else {
                return false;
            };
            *entry = v;
        }
        let Some(term) = eq.rhs.checked_mul(lambda) else {
            return false;
        };
        let Some(v) = rhs.checked_add(term) else {
            return false;
        };
        rhs = v;
    }
    coeffs.retain(|_, c| *c != 0);

    // The re-derived combination must match the stated `combined`/`constant` row.
    if rhs != cert.constant {
        return false;
    }
    let stated: BTreeMap<SymbolId, i128> = cert.combined.iter().copied().collect();
    // Reject duplicate or zero entries in `combined` (a tampered/malformed row).
    if stated.len() != cert.combined.len() || cert.combined.iter().any(|&(_, c)| c == 0) {
        return false;
    }
    if stated != coeffs {
        return false;
    }

    // Integer infeasibility: gcd(combined coeffs) ∤ constant (gcd(∅) = 0; 0 ∤ d ⇔ d ≠ 0).
    let mut g: i128 = 0;
    for &(_, c) in &cert.combined {
        g = gcd(g, c);
    }
    if g == 0 {
        return cert.constant != 0;
    }
    cert.constant % g != 0
}

/// A normalized integer equality `Σ coeffs·xᵢ = rhs` (constant moved to the
/// right). The coefficient map omits zero entries; an empty map is a constant row
/// `0 = rhs`. This is the public, self-contained form the certificate refers to,
/// so the independent checker can re-derive without trusting the term IR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Equality {
    /// Coefficients keyed by symbol, sorted (a `BTreeMap`), zero entries omitted.
    pub coeffs: BTreeMap<SymbolId, i128>,
    /// Right-hand side constant.
    pub rhs: i128,
}

/// An independently-checkable "integer Farkas" refutation of a system of integer
/// equalities `E_i: Σ_j a_{ij}·x_j = c_i`.
///
/// It certifies that the integer combination `Σ_i multipliers[i]·E_i` is the row
/// `Σ_j combined_j·x_j = constant`, which is integer-infeasible because
/// `gcd(combined coeffs) ∤ constant` (with `gcd(∅) = 0`, and `0 ∤ d` iff
/// `d ≠ 0` — the all-zero `0 = d≠0` case). Validating it ([`check_diophantine_certificate`])
/// re-derives the combination from the *original* equalities and shares no code
/// with the elimination that produced it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiophantineCertificate {
    /// One integer multiplier `λ_i` per input equality (same order as `equalities`).
    pub multipliers: Vec<i128>,
    /// The combined row's coefficients, sorted by [`SymbolId`], zero entries omitted.
    pub combined: Vec<(SymbolId, i128)>,
    /// The combined row's right-hand side constant `d`.
    pub constant: i128,
}

/// A normalized equality [`Row`] carrying its provenance: the integer combination
/// `Σ combo_i·E_i` of the *original* equalities (by index) that produced it.
struct Row {
    coeffs: BTreeMap<SymbolId, i128>,
    rhs: i128,
    /// `combo[i]` is the multiplier `λ_i` of original equality `i`. Initialized to
    /// the unit vector `eᵢ` for input row `i`; every integer row op updates it
    /// identically to the coefficient/rhs update.
    combo: Vec<i128>,
}

/// Builds the normalized [`Row`] for the integer equality `a = b`, or `None` if
/// either side is non-linear or an `i128` overflow occurs while normalizing. The
/// row's provenance `combo` is the unit vector `eᵢ` of length `m` selecting
/// equality `idx` among the `m` originals.
fn equality_row(arena: &TermArena, a: TermId, b: TermId, idx: usize, m: usize) -> Option<Row> {
    let (mut coeffs, ka) = int_linear(arena, a)?;
    let (cb, kb) = int_linear(arena, b)?;
    // Move `b` to the left: `Σ (ca-cb)·x = -(ka-kb)`, then flip to RHS form below.
    for (sym, c) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        *entry = entry.checked_sub(c)?;
    }
    coeffs.retain(|_, c| *c != 0);
    // `Σ coeffs·x = -(ka - kb) = kb - ka`.
    let rhs = kb.checked_sub(ka)?;
    let mut combo = vec![0i128; m];
    combo[idx] = 1;
    Some(Row { coeffs, rhs, combo })
}

/// The public, self-contained [`Equality`] for the integer equality `a = b`, or
/// `None` if either side is non-linear or an `i128` overflow occurs. Same
/// normalization as [`equality_row`] but without provenance — this is what the
/// certificate's `equalities` and the checker re-derive against.
fn equality_of(arena: &TermArena, a: TermId, b: TermId) -> Option<Equality> {
    let (mut coeffs, ka) = int_linear(arena, a)?;
    let (cb, kb) = int_linear(arena, b)?;
    for (sym, c) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        *entry = entry.checked_sub(c)?;
    }
    coeffs.retain(|_, c| *c != 0);
    let rhs = kb.checked_sub(ka)?;
    Some(Equality { coeffs, rhs })
}

/// Decides whether a system of integer equality [`Row`]s is integer-infeasible by
/// fraction-free GCD-based row reduction. Returns `Some(contradiction_row)` — a
/// genuine integer-infeasible row carrying its provenance `combo` — on a
/// refutation; `None` on satisfiability-undetermined or `i128` overflow.
fn system_is_infeasible(mut rows: Vec<Row>) -> Option<Row> {
    // An empty system is trivially feasible.
    if rows.is_empty() {
        return None;
    }
    // Per-row check first: a single row already infeasible (constant row `0 = c`
    // with `c ≠ 0`, or `gcd(coeffs) ∤ rhs`) refutes the whole system. This also
    // exactly reproduces the single-equation GCD test, so no regression.
    if let Some(i) = rows.iter().position(row_is_infeasible) {
        return Some(rows.swap_remove(i));
    }

    // Deterministic pivot order: columns are symbol ids in ascending order. A
    // `BTreeSet` gives sorted, de-duplicated symbols so the elimination order is
    // stable (no hash-map iteration in the result).
    let columns: Vec<SymbolId> = rows
        .iter()
        .flat_map(|r| r.coeffs.keys().copied())
        .collect::<BTreeSet<SymbolId>>()
        .into_iter()
        .collect();

    // Fraction-free Gaussian / Hermite-style elimination. For each pivot column,
    // pick a pivot row (one with the smallest nonzero |coeff| in that column,
    // among rows not yet used as a pivot), then integer-eliminate that column from
    // every other unpivoted row using cross-multiplication by the gcd's cofactors.
    let mut pivoted = vec![false; rows.len()];
    for &col in &columns {
        // Find an unpivoted row with a nonzero entry in this column, preferring the
        // smallest magnitude to keep coefficients small (deterministic by index on
        // ties).
        let mut pivot: Option<usize> = None;
        for (i, used) in pivoted.iter().enumerate() {
            if *used {
                continue;
            }
            match rows[i].coeffs.get(&col).copied() {
                Some(c) if c != 0 => {
                    let better = match pivot {
                        None => true,
                        Some(p) => {
                            c.unsigned_abs()
                                < rows[p]
                                    .coeffs
                                    .get(&col)
                                    .copied()
                                    .unwrap_or(0)
                                    .unsigned_abs()
                        }
                    };
                    if better {
                        pivot = Some(i);
                    }
                }
                _ => {}
            }
        }
        let Some(p) = pivot else {
            continue; // no row carries this column among the unpivoted rows.
        };
        pivoted[p] = true;
        let pc = rows[p].coeffs[&col];

        // Eliminate `col` from every other unpivoted row.
        for i in 0..rows.len() {
            if i == p || pivoted[i] {
                continue;
            }
            let Some(ic) = rows[i].coeffs.get(&col).copied() else {
                continue;
            };
            if ic == 0 {
                continue;
            }
            // Row_i := (pc/g)·Row_i − (ic/g)·Row_p, with g = gcd(pc, ic). This is an
            // integer-preserving combination that zeroes `col` in Row_i. All ops are
            // checked; on overflow we abandon the proof attempt.
            let g = gcd(pc, ic);
            let (Some(fi), Some(fp)) = (pc.checked_div(g), ic.checked_div(g)) else {
                return None;
            };
            if !row_axpy(&mut rows, i, p, fi, fp) {
                return None; // overflow during combination → not refuted.
            }
            // The combined row may now be a contradiction; check eagerly.
            if row_is_infeasible(&rows[i]) {
                return Some(rows.swap_remove(i));
            }
        }
    }

    // Final sweep: any surviving row that is now a contradiction.
    rows.into_iter().find(row_is_infeasible)
}

/// In place: `Row_i := fi·Row_i − fp·Row_p`. Returns `false` on any `i128`
/// overflow (the caller then abandons the proof attempt). After the update,
/// zero coefficients are pruned so emptiness means a constant row.
fn row_axpy(rows: &mut [Row], i: usize, p: usize, fi: i128, fp: i128) -> bool {
    // Gather the pivot row's data first (immutable borrow released before mutating).
    let pivot_coeffs: Vec<(SymbolId, i128)> =
        rows[p].coeffs.iter().map(|(&s, &c)| (s, c)).collect();
    let pivot_rhs = rows[p].rhs;
    let pivot_combo: Vec<i128> = rows[p].combo.clone();

    // Scale row i by fi (coeffs, rhs, and the provenance vector identically).
    {
        let row = &mut rows[i];
        for c in row.coeffs.values_mut() {
            let Some(v) = c.checked_mul(fi) else {
                return false;
            };
            *c = v;
        }
        let Some(v) = row.rhs.checked_mul(fi) else {
            return false;
        };
        row.rhs = v;
        for l in &mut row.combo {
            let Some(v) = l.checked_mul(fi) else {
                return false;
            };
            *l = v;
        }
    }

    // Subtract fp·pivot.
    for (sym, pc) in pivot_coeffs {
        let Some(term) = pc.checked_mul(fp) else {
            return false;
        };
        let row = &mut rows[i];
        let entry = row.coeffs.entry(sym).or_insert(0);
        let Some(v) = entry.checked_sub(term) else {
            return false;
        };
        *entry = v;
    }
    {
        let Some(term) = pivot_rhs.checked_mul(fp) else {
            return false;
        };
        let Some(v) = rows[i].rhs.checked_sub(term) else {
            return false;
        };
        rows[i].rhs = v;
    }
    // Provenance: combo_i := fi·combo_i − fp·combo_p (the fi scale was applied above).
    for (idx, &pl) in pivot_combo.iter().enumerate() {
        let Some(term) = pl.checked_mul(fp) else {
            return false;
        };
        let Some(v) = rows[i].combo[idx].checked_sub(term) else {
            return false;
        };
        rows[i].combo[idx] = v;
    }

    rows[i].coeffs.retain(|_, c| *c != 0);
    true
}

/// Whether a single normalized row `Σ gᵢ·xᵢ = rhs` is integer-infeasible: either a
/// constant row `0 = rhs` with `rhs ≠ 0`, or `gcd(gᵢ) ∤ rhs`.
fn row_is_infeasible(row: &Row) -> bool {
    let mut g: i128 = 0;
    for &c in row.coeffs.values() {
        g = gcd(g, c);
    }
    if g == 0 {
        // No variables: `0 = rhs`, unsat iff nonzero.
        return row.rhs != 0;
    }
    row.rhs % g != 0
}

/// Whether the integer equation `a = b` has no integer solution by the GCD test.
fn equation_is_infeasible(arena: &TermArena, a: TermId, b: TermId) -> bool {
    let (Some((mut coeffs, ka)), Some((cb, kb))) = (int_linear(arena, a), int_linear(arena, b))
    else {
        return false; // non-linear (var·var, div/mod, …): not our test
    };
    // Move `b` to the left: `Σ (ca-cb)·x = -(ka-kb)`.
    for (sym, c) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        let Some(v) = entry.checked_sub(c) else {
            return false;
        };
        *entry = v;
    }
    let Some(constant) = ka.checked_sub(kb) else {
        return false;
    };
    coeffs.retain(|_, c| *c != 0);

    let mut g: i128 = 0;
    for &c in coeffs.values() {
        g = gcd(g, c);
    }
    if g == 0 {
        // No variables remain: the equation is `constant = 0`, unsat iff non-zero.
        return constant != 0;
    }
    // `Σ coeffs·x = -constant` has an integer solution iff `g | constant`.
    constant % g != 0
}

/// Greatest common divisor of two (possibly negative) integers, as a positive
/// `i128`. `gcd(0, x) = |x|`.
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    i128::try_from(a).unwrap_or(i128::MAX)
}

/// The linear form of an integer term — a coefficient per symbol plus a constant —
/// or `None` if the term is non-linear (`var·var`, `div`/`mod`, an unsupported
/// operator) or an `i128` overflow occurs.
fn int_linear(arena: &TermArena, t: TermId) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    match arena.node(t) {
        TermNode::IntConst(n) => Some((BTreeMap::new(), *n)),
        TermNode::Symbol(s) => Some((BTreeMap::from([(*s, 1)]), 0)),
        TermNode::App { op, args } => match (op, &args[..]) {
            (Op::IntNeg, [x]) => scale(int_linear(arena, *x)?, -1),
            (Op::IntAdd, [x, y]) => combine(int_linear(arena, *x)?, int_linear(arena, *y)?, false),
            (Op::IntSub, [x, y]) => combine(int_linear(arena, *x)?, int_linear(arena, *y)?, true),
            (Op::IntMul, [x, y]) => {
                // Linear only if one factor is a (variable-free) constant.
                let (lx, ly) = (int_linear(arena, *x)?, int_linear(arena, *y)?);
                if lx.0.is_empty() {
                    scale(ly, lx.1)
                } else if ly.0.is_empty() {
                    scale(lx, ly.1)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// `a ± b` over linear forms (`sub` selects subtraction).
fn combine(
    a: (BTreeMap<SymbolId, i128>, i128),
    b: (BTreeMap<SymbolId, i128>, i128),
    sub: bool,
) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    let (mut coeffs, ka) = a;
    let (cb, kb) = b;
    for (sym, v) in cb {
        let entry = coeffs.entry(sym).or_insert(0);
        *entry = if sub {
            entry.checked_sub(v)?
        } else {
            entry.checked_add(v)?
        };
    }
    let k = if sub {
        ka.checked_sub(kb)?
    } else {
        ka.checked_add(kb)?
    };
    Some((coeffs, k))
}

/// `factor · l` over a linear form.
fn scale(
    l: (BTreeMap<SymbolId, i128>, i128),
    factor: i128,
) -> Option<(BTreeMap<SymbolId, i128>, i128)> {
    let (coeffs, k) = l;
    let mut out = BTreeMap::new();
    for (sym, v) in coeffs {
        out.insert(sym, v.checked_mul(factor)?);
    }
    Some((out, k.checked_mul(factor)?))
}

#[cfg(test)]
mod tests {
    use super::{
        DiophantineCertificate, check_diophantine_certificate, prove_lia_unsat_by_diophantine,
        prove_lia_unsat_by_diophantine_certified, prove_lia_unsat_by_gcd,
    };
    use axeyum_ir::{TermArena, TermId};

    fn ivar(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
        arena.int_var(name).unwrap()
    }

    /// `coeff·var` helper.
    fn term(arena: &mut TermArena, coeff: i128, var: TermId) -> TermId {
        let c = arena.int_const(coeff);
        arena.int_mul(c, var).unwrap()
    }

    #[test]
    fn even_combination_equal_to_odd_is_unsat() {
        // 2x + 4y = 3 : gcd(2,4)=2 ∤ 3 ⇒ UNSAT (unbounded — the simplex/B&B miss it).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let two = arena.int_const(2);
        let four = arena.int_const(4);
        let three = arena.int_const(3);
        let tx = arena.int_mul(two, x).unwrap();
        let fy = arena.int_mul(four, y).unwrap();
        let lhs = arena.int_add(tx, fy).unwrap();
        let eq = arena.eq(lhs, three).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn coprime_combination_is_not_refuted() {
        // 2x + 3y = 1 : gcd(2,3)=1 | 1 ⇒ has a solution, not refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let two = arena.int_const(2);
        let three = arena.int_const(3);
        let one = arena.int_const(1);
        let tx = arena.int_mul(two, x).unwrap();
        let ty = arena.int_mul(three, y).unwrap();
        let lhs = arena.int_add(tx, ty).unwrap();
        let eq = arena.eq(lhs, one).unwrap();
        assert!(!prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn single_coefficient_nondivisor_is_unsat() {
        // 2x = 5 ⇒ UNSAT.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let two = arena.int_const(2);
        let five = arena.int_const(5);
        let tx = arena.int_mul(two, x).unwrap();
        let eq = arena.eq(tx, five).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    #[test]
    fn inequality_is_not_an_equation() {
        // x ≤ 3 is not an equation — the GCD test does not apply.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = arena.int_const(3);
        let le = arena.int_le(x, three).unwrap();
        assert!(!prove_lia_unsat_by_gcd(&arena, &[le]));
    }

    #[test]
    fn rhs_with_variable_is_handled() {
        // 3x = 2y + 1 ⇒ 3x - 2y = 1 : gcd(3,2)=1 | 1 ⇒ has a solution, not refuted.
        // 3x = 3y + 1 ⇒ 3x - 3y = 1 : gcd(3,3)=3 ∤ 1 ⇒ UNSAT.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let three = arena.int_const(3);
        let one = arena.int_const(1);
        let tx = arena.int_mul(three, x).unwrap();
        let ty = arena.int_mul(three, y).unwrap();
        let rhs = arena.int_add(ty, one).unwrap();
        let eq = arena.eq(tx, rhs).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
    }

    // ----------------------------------------------------------------------
    // System-level Diophantine refutation (`prove_lia_unsat_by_diophantine`).
    // ----------------------------------------------------------------------

    /// `x + y = a`.
    fn eq_xy(arena: &mut TermArena, x: TermId, y: TermId, a: i128) -> TermId {
        let sum = arena.int_add(x, y).unwrap();
        let c = arena.int_const(a);
        arena.eq(sum, c).unwrap()
    }

    #[test]
    fn diophantine_subsumes_single_equation_gcd() {
        // Every single-equation case the GCD test refutes is still refuted.
        // 2x + 4y = 3.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let tx = term(&mut arena, 2, x);
        let fy = term(&mut arena, 4, y);
        let lhs = arena.int_add(tx, fy).unwrap();
        let three = arena.int_const(3);
        let eq = arena.eq(lhs, three).unwrap();
        assert!(prove_lia_unsat_by_gcd(&arena, &[eq]));
        assert!(prove_lia_unsat_by_diophantine(&arena, &[eq]));
    }

    #[test]
    fn two_equations_combine_to_zero_equals_one() {
        // x + y = 1 ∧ x + y = 2 ⇒ subtract ⇒ 0 = 1 ⇒ UNSAT. The per-equation GCD
        // test cannot see this (each equation alone is feasible).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let e1 = eq_xy(&mut arena, x, y, 1);
        let e2 = eq_xy(&mut arena, x, y, 2);
        assert!(!prove_lia_unsat_by_gcd(&arena, &[e1, e2]));
        assert!(prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn three_variable_system_contradiction() {
        // x + y + z = 1 ∧ x + y + z = 2 ⇒ 0 = 1 ⇒ UNSAT.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let z = ivar(&mut arena, "z");
        let xy = arena.int_add(x, y).unwrap();
        let xyz = arena.int_add(xy, z).unwrap();
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let e1 = arena.eq(xyz, one).unwrap();
        let e2 = arena.eq(xyz, two).unwrap();
        assert!(!prove_lia_unsat_by_gcd(&arena, &[e1, e2]));
        assert!(prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn scaled_rows_contradiction() {
        // 2x + 2y = 2 ∧ 2x + 2y = 3. The second alone is already gcd-infeasible
        // (gcd(2,2)=2 ∤ 3), but even ignoring that, the pair combines to 0 = 2.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let mk = |arena: &mut TermArena, rhs: i128| {
            let tx = term(arena, 2, x);
            let ty = term(arena, 2, y);
            let lhs = arena.int_add(tx, ty).unwrap();
            let c = arena.int_const(rhs);
            arena.eq(lhs, c).unwrap()
        };
        let e1 = mk(&mut arena, 2);
        let e2 = mk(&mut arena, 3);
        assert!(prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn each_equation_passes_gcd_but_system_infeasible() {
        // The real win: every equation individually passes its own GCD test, yet the
        // system is integer-infeasible.
        //   (1)  x + y = 0          gcd(1,1)=1 | 0  ✓ feasible alone
        //   (2)  x - y = 0          gcd(1,1)=1 | 0  ✓ feasible alone  ⇒ x = y
        //   (3)  2x + 2y = 1        gcd(2,2)=2 ∤ 1  — actually infeasible alone.
        // To make each row pass GCD individually we instead use coprime per-row
        // coefficients that combine to an odd contradiction:
        //   (1)  x + y = 0          (feasible alone)
        //   (2)  x - y = 1          (feasible alone)  ⇒ adding: 2x = 1, but each
        //    row's gcd divides its rhs. The combination 2x = 1 has gcd 2 ∤ 1.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        // x + y = 0
        let xpy = arena.int_add(x, y).unwrap();
        let zero = arena.int_const(0);
        let e1 = arena.eq(xpy, zero).unwrap();
        // x - y = 1
        let xmy = arena.int_sub(x, y).unwrap();
        let one = arena.int_const(1);
        let e2 = arena.eq(xmy, one).unwrap();
        // Each passes its own gcd test (1 divides everything).
        assert!(!prove_lia_unsat_by_gcd(&arena, &[e1]));
        assert!(!prove_lia_unsat_by_gcd(&arena, &[e2]));
        assert!(!prove_lia_unsat_by_gcd(&arena, &[e1, e2]));
        // The system: x+y=0, x-y=1 ⇒ 2x = 1 ⇒ no integer x ⇒ UNSAT.
        assert!(prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn satisfiable_system_not_refuted() {
        // x + y = 2 ∧ x - y = 0 ⇒ x = y = 1 (SAT). Must NOT be refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let xpy = arena.int_add(x, y).unwrap();
        let two = arena.int_const(2);
        let e1 = arena.eq(xpy, two).unwrap();
        let xmy = arena.int_sub(x, y).unwrap();
        let zero = arena.int_const(0);
        let e2 = arena.eq(xmy, zero).unwrap();
        assert!(!prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn satisfiable_three_var_system_not_refuted() {
        // x + y + z = 3 ∧ x + y = 2 ∧ x = 1 ⇒ x=1,y=1,z=1 (SAT). Not refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let z = ivar(&mut arena, "z");
        let xy = arena.int_add(x, y).unwrap();
        let xyz = arena.int_add(xy, z).unwrap();
        let three = arena.int_const(3);
        let e1 = arena.eq(xyz, three).unwrap();
        let two = arena.int_const(2);
        let e2 = arena.eq(xy, two).unwrap();
        let one = arena.int_const(1);
        let e3 = arena.eq(x, one).unwrap();
        assert!(!prove_lia_unsat_by_diophantine(&arena, &[e1, e2, e3]));
    }

    #[test]
    fn underdetermined_feasible_system_not_refuted() {
        // 2x + 3y = 5 ∧ x + y = 2 ⇒ x=1,y=1 (SAT). gcd per row divides rhs; the
        // combination stays feasible — must not be refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let tx = term(&mut arena, 2, x);
        let ty = term(&mut arena, 3, y);
        let lhs1 = arena.int_add(tx, ty).unwrap();
        let five = arena.int_const(5);
        let e1 = arena.eq(lhs1, five).unwrap();
        let e2 = eq_xy(&mut arena, x, y, 2);
        assert!(!prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    #[test]
    fn inequalities_in_system_are_ignored() {
        // x + y = 1 ∧ x + y = 2 ∧ x ≤ 5. The inequality is ignored; the equality
        // subset is still UNSAT ⇒ whole system UNSAT (sound).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let e1 = eq_xy(&mut arena, x, y, 1);
        let e2 = eq_xy(&mut arena, x, y, 2);
        let five = arena.int_const(5);
        let le = arena.int_le(x, five).unwrap();
        assert!(prove_lia_unsat_by_diophantine(&arena, &[e1, le, e2]));
    }

    #[test]
    fn satisfiable_with_only_inequalities_not_refuted() {
        // Only inequalities (no equalities) ⇒ no equality subsystem ⇒ not refuted.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = arena.int_const(3);
        let le = arena.int_le(x, three).unwrap();
        assert!(!prove_lia_unsat_by_diophantine(&arena, &[le]));
    }

    #[test]
    fn overflow_in_system_returns_not_refuted() {
        // Huge coefficients whose integer combination would overflow i128. The
        // elimination cross-multiplies coprime giant coefficients; the test must
        // bail out gracefully (no panic, no wrap, no spurious unsat).
        let big_a: i128 = 170_141_183_460_469_231_731; // > 2^67, coprime to big_b
        let big_b: i128 = 170_141_183_460_469_231_733; // (both prime-ish, gcd small)
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        // big_a·x + 1·y = 1
        let ax = term(&mut arena, big_a, x);
        let lhs1 = arena.int_add(ax, y).unwrap();
        let one = arena.int_const(1);
        let e1 = arena.eq(lhs1, one).unwrap();
        // big_b·x + 1·y = 2  (eliminating y cross-multiplies big_a·big_b → overflow)
        let bx = term(&mut arena, big_b, x);
        let lhs2 = arena.int_add(bx, y).unwrap();
        let two = arena.int_const(2);
        let e2 = arena.eq(lhs2, two).unwrap();
        // Must not panic; returns false (not refuted) on overflow.
        let refuted = prove_lia_unsat_by_diophantine(&arena, &[e1, e2]);
        assert!(!refuted);
    }

    // ----------------------------------------------------------------------
    // Independently-checkable Diophantine certificates.
    // ----------------------------------------------------------------------

    /// Every refuted system from the suite above yields a certificate its
    /// independent checker accepts (round-trip), and the combination is genuinely
    /// `gcd ∤ const`.
    #[test]
    fn certificate_round_trip_accepts_all_refuted_systems() {
        // x + y = 1 ∧ x + y = 2.
        {
            let mut arena = TermArena::new();
            let x = ivar(&mut arena, "x");
            let y = ivar(&mut arena, "y");
            let e1 = eq_xy(&mut arena, x, y, 1);
            let e2 = eq_xy(&mut arena, x, y, 2);
            let (eqs, cert) =
                prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).expect("refuted");
            assert!(check_diophantine_certificate(&eqs, &cert));
        }
        // x + y = 0 ∧ x − y = 1 (the "each row passes gcd, system fails" win).
        {
            let mut arena = TermArena::new();
            let x = ivar(&mut arena, "x");
            let y = ivar(&mut arena, "y");
            let xpy = arena.int_add(x, y).unwrap();
            let zero = arena.int_const(0);
            let e1 = arena.eq(xpy, zero).unwrap();
            let xmy = arena.int_sub(x, y).unwrap();
            let one = arena.int_const(1);
            let e2 = arena.eq(xmy, one).unwrap();
            let (eqs, cert) =
                prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).expect("refuted");
            assert!(check_diophantine_certificate(&eqs, &cert));
        }
        // 2x + 4y = 3 (single equation).
        {
            let mut arena = TermArena::new();
            let x = ivar(&mut arena, "x");
            let y = ivar(&mut arena, "y");
            let tx = term(&mut arena, 2, x);
            let fy = term(&mut arena, 4, y);
            let lhs = arena.int_add(tx, fy).unwrap();
            let three = arena.int_const(3);
            let eq = arena.eq(lhs, three).unwrap();
            let (eqs, cert) =
                prove_lia_unsat_by_diophantine_certified(&arena, &[eq]).expect("refuted");
            assert!(check_diophantine_certificate(&eqs, &cert));
        }
        // Three-variable x + y + z = 1 ∧ x + y + z = 2.
        {
            let mut arena = TermArena::new();
            let x = ivar(&mut arena, "x");
            let y = ivar(&mut arena, "y");
            let z = ivar(&mut arena, "z");
            let xy = arena.int_add(x, y).unwrap();
            let xyz = arena.int_add(xy, z).unwrap();
            let one = arena.int_const(1);
            let two = arena.int_const(2);
            let e1 = arena.eq(xyz, one).unwrap();
            let e2 = arena.eq(xyz, two).unwrap();
            let (eqs, cert) =
                prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).expect("refuted");
            assert!(check_diophantine_certificate(&eqs, &cert));
            // The combination has gcd ∤ const (here gcd(∅)=0 ∤ 1).
            let mut g: i128 = 0;
            for &(_, c) in &cert.combined {
                g = super::gcd(g, c);
            }
            assert!(if g == 0 {
                cert.constant != 0
            } else {
                cert.constant % g != 0
            });
        }
    }

    /// Hand-verified small case: `x + y = 1 ∧ x + y = 2`. A valid Farkas
    /// combination is λ = (−1, 1) giving `0 = 1`, and `gcd(∅) = 0 ∤ 1`. Several
    /// valid λ exist (e.g. scaled), so we assert the CHECKER accepts the emitted
    /// one and that the combination is the empty-coeff `0 = nonzero` row.
    #[test]
    fn certificate_hand_verified_zero_equals_one() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let e1 = eq_xy(&mut arena, x, y, 1);
        let e2 = eq_xy(&mut arena, x, y, 2);
        let (eqs, cert) =
            prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).expect("refuted");
        assert!(check_diophantine_certificate(&eqs, &cert));
        // Contradiction is a constant row: no surviving variable coefficients.
        assert!(cert.combined.is_empty());
        assert_ne!(cert.constant, 0);
        // The hand multiplier (−1, +1) is itself a valid certificate the checker
        // accepts (whatever scaling/sign the elimination happened to pick).
        let hand = DiophantineCertificate {
            multipliers: vec![-1, 1],
            combined: vec![],
            constant: 1,
        };
        assert!(check_diophantine_certificate(&eqs, &hand));
    }

    /// Tampering with a multiplier, a combined coefficient, or the constant makes
    /// the independent checker reject.
    #[test]
    fn certificate_tamper_is_rejected() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let tx = term(&mut arena, 2, x);
        let fy = term(&mut arena, 4, y);
        let lhs = arena.int_add(tx, fy).unwrap();
        let three = arena.int_const(3);
        let eq = arena.eq(lhs, three).unwrap();
        let (eqs, cert) = prove_lia_unsat_by_diophantine_certified(&arena, &[eq]).expect("refuted");
        assert!(check_diophantine_certificate(&eqs, &cert));

        // Tamper a multiplier.
        let mut t1 = cert.clone();
        t1.multipliers[0] = t1.multipliers[0].checked_add(1).unwrap();
        assert!(!check_diophantine_certificate(&eqs, &t1));

        // Tamper a combined coefficient (if any survives).
        if !cert.combined.is_empty() {
            let mut t2 = cert.clone();
            t2.combined[0].1 = t2.combined[0].1.checked_add(1).unwrap();
            assert!(!check_diophantine_certificate(&eqs, &t2));
        }

        // Tamper the constant.
        let mut t3 = cert.clone();
        t3.constant = t3.constant.checked_add(1).unwrap();
        assert!(!check_diophantine_certificate(&eqs, &t3));
    }

    /// A certificate for one system, checked against a DIFFERENT system, is
    /// rejected — the checker is independent of the elimination's provenance.
    #[test]
    fn certificate_cross_system_is_rejected() {
        // System A: x + y = 1 ∧ x + y = 2 (refuted).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let a1 = eq_xy(&mut arena, x, y, 1);
        let a2 = eq_xy(&mut arena, x, y, 2);
        let (_eqs_a, cert_a) =
            prove_lia_unsat_by_diophantine_certified(&arena, &[a1, a2]).expect("refuted");

        // System B: 2x + 2y = 2 ∧ 2x + 2y = 5 (also refuted, different originals).
        let mk = |arena: &mut TermArena, rhs: i128| {
            let tx = term(arena, 2, x);
            let ty = term(arena, 2, y);
            let lhs = arena.int_add(tx, ty).unwrap();
            let c = arena.int_const(rhs);
            arena.eq(lhs, c).unwrap()
        };
        let b1 = mk(&mut arena, 2);
        let b2 = mk(&mut arena, 5);
        let (eqs_b, _cert_b) =
            prove_lia_unsat_by_diophantine_certified(&arena, &[b1, b2]).expect("refuted");

        // A's certificate against B's equalities must not validate.
        assert!(!check_diophantine_certificate(&eqs_b, &cert_a));
    }

    /// A satisfiable system produces no certificate (mirrors the boolean
    /// dispatch returning `false`).
    #[test]
    fn certificate_satisfiable_system_yields_none() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let xpy = arena.int_add(x, y).unwrap();
        let two = arena.int_const(2);
        let e1 = arena.eq(xpy, two).unwrap();
        let xmy = arena.int_sub(x, y).unwrap();
        let zero = arena.int_const(0);
        let e2 = arena.eq(xmy, zero).unwrap();
        assert!(prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).is_none());
        assert!(!prove_lia_unsat_by_diophantine(&arena, &[e1, e2]));
    }

    /// Overflow during elimination yields no certificate (graceful `None`), never
    /// a panic or a spurious certificate.
    #[test]
    fn certificate_overflow_yields_none() {
        let big_a: i128 = 170_141_183_460_469_231_731;
        let big_b: i128 = 170_141_183_460_469_231_733;
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let ax = term(&mut arena, big_a, x);
        let lhs1 = arena.int_add(ax, y).unwrap();
        let one = arena.int_const(1);
        let e1 = arena.eq(lhs1, one).unwrap();
        let bx = term(&mut arena, big_b, x);
        let lhs2 = arena.int_add(bx, y).unwrap();
        let two = arena.int_const(2);
        let e2 = arena.eq(lhs2, two).unwrap();
        assert!(prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).is_none());
    }

    /// A malformed certificate (wrong multiplier count) is conservatively rejected.
    #[test]
    fn certificate_wrong_multiplier_count_is_rejected() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let e1 = eq_xy(&mut arena, x, y, 1);
        let e2 = eq_xy(&mut arena, x, y, 2);
        let (eqs, cert) =
            prove_lia_unsat_by_diophantine_certified(&arena, &[e1, e2]).expect("refuted");
        let bad = DiophantineCertificate {
            multipliers: vec![cert.multipliers[0]], // too few
            combined: cert.combined.clone(),
            constant: cert.constant,
        };
        assert!(!check_diophantine_certificate(&eqs, &bad));
    }
}
