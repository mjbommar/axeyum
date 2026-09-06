//! Cofactor-preserving **linear elimination**: solve for the unknowns a system
//! already determines, instead of asking `Buchberger`'s algorithm to rediscover
//! Cramer's rule by monomial reduction.
//!
//! # The observation this module acts on
//!
//! Many polynomial systems are *linear* in the variables that matter. Euler's
//! line is the motivating case: its four hypotheses
//!
//! ```text
//! |OA|² − |OB|² = 0      |OB|² − |OC|² = 0      (H−A)·(C−B) = 0      (H−B)·(A−C) = 0
//! ```
//!
//! are quadratic in the vertex coordinates `ax…cy` but **affine in the four
//! unknowns** `ox, oy, hx, hy` — the squares of the unknown cancel in the first
//! two, and the last two never had any. Two 2×2 systems over `ℚ[ax…cy]`
//! determine `O` and `H` outright. A Gröbner engine given those generators
//! spends its whole budget recovering that fact one S-polynomial at a time: the
//! `geometry-frontier` lane measured the basis still growing at one element per
//! two S-pairs after 65 pairs, with 528 pairs queued and no closure in sight.
//!
//! # Why the certificate survives
//!
//! This is a `cas-certificate` route: the deliverable is not a verdict but an
//! identity `target = Σ cofactorᵢ·generatorᵢ` that an **independent checker**
//! re-derives by polynomial arithmetic alone. A solved-form substitution that
//! replaced the generators with solved equations would prove something else.
//!
//! So nothing here changes the generator list. The elimination is arranged as a
//! *derivation of cofactors in the original generators*, using the adjugate
//! identity
//!
//! ```text
//! adj(M) · (M·u + k)  =  det(M)·u + adj(M)·k
//! ```
//!
//! Writing the block's generators as `gᵢ = Σⱼ M[i][j]·uⱼ + kᵢ`, that identity
//! reads, one unknown at a time,
//!
//! ```text
//! det(M)·uⱼ  =  Sⱼ  +  Σᵢ adj(M)[j][i] · gᵢ            with  S = −adj(M)·k
//! ```
//!
//! — an explicit statement that `det(M)·uⱼ` equals a polynomial **free of the
//! unknowns** plus a combination of the original `gᵢ` with cofactors `adj(M)[j][i]`
//! that live in the coefficient ring. Substituting that into the target, and
//! clearing the target's degree `d` in the block's unknowns with `det(M)^d`,
//! yields
//!
//! ```text
//! det(M)^d · target  =  residue  +  Σᵢ cofactorᵢ · gᵢ
//! ```
//!
//! with `residue` free of the unknowns. Every cofactor is against an **original**
//! generator, and the identity is checkable by expansion, exactly like one
//! `groebner_cert` produces. The two routes are interchangeable at the artifact:
//! same generators, same shape, same checker.
//!
//! The price is the `det(M)^d` multiplier, which must be divided back out. On a
//! saturated problem that is free — the determinant of a geometric construction
//! is normally a multiple of the very non-degeneracy condition the theorem needs,
//! and the Rabinowitsch generator `d·z − 1` is exactly an inverse for it. See
//! [`crate::geometry_certify::certify_by_linear_elimination`], which does that
//! division and stays inside the original generator list while doing it.
//!
//! # What this module does not do
//!
//! It decides nothing. A nonzero [`LinearElimination::residue`] is not a claim
//! that the target lies outside the ideal — it is the part of the question that
//! linear algebra did not answer, and the caller is expected to hand it to a
//! general ideal-membership route over the (much smaller) remaining system.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};

/// The largest square subsystem this module will invert.
///
/// The determinant is a Laplace expansion, so the cost is `k!` polynomial
/// products; `6` is 720 and already far beyond the 2×2 blocks classical plane
/// geometry produces. A ceiling rather than a recursion guard, because an
/// unbounded one would turn a mis-detected block into a hang.
const MAX_BLOCK: usize = 6;

/// The largest number of square subsystems examined when a component has more
/// generators than unknowns.
const MAX_ROW_CHOICES: usize = 256;

/// One square subsystem of the generators, solved by Cramer's rule.
///
/// `rows` indexes the caller's generator slice, `unknowns` names the variables
/// eliminated, and `determinant` is `det(M)` for the coefficient matrix `M[i][j]`
/// = the coefficient of `unknowns[j]` in `generators[rows[i]]`. It is nonzero by
/// construction: a singular block is never reported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearBlock {
    /// The variables this block eliminates, in ascending name order.
    pub unknowns: Vec<String>,
    /// Indices into the caller's generator slice; `rows.len() == unknowns.len()`.
    pub rows: Vec<usize>,
    /// `det(M)`, never the zero polynomial.
    pub determinant: MvPoly,
}

/// The identity produced by [`eliminate`].
///
/// The invariant, and the only thing a consumer should rely on:
///
/// ```text
/// multiplier · target  =  residue  +  Σᵢ cofactors[i] · generators[i]
/// ```
///
/// with `residue` free of every variable in every block's `unknowns`, and
/// `multiplier` the product of `blockᵢ.determinant^powers[i]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearElimination {
    /// The subsystems inverted, in the order they were applied.
    pub blocks: Vec<LinearBlock>,
    /// `powers[i]` is the target's degree in `blocks[i].unknowns` at the moment
    /// that block was applied — the power of its determinant in `multiplier`.
    pub powers: Vec<u32>,
    /// `Π blocks[i].determinant^powers[i]`.
    pub multiplier: MvPoly,
    /// One cofactor per caller-supplied generator, positionally aligned.
    pub cofactors: Vec<MvPoly>,
    /// What linear algebra could not remove: free of every eliminated unknown.
    pub residue: MvPoly,
}

/// A polynomial carried with its representation in the generators: the value it
/// denotes is `residue + Σ cofactors[i]·generators[i]`.
///
/// The same bookkeeping idea as `groebner_cert::Tracked`, and deliberately a
/// separate implementation — the two modules share no code, so a bug in one
/// cannot launder a certificate through the other.
#[derive(Debug, Clone)]
struct Tracked {
    residue: MvPoly,
    cofactors: Vec<MvPoly>,
}

impl Tracked {
    /// A value with no generator content.
    fn plain(residue: MvPoly, generators: usize) -> Tracked {
        Tracked {
            residue,
            cofactors: vec![MvPoly::zero(); generators],
        }
    }

    fn add(&self, other: &Tracked) -> Option<Tracked> {
        let mut cofactors = Vec::with_capacity(self.cofactors.len());
        for (left, right) in self.cofactors.iter().zip(other.cofactors.iter()) {
            cofactors.push(left.add(right)?);
        }
        Some(Tracked {
            residue: self.residue.add(&other.residue)?,
            cofactors,
        })
    }

    /// `(x_r + Σ xᵢgᵢ)·(y_r + Σ yⱼgⱼ)`, keeping the cross term inside the
    /// generator ideal: `(Σ xᵢgᵢ)(Σ yⱼgⱼ) = Σᵢ (xᵢ · Σⱼ yⱼgⱼ) gᵢ`.
    fn mul(&self, other: &Tracked, generators: &[MvPoly]) -> Option<Tracked> {
        let other_combination = combination(&other.cofactors, generators)?;
        let mut cofactors = Vec::with_capacity(self.cofactors.len());
        for (index, mine) in self.cofactors.iter().enumerate() {
            let mut slot = self.residue.mul(&other.cofactors[index])?;
            slot = slot.add(&other.residue.mul(mine)?)?;
            if !mine.is_zero() {
                slot = slot.add(&mine.mul(&other_combination)?)?;
            }
            cofactors.push(slot);
        }
        Some(Tracked {
            residue: self.residue.mul(&other.residue)?,
            cofactors,
        })
    }
}

/// `Σᵢ cofactors[i]·generators[i]`, expanded.
///
/// The public form of the bookkeeping invariant: a caller that wants to confirm
/// a [`LinearElimination`] without trusting this module recomputes
/// `multiplier·target` and compares it with `residue` plus this.
#[must_use]
pub fn combination(cofactors: &[MvPoly], generators: &[MvPoly]) -> Option<MvPoly> {
    let mut total = MvPoly::zero();
    for (cofactor, generator) in cofactors.iter().zip(generators.iter()) {
        if cofactor.is_zero() {
            continue;
        }
        total = total.add(&cofactor.mul(generator)?)?;
    }
    Some(total)
}

/// Split `poly` into `(coefficients, constant)` with
/// `poly = Σⱼ coefficients[j]·unknowns[j] + constant`.
///
/// `None` when `poly` is not affine in `unknowns` **jointly** — a monomial
/// carrying two of them, or one of them squared. That joint test is the one that
/// matters: `degree_in` is per-variable, and `ox·oy` has degree one in each while
/// being quadratic in the pair.
fn affine_split(poly: &MvPoly, unknowns: &[String]) -> Option<(Vec<MvPoly>, MvPoly)> {
    let mut coefficients = vec![Vec::new(); unknowns.len()];
    let mut constant: Vec<(Monomial, Rational)> = Vec::new();
    for (mono, coeff) in poly.terms() {
        let mut carried: Option<usize> = None;
        let mut degree = 0u32;
        for (slot, unknown) in unknowns.iter().enumerate() {
            let exponent = mono.exponent_of(unknown);
            if exponent > 0 {
                degree = degree.checked_add(exponent)?;
                carried = Some(slot);
            }
        }
        if degree > 1 {
            return None;
        }
        match carried {
            Some(slot) => coefficients[slot].push((strip(mono, unknowns), *coeff)),
            None => constant.push((mono.clone(), *coeff)),
        }
    }
    let mut columns = Vec::with_capacity(unknowns.len());
    for terms in coefficients {
        columns.push(MvPoly::from_terms(terms)?);
    }
    Some((columns, MvPoly::from_terms(constant)?))
}

/// `mono` with every variable in `unknowns` removed.
fn strip(mono: &Monomial, unknowns: &[String]) -> Monomial {
    let kept: Vec<(&str, u32)> = mono
        .powers()
        .filter(|(name, _)| !unknowns.iter().any(|unknown| unknown == name))
        .collect();
    Monomial::from_powers(&kept)
}

/// Group `poly` by its monomial in `unknowns`: the exponent vector maps to the
/// coefficient over the remaining variables.
fn group_by_unknowns(poly: &MvPoly, unknowns: &[String]) -> Option<BTreeMap<Vec<u32>, MvPoly>> {
    let mut buckets: BTreeMap<Vec<u32>, Vec<(Monomial, Rational)>> = BTreeMap::new();
    for (mono, coeff) in poly.terms() {
        let key: Vec<u32> = unknowns
            .iter()
            .map(|unknown| mono.exponent_of(unknown))
            .collect();
        buckets
            .entry(key)
            .or_default()
            .push((strip(mono, unknowns), *coeff));
    }
    let mut grouped = BTreeMap::new();
    for (key, terms) in buckets {
        grouped.insert(key, MvPoly::from_terms(terms)?);
    }
    Some(grouped)
}

/// The determinant of a square polynomial matrix, by Laplace expansion along the
/// first row. `None` on coefficient overflow or a matrix wider than [`MAX_BLOCK`].
fn determinant(matrix: &[Vec<MvPoly>]) -> Option<MvPoly> {
    let size = matrix.len();
    if size > MAX_BLOCK {
        return None;
    }
    if size == 0 {
        return Some(MvPoly::constant(Rational::integer(1)));
    }
    if size == 1 {
        return Some(matrix[0][0].clone());
    }
    let mut total = MvPoly::zero();
    for column in 0..size {
        if matrix[0][column].is_zero() {
            continue;
        }
        let sub = minor(matrix, 0, column);
        let mut term = matrix[0][column].mul(&determinant(&sub)?)?;
        if column % 2 == 1 {
            term = term.neg()?;
        }
        total = total.add(&term)?;
    }
    Some(total)
}

/// The matrix with `skip_row` and `skip_column` deleted.
fn minor(matrix: &[Vec<MvPoly>], skip_row: usize, skip_column: usize) -> Vec<Vec<MvPoly>> {
    matrix
        .iter()
        .enumerate()
        .filter(|(row, _)| *row != skip_row)
        .map(|(_, entries)| {
            entries
                .iter()
                .enumerate()
                .filter(|(column, _)| *column != skip_column)
                .map(|(_, entry)| entry.clone())
                .collect()
        })
        .collect()
}

/// `adj(M)[j][i]` — the `(i, j)` cofactor `(−1)^(i+j)·det(minor(i, j))`, which is
/// the coefficient of generator `i` in the expression for `det(M)·unknownⱼ`.
// The adjugate is the TRANSPOSE of the cofactor matrix, so the write index is
// `[column][row]` while the cofactor being computed is `(row, column)`. An
// iterator over rows would hide exactly the swap that makes this correct.
#[allow(clippy::needless_range_loop)]
fn adjugate(matrix: &[Vec<MvPoly>]) -> Option<Vec<Vec<MvPoly>>> {
    let size = matrix.len();
    let mut adj = vec![vec![MvPoly::zero(); size]; size];
    for row in 0..size {
        for column in 0..size {
            let mut entry = determinant(&minor(matrix, row, column))?;
            if (row + column) % 2 == 1 {
                entry = entry.neg()?;
            }
            adj[column][row] = entry;
        }
    }
    Some(adj)
}

/// Variables every generator is at most degree one in, and that at least one
/// generator mentions.
fn candidate_unknowns(generators: &[MvPoly]) -> BTreeSet<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for generator in generators {
        seen.extend(generator.variables());
    }
    seen.into_iter()
        .filter(|variable| {
            generators
                .iter()
                .all(|generator| generator.degree_in(variable) <= 1)
        })
        .collect()
}

/// Disjoint-set forest over `generators.len() + candidates.len()` nodes.
struct Components {
    parent: Vec<usize>,
}

impl Components {
    fn new(size: usize) -> Components {
        Components {
            parent: (0..size).collect(),
        }
    }

    fn find(&mut self, node: usize) -> usize {
        let mut current = node;
        while self.parent[current] != current {
            self.parent[current] = self.parent[self.parent[current]];
            current = self.parent[current];
        }
        current
    }

    fn union(&mut self, left: usize, right: usize) {
        let (left, right) = (self.find(left), self.find(right));
        if left != right {
            self.parent[right] = left;
        }
    }
}

/// One step of [`choices_capped`]: extend `stack` from `start` onwards.
fn walk_choices(
    items: &[usize],
    take: usize,
    start: usize,
    cap: usize,
    stack: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
) {
    if out.len() >= cap {
        return;
    }
    if stack.len() == take {
        out.push(stack.clone());
        return;
    }
    for index in start..items.len() {
        stack.push(items[index]);
        walk_choices(items, take, index + 1, cap, stack, out);
        stack.pop();
    }
}

/// The `k`-subsets of `items`, in ascending lexicographic order, capped at
/// `cap`.
fn choices_capped(items: &[usize], take: usize, cap: usize) -> Vec<Vec<usize>> {
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    walk_choices(items, take, 0, cap, &mut stack, &mut out);
    out
}

/// How hard [`detect_linear_blocks_where`] looks, and which determinants it is
/// allowed to come back with.
///
/// # Why a determinant filter belongs *inside* the search
///
/// The detector's answer is not simply "a nonsingular square subsystem": it is
/// one whose determinant the **caller** can afterwards divide back out. For
/// [`crate::geometry_certify`] that means a determinant which is a product of the
/// theorem's stated non-degeneracy conditions, because those are the only things
/// the certificate can invert (the Rabinowitsch generator `d·z − 1`).
///
/// Until 2026-09-05 the two halves were separate: the search stopped at the
/// **first** nonsingular subsystem it found, and the certifier then discarded it
/// if the determinant was unusable — with no second look. That threw away the
/// only question that mattered. A component with fifteen candidate unknowns has
/// hundreds of square subsystems and the search was examining exactly one of
/// them, chosen by nothing more meaningful than alphabetical order.
///
/// Passing the filter in fixes that: an unusable determinant now advances the
/// search instead of ending it. Soundness is untouched either way — a block is a
/// *proposal*, and `eliminate_blocks` re-derives and re-checks every determinant
/// it is handed.
pub struct BlockSearch<'a> {
    /// Upper bound on the subsets enumerated at each size, for the unknowns and
    /// for the rows independently. A ceiling rather than a guess: the number of
    /// subsets is binomial in the candidate count, so an uncapped search is not a
    /// slow search but an unbounded one.
    pub choices: usize,
    /// Total square subsystems the search may examine before giving up. The
    /// per-size caps bound each list; this bounds their product, which is what
    /// actually costs time.
    pub examined: usize,
    /// Whether a determinant is one the caller can use. `|_| true` reproduces the
    /// unfiltered search exactly.
    pub accept: &'a dyn Fn(&MvPoly) -> bool,
}

impl BlockSearch<'_> {
    /// The search [`detect_linear_blocks`] performs: every determinant accepted,
    /// capped at the module's `MAX_ROW_CHOICES` (256) subsets per size.
    #[must_use]
    pub fn permissive() -> BlockSearch<'static> {
        BlockSearch {
            choices: MAX_ROW_CHOICES,
            examined: usize::MAX,
            accept: &|_| true,
        }
    }
}

/// Find the square subsystems of `generators` that determine, outright, the
/// variables `target` needs eliminated.
///
/// A variable is a **candidate** when it occurs in `target` and every generator
/// is at most degree one in it. Restricting to `target`'s variables is what makes
/// the choice well-posed rather than arbitrary: a system is usually affine in
/// many variables at once (`a·x + b·y − 1` is affine in `a` and in `b` just as
/// much as in `x`), and the ones worth spending a determinant on are the ones
/// standing between the target and an answer.
///
/// The candidates and the generators that mention them form a bipartite
/// incidence graph. Each connected component contributes at most one block: the
/// largest square subsystem inside it whose rows are jointly affine in the chosen
/// unknowns and whose coefficient matrix is nonsingular. Components are the right
/// unit because they guarantee the property the elimination needs — a block's
/// unknowns appear in no other block's rows, so the blocks do not interfere.
///
/// Detection is a heuristic and is allowed to be wrong in either direction: a
/// block it misses costs reach, and a block it should not have chosen produces an
/// identity that simply fails to check, or an [`eliminate_blocks`] that returns
/// `None`. Nothing about soundness rests on it.
///
/// ```
/// use axeyum_cas::linear_elim::detect_linear_blocks;
/// use axeyum_cas::mvpoly::MvPoly;
///
/// // 2x + 3y − 7 = 0 and x − y = 0 determine x and y over ℚ.
/// let x = MvPoly::var("x");
/// let y = MvPoly::var("y");
/// let two = MvPoly::constant(axeyum_ir::Rational::integer(2));
/// let three = MvPoly::constant(axeyum_ir::Rational::integer(3));
/// let seven = MvPoly::constant(axeyum_ir::Rational::integer(7));
/// let generators = vec![
///     two.mul(&x).unwrap().add(&three.mul(&y).unwrap()).unwrap().sub(&seven).unwrap(),
///     x.sub(&y).unwrap(),
/// ];
/// let blocks = detect_linear_blocks(&generators, &x.add(&y).unwrap());
/// assert_eq!(blocks.len(), 1);
/// assert_eq!(blocks[0].unknowns, vec!["x".to_string(), "y".to_string()]);
/// ```
#[must_use]
pub fn detect_linear_blocks(generators: &[MvPoly], target: &MvPoly) -> Vec<LinearBlock> {
    detect_linear_blocks_where(
        generators,
        std::slice::from_ref(target),
        &BlockSearch::permissive(),
    )
}

/// [`detect_linear_blocks`] against **several** targets at once and a
/// caller-supplied [`BlockSearch`].
///
/// # Why several targets
///
/// A theorem's conclusions are stated one component at a time — `4P.x = …`,
/// `4P.y = …`, `4P.z = …` — while the unknown the hypotheses actually determine
/// is the whole point `P`. Scoping the candidate unknowns to **one** conclusion
/// then asks the wrong question: `centroid-x` mentions `px` and none of `py`,
/// `pz`, so no subsystem over the three coordinates is ever considered, and the
/// component the detector does find is whatever alphabetically-first square block
/// the hypotheses happen to admit. Taking the union of the conclusions' variables
/// makes the unknown set the *theorem's*, not one component's.
///
/// # What it does not fix
///
/// Widening the scope decides which subsystems are **offered**; whether any of
/// them is usable is a separate question, and on
/// `tetrahedron-medians-concurrent` the answer measured 2026-09-05 is no — see
/// [`crate::geometry_certify::certify_by_linear_elimination`]'s "when the
/// widened search still declines" section for the enumeration.
#[must_use]
pub fn detect_linear_blocks_where(
    generators: &[MvPoly],
    targets: &[MvPoly],
    search: &BlockSearch<'_>,
) -> Vec<LinearBlock> {
    let mut wanted: BTreeSet<String> = BTreeSet::new();
    for target in targets {
        wanted.extend(target.variables());
    }
    let candidates: Vec<String> = candidate_unknowns(generators)
        .into_iter()
        .filter(|variable| wanted.contains(variable))
        .collect();
    if candidates.is_empty() {
        return Vec::new();
    }
    let offset = generators.len();
    let mut components = Components::new(offset + candidates.len());
    for (index, generator) in generators.iter().enumerate() {
        for (slot, candidate) in candidates.iter().enumerate() {
            if generator.degree_in(candidate) == 1 {
                components.union(index, offset + slot);
            }
        }
    }

    let mut grouped_rows: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut grouped_unknowns: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for (slot, candidate) in candidates.iter().enumerate() {
        let root = components.find(offset + slot);
        grouped_unknowns
            .entry(root)
            .or_default()
            .push(candidate.clone());
    }
    for index in 0..generators.len() {
        let root = components.find(index);
        if grouped_unknowns.contains_key(&root) {
            grouped_rows.entry(root).or_default().push(index);
        }
    }

    let mut blocks = Vec::new();
    for (root, unknowns) in grouped_unknowns {
        let rows = grouped_rows.get(&root).cloned().unwrap_or_default();
        let cap = unknowns.len().min(rows.len()).min(MAX_BLOCK);
        // Largest first, then smaller: a component that is underdetermined, or
        // whose rows are not jointly affine in all of its unknowns, still yields
        // whatever square subsystem it does contain. The rest stays in the residue
        // for whatever route the caller hands it to next. `x·y − 1` is the case
        // that forces this: it admits no 2×2 block over `{x, y}` and a perfectly
        // good 1×1 one over `{x}`.
        let positions: Vec<usize> = (0..unknowns.len()).collect();
        let mut found = false;
        let mut examined = 0usize;
        for size in (1..=cap).rev() {
            for chosen in choices_capped(&positions, size, search.choices) {
                let picked: Vec<String> = chosen
                    .iter()
                    .map(|&index| unknowns[index].clone())
                    .collect();
                for candidate_rows in choices_capped(&rows, size, search.choices) {
                    if examined >= search.examined {
                        break;
                    }
                    examined += 1;
                    let Some((_, det)) = coefficient_matrix(generators, &candidate_rows, &picked)
                    else {
                        continue;
                    };
                    if det.is_zero() {
                        continue;
                    }
                    // An unusable determinant advances the search rather than
                    // ending it. See `BlockSearch::accept`.
                    if !(search.accept)(&det) {
                        continue;
                    }
                    blocks.push(LinearBlock {
                        unknowns: picked.clone(),
                        rows: candidate_rows,
                        determinant: det,
                    });
                    found = true;
                    break;
                }
                if found {
                    break;
                }
            }
            if found {
                break;
            }
        }
    }
    blocks
}

/// The coefficient matrix of `rows` in `unknowns`, with its determinant.
/// `None` when a row is not jointly affine in the unknowns, or on overflow.
fn coefficient_matrix(
    generators: &[MvPoly],
    rows: &[usize],
    unknowns: &[String],
) -> Option<(Vec<Vec<MvPoly>>, MvPoly)> {
    let mut matrix = Vec::with_capacity(rows.len());
    for &row in rows {
        let (coefficients, _) = affine_split(&generators[row], unknowns)?;
        matrix.push(coefficients);
    }
    let det = determinant(&matrix)?;
    Some((matrix, det))
}

/// Eliminate every block [`detect_linear_blocks`] finds from `target`, producing
/// a cofactor identity in the **original** generators.
///
/// Returns `None` only on `i128` coefficient or `u32` exponent overflow — this
/// routine has no budget and no search, so it either produces the identity or
/// reports that exact arithmetic ran out of room. That is a deliberate contrast
/// with `groebner_cert`, whose declines are usually ceilings.
///
/// ```
/// use axeyum_cas::linear_elim::{combination, eliminate};
/// use axeyum_cas::mvpoly::MvPoly;
/// use axeyum_ir::Rational;
///
/// let int = |n| MvPoly::constant(Rational::integer(n));
/// let (a, x, y) = (MvPoly::var("a"), MvPoly::var("x"), MvPoly::var("y"));
/// // a·x − 1 = 0 and y − x = 0, so a·y − 1 = 0 as well.
/// let generators = vec![
///     a.mul(&x).unwrap().sub(&int(1)).unwrap(),
///     y.sub(&x).unwrap(),
/// ];
/// let target = a.mul(&y).unwrap().sub(&int(1)).unwrap();
/// let done = eliminate(&generators, &target).unwrap();
/// assert!(done.residue.is_zero(), "linear algebra settles it outright");
/// // The identity is exact, and against the ORIGINAL generators.
/// let left = done.multiplier.mul(&target).unwrap();
/// let right = combination(&done.cofactors, &generators).unwrap();
/// assert_eq!(left, right.add(&done.residue).unwrap());
/// ```
#[must_use]
pub fn eliminate(generators: &[MvPoly], target: &MvPoly) -> Option<LinearElimination> {
    eliminate_blocks(generators, target, detect_linear_blocks(generators, target))
}

/// [`eliminate`] against a caller-chosen block decomposition.
///
/// Exposed so a caller can pin the decomposition rather than inherit the
/// heuristic — and so the heuristic itself is testable against a hand-written
/// answer.
#[must_use]
pub fn eliminate_blocks(
    generators: &[MvPoly],
    target: &MvPoly,
    blocks: Vec<LinearBlock>,
) -> Option<LinearElimination> {
    let mut current = Tracked::plain(target.clone(), generators.len());
    let mut multiplier = MvPoly::constant(Rational::integer(1));
    let mut powers = Vec::with_capacity(blocks.len());

    for block in &blocks {
        let (matrix, det) = coefficient_matrix(generators, &block.rows, &block.unknowns)?;
        if det != block.determinant || det.is_zero() {
            return None;
        }
        let adj = adjugate(&matrix)?;

        // `det·unknownⱼ = Sⱼ + Σᵢ adj[j][i]·generators[rows[i]]`.
        let mut solved: Vec<Tracked> = Vec::with_capacity(block.unknowns.len());
        for adjugate_row in &adj {
            let mut cofactors = vec![MvPoly::zero(); generators.len()];
            let mut constant = MvPoly::zero();
            for (slot, &row) in block.rows.iter().enumerate() {
                let (_, offset) = affine_split(&generators[row], &block.unknowns)?;
                constant = constant.add(&adjugate_row[slot].mul(&offset)?)?;
                cofactors[row] = adjugate_row[slot].clone();
            }
            solved.push(Tracked {
                residue: constant.neg()?,
                cofactors,
            });
        }

        let grouped = group_by_unknowns(&current.residue, &block.unknowns)?;
        let degree = grouped
            .keys()
            .map(|key| key.iter().copied().map(u64::from).sum::<u64>())
            .max()
            .unwrap_or(0);
        let degree = u32::try_from(degree).ok()?;
        let det_power = det.pow(degree)?;

        let mut rebuilt = Tracked::plain(MvPoly::zero(), generators.len());
        for (key, coefficient) in &grouped {
            let used = key
                .iter()
                .try_fold(0u32, |acc, exponent| acc.checked_add(*exponent))?;
            let scale = det.pow(degree.checked_sub(used)?)?;
            let mut term = Tracked::plain(coefficient.mul(&scale)?, generators.len());
            for (slot, &exponent) in key.iter().enumerate() {
                for _ in 0..exponent {
                    term = term.mul(&solved[slot], generators)?;
                }
            }
            rebuilt = rebuilt.add(&term)?;
        }

        // `det^degree · (residue + Σ cofactors·gen) = rebuilt.residue + Σ (rebuilt + det^degree·cofactors)·gen`.
        let mut cofactors = Vec::with_capacity(generators.len());
        for (carried, fresh) in current.cofactors.iter().zip(rebuilt.cofactors.iter()) {
            cofactors.push(carried.mul(&det_power)?.add(fresh)?);
        }
        // Defensive: the whole point of the block is that the unknowns are gone.
        // A `Some` return that still mentions one would be a wrong identity that
        // happened to expand, so refuse rather than emit it.
        for unknown in &block.unknowns {
            if rebuilt.residue.degree_in(unknown) > 0 {
                return None;
            }
        }
        current = Tracked {
            residue: rebuilt.residue,
            cofactors,
        };
        multiplier = multiplier.mul(&det_power)?;
        powers.push(degree);
    }

    // The documented invariant, enforced once at the end rather than trusted from
    // the per-block checks: a later block substitutes into the coefficient ring,
    // and in principle its solved values could reintroduce an earlier block's
    // unknown. An identity that expands correctly but leaves an unknown standing
    // is not the identity this function promises, so refuse it.
    for block in &blocks {
        for unknown in &block.unknowns {
            if current.residue.degree_in(unknown) > 0 {
                return None;
            }
        }
    }

    Some(LinearElimination {
        blocks,
        powers,
        multiplier,
        cofactors: current.cofactors,
        residue: current.residue,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        BlockSearch, combination, detect_linear_blocks, detect_linear_blocks_where, eliminate,
        eliminate_blocks,
    };
    use crate::mvpoly::MvPoly;
    use axeyum_ir::Rational;

    fn int(value: i128) -> MvPoly {
        MvPoly::constant(Rational::integer(value))
    }

    /// Two generators that determine `p` and `q`, connected so they form one
    /// component: `2p + q − 3` and `e·q − 5`.
    ///
    /// The `2×2` block over `{p, q}` has determinant `2e`; the `1×1` block over
    /// `{p}` has determinant `2`. A caller that can only divide by constants
    /// therefore wants the second, and the unfiltered search hands it the first.
    fn two_blocks_one_usable() -> (Vec<MvPoly>, MvPoly) {
        let (p, q, e) = (MvPoly::var("p"), MvPoly::var("q"), MvPoly::var("e"));
        let first = int(2)
            .mul(&p)
            .unwrap()
            .add(&q)
            .unwrap()
            .sub(&int(3))
            .unwrap();
        let second = e.mul(&q).unwrap().sub(&int(5)).unwrap();
        (vec![first, second], p.add(&q).unwrap())
    }

    /// An unusable determinant advances the search instead of ending it.
    ///
    /// Delete the `accept` check in `detect_linear_blocks_where` and this dies:
    /// the filtered search comes back with the `{p, q}` block the permissive one
    /// already returns, and the two halves of the assertion collapse together.
    #[test]
    fn a_rejected_determinant_advances_the_block_search() {
        let (generators, target) = two_blocks_one_usable();
        let permissive = detect_linear_blocks(&generators, &target);
        assert_eq!(
            permissive.len(),
            1,
            "one component, so at most one block: {permissive:?}"
        );
        assert_eq!(
            permissive[0].unknowns,
            vec!["p".to_string(), "q".to_string()],
            "the unfiltered search stops at the largest square subsystem"
        );

        let constants_only = |determinant: &MvPoly| determinant.total_degree() == 0;
        let filtered = detect_linear_blocks_where(
            &generators,
            std::slice::from_ref(&target),
            &BlockSearch {
                choices: 256,
                examined: usize::MAX,
                accept: &constants_only,
            },
        );
        assert_eq!(filtered.len(), 1, "a usable block exists: {filtered:?}");
        assert_eq!(
            filtered[0].unknowns,
            vec!["p".to_string()],
            "the search kept looking past the determinant the caller cannot use"
        );
        assert_eq!(filtered[0].determinant, int(2));
    }

    /// Joint targets see an unknown no single target mentions.
    ///
    /// `p − 1` and `q − 2` determine two variables in two separate components.
    /// Scoped to the target `p`, only the first is a candidate — which is exactly
    /// the shape of a theorem whose conclusions are stated one component at a
    /// time. Delete the union in `detect_linear_blocks_where` (use `targets[0]`)
    /// and the second assertion drops to one block.
    #[test]
    fn joint_targets_see_unknowns_no_single_target_mentions() {
        let (p, q) = (MvPoly::var("p"), MvPoly::var("q"));
        let generators = vec![p.sub(&int(1)).unwrap(), q.sub(&int(2)).unwrap()];

        let alone = detect_linear_blocks(&generators, &p);
        assert_eq!(alone.len(), 1, "only `p` is in scope: {alone:?}");
        assert_eq!(alone[0].unknowns, vec!["p".to_string()]);

        let together = detect_linear_blocks_where(
            &generators,
            &[p.clone(), q.clone()],
            &BlockSearch::permissive(),
        );
        assert_eq!(
            together.len(),
            2,
            "both components are in scope now: {together:?}"
        );
        assert_eq!(together[0].unknowns, vec!["p".to_string()]);
        assert_eq!(together[1].unknowns, vec!["q".to_string()]);
    }

    /// The search budget is a budget: exhausted, it returns fewer blocks, never
    /// wrong ones.
    ///
    /// Delete the `examined >= search.examined` break and this dies — the search
    /// finds the block it is not allowed to look for.
    #[test]
    fn an_exhausted_search_budget_returns_no_block() {
        let (generators, target) = two_blocks_one_usable();
        let starved = detect_linear_blocks_where(
            &generators,
            std::slice::from_ref(&target),
            &BlockSearch {
                choices: 256,
                examined: 0,
                accept: &|_| true,
            },
        );
        assert!(
            starved.is_empty(),
            "a zero budget examined a subsystem anyway: {starved:?}"
        );
        assert_eq!(
            detect_linear_blocks_where(
                &generators,
                std::slice::from_ref(&target),
                &BlockSearch::permissive(),
            )
            .len(),
            1,
            "the positive control: with a budget the block is there"
        );
    }

    /// The subset ceiling is honoured too, and it is *not* the same knob.
    ///
    /// `e·p + q − 3` and `q − 5`: the only determinant a constants-only caller
    /// can use belongs to `{q}`, the **second** size-one subset in alphabetical
    /// order. With `choices: 1` the search enumerates one subset per size and
    /// cannot reach it; with the ordinary ceiling it can. Delete the cap in
    /// `choices_capped` and the first half of this dies.
    #[test]
    fn the_subset_ceiling_bounds_what_the_search_enumerates() {
        let (p, q, e) = (MvPoly::var("p"), MvPoly::var("q"), MvPoly::var("e"));
        let generators = vec![
            e.mul(&p).unwrap().add(&q).unwrap().sub(&int(3)).unwrap(),
            q.sub(&int(5)).unwrap(),
        ];
        let target = p.add(&q).unwrap();
        let constants_only = |determinant: &MvPoly| determinant.total_degree() == 0;

        let starved = detect_linear_blocks_where(
            &generators,
            std::slice::from_ref(&target),
            &BlockSearch {
                choices: 1,
                examined: usize::MAX,
                accept: &constants_only,
            },
        );
        assert!(
            starved.is_empty(),
            "one subset per size cannot reach `{{q}}`: {starved:?}"
        );

        let full = detect_linear_blocks_where(
            &generators,
            std::slice::from_ref(&target),
            &BlockSearch {
                choices: 256,
                examined: usize::MAX,
                accept: &constants_only,
            },
        );
        assert_eq!(full.len(), 1, "the positive control: {full:?}");
        assert_eq!(full[0].unknowns, vec!["q".to_string()]);
    }

    /// The invariant, re-derived without any of the bookkeeping above: this is
    /// what an independent checker does, and it is the only thing that makes the
    /// route sound.
    fn identity_holds(generators: &[MvPoly], target: &MvPoly) -> bool {
        let Some(done) = eliminate(generators, target) else {
            return false;
        };
        let left = done.multiplier.mul(target).expect("product");
        let right = combination(&done.cofactors, generators)
            .expect("combination")
            .add(&done.residue)
            .expect("sum");
        left == right
    }

    #[test]
    fn a_two_by_two_system_is_solved_and_the_identity_is_exact() {
        // 2x + 3y = 7, x − y = 0. Determinant −5, solution x = y = 7/5.
        let (x, y) = (MvPoly::var("x"), MvPoly::var("y"));
        let generators = vec![
            int(2)
                .mul(&x)
                .unwrap()
                .add(&int(3).mul(&y).unwrap())
                .unwrap()
                .sub(&int(7))
                .unwrap(),
            x.sub(&y).unwrap(),
        ];
        let target = x.sub(&y).unwrap();
        let done = eliminate(&generators, &target).expect("eliminated");
        assert_eq!(done.blocks.len(), 1);
        assert!(done.residue.is_zero());
        assert!(identity_holds(&generators, &target));
    }

    /// The determinant is a *polynomial*, not a number: that is the whole point,
    /// and it is what a geometric construction produces.
    ///
    /// This is Cramer's rule, symbolically. The target mentions both unknowns, so
    /// detection picks both and the multiplier comes out as the full `a·d − b·c`.
    #[test]
    fn the_determinant_may_be_symbolic() {
        // a·x + b·y = 1, c·x + d·y = 0 over ℚ[a,b,c,d]. Determinant a·d − b·c,
        // solution x = d/(ad−bc), y = −c/(ad−bc).
        let [first, second, third, fourth, x, y] = ["a", "b", "c", "d", "x", "y"].map(MvPoly::var);
        let generators = vec![
            first
                .mul(&x)
                .unwrap()
                .add(&second.mul(&y).unwrap())
                .unwrap()
                .sub(&int(1))
                .unwrap(),
            third
                .mul(&x)
                .unwrap()
                .add(&fourth.mul(&y).unwrap())
                .unwrap(),
        ];
        let target = x.add(&y).unwrap();
        let done = eliminate(&generators, &target).expect("eliminated");
        assert_eq!(done.blocks.len(), 1);
        assert_eq!(
            done.blocks[0].unknowns,
            vec!["x".to_string(), "y".to_string()]
        );
        assert_eq!(
            done.multiplier,
            first
                .mul(&fourth)
                .unwrap()
                .sub(&second.mul(&third).unwrap())
                .unwrap(),
            "the multiplier is exactly the symbolic determinant"
        );
        // (a·d − b·c)·(x + y) = d − c.
        assert_eq!(done.residue, fourth.sub(&third).unwrap());
        assert!(identity_holds(&generators, &target));
    }

    /// Two independent blocks, which is the Euler shape: `O` from two equations
    /// and `H` from two more, with nothing shared but the coefficient ring.
    #[test]
    fn independent_blocks_are_detected_separately_and_both_applied() {
        let [px, py, qx, qy, sx, sy] = ["p", "q", "u", "v", "s", "t"].map(MvPoly::var);
        let generators = vec![
            px.clone().sub(&sx).unwrap(),
            py.clone().sub(&sy).unwrap(),
            qx.clone().sub(&sx).unwrap(),
            qy.clone().sub(&sy).unwrap(),
        ];
        // (p − q)·(p' − q') vanishes on the variety, and elimination sees it.
        let target = px.sub(&qx).unwrap().mul(&py.sub(&qy).unwrap()).unwrap();
        let blocks = detect_linear_blocks(&generators, &target);
        assert_eq!(blocks.len(), 4, "each equation determines one variable");
        let done = eliminate(&generators, &target).expect("eliminated");
        assert!(done.residue.is_zero());
        assert!(identity_holds(&generators, &target));
    }

    /// A target that linear algebra genuinely cannot settle keeps a residue, and
    /// the identity still holds — a residue is a handover, not a verdict.
    #[test]
    fn an_unsettled_target_keeps_a_residue_and_still_recombines() {
        let (x, free) = (MvPoly::var("x"), MvPoly::var("s"));
        let generators = vec![x.sub(&free).unwrap()];
        let target = free.mul(&free).unwrap().sub(&int(2)).unwrap();
        let done = eliminate(&generators, &target).expect("eliminated");
        assert!(!done.residue.is_zero(), "s² − 2 is not in (x − s)");
        assert!(identity_holds(&generators, &target));
    }

    /// A variable that appears squared in any generator is not a candidate, so a
    /// nonlinear system is left entirely alone rather than mis-solved.
    #[test]
    fn a_nonlinear_system_yields_no_block() {
        let x = MvPoly::var("x");
        let generators = vec![x.mul(&x).unwrap().sub(&int(2)).unwrap()];
        assert!(detect_linear_blocks(&generators, &x).is_empty());
        let done = eliminate(&generators, &x).expect("eliminated");
        assert_eq!(done.multiplier, int(1));
        assert_eq!(done.residue, x);
    }

    /// The joint-degree test is the one that is easy to get wrong: `x·y` has
    /// degree one in each variable and is quadratic in the pair, so a 2×2 block
    /// over `{x, y}` must be refused even though `degree_in` says one everywhere.
    ///
    /// What detection falls back to is the 1×1 block, which is legitimate —
    /// `x·y − 1` really is affine in `x` alone, with coefficient `y` — and that is
    /// the distinction the joint test draws.
    #[test]
    fn a_bilinear_generator_is_not_treated_as_affine() {
        let (x, y) = (MvPoly::var("x"), MvPoly::var("y"));
        let generators = vec![x.mul(&y).unwrap().sub(&int(1)).unwrap(), x.sub(&y).unwrap()];
        let target = x.add(&y).unwrap();
        let blocks = detect_linear_blocks(&generators, &target);
        assert_eq!(blocks.len(), 1, "one component, one block: {blocks:?}");
        assert_ne!(
            blocks[0].unknowns,
            vec!["x".to_string(), "y".to_string()],
            "a bilinear row must not be inverted as a jointly linear one"
        );
        assert!(identity_holds(&generators, &target));

        // And the row on its own admits no 2×2 block at all.
        assert!(
            super::coefficient_matrix(&generators, &[0], &["x".to_string(), "y".to_string()])
                .is_none(),
            "x·y − 1 is not affine in {{x, y}} jointly"
        );
    }

    /// A singular block is never reported, because Cramer's rule would divide by
    /// zero and the multiplier would be the zero polynomial — which multiplies
    /// every target into the ideal and would prove anything.
    #[test]
    fn a_singular_system_is_refused() {
        let (x, y) = (MvPoly::var("x"), MvPoly::var("y"));
        let generators = vec![
            x.add(&y).unwrap().sub(&int(1)).unwrap(),
            int(2)
                .mul(&x)
                .unwrap()
                .add(&int(2).mul(&y).unwrap())
                .unwrap()
                .sub(&int(2))
                .unwrap(),
        ];
        let blocks = detect_linear_blocks(&generators, &x.add(&y).unwrap());
        assert!(
            blocks.iter().all(|block| block.unknowns.len() < 2),
            "the rows are proportional, so no 2x2 block may be reported: {blocks:?}"
        );
        assert!(
            blocks.iter().all(|block| !block.determinant.is_zero()),
            "a singular block would make the multiplier zero, which multiplies every target \
             into every ideal"
        );
    }

    /// A hand-written block that is *wrong* must not produce an accepted
    /// identity. This is the control on the whole design: detection is untrusted,
    /// so being handed a bad decomposition has to fail loudly rather than emit a
    /// certificate that expands to something else.
    #[test]
    fn a_hand_written_block_that_does_not_hold_is_refused() {
        let (x, y) = (MvPoly::var("x"), MvPoly::var("y"));
        let generators = vec![x.mul(&y).unwrap().sub(&int(1)).unwrap()];
        let block = super::LinearBlock {
            unknowns: vec!["x".to_string()],
            rows: vec![0],
            determinant: MvPoly::var("y"),
        };
        // This one is legitimate: x·y − 1 IS affine in x with coefficient y, so
        // y·x = 1 + (x·y − 1) and the residue is the constant 1.
        let done = eliminate_blocks(&generators, &x, vec![block]).expect("eliminated");
        assert_eq!(done.multiplier, y);
        assert_eq!(done.residue, int(1));
        let left = done.multiplier.mul(&x).expect("product");
        let right = combination(&done.cofactors, &generators)
            .expect("combination")
            .add(&done.residue)
            .expect("sum");
        assert_eq!(left, right);

        // This one is not: the declared determinant is a lie.
        let liar = super::LinearBlock {
            unknowns: vec!["x".to_string()],
            rows: vec![0],
            determinant: MvPoly::var("x"),
        };
        assert!(
            eliminate_blocks(&generators, &x, vec![liar]).is_none(),
            "a block whose declared determinant is not the real one must be refused"
        );
    }
}
