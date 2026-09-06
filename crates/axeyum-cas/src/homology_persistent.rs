//! Persistent homology of a filtration, over `F_2`.
//!
//! # What this computes
//!
//! A **filtration** is a total order on the simplices of a complex, given
//! here as `Vec<Vec<usize>>` (each entry a sorted, deduplicated vertex list),
//! such that every face of a simplex appears strictly before it -- the
//! standard requirement that lets each prefix of the list be read as an
//! actual sub-complex. [`persistent_homology`] validates this
//! ([`build_boundary_columns`] returns `None` on a violation) and then runs
//! the **standard column-reduction algorithm** (Zomorodian-Carlsson) over
//! `F_2`: each simplex's boundary, as a set of earlier-simplex indices, is a
//! column; columns are reduced left to right by adding (symmetric
//! difference, since coefficients are mod 2) an earlier column with the same
//! "low" (its highest surviving index) until either the column empties out
//! (a birth: a new cycle, possibly never killed) or its low is new (a death:
//! it kills the class born at that low).
//!
//! From the reduction: a **finite bar** is a pair `(birth, death)` for every
//! `low -> col` entry recorded during reduction, at dimension
//! `dim(simplex[birth])`; an **essential (infinite) bar** is any index whose
//! column reduces to empty and that is never later selected as a `low`.
//!
//! # What is certified
//!
//! [`PersistenceCertificate::verify`] re-derives every claim:
//!
//! - re-runs the reduction from `self.filtration` alone (an independent
//!   re-derivation, not a copy: [`reduce_persistence`] is deterministic, so a
//!   forged `low_to_col` disagrees with what a fresh run produces) and
//!   compares to the recorded `low_to_col` map (`reduction_matches`);
//! - recomputes the finite and essential bars from that (verified)
//!   `low_to_col` and compares to the recorded `pairs`/`essential`
//!   (`pairs_match`);
//! - checks **Euler-characteristic consistency at every filtration step**:
//!   the alternating sum of the prefix complex's own simplex counts must
//!   equal the alternating sum, by dimension, of the persistence diagram's
//!   bars alive at that step (`euler_characteristic_at_every_step`) -- a
//!   genuine additional identity (Euler-Poincare for every sub-level
//!   complex), not a restatement of the reduction.
//!
//! # Cost profile
//!
//! The reduction is `O(n^3)` worst case (each of `n` columns can be reduced
//! against up to `n` others, each an `O(n)` symmetric difference); the
//! Euler-characteristic guard is `O(n^2)` (checked at every one of `n`
//! steps). No Smith form, cofactor determinant, or `Rational` arithmetic is
//! involved anywhere in this module -- it is pure `F_2` combinatorics on
//! `BTreeSet<usize>`.

use std::collections::{BTreeMap, BTreeSet};

use super::SimplicialComplex;

/// Build, for every simplex in filtration order, its boundary column: the
/// set of indices (into `filtration`) of its codimension-1 faces. Returns
/// `None` if the filtration is invalid: a face missing from the list
/// entirely, or appearing at or after the simplex it bounds (the "every face
/// before its cofaces" requirement).
fn build_boundary_columns(filtration: &[Vec<usize>]) -> Option<Vec<BTreeSet<usize>>> {
    let mut index_of: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    for (i, simplex) in filtration.iter().enumerate() {
        let mut sorted = simplex.clone();
        sorted.sort_unstable();
        sorted.dedup();
        if sorted.len() != simplex.len() {
            return None; // a repeated vertex within one simplex: not a valid simplex
        }
        if index_of.insert(sorted, i).is_some() {
            return None; // the same simplex appears twice in the filtration
        }
    }
    let mut columns = Vec::with_capacity(filtration.len());
    for (i, simplex) in filtration.iter().enumerate() {
        let mut column = BTreeSet::new();
        if simplex.len() > 1 {
            for l in 0..simplex.len() {
                let mut face = simplex.clone();
                face.remove(l);
                let &face_idx = index_of.get(&face)?;
                if face_idx >= i {
                    return None; // a face appearing at or after its coface
                }
                column.insert(face_idx);
            }
        }
        columns.push(column);
    }
    Some(columns)
}

/// Run the standard column-reduction algorithm over `F_2` on the boundary
/// columns of a (already validated) filtration. Returns the fully reduced
/// columns and the `low -> col` map recorded during reduction.
fn reduce_persistence(
    mut columns: Vec<BTreeSet<usize>>,
) -> (Vec<BTreeSet<usize>>, BTreeMap<usize, usize>) {
    let mut low_to_col: BTreeMap<usize, usize> = BTreeMap::new();
    for j in 0..columns.len() {
        loop {
            let Some(&low) = columns[j].iter().next_back() else {
                break; // column emptied out: a birth (possibly essential)
            };
            let Some(&pivot_col) = low_to_col.get(&low) else {
                low_to_col.insert(low, j);
                break; // a new low: (low, j) is a finite pair
            };
            let other = columns[pivot_col].clone();
            columns[j] = columns[j].symmetric_difference(&other).copied().collect();
        }
    }
    (columns, low_to_col)
}

/// Derive `(finite pairs, essential births)` from a fully reduced column set
/// and its `low_to_col` map, each finite pair as `(dimension, birth, death)`
/// and each essential birth as `(dimension, birth)`, both sorted. Shared by
/// [`persistent_homology`] (the producer) and [`pairs_match`] (the guard
/// that re-derives the same thing from a certificate under test).
fn derive_pairs(
    filtration: &[Vec<usize>],
    reduced: &[BTreeSet<usize>],
    low_to_col: &BTreeMap<usize, usize>,
) -> (Vec<(usize, usize, usize)>, Vec<(usize, usize)>) {
    let mut pairs: Vec<(usize, usize, usize)> = low_to_col
        .iter()
        .map(|(&birth, &death)| (filtration[birth].len() - 1, birth, death))
        .collect();
    pairs.sort_unstable();

    let mut essential: Vec<(usize, usize)> = (0..filtration.len())
        .filter(|&i| reduced[i].is_empty() && !low_to_col.contains_key(&i))
        .map(|i| (filtration[i].len() - 1, i))
        .collect();
    essential.sort_unstable();

    (pairs, essential)
}

/// A checkable certificate of the persistent homology (over `F_2`) of a
/// filtration. See the module documentation for what
/// [`verify`](Self::verify) re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistenceCertificate {
    /// The filtration: simplices (sorted vertex lists) in insertion order.
    pub filtration: Vec<Vec<usize>>,
    /// The `low -> col` map the standard reduction produced: `low_to_col[l] =
    /// j` records that column `j`, once fully reduced, has low `l` -- i.e.
    /// the pair `(birth = l, death = j)`.
    pub low_to_col: BTreeMap<usize, usize>,
    /// Finite bars, as `(dimension, birth, death)`, sorted.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, as `(dimension, birth)`, sorted.
    pub essential: Vec<(usize, usize)>,
}

/// The result of a successful [`PersistenceCertificate::verify`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PersistenceReport {
    /// Finite bars, recomputed.
    pub pairs: Vec<(usize, usize, usize)>,
    /// Essential (infinite) bars, recomputed.
    pub essential: Vec<(usize, usize)>,
}

/// Compute the persistent homology (over `F_2`) of `filtration`.
///
/// Returns `None` if `filtration` is not a valid filtration: a face missing
/// from the list, a face at or after its own coface, a repeated simplex, or
/// a simplex with a repeated vertex.
#[must_use]
pub fn persistent_homology(filtration: &[Vec<usize>]) -> Option<PersistenceCertificate> {
    let normalized: Vec<Vec<usize>> = filtration
        .iter()
        .map(|s| {
            let mut sorted = s.clone();
            sorted.sort_unstable();
            sorted
        })
        .collect();
    let columns = build_boundary_columns(&normalized)?;
    let (reduced, low_to_col) = reduce_persistence(columns);
    let (pairs, essential) = derive_pairs(&normalized, &reduced, &low_to_col);

    Some(PersistenceCertificate {
        filtration: normalized,
        low_to_col,
        pairs,
        essential,
    })
}

/// Guard: re-running the reduction on `self.filtration` alone reproduces the
/// recorded `low_to_col` map exactly.
fn reduction_matches(certificate: &PersistenceCertificate) -> Result<Vec<BTreeSet<usize>>, String> {
    let columns = build_boundary_columns(&certificate.filtration)
        .ok_or_else(|| "the recorded filtration is not a valid filtration".to_string())?;
    let (reduced, low_to_col) = reduce_persistence(columns);
    if low_to_col != certificate.low_to_col {
        return Err(format!(
            "reduction mismatch: fresh reduction gives low_to_col {low_to_col:?}, certificate claims {:?}",
            certificate.low_to_col
        ));
    }
    Ok(reduced)
}

/// Guard: the recorded `pairs`/`essential` are exactly what
/// [`derive_pairs`]-style derivation gives from the (already verified)
/// `low_to_col` and `reduced` columns.
fn pairs_match(
    certificate: &PersistenceCertificate,
    reduced: &[BTreeSet<usize>],
) -> Result<(Vec<(usize, usize, usize)>, Vec<(usize, usize)>), String> {
    let (pairs, essential) = derive_pairs(&certificate.filtration, reduced, &certificate.low_to_col);
    if pairs != certificate.pairs {
        return Err(format!(
            "pairs mismatch: recomputed {pairs:?}, certificate claims {:?}",
            certificate.pairs
        ));
    }
    if essential != certificate.essential {
        return Err(format!(
            "essential bar mismatch: recomputed {essential:?}, certificate claims {:?}",
            certificate.essential
        ));
    }
    Ok((pairs, essential))
}

/// Guard: at every prefix length `m` in `1..=n`, the alternating sum of the
/// prefix complex's own simplex counts by dimension equals the alternating
/// sum, by dimension, of the persistence diagram's bars alive at step `m`
/// (born by index `m - 1`, not yet killed by index `m`) -- the
/// Euler-Poincare identity for every sub-level complex in the filtration.
fn euler_characteristic_at_every_step(certificate: &PersistenceCertificate) -> Result<(), String> {
    let n = certificate.filtration.len();
    let mut dim_counts = vec![0i128; n]; // dim_counts[d] = running count of dimension-d simplices
    let mut complex_euler: Vec<i128> = Vec::with_capacity(n);
    let mut running = 0i128;
    for simplex in &certificate.filtration {
        let dim = simplex.len() - 1;
        dim_counts[dim] += 1;
        running += if dim % 2 == 0 { 1 } else { -1 };
        complex_euler.push(running);
    }

    for m in 1..=n {
        let bars_euler: i128 = certificate
            .pairs
            .iter()
            .filter(|&&(_, birth, death)| birth < m && death >= m)
            .map(|&(dim, _, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
            .sum::<i128>()
            + certificate
                .essential
                .iter()
                .filter(|&&(_, birth)| birth < m)
                .map(|&(dim, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
                .sum::<i128>();
        if bars_euler != complex_euler[m - 1] {
            return Err(format!(
                "Euler characteristic mismatch at filtration step {m}: complex gives {}, the persistence diagram gives {bars_euler}",
                complex_euler[m - 1]
            ));
        }
    }
    Ok(())
}

impl PersistenceCertificate {
    /// Re-derive every claim in this certificate from `self.filtration`
    /// alone. See the module documentation for exactly what each guard would
    /// miss if it were absent.
    ///
    /// # Errors
    ///
    /// Returns a distinct, descriptive `Err(String)` for whichever guard
    /// fails first: an invalid filtration, a reduction mismatch, a
    /// pairs/essential mismatch, or an Euler-characteristic inconsistency at
    /// some filtration step.
    pub fn verify(&self) -> Result<PersistenceReport, String> {
        let reduced = reduction_matches(self)?;
        let (pairs, essential) = pairs_match(self, &reduced)?;
        euler_characteristic_at_every_step(self)?;
        Ok(PersistenceReport { pairs, essential })
    }
}

/// Build a [`SimplicialComplex`] from the first `m` simplices of a
/// filtration -- a convenience for constructing test fixtures and for a
/// caller who wants the actual complex at some step (not exercised by
/// [`verify`](PersistenceCertificate::verify), which works from simplex
/// counts alone).
#[must_use]
pub fn prefix_complex(filtration: &[Vec<usize>], m: usize) -> Option<SimplicialComplex> {
    let maximal: Vec<Vec<usize>> = filtration.get(..m)?.to_vec();
    // `from_maximal_simplices` closes under subsets already, and a prefix of
    // a valid filtration consists of simplices whose every face already
    // appears earlier in the same prefix, so treating each one as its own
    // "maximal" simplex and letting the constructor re-derive subsets is
    // safe (it will just re-insert already-present faces).
    SimplicialComplex::from_maximal_simplices(&maximal)
}

#[cfg(test)]
mod tests {
    use super::persistent_homology;

    /// A filtration building the 3-vertex circle then filling it in: three
    /// vertices, then two edges, then the closing edge (which creates the
    /// `H_1` class), then the 2-simplex (which kills it).
    fn circle_then_fill() -> Vec<Vec<usize>> {
        vec![
            vec![0],
            vec![1],
            vec![2],
            vec![0, 1],
            vec![1, 2],
            vec![0, 2], // the closing edge, index 5
            vec![0, 1, 2], // the triangle, index 6
        ]
    }

    #[test]
    fn circle_then_fill_has_one_h1_bar_born_at_the_closing_edge() {
        let filtration = circle_then_fill();
        let certificate = persistent_homology(&filtration).expect("valid filtration");
        certificate.verify().expect("certificate verifies");

        let h1_bars: Vec<_> = certificate
            .pairs
            .iter()
            .filter(|&&(dim, _, _)| dim == 1)
            .collect();
        assert_eq!(h1_bars.len(), 1, "expected exactly one H_1 bar");
        assert_eq!(*h1_bars[0], (1, 5, 6), "born at the closing edge, dying at the triangle");

        // H_0: one essential bar (the whole complex's single surviving
        // component), and two finite bars (the merges as edges are added).
        let h0_essential: Vec<_> = certificate
            .essential
            .iter()
            .filter(|&&(dim, _)| dim == 0)
            .collect();
        assert_eq!(h0_essential.len(), 1);
        let h0_pairs: Vec<_> = certificate
            .pairs
            .iter()
            .filter(|&&(dim, _, _)| dim == 0)
            .collect();
        assert_eq!(h0_pairs.len(), 2);
    }

    /// The 7-vertex torus triangulation's own vertex/edge/triangle lists,
    /// concatenated in an order that is a valid filtration (every edge's
    /// vertices precede it; every triangle's edges precede it) -- vertices,
    /// then edges sorted lexicographically, then the 14 triangles in the
    /// order `homology.rs`'s own torus fixture lists them.
    fn torus_filtration() -> Vec<Vec<usize>> {
        let triangles: &[&[usize]] = &[
            &[0, 1, 3],
            &[0, 1, 5],
            &[0, 2, 3],
            &[0, 2, 6],
            &[0, 4, 5],
            &[0, 4, 6],
            &[1, 2, 4],
            &[1, 2, 6],
            &[1, 3, 4],
            &[1, 5, 6],
            &[2, 3, 5],
            &[2, 4, 5],
            &[3, 4, 6],
            &[3, 5, 6],
        ];
        let mut edges: std::collections::BTreeSet<[usize; 2]> = std::collections::BTreeSet::new();
        for triangle in triangles {
            for i in 0..3 {
                for j in (i + 1)..3 {
                    let mut pair = [triangle[i], triangle[j]];
                    pair.sort_unstable();
                    edges.insert(pair);
                }
            }
        }
        let mut filtration: Vec<Vec<usize>> = (0..7).map(|v| vec![v]).collect();
        filtration.extend(edges.iter().map(|e| e.to_vec()));
        filtration.extend(triangles.iter().map(|t| t.to_vec()));
        filtration
    }

    #[test]
    fn torus_filtration_verifies_and_matches_its_own_euler_characteristic() {
        let filtration = torus_filtration();
        assert_eq!(filtration.len(), 7 + 21 + 14);
        let certificate = persistent_homology(&filtration).expect("valid filtration");
        certificate.verify().expect("certificate verifies");
        // The full complex (all 42 simplices) has Euler characteristic 0
        // (the torus): 7 - 21 + 14 = 0. Confirm the diagram's own bars sum
        // to this at the final step, as a sanity check beside `verify`'s
        // own (per-step) Euler-characteristic guard.
        let n = filtration.len();
        let alive_euler: i128 = certificate
            .pairs
            .iter()
            .filter(|&&(_, birth, death)| birth < n && death >= n)
            .map(|&(dim, _, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
            .sum::<i128>()
            + certificate
                .essential
                .iter()
                .filter(|&&(_, birth)| birth < n)
                .map(|&(dim, _)| if dim % 2 == 0 { 1i128 } else { -1i128 })
                .sum::<i128>();
        assert_eq!(alive_euler, 0);
    }

    #[test]
    fn an_out_of_order_filtration_is_refused() {
        // The edge {0, 1} appears BEFORE vertex 1: invalid.
        let filtration = vec![vec![0], vec![0, 1], vec![1]];
        assert!(persistent_homology(&filtration).is_none());
    }

    #[test]
    fn a_filtration_with_a_missing_face_is_refused() {
        // The triangle's edge {1, 2} never appears at all.
        let filtration = vec![vec![0], vec![1], vec![2], vec![0, 1], vec![0, 2], vec![0, 1, 2]];
        assert!(persistent_homology(&filtration).is_none());
    }

    /// ADVERSARIAL. Forge only the recorded `low_to_col` map (and the pairs
    /// derived from it, so `pairs_match` alone would not catch this),
    /// leaving `filtration` genuine. `reduction_matches` re-runs the
    /// reduction and disagrees. Confirmed by mutation: disabling only
    /// `reduction_matches` leaves every other test in this module green.
    #[test]
    fn verify_refuses_a_forged_low_to_col_with_matching_forged_pairs() {
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(certificate.verify().is_ok(), "genuine certificate must verify");

        // Forge low_to_col to swap the death of the (5, 6) pair to a bogus
        // (5, 4): 4 is not >= 5, so this claims edge 4 (already present)
        // kills a class born at 5, an impossible ordering violation the
        // reduction itself would never produce.
        certificate.low_to_col.insert(5, 4);
        certificate.pairs = vec![(1, 5, 4)]
            .into_iter()
            .chain(certificate.pairs.iter().copied().filter(|&(_, b, _)| b != 5))
            .collect();
        certificate.pairs.sort_unstable();
        let err = certificate
            .verify()
            .expect_err("a forged low_to_col must be refused");
        assert!(err.contains("reduction mismatch"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only `essential`, leaving `low_to_col` and `pairs`
    /// genuine: `pairs_match` recomputes essential bars from the (verified)
    /// reduction and disagrees. Confirmed by mutation: disabling only the
    /// essential-bar comparison in `pairs_match` leaves every other test in
    /// this module green.
    #[test]
    fn verify_refuses_a_forged_essential_bar() {
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(certificate.verify().is_ok(), "genuine certificate must verify");

        certificate.essential.push((1, 6)); // a fabricated infinite H_1 bar
        certificate.essential.sort_unstable();
        let err = certificate
            .verify()
            .expect_err("a forged essential bar must be refused");
        assert!(err.contains("essential"), "got: {err}");
    }

    /// ADVERSARIAL. Forge only `pairs` to swap a death index, keeping it
    /// consistent with what `low_to_col` alone implies (by ALSO forging
    /// `low_to_col` the same way) so this is really testing that
    /// `euler_characteristic_at_every_step` fires as a genuinely separate
    /// identity: shift the closing edge's death from the triangle (6) to
    /// one step earlier -- a value not reachable by any reduction of this
    /// filtration, but constructed here to isolate the Euler-characteristic
    /// guard specifically by leaving `reduction_matches` unable to run (it
    /// would already refuse this forgery too; this test instead calls the
    /// guard function directly with a hand-built inconsistent certificate,
    /// the same isolation pattern the parent module uses for its own
    /// hard-to-isolate guards).
    #[test]
    fn euler_characteristic_guard_refuses_a_bar_alive_at_the_wrong_step_directly() {
        use super::euler_characteristic_at_every_step;
        let filtration = circle_then_fill();
        let mut certificate = persistent_homology(&filtration).expect("valid filtration");
        assert!(euler_characteristic_at_every_step(&certificate).is_ok());

        // Move the (1, 5, 6) bar's death one step earlier, to 5 itself --
        // an edge cannot die at its own birth index, so this both breaks
        // the Euler count at step 6 (the class is now claimed dead before
        // the triangle that actually kills it arrives) and is never
        // producible by a genuine reduction.
        certificate.pairs = certificate
            .pairs
            .iter()
            .map(|&(dim, birth, death)| {
                if (dim, birth, death) == (1, 5, 6) {
                    (dim, birth, 5)
                } else {
                    (dim, birth, death)
                }
            })
            .collect();
        let err = euler_characteristic_at_every_step(&certificate)
            .expect_err("a bar alive at the wrong step must be refused");
        assert!(err.contains("Euler characteristic mismatch"), "got: {err}");
    }
}
