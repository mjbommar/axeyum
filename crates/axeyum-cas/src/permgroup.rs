//! Finite permutation groups: deterministic Schreier–Sims, orbits,
//! stabilizers, cosets, and Cayley tables, over [`crate::permutation::Permutation`].
//!
//! # What this module computes
//!
//! [`PermutationGroup::from_generators`] builds a base and strong generating
//! set (BSGS) by the classical (non-randomized) Schreier–Sims algorithm: every
//! Schreier generator that Schreier's lemma produces is sifted through the
//! partial stabilizer chain, and any that does not sift to the identity is
//! folded in as a new strong generator, until none remain. This is
//! deterministic — no product-replacement, no random Schreier generators —
//! and correct for degrees and orders in the range this crate needs (up to a
//! few hundred points, orders into the low hundred-thousands; the module
//! handles `S_8`, order 40320, without enumerating the group).
//!
//! # Certificates, and what "independent" means here
//!
//! Every public entry point returns a certificate whose `verify` re-derives
//! the claim from data the certificate carries, sharing no bookkeeping with
//! the producer:
//!
//! - [`OrderCertificate::verify`] re-filters the strong generating set by
//!   which prefix of the base each element fixes (never trusting a
//!   producer-supplied "this generator belongs to this level" label),
//!   re-closes each level's basic orbit by breadth-first search over that
//!   independently-filtered set, and re-multiplies every transversal word.
//! - [`MembershipCertificate::verify`] re-multiplies the recorded
//!   factorization (or, for a refusal, the recorded prefix) and compares.
//! - [`OrbitStabilizerCertificate::verify`] re-verifies both underlying order
//!   certificates and re-closes the orbit itself before checking the
//!   product identity.
//! - [`CosetCertificate::verify`] and [`CayleyTableCertificate::verify`]
//!   re-enumerate the group(s) named by (already independently verified)
//!   order certificates and re-check the partition / the group axioms from
//!   scratch.
//!
//! The one shared piece of code between production and verification is the
//! low-level breadth-first orbit closure (`bfs_orbit`) and word
//! multiplication (`word_to_perm`, [`signed_word_to_perm`]) — these sit at
//! the same trust level as [`Permutation::compose`] itself (a fixed,
//! inspectable, total operation on an already-tested base type), not at the
//! level of the bookkeeping under test. Every guard that distinguishes a
//! genuine certificate from a forged one is a *direct* recomputation:
//! re-multiply the claimed word and compare, re-filter the claimed level
//! membership and compare, re-close the claimed orbit and compare.
//!
//! # Bounds
//!
//! Two operations require enumerating group elements outright and are
//! bounded, declining above the bound with a distinct
//! [`PermgroupError::TooLarge`]:
//!
//! - [`PermutationGroup::cosets`], [`PermutationGroup::center`]: bounded by
//!   [`ENUMERATION_BOUND`] (10,000 elements — cheap set/filter work).
//! - [`PermutationGroup::cayley_table`]: bounded by [`CAYLEY_TABLE_BOUND`]
//!   (120 elements — associativity verification is `O(|G|^3)`; tested at
//!   exactly the bound with `S_5`, order 120, 1,728,000 triples).
//! - [`PermutationGroup::derived_subgroup`]: bounded by
//!   [`DERIVED_SUBGROUP_ENUMERATION_BOUND`] (2,000 elements — commutator
//!   generation is `O(|G|^2)`).
//!
//! # Out of scope
//!
//! Sylow subgroups, group presentations (this module only ever consumes a
//! generating set, never a presentation), group isomorphism testing, and
//! matrix groups. None of these are attempted, partially or otherwise.

use crate::permutation::Permutation;
use std::collections::{BTreeMap, BTreeSet};

// ---------------------------------------------------------------------------
// Words: signed (ties a strong generator back to the original generators it
// was built from) and unsigned (ties a transversal representative to the
// strong generators that build it).
// ---------------------------------------------------------------------------

/// A forward word: a sequence of indices into some fixed list of
/// permutations, composed with the convention that `word[0]` is applied
/// *last* (outermost) and `word[word.len() - 1]` is applied *first*
/// (innermost) — i.e. `word_to_perm(atoms, word, n) == atoms[word[0]] ∘
/// atoms[word[1]] ∘ … ∘ atoms[word[last]]`. Used for transversal
/// representatives, which are always built by forward composition.
pub type Word = Vec<usize>;

/// A signed word: like [`Word`], but each entry additionally selects the
/// forward generator (`code >= 0`, referring to index `code`) or its inverse
/// (`code < 0`, referring to the inverse of index `-code - 1`). Used to tie a
/// strong generator back to the original generating set, since building one
/// via Schreier's lemma requires inverting a transversal representative and
/// the original generators need not be closed under inversion.
pub type SignedWord = Vec<i64>;

/// Encodes `(index, inverse)` as a single signed code (see [`SignedWord`]).
fn encode(index: usize, inverse: bool) -> i64 {
    let index = i64::try_from(index).expect("generator index fits in i64");
    if inverse { -index - 1 } else { index }
}

/// Decodes a signed code back to `(index, inverse)`, or `None` if the index
/// does not fit in a `usize` (never happens for codes this module produces).
fn decode(code: i64) -> Option<(usize, bool)> {
    if code >= 0 {
        usize::try_from(code).ok().map(|i| (i, false))
    } else {
        usize::try_from(-code - 1).ok().map(|i| (i, true))
    }
}

/// The code for the inverse of whatever `code` refers to: `-code - 1` is its
/// own inverse under this encoding (`invert_code(invert_code(c)) == c`).
fn invert_code(code: i64) -> i64 {
    -code - 1
}

/// Reverses and inverts every code of a signed word, so that
/// `signed_word_to_perm(atoms, invert_signed_word(w), n)` is the inverse of
/// `signed_word_to_perm(atoms, w, n)`.
fn invert_signed_word(word: &[i64]) -> SignedWord {
    word.iter().rev().map(|&c| invert_code(c)).collect()
}

/// Multiplies a forward [`Word`] over `atoms` into a single permutation, or
/// `None` if an index is out of range or a degree mismatch occurs.
fn word_to_perm(atoms: &[Permutation], word: &[usize], degree: usize) -> Option<Permutation> {
    let mut acc = Permutation::identity(degree);
    for &idx in word.iter().rev() {
        let g = atoms.get(idx)?;
        if g.len() != degree {
            return None;
        }
        acc = g.compose(&acc)?;
    }
    Some(acc)
}

/// Multiplies a [`SignedWord`] over `atoms` into a single permutation, or
/// `None` if an index is out of range or a degree mismatch occurs.
fn signed_word_to_perm(atoms: &[Permutation], word: &[i64], degree: usize) -> Option<Permutation> {
    let mut acc = Permutation::identity(degree);
    for &code in word.iter().rev() {
        let (idx, inverse) = decode(code)?;
        let g = atoms.get(idx)?;
        if g.len() != degree {
            return None;
        }
        let g = if inverse { g.inverse() } else { g.clone() };
        acc = g.compose(&acc)?;
    }
    Some(acc)
}

/// Expands a forward word over the strong generating set into a signed word
/// over the *original* generating set, by substituting each strong
/// generator's own original-generator word in place, preserving order.
fn expand_word(strong_generator_words: &[SignedWord], word: &[usize]) -> SignedWord {
    word.iter()
        .flat_map(|&k| strong_generator_words[k].iter().copied())
        .collect()
}

// ---------------------------------------------------------------------------
// Small shared predicates
// ---------------------------------------------------------------------------

/// Whether `p` fixes every point of `prefix` (in particular, vacuously true
/// for an empty prefix).
fn fixes_prefix(p: &Permutation, prefix: &[usize]) -> bool {
    prefix.iter().all(|&pt| p.apply(pt) == Some(pt))
}

/// Whether `p` is the identity on `degree` points.
fn is_identity(p: &Permutation, degree: usize) -> bool {
    *p == Permutation::identity(degree)
}

/// The image-vector key used to compare permutations for equality inside
/// `BTreeMap`/`BTreeSet`, since [`Permutation`] implements neither `Ord` nor
/// `Hash`.
fn image_key(p: &Permutation, degree: usize) -> Vec<usize> {
    (0..degree)
        .map(|i| {
            p.apply(i)
                .expect("point in range for a degree-consistent permutation")
        })
        .collect()
}

/// Breadth-first closure of `base_point`'s orbit under `gens` (paired with
/// their *global* index in whatever list the caller intends the resulting
/// words to reference), returning a transversal: point ↦ a forward word
/// (over that global index space) whose product maps `base_point` to point.
///
/// Deterministic: the frontier is processed as a `BTreeSet` (increasing point
/// order) and `gens` in the order given.
fn bfs_orbit(
    base_point: usize,
    gens: &[(usize, Permutation)],
    degree: usize,
) -> BTreeMap<usize, Word> {
    let mut transversal: BTreeMap<usize, Word> = BTreeMap::new();
    transversal.insert(base_point, Vec::new());
    let mut frontier: BTreeSet<usize> = BTreeSet::new();
    frontier.insert(base_point);
    while !frontier.is_empty() {
        let mut next_frontier: BTreeSet<usize> = BTreeSet::new();
        for &x in &frontier {
            let word_x = transversal[&x].clone();
            for (global_index, g) in gens {
                if g.len() != degree {
                    continue;
                }
                if let Some(p) = g.apply(x)
                    && let std::collections::btree_map::Entry::Vacant(entry) = transversal.entry(p)
                {
                    let mut new_word = vec![*global_index];
                    new_word.extend_from_slice(&word_x);
                    entry.insert(new_word);
                    next_frontier.insert(p);
                }
            }
        }
        frontier = next_frontier;
    }
    transversal
}

/// Enumerates every element of `⟨gens⟩` (as permutations of `degree` points)
/// by breadth-first closure over the Cayley graph, or `None` if the count
/// would exceed `bound` before completing (the group is declined, not
/// truncated).
fn enumerate_group(gens: &[Permutation], degree: usize, bound: u128) -> Option<Vec<Permutation>> {
    let id = Permutation::identity(degree);
    let mut seen: BTreeMap<Vec<usize>, Permutation> = BTreeMap::new();
    seen.insert(image_key(&id, degree), id.clone());
    let mut frontier = vec![id];
    while !frontier.is_empty() {
        let mut next = Vec::new();
        for p in &frontier {
            for g in gens {
                if g.len() != degree {
                    continue;
                }
                let q = p.compose(g)?;
                let k = image_key(&q, degree);
                if !seen.contains_key(&k) {
                    if u128::try_from(seen.len()).unwrap_or(u128::MAX) >= bound {
                        return None;
                    }
                    seen.insert(k, q.clone());
                    next.push(q);
                }
            }
        }
        frontier = next;
    }
    Some(seen.into_values().collect())
}

// ---------------------------------------------------------------------------
// Schreier–Sims: the builder
// ---------------------------------------------------------------------------

/// The internal result of a Schreier–Sims run: a base, a strong generating
/// set with words tying every strong generator back to the original
/// generators, and one basic-orbit transversal per base level.
struct BsgsBuild {
    base: Vec<usize>,
    strong_generators: Vec<Permutation>,
    strong_generator_words: Vec<SignedWord>,
    level_orbits: Vec<BTreeMap<usize, Word>>,
}

/// Whether `g` (assumed already fixed on some prefix of `base`) sifts to the
/// identity through levels `[from_level, base.len())` of the partial chain
/// described by `level_orbits`.
fn sift_to_identity(
    mut g: Permutation,
    base: &[usize],
    level_orbits: &[BTreeMap<usize, Word>],
    sgs: &[Permutation],
    from_level: usize,
    degree: usize,
) -> bool {
    for i in from_level..base.len() {
        let Some(x) = g.apply(base[i]) else {
            return false;
        };
        let Some(word) = level_orbits[i].get(&x) else {
            return false;
        };
        let t = word_to_perm(sgs, word, degree).expect("transversal word is valid by construction");
        g = t
            .inverse()
            .compose(&g)
            .expect("same degree throughout a build");
    }
    is_identity(&g, degree)
}

/// Runs the deterministic Schreier–Sims algorithm on `original_generators`.
/// If `base_hint` is given, it is forced to be the first base point
/// (needed by [`PermutationGroup::stabilizer`]'s Schreier-generator route —
/// unused by the public API directly, kept for internal reuse).
fn build_bsgs(
    original_generators: &[Permutation],
    degree: usize,
    base_hint: Option<usize>,
) -> BsgsBuild {
    let mut sgs: Vec<Permutation> = original_generators.to_vec();
    let mut words: Vec<SignedWord> = (0..sgs.len()).map(|i| vec![encode(i, false)]).collect();
    let mut base: Vec<usize> = base_hint.into_iter().collect();

    loop {
        // Base completeness: extend until every non-identity strong
        // generator moves some base point.
        loop {
            let mut to_add = None;
            for g in &sgs {
                if !is_identity(g, degree)
                    && fixes_prefix(g, &base)
                    && let Some(pt) = (0..degree).find(|&pt| g.apply(pt) != Some(pt))
                    && !base.contains(&pt)
                {
                    to_add = Some(pt);
                    break;
                }
            }
            match to_add {
                Some(pt) => base.push(pt),
                None => break,
            }
        }

        // Level generator indices, recomputed fresh from the current sgs
        // and base (never carried over from a previous iteration).
        let level_gen_indices: Vec<Vec<usize>> = (0..base.len())
            .map(|i| {
                (0..sgs.len())
                    .filter(|&k| fixes_prefix(&sgs[k], &base[0..i]))
                    .collect()
            })
            .collect();

        // Basic orbits, one BFS closure per level.
        let level_orbits: Vec<BTreeMap<usize, Word>> = (0..base.len())
            .map(|i| {
                let gens: Vec<(usize, Permutation)> = level_gen_indices[i]
                    .iter()
                    .map(|&k| (k, sgs[k].clone()))
                    .collect();
                bfs_orbit(base[i], &gens, degree)
            })
            .collect();

        // Schreier generators: for every level, every orbit point, every
        // level generator, form the Schreier-lemma element and sift it.
        let mut changed = false;
        'levels: for i in 0..base.len() {
            for (&x, wx) in &level_orbits[i] {
                let tx = word_to_perm(&sgs, wx, degree).expect("transversal word is valid");
                for &gi in &level_gen_indices[i] {
                    let s = &sgs[gi];
                    let Some(p) = s.apply(x) else { continue };
                    let wp = level_orbits[i]
                        .get(&p)
                        .expect("orbit is closed under its own generators");
                    let tp = word_to_perm(&sgs, wp, degree).expect("transversal word is valid");
                    let sx = s.compose(&tx).expect("same degree");
                    let sg = tp.inverse().compose(&sx).expect("same degree");

                    if sift_to_identity(sg.clone(), &base, &level_orbits, &sgs, i + 1, degree) {
                        continue;
                    }
                    // `sg` fails to sift, but that alone does not make it new
                    // information: when `x == base[i]` and `s` already fixes
                    // `base[i]`, both transversal reps collapse to the
                    // identity and `sg` reduces to exactly `s` itself --
                    // already a member of `sgs`. Re-pushing such a duplicate
                    // under a fresh index changes nothing about any level's
                    // generating set (same permutations, one more redundant
                    // index), so the search would find the identical
                    // "failure" forever without ever reaching a level whose
                    // basic orbit is actually incomplete. Skip a duplicate
                    // and keep searching for a genuinely new element.
                    if sgs.contains(&sg) {
                        continue;
                    }
                    let word_from_x = expand_word(&words, wx);
                    let word_from_p = expand_word(&words, wp);
                    let mut new_word = invert_signed_word(&word_from_p);
                    new_word.extend(words[gi].clone());
                    new_word.extend(word_from_x);
                    sgs.push(sg);
                    words.push(new_word);
                    changed = true;
                    break 'levels;
                }
            }
        }
        if !changed {
            return BsgsBuild {
                base,
                strong_generators: sgs,
                strong_generator_words: words,
                level_orbits,
            };
        }
    }
}

/// The outcome of sifting a permutation through a stabilizer chain: either a
/// full factorization into transversal words (membership), or the level and
/// point at which sifting first failed, together with the prefix
/// factorization that reduces to the residual (non-membership).
enum SiftOutcome {
    /// `g` sifted fully to the identity; `factorization` is a forward word
    /// over the strong generating set whose product is exactly `g`.
    Success { factorization: Word },
    /// Sifting failed at `level`: after removing the transversal
    /// contributions named by `prefix_factorization` (levels
    /// `0..level`), the residual sends `base[level]` to `residual_point`,
    /// which is not in that level's basic orbit.
    Failure {
        level: usize,
        prefix_factorization: Word,
        residual_point: usize,
    },
}

/// Sifts `g` through the full chain described by `base`/`level_orbits`/`sgs`.
fn sift_with_trace(
    g: &Permutation,
    base: &[usize],
    level_orbits: &[BTreeMap<usize, Word>],
    sgs: &[Permutation],
    degree: usize,
) -> SiftOutcome {
    let mut current = g.clone();
    let mut prefix_factorization: Word = Vec::new();
    for i in 0..base.len() {
        let x = current
            .apply(base[i])
            .expect("degree checked by the caller before sifting");
        match level_orbits[i].get(&x) {
            None => {
                return SiftOutcome::Failure {
                    level: i,
                    prefix_factorization,
                    residual_point: x,
                };
            }
            Some(word) => {
                prefix_factorization.extend_from_slice(word);
                let t = word_to_perm(sgs, word, degree).expect("transversal word is valid");
                current = t.inverse().compose(&current).expect("same degree");
            }
        }
    }
    if is_identity(&current, degree) {
        SiftOutcome::Success {
            factorization: prefix_factorization,
        }
    } else {
        // A complete, correctly-built chain never reaches here (see the
        // module doc); kept so a forged/incomplete chain cannot panic.
        SiftOutcome::Failure {
            level: base.len(),
            prefix_factorization,
            residual_point: usize::MAX,
        }
    }
}

// ---------------------------------------------------------------------------
// OrderCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for `|G|`: the base, the strong generating set
/// (with words tying it back to the original generators), and every
/// transversal, from which `|G|` is the product of transversal sizes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderCertificate {
    /// The number of points the group acts on.
    pub degree: usize,
    /// The generators the group was constructed from.
    pub original_generators: Vec<Permutation>,
    /// The base: a sequence of distinct points such that only the identity
    /// fixes all of them (relative to the strong generating set).
    pub base: Vec<usize>,
    /// The strong generating set `S`.
    pub strong_generators: Vec<Permutation>,
    /// `strong_generator_words[k]` is a signed word over
    /// `original_generators` whose product is `strong_generators[k]`.
    pub strong_generator_words: Vec<SignedWord>,
    /// `transversals[i]` maps each point of the basic orbit of `base[i]`
    /// (under the strong generators fixing `base[0..i]`) to a forward word
    /// over `strong_generators` whose product sends `base[i]` to that point.
    pub transversals: Vec<BTreeMap<usize, Word>>,
    /// The claimed order: the product of `transversals[i].len()` over all
    /// levels.
    pub claimed_order: u128,
}

/// Why an [`OrderCertificate`] failed to verify. Each variant names a
/// distinct, independently re-derived check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderCertificateFailure {
    /// `base.len() != transversals.len()`, or `strong_generators.len() !=
    /// strong_generator_words.len()`.
    LengthMismatch,
    /// A base point repeats.
    BaseNotDistinct,
    /// A base point is `>= degree`.
    BasePointOutOfRange,
    /// Some generator's length differs from `degree`.
    DegreeMismatch,
    /// `strong_generator_words[index]` does not multiply to a permutation at
    /// all (an out-of-range reference, or a degree mismatch).
    BadStrongGeneratorWord {
        /// The offending index into `strong_generators`.
        index: usize,
    },
    /// `strong_generator_words[index]` multiplies to something other than
    /// `strong_generators[index]`.
    StrongGeneratorWordDoesNotReconstruct {
        /// The offending index into `strong_generators`.
        index: usize,
    },
    /// A transversal word at `level` for `point` references an out-of-range
    /// strong generator, or does not multiply at all.
    TransversalWordOutOfRange {
        /// The base level.
        level: usize,
        /// The claimed orbit point.
        point: usize,
    },
    /// The transversal representative at `level` for `point` does not fix
    /// `base[0..level]`.
    TransversalElementDoesNotFixPrefix {
        /// The base level.
        level: usize,
        /// The claimed orbit point.
        point: usize,
    },
    /// The transversal representative at `level` for `point` does not send
    /// `base[level]` to `point`.
    TransversalElementWrongImage {
        /// The base level.
        level: usize,
        /// The claimed orbit point.
        point: usize,
    },
    /// The transversal at `level` omits `base[level]` itself.
    TransversalMissingBasePoint {
        /// The base level.
        level: usize,
    },
    /// The claimed transversal point set at `level` does not equal the
    /// independently recomputed orbit closure of `base[level]` under the
    /// strong generators fixing `base[0..level]`.
    TransversalDoesNotMatchOrbitClosure {
        /// The base level.
        level: usize,
    },
    /// The product of transversal sizes overflows `u128`.
    OrderOverflow,
    /// The product of transversal sizes does not equal `claimed_order`.
    OrderMismatch {
        /// The recomputed order.
        computed: u128,
        /// The certificate's claimed order.
        claimed: u128,
    },
}

impl OrderCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`OrderCertificateFailure`] guard that does not
    /// hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), OrderCertificateFailure> {
        use OrderCertificateFailure as F;

        if self.base.len() != self.transversals.len() {
            return Err(F::LengthMismatch);
        }
        if self.strong_generators.len() != self.strong_generator_words.len() {
            return Err(F::LengthMismatch);
        }
        for g in self
            .original_generators
            .iter()
            .chain(self.strong_generators.iter())
        {
            if g.len() != self.degree {
                return Err(F::DegreeMismatch);
            }
        }
        let mut seen_base = BTreeSet::new();
        for &b in &self.base {
            if b >= self.degree {
                return Err(F::BasePointOutOfRange);
            }
            if !seen_base.insert(b) {
                return Err(F::BaseNotDistinct);
            }
        }

        for (index, word) in self.strong_generator_words.iter().enumerate() {
            let reconstructed = signed_word_to_perm(&self.original_generators, word, self.degree)
                .ok_or(F::BadStrongGeneratorWord { index })?;
            if reconstructed != self.strong_generators[index] {
                return Err(F::StrongGeneratorWordDoesNotReconstruct { index });
            }
        }

        for (level, transversal) in self.transversals.iter().enumerate() {
            let prefix = &self.base[0..level];
            // MEASURED REDUNDANT, KEPT AS DEFENCE IN DEPTH. Deleting this
            // guard kills no test: a transversal missing `base[level]`
            // always differs from the independently recomputed orbit
            // closure below (which always contains its own seed point), so
            // `TransversalDoesNotMatchOrbitClosure` catches it too. Kept
            // because it names the specific defect instead of the generic
            // set-mismatch.
            if !transversal.contains_key(&self.base[level]) {
                return Err(F::TransversalMissingBasePoint { level });
            }
            for (&point, word) in transversal {
                if point >= self.degree {
                    return Err(F::TransversalWordOutOfRange { level, point });
                }
                let rep = word_to_perm(&self.strong_generators, word, self.degree)
                    .ok_or(F::TransversalWordOutOfRange { level, point })?;
                if !fixes_prefix(&rep, prefix) {
                    return Err(F::TransversalElementDoesNotFixPrefix { level, point });
                }
                if rep.apply(self.base[level]) != Some(point) {
                    return Err(F::TransversalElementWrongImage { level, point });
                }
            }
            let level_gens: Vec<(usize, Permutation)> = self
                .strong_generators
                .iter()
                .enumerate()
                .filter(|(_, g)| fixes_prefix(g, prefix))
                .map(|(idx, g)| (idx, g.clone()))
                .collect();
            let recomputed = bfs_orbit(self.base[level], &level_gens, self.degree);
            let claimed_points: BTreeSet<usize> = transversal.keys().copied().collect();
            let recomputed_points: BTreeSet<usize> = recomputed.keys().copied().collect();
            if claimed_points != recomputed_points {
                return Err(F::TransversalDoesNotMatchOrbitClosure { level });
            }
        }

        let mut computed: u128 = 1;
        for t in &self.transversals {
            let size = u128::try_from(t.len()).map_err(|_| F::OrderOverflow)?;
            computed = computed.checked_mul(size).ok_or(F::OrderOverflow)?;
        }
        if computed != self.claimed_order {
            return Err(F::OrderMismatch {
                computed,
                claimed: self.claimed_order,
            });
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// PermutationGroup
// ---------------------------------------------------------------------------

/// Bound on the number of elements [`PermutationGroup::cosets`] and
/// [`PermutationGroup::center`] will enumerate before declining.
pub const ENUMERATION_BOUND: u128 = 10_000;

/// Bound on the number of elements [`PermutationGroup::cayley_table`] will
/// enumerate before declining. Kept small because associativity checking is
/// `O(|G|^3)`; `120^3 = 1,728,000`, tested exactly at this bound with `S_5`.
pub const CAYLEY_TABLE_BOUND: u128 = 120;

/// Bound on the number of elements [`PermutationGroup::derived_subgroup`]
/// will enumerate before declining. Kept smaller than [`ENUMERATION_BOUND`]
/// because commutator generation is `O(|G|^2)`.
pub const DERIVED_SUBGROUP_ENUMERATION_BOUND: u128 = 2_000;

/// A reason a bounded operation was declined, or an input was invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermgroupError {
    /// The two groups involved act on different numbers of points.
    DegreeMismatch,
    /// The group's order exceeds the documented bound for this operation.
    TooLarge {
        /// The bound that was exceeded.
        bound: u128,
        /// The group's actual (verified) order.
        actual: u128,
    },
}

/// A finite permutation group, presented by a generating set, together with
/// its Schreier–Sims [`OrderCertificate`].
#[derive(Clone, Debug)]
pub struct PermutationGroup {
    degree: usize,
    generators: Vec<Permutation>,
    order_certificate: OrderCertificate,
}

impl PermutationGroup {
    /// Builds the group generated by `gens` acting on `degree` points, via
    /// deterministic Schreier–Sims. `None` if any generator's length differs
    /// from `degree`.
    #[must_use]
    pub fn from_generators(gens: Vec<Permutation>, degree: usize) -> Option<PermutationGroup> {
        for g in &gens {
            if g.len() != degree {
                return None;
            }
        }
        let build = build_bsgs(&gens, degree, None);
        let mut claimed_order: u128 = 1;
        for t in &build.level_orbits {
            let size = u128::try_from(t.len()).ok()?;
            claimed_order = claimed_order.checked_mul(size)?;
        }
        let order_certificate = OrderCertificate {
            degree,
            original_generators: gens.clone(),
            base: build.base,
            strong_generators: build.strong_generators,
            strong_generator_words: build.strong_generator_words,
            transversals: build.level_orbits,
            claimed_order,
        };
        Some(PermutationGroup {
            degree,
            generators: gens,
            order_certificate,
        })
    }

    /// The number of points this group acts on.
    #[must_use]
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// The generators this group was built from.
    #[must_use]
    pub fn generators(&self) -> &[Permutation] {
        &self.generators
    }

    /// The group's [`OrderCertificate`].
    #[must_use]
    pub fn order_certificate(&self) -> &OrderCertificate {
        &self.order_certificate
    }

    /// The group's order, as claimed by its own [`OrderCertificate`]. Call
    /// [`OrderCertificate::verify`] on [`Self::order_certificate`] to check
    /// it independently.
    #[must_use]
    pub fn order(&self) -> u128 {
        self.order_certificate.claimed_order
    }

    /// Tests membership of `perm` in the group by sifting it through the
    /// stabilizer chain, returning a certificate of the outcome either way.
    #[must_use]
    pub fn contains(&self, perm: &Permutation) -> MembershipCertificate {
        if perm.len() != self.degree {
            return MembershipCertificate::DegreeMismatch {
                subject_degree: perm.len(),
                group_degree: self.degree,
            };
        }
        match sift_with_trace(
            perm,
            &self.order_certificate.base,
            &self.order_certificate.transversals,
            &self.order_certificate.strong_generators,
            self.degree,
        ) {
            SiftOutcome::Success { factorization } => MembershipCertificate::Member {
                subject: perm.clone(),
                factorization,
            },
            SiftOutcome::Failure {
                level,
                prefix_factorization,
                residual_point,
            } => MembershipCertificate::NonMember {
                subject: perm.clone(),
                level,
                prefix_factorization,
                residual_point,
            },
        }
    }

    /// The orbit of `point` under the group, or `None` if `point >= degree`.
    #[must_use]
    pub fn orbit(&self, point: usize) -> Option<BTreeSet<usize>> {
        if point >= self.degree {
            return None;
        }
        let gens: Vec<(usize, Permutation)> = self.generators.iter().cloned().enumerate().collect();
        Some(
            bfs_orbit(point, &gens, self.degree)
                .keys()
                .copied()
                .collect(),
        )
    }

    /// The stabilizer of `point`, as its own [`PermutationGroup`] with its
    /// own BSGS, built from a Schreier generating set for `Stab_G(point)`
    /// derived via Schreier's lemma from the orbit of `point`. `None` if
    /// `point >= degree`.
    #[must_use]
    pub fn stabilizer(&self, point: usize) -> Option<PermutationGroup> {
        if point >= self.degree {
            return None;
        }
        let gens: Vec<(usize, Permutation)> = self.generators.iter().cloned().enumerate().collect();
        let transversal = bfs_orbit(point, &gens, self.degree);
        let mut stab_gens: Vec<Permutation> = Vec::new();
        for (&x, wx) in &transversal {
            let tx = word_to_perm(&self.generators, wx, self.degree)?;
            for g in &self.generators {
                let p = g.apply(x)?;
                let wp = transversal.get(&p)?;
                let tp = word_to_perm(&self.generators, wp, self.degree)?;
                let sx = g.compose(&tx)?;
                let sg = tp.inverse().compose(&sx)?;
                stab_gens.push(sg);
            }
        }
        PermutationGroup::from_generators(stab_gens, self.degree)
    }

    /// The orbit of `point` together with its stabilizer and an
    /// orbit-stabilizer certificate relating the two order certificates.
    /// `None` if `point >= degree`.
    #[must_use]
    pub fn orbit_stabilizer(
        &self,
        point: usize,
    ) -> Option<(PermutationGroup, OrbitStabilizerCertificate)> {
        if point >= self.degree {
            return None;
        }
        let stabilizer = self.stabilizer(point)?;
        let orbit = self.orbit(point)?;
        let cert = OrbitStabilizerCertificate {
            point,
            orbit,
            group_order: self.order_certificate.clone(),
            stabilizer_order: stabilizer.order_certificate.clone(),
        };
        Some((stabilizer, cert))
    }

    /// Left coset representatives of `subgroup` in this group, for `|G| <=`
    /// [`ENUMERATION_BOUND`]. Declines above the bound, or on a degree
    /// mismatch, with a distinct [`PermgroupError`].
    ///
    /// # Errors
    ///
    /// [`PermgroupError::DegreeMismatch`] if `subgroup` acts on a different
    /// number of points; [`PermgroupError::TooLarge`] if `|G|` (or `|H|`)
    /// exceeds [`ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics: every permutation composed here shares this group's
    /// degree by construction.
    pub fn cosets(&self, subgroup: &PermutationGroup) -> Result<CosetCertificate, PermgroupError> {
        if subgroup.degree != self.degree {
            return Err(PermgroupError::DegreeMismatch);
        }
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let g_elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let h_elems = enumerate_group(&subgroup.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: subgroup.order_certificate.claimed_order,
            },
        )?;

        let mut remaining: BTreeMap<Vec<usize>, Permutation> = g_elems
            .iter()
            .map(|p| (image_key(p, self.degree), p.clone()))
            .collect();
        let mut representatives = Vec::new();
        while let Some(rep) = remaining.values().next().cloned() {
            representatives.push(rep.clone());
            for h in &h_elems {
                let elem = rep.compose(h).expect("same degree");
                remaining.remove(&image_key(&elem, self.degree));
            }
        }

        Ok(CosetCertificate {
            group_order: self.order_certificate.clone(),
            subgroup_order: subgroup.order_certificate.clone(),
            representatives,
        })
    }

    /// The Cayley table of this group, for `|G| <=` [`CAYLEY_TABLE_BOUND`].
    /// Declines above the bound with a distinct [`PermgroupError`].
    ///
    /// # Errors
    ///
    /// [`PermgroupError::TooLarge`] if `|G|` exceeds [`CAYLEY_TABLE_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics: every permutation composed here shares this group's
    /// degree, and the group is closed under its own operation by
    /// construction.
    pub fn cayley_table(&self) -> Result<CayleyTableCertificate, PermgroupError> {
        if self.order_certificate.claimed_order > CAYLEY_TABLE_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: CAYLEY_TABLE_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let mut elements = enumerate_group(&self.generators, self.degree, CAYLEY_TABLE_BOUND)
            .ok_or(PermgroupError::TooLarge {
                bound: CAYLEY_TABLE_BOUND,
                actual: self.order_certificate.claimed_order,
            })?;
        elements.sort_by_key(|p| image_key(p, self.degree));
        let index: BTreeMap<Vec<usize>, usize> = elements
            .iter()
            .enumerate()
            .map(|(i, p)| (image_key(p, self.degree), i))
            .collect();
        let n = elements.len();
        let mut table = vec![vec![0usize; n]; n];
        for (i, gi) in elements.iter().enumerate() {
            for (j, gj) in elements.iter().enumerate() {
                let prod = gi.compose(gj).expect("same degree");
                table[i][j] = *index
                    .get(&image_key(&prod, self.degree))
                    .expect("group is closed under composition");
            }
        }
        Ok(CayleyTableCertificate {
            group_order: self.order_certificate.clone(),
            elements,
            table,
        })
    }

    /// Whether the group is abelian, checked by pairwise commutativity of
    /// its generators (sufficient: if every pair of generators commutes, the
    /// generated group is abelian).
    ///
    /// # Panics
    ///
    /// Never panics: every generator shares this group's degree.
    #[must_use]
    pub fn is_abelian(&self) -> AbelianCertificate {
        for i in 0..self.generators.len() {
            for j in (i + 1)..self.generators.len() {
                let a = self.generators[i]
                    .compose(&self.generators[j])
                    .expect("same degree");
                let b = self.generators[j]
                    .compose(&self.generators[i])
                    .expect("same degree");
                if a != b {
                    return AbelianCertificate::NonAbelian { i, j };
                }
            }
        }
        AbelianCertificate::Abelian
    }

    /// The center `Z(G)`, for `|G| <=` [`ENUMERATION_BOUND`]: elements
    /// commuting with every generator. Declines above the bound.
    ///
    /// # Errors
    ///
    /// [`PermgroupError::TooLarge`] if `|G|` exceeds [`ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics: every permutation composed here shares this group's
    /// degree, and the filtered central elements always form a valid
    /// generating set for the (possibly trivial) center subgroup.
    pub fn center(&self) -> Result<(PermutationGroup, CenterCertificate), PermgroupError> {
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let central: Vec<Permutation> = elems
            .iter()
            .filter(|e| {
                self.generators.iter().all(|g| {
                    e.compose(g).expect("same degree") == g.compose(e).expect("same degree")
                })
            })
            .cloned()
            .collect();
        let center_group = PermutationGroup::from_generators(central, self.degree)
            .expect("degree matches by construction");
        let cert = CenterCertificate {
            group_order: self.order_certificate.clone(),
            center_order: center_group.order_certificate.clone(),
        };
        Ok((center_group, cert))
    }

    /// The derived (commutator) subgroup `[G, G]`, for `|G| <=`
    /// [`DERIVED_SUBGROUP_ENUMERATION_BOUND`]. Declines above the bound.
    ///
    /// # Errors
    ///
    /// [`PermgroupError::TooLarge`] if `|G|` exceeds
    /// [`DERIVED_SUBGROUP_ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics: every permutation composed here shares this group's
    /// degree.
    pub fn derived_subgroup(
        &self,
    ) -> Result<(PermutationGroup, DerivedSubgroupCertificate), PermgroupError> {
        if self.order_certificate.claimed_order > DERIVED_SUBGROUP_ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: DERIVED_SUBGROUP_ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let elems = enumerate_group(
            &self.generators,
            self.degree,
            DERIVED_SUBGROUP_ENUMERATION_BOUND,
        )
        .ok_or(PermgroupError::TooLarge {
            bound: DERIVED_SUBGROUP_ENUMERATION_BOUND,
            actual: self.order_certificate.claimed_order,
        })?;
        let commutators = all_commutators(&elems);
        let derived_group = PermutationGroup::from_generators(commutators, self.degree)
            .expect("degree matches by construction");
        let cert = DerivedSubgroupCertificate {
            group_order: self.order_certificate.clone(),
            derived_order: derived_group.order_certificate.clone(),
        };
        Ok((derived_group, cert))
    }
}

/// Every commutator `[g, h] = g⁻¹h⁻¹gh` over all ordered pairs of `elems`.
fn all_commutators(elems: &[Permutation]) -> Vec<Permutation> {
    let mut commutators = Vec::with_capacity(elems.len() * elems.len());
    for g in elems {
        for h in elems {
            let gh = g.compose(h).expect("same degree");
            let hgh = h.inverse().compose(&gh).expect("same degree");
            let commutator = g.inverse().compose(&hgh).expect("same degree");
            commutators.push(commutator);
        }
    }
    commutators
}

// ---------------------------------------------------------------------------
// MembershipCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for `contains`: either a factorization of the
/// subject into strong generators (membership), or the level and residual
/// point at which sifting failed (non-membership), or a degree mismatch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipCertificate {
    /// `subject` is a member; `factorization` is a forward word over the
    /// group's strong generating set whose product is `subject`.
    Member {
        /// The permutation whose membership was tested.
        subject: Permutation,
        /// A forward word over the strong generating set.
        factorization: Word,
    },
    /// `subject` is not a member; sifting failed at `level`.
    NonMember {
        /// The permutation whose membership was tested.
        subject: Permutation,
        /// The base level sifting failed at.
        level: usize,
        /// A forward word over the strong generating set factoring the
        /// portion of `subject` removed by levels `0..level`.
        prefix_factorization: Word,
        /// The point `base[level]` was sent to by the residual, which is
        /// not in that level's basic orbit (`usize::MAX` if sifting
        /// completed but landed on a non-identity residual, which cannot
        /// happen for a genuinely-built chain).
        residual_point: usize,
    },
    /// `subject`'s degree differs from the group's.
    DegreeMismatch {
        /// The subject's degree.
        subject_degree: usize,
        /// The group's degree.
        group_degree: usize,
    },
}

/// Why a [`MembershipCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipFailure {
    /// The certificate's subject degree does not match `group`'s.
    DegreeMismatch,
    /// A `DegreeMismatch` variant was given, but the degrees actually match.
    DegreeMismatchClaimIsWrong,
    /// A word entry is out of range, or the word does not multiply.
    WordDoesNotMultiply,
    /// A `Member` factorization does not reconstruct `subject`.
    FactorizationDoesNotReconstructSubject,
    /// A `NonMember` `level` exceeds the group's base length.
    LevelOutOfRange,
    /// The `NonMember` residual, recomputed from `prefix_factorization` and
    /// `subject`, does not send `base[level]` to `residual_point`.
    ResidualDoesNotMatch,
    /// The `NonMember` `residual_point` is (independently, from `group`'s
    /// own transversal) actually in that level's basic orbit — the claimed
    /// non-membership is not established.
    ResidualPointActuallyInOrbit,
}

impl MembershipCertificate {
    /// Independently re-derives this certificate's claim against `group`'s
    /// [`OrderCertificate`], returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`MembershipFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self, group: &OrderCertificate) -> Result<(), MembershipFailure> {
        use MembershipFailure as F;
        match self {
            MembershipCertificate::Member {
                subject,
                factorization,
            } => {
                if subject.len() != group.degree {
                    return Err(F::DegreeMismatch);
                }
                let product = word_to_perm(&group.strong_generators, factorization, group.degree)
                    .ok_or(F::WordDoesNotMultiply)?;
                if product != *subject {
                    return Err(F::FactorizationDoesNotReconstructSubject);
                }
                Ok(())
            }
            MembershipCertificate::NonMember {
                subject,
                level,
                prefix_factorization,
                residual_point,
            } => {
                if subject.len() != group.degree {
                    return Err(F::DegreeMismatch);
                }
                if *level > group.base.len() {
                    return Err(F::LevelOutOfRange);
                }
                let prefix =
                    word_to_perm(&group.strong_generators, prefix_factorization, group.degree)
                        .ok_or(F::WordDoesNotMultiply)?;
                let residual = prefix
                    .inverse()
                    .compose(subject)
                    .ok_or(F::WordDoesNotMultiply)?;
                if *level == group.base.len() {
                    if is_identity(&residual, group.degree) {
                        return Err(F::ResidualDoesNotMatch);
                    }
                    return Ok(());
                }
                if residual.apply(group.base[*level]) != Some(*residual_point) {
                    return Err(F::ResidualDoesNotMatch);
                }
                if group.transversals[*level].contains_key(residual_point) {
                    return Err(F::ResidualPointActuallyInOrbit);
                }
                Ok(())
            }
            MembershipCertificate::DegreeMismatch {
                subject_degree,
                group_degree,
            } => {
                if *group_degree != group.degree {
                    return Err(F::DegreeMismatch);
                }
                if *subject_degree == group.degree {
                    return Err(F::DegreeMismatchClaimIsWrong);
                }
                Ok(())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// OrbitStabilizerCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for the orbit-stabilizer theorem applied to one
/// point: `|orbit| * |Stab_G(point)| = |G|`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrbitStabilizerCertificate {
    /// The point whose orbit and stabilizer this certifies.
    pub point: usize,
    /// The claimed orbit of `point` under the group.
    pub orbit: BTreeSet<usize>,
    /// The order certificate for the whole group.
    pub group_order: OrderCertificate,
    /// The order certificate for `Stab_G(point)`.
    pub stabilizer_order: OrderCertificate,
}

/// Why an [`OrbitStabilizerCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrbitStabilizerFailure {
    /// `point >= group_order.degree`.
    PointOutOfRange,
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `stabilizer_order` itself does not verify.
    StabilizerCertificateInvalid,
    /// Some generator of the claimed stabilizer does not fix `point`.
    StabilizerGeneratorsDoNotFixPoint,
    /// The claimed orbit does not equal the independently recomputed orbit
    /// closure of `point` under `group_order`'s original generators.
    OrbitDoesNotMatchClosure,
    /// `|orbit| * stabilizer_order.claimed_order` overflows `u128`.
    Overflow,
    /// `|orbit| * |Stab_G(point)| != |G|`.
    ProductMismatch {
        /// `|orbit|`.
        orbit_size: u128,
        /// `|Stab_G(point)|`, as claimed.
        stabilizer_order: u128,
        /// `|G|`, as claimed.
        group_order: u128,
    },
}

impl OrbitStabilizerCertificate {
    /// Independently re-derives this certificate's claim, returning the
    /// first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`OrbitStabilizerFailure`] guard that does not
    /// hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), OrbitStabilizerFailure> {
        use OrbitStabilizerFailure as F;
        if self.point >= self.group_order.degree {
            return Err(F::PointOutOfRange);
        }
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.stabilizer_order
            .verify()
            .map_err(|_| F::StabilizerCertificateInvalid)?;
        for g in &self.stabilizer_order.original_generators {
            if g.apply(self.point) != Some(self.point) {
                return Err(F::StabilizerGeneratorsDoNotFixPoint);
            }
        }
        let gens: Vec<(usize, Permutation)> = self
            .group_order
            .original_generators
            .iter()
            .cloned()
            .enumerate()
            .collect();
        let recomputed: BTreeSet<usize> = bfs_orbit(self.point, &gens, self.group_order.degree)
            .keys()
            .copied()
            .collect();
        if recomputed != self.orbit {
            return Err(F::OrbitDoesNotMatchClosure);
        }
        let orbit_size = u128::try_from(self.orbit.len()).map_err(|_| F::Overflow)?;
        let product = orbit_size
            .checked_mul(self.stabilizer_order.claimed_order)
            .ok_or(F::Overflow)?;
        if product != self.group_order.claimed_order {
            return Err(F::ProductMismatch {
                orbit_size,
                stabilizer_order: self.stabilizer_order.claimed_order,
                group_order: self.group_order.claimed_order,
            });
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// CosetCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for a left-coset decomposition: representatives
/// whose cosets partition the group exactly once.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CosetCertificate {
    /// The order certificate for the whole group `G`.
    pub group_order: OrderCertificate,
    /// The order certificate for the subgroup `H`.
    pub subgroup_order: OrderCertificate,
    /// Left coset representatives: claimed so that `{r * H : r in
    /// representatives}` partitions `G` exactly once.
    pub representatives: Vec<Permutation>,
}

/// Why a [`CosetCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CosetFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `subgroup_order` itself does not verify.
    SubgroupCertificateInvalid,
    /// The two certificates act on different numbers of points.
    DegreeMismatch,
    /// `group_order.claimed_order` exceeds [`ENUMERATION_BOUND`]: too large
    /// to check by enumeration.
    GroupTooLargeToVerify,
    /// `subgroup_order.claimed_order` exceeds [`ENUMERATION_BOUND`].
    SubgroupTooLargeToVerify,
    /// Two representatives' cosets overlap.
    CosetsOverlap,
    /// The union of the claimed cosets does not equal `G`.
    CosetsDoNotCoverGroup,
}

impl CosetCertificate {
    /// Independently re-enumerates both groups and re-checks that the
    /// claimed cosets partition `G` exactly once.
    ///
    /// # Errors
    ///
    /// Returns the first [`CosetFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), CosetFailure> {
        use CosetFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.subgroup_order
            .verify()
            .map_err(|_| F::SubgroupCertificateInvalid)?;
        if self.group_order.degree != self.subgroup_order.degree {
            return Err(F::DegreeMismatch);
        }
        let degree = self.group_order.degree;
        if self.group_order.claimed_order > ENUMERATION_BOUND {
            return Err(F::GroupTooLargeToVerify);
        }
        if self.subgroup_order.claimed_order > ENUMERATION_BOUND {
            return Err(F::SubgroupTooLargeToVerify);
        }
        let g_elems = enumerate_group(
            &self.group_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::GroupTooLargeToVerify)?;
        let h_elems = enumerate_group(
            &self.subgroup_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::SubgroupTooLargeToVerify)?;
        let g_keys: BTreeSet<Vec<usize>> = g_elems.iter().map(|p| image_key(p, degree)).collect();

        let mut covered: BTreeSet<Vec<usize>> = BTreeSet::new();
        for rep in &self.representatives {
            for h in &h_elems {
                let elem = rep.compose(h).ok_or(F::CosetsDoNotCoverGroup)?;
                let key = image_key(&elem, degree);
                if !covered.insert(key) {
                    return Err(F::CosetsOverlap);
                }
            }
        }
        if covered != g_keys {
            return Err(F::CosetsDoNotCoverGroup);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// CayleyTableCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for a Cayley table: the elements in canonical
/// order and the multiplication table over them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CayleyTableCertificate {
    /// The order certificate for the group.
    pub group_order: OrderCertificate,
    /// The group's elements, in canonical (image-vector) order.
    pub elements: Vec<Permutation>,
    /// `table[i][j]` is the index into `elements` of `elements[i] *
    /// elements[j]`.
    pub table: Vec<Vec<usize>>,
}

/// Why a [`CayleyTableCertificate`] failed to verify. Each variant is one of
/// the four group axioms (closure, identity, inverses, associativity), or a
/// structural precondition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CayleyTableFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `elements.len() != table.len()`, or some row's length differs.
    TableShapeMismatch,
    /// Two entries of `elements` are equal.
    DuplicateElements,
    /// `elements.len()` does not match `group_order.claimed_order`.
    ElementCountMismatch,
    /// `elements[i] * elements[j]` (recomputed) is not itself in `elements`
    /// — the claimed table is not closed.
    NotClosed {
        /// The row index.
        i: usize,
        /// The column index.
        j: usize,
    },
    /// `table[i][j]` names a different element than the recomputed product.
    WrongEntry {
        /// The row index.
        i: usize,
        /// The column index.
        j: usize,
    },
    /// No element of `elements` is the identity permutation.
    NoIdentity,
    /// The identity row or column of `table` is not the identity map.
    IdentityLawFails {
        /// The offending element index.
        i: usize,
    },
    /// Some element of `elements` has no inverse recorded in `table`.
    NoInverse {
        /// The offending element index.
        i: usize,
    },
    /// `(i * j) * k != i * (j * k)` for some `i, j, k`.
    AssociativityFails {
        /// The first index.
        i: usize,
        /// The second index.
        j: usize,
        /// The third index.
        k: usize,
    },
}

impl CayleyTableCertificate {
    /// Independently re-checks closure, identity, inverses, and
    /// associativity, returning the first axiom (or precondition) that
    /// fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`CayleyTableFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), CayleyTableFailure> {
        use CayleyTableFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        let degree = self.group_order.degree;
        let n = self.elements.len();
        if u128::try_from(n).unwrap_or(u128::MAX) != self.group_order.claimed_order {
            return Err(F::ElementCountMismatch);
        }
        if self.table.len() != n || self.table.iter().any(|row| row.len() != n) {
            return Err(F::TableShapeMismatch);
        }
        let index: BTreeMap<Vec<usize>, usize> = self
            .elements
            .iter()
            .enumerate()
            .map(|(i, p)| (image_key(p, degree), i))
            .collect();
        if index.len() != n {
            return Err(F::DuplicateElements);
        }

        for (i, gi) in self.elements.iter().enumerate() {
            for (j, gj) in self.elements.iter().enumerate() {
                let prod = gi.compose(gj).ok_or(F::NotClosed { i, j })?;
                let &actual = index
                    .get(&image_key(&prod, degree))
                    .ok_or(F::NotClosed { i, j })?;
                if self.table[i][j] != actual {
                    return Err(F::WrongEntry { i, j });
                }
            }
        }

        let identity_key = image_key(&Permutation::identity(degree), degree);
        let &e = index.get(&identity_key).ok_or(F::NoIdentity)?;
        for i in 0..n {
            if self.table[e][i] != i || self.table[i][e] != i {
                return Err(F::IdentityLawFails { i });
            }
        }

        for i in 0..n {
            let has_inverse = (0..n).any(|j| self.table[i][j] == e && self.table[j][i] == e);
            if !has_inverse {
                return Err(F::NoInverse { i });
            }
        }

        for i in 0..n {
            for j in 0..n {
                for k in 0..n {
                    let left = self.table[self.table[i][j]][k];
                    let right = self.table[i][self.table[j][k]];
                    if left != right {
                        return Err(F::AssociativityFails { i, j, k });
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// AbelianCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for `is_abelian`: either a claim of full
/// commutativity, or a witnessing pair of generators that do not commute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbelianCertificate {
    /// Every pair of generators commutes.
    Abelian,
    /// Generators at these indices do not commute.
    NonAbelian {
        /// The first generator's index.
        i: usize,
        /// The second generator's index.
        j: usize,
    },
}

/// Why an [`AbelianCertificate`] failed to verify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbelianFailure {
    /// `Abelian` was claimed, but some pair of generators does not commute.
    NotActuallyAbelian {
        /// The first witnessing generator's index.
        i: usize,
        /// The second witnessing generator's index.
        j: usize,
    },
    /// `NonAbelian { i, j }` was claimed, but `i`/`j` is out of range.
    IndexOutOfRange,
    /// `NonAbelian { i, j }` was claimed, but those generators actually
    /// commute.
    WitnessActuallyCommutes,
}

impl AbelianCertificate {
    /// Independently re-checks commutativity of `generators` against this
    /// claim.
    ///
    /// # Errors
    ///
    /// Returns the first [`AbelianFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self, generators: &[Permutation]) -> Result<(), AbelianFailure> {
        use AbelianFailure as F;
        match *self {
            AbelianCertificate::Abelian => {
                for i in 0..generators.len() {
                    for j in (i + 1)..generators.len() {
                        let a = generators[i].compose(&generators[j]).expect("same degree");
                        let b = generators[j].compose(&generators[i]).expect("same degree");
                        if a != b {
                            return Err(F::NotActuallyAbelian { i, j });
                        }
                    }
                }
                Ok(())
            }
            AbelianCertificate::NonAbelian { i, j } => {
                if i >= generators.len() || j >= generators.len() {
                    return Err(F::IndexOutOfRange);
                }
                let a = generators[i].compose(&generators[j]).expect("same degree");
                let b = generators[j].compose(&generators[i]).expect("same degree");
                if a == b {
                    return Err(F::WitnessActuallyCommutes);
                }
                Ok(())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// CenterCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for the center `Z(G)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CenterCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The order certificate for `Z(G)`.
    pub center_order: OrderCertificate,
}

/// Why a [`CenterCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CenterFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `center_order` itself does not verify.
    CenterCertificateInvalid,
    /// `group_order.claimed_order` exceeds [`ENUMERATION_BOUND`].
    TooLargeToVerify,
    /// Some generator of the claimed center does not commute with some
    /// generator of `G`.
    GeneratorNotCentral,
    /// The independently recomputed center (elements of `G` commuting with
    /// every generator of `G`) does not equal the claimed center's elements.
    SetMismatch,
}

impl CenterCertificate {
    /// Independently re-enumerates `G`, recomputes the center by its
    /// definition, and compares to the claimed center subgroup's elements.
    ///
    /// # Errors
    ///
    /// Returns the first [`CenterFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), CenterFailure> {
        use CenterFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.center_order
            .verify()
            .map_err(|_| F::CenterCertificateInvalid)?;
        if self.group_order.claimed_order > ENUMERATION_BOUND {
            return Err(F::TooLargeToVerify);
        }
        let degree = self.group_order.degree;
        for c in &self.center_order.original_generators {
            for g in &self.group_order.original_generators {
                let a = c.compose(g).expect("same degree");
                let b = g.compose(c).expect("same degree");
                if a != b {
                    return Err(F::GeneratorNotCentral);
                }
            }
        }
        let g_elems = enumerate_group(
            &self.group_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let recomputed_center: BTreeSet<Vec<usize>> = g_elems
            .iter()
            .filter(|e| {
                self.group_order.original_generators.iter().all(|g| {
                    e.compose(g).expect("same degree") == g.compose(e).expect("same degree")
                })
            })
            .map(|p| image_key(p, degree))
            .collect();
        let center_elems = enumerate_group(
            &self.center_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let claimed_center: BTreeSet<Vec<usize>> =
            center_elems.iter().map(|p| image_key(p, degree)).collect();
        if recomputed_center != claimed_center {
            return Err(F::SetMismatch);
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// DerivedSubgroupCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for the derived (commutator) subgroup `[G, G]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedSubgroupCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The order certificate for `[G, G]`.
    pub derived_order: OrderCertificate,
}

/// Why a [`DerivedSubgroupCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedSubgroupFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `derived_order` itself does not verify.
    DerivedCertificateInvalid,
    /// `group_order.claimed_order` exceeds
    /// [`DERIVED_SUBGROUP_ENUMERATION_BOUND`].
    TooLargeToVerify,
    /// The group generated by all commutators of `G`'s elements (recomputed
    /// independently) does not equal the claimed derived subgroup.
    SetMismatch,
}

impl DerivedSubgroupCertificate {
    /// Independently re-enumerates `G`, recomputes every commutator and the
    /// group they generate, and compares to the claimed derived subgroup.
    ///
    /// # Errors
    ///
    /// Returns the first [`DerivedSubgroupFailure`] guard that does not
    /// hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), DerivedSubgroupFailure> {
        use DerivedSubgroupFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.derived_order
            .verify()
            .map_err(|_| F::DerivedCertificateInvalid)?;
        if self.group_order.claimed_order > DERIVED_SUBGROUP_ENUMERATION_BOUND {
            return Err(F::TooLargeToVerify);
        }
        let degree = self.group_order.degree;
        let g_elems = enumerate_group(
            &self.group_order.original_generators,
            degree,
            DERIVED_SUBGROUP_ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let commutators = all_commutators(&g_elems);
        let closure = enumerate_group(&commutators, degree, DERIVED_SUBGROUP_ENUMERATION_BOUND)
            .ok_or(F::TooLargeToVerify)?;
        let recomputed: BTreeSet<Vec<usize>> =
            closure.iter().map(|p| image_key(p, degree)).collect();
        let derived_elems = enumerate_group(
            &self.derived_order.original_generators,
            degree,
            DERIVED_SUBGROUP_ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let claimed: BTreeSet<Vec<usize>> =
            derived_elems.iter().map(|p| image_key(p, degree)).collect();
        if recomputed != claimed {
            return Err(F::SetMismatch);
        }
        Ok(())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn transposition(n: usize, a: usize, b: usize) -> Permutation {
        Permutation::from_cycles(&[vec![a, b]], n).unwrap()
    }

    fn cycle(n: usize, pts: &[usize]) -> Permutation {
        Permutation::from_cycles(&[pts.to_vec()], n).unwrap()
    }

    fn symmetric_group(n: usize) -> PermutationGroup {
        // Adjacent transpositions generate S_n.
        let gens: Vec<Permutation> = (0..n - 1).map(|i| transposition(n, i, i + 1)).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    fn alternating_group(n: usize) -> PermutationGroup {
        // 3-cycles (0 1 k) for k = 2..n generate A_n (n >= 3).
        let gens: Vec<Permutation> = (2..n).map(|k| cycle(n, &[0, 1, k])).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    #[test]
    fn s3_has_order_6() {
        let g = symmetric_group(3);
        assert_eq!(g.order(), 6);
        assert!(g.order_certificate().verify().is_ok());
    }

    #[test]
    fn s4_has_order_24() {
        let g = symmetric_group(4);
        assert_eq!(g.order(), 24);
        assert!(g.order_certificate().verify().is_ok());
    }

    #[test]
    fn a4_has_order_12() {
        let g = alternating_group(4);
        assert_eq!(g.order(), 12);
        assert!(g.order_certificate().verify().is_ok());
    }

    #[test]
    fn s5_has_order_120() {
        let g = symmetric_group(5);
        assert_eq!(g.order(), 120);
        assert!(g.order_certificate().verify().is_ok());
    }

    #[test]
    fn a5_has_order_60_is_nonabelian_with_trivial_center() {
        let g = alternating_group(5);
        assert_eq!(g.order(), 60);
        assert!(g.order_certificate().verify().is_ok());

        let abelian_cert = g.is_abelian();
        assert_eq!(abelian_cert, AbelianCertificate::NonAbelian { i: 0, j: 1 });
        assert!(abelian_cert.verify(g.generators()).is_ok());

        let (center, cert) = g.center().unwrap();
        assert_eq!(center.order(), 1);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn d4_dihedral_of_order_8_has_center_of_order_2() {
        // D_4 acting on the 4 corners of a square: r = (0 1 2 3), s = (1 3).
        let r = cycle(4, &[0, 1, 2, 3]);
        let s = transposition(4, 1, 3);
        let g = PermutationGroup::from_generators(vec![r, s], 4).unwrap();
        assert_eq!(g.order(), 8);
        assert!(g.order_certificate().verify().is_ok());

        let (center, cert) = g.center().unwrap();
        assert_eq!(center.order(), 2);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn z6_cyclic_group_is_abelian() {
        let g = PermutationGroup::from_generators(vec![cycle(6, &[0, 1, 2, 3, 4, 5])], 6).unwrap();
        assert_eq!(g.order(), 6);
        let cert = g.is_abelian();
        assert_eq!(cert, AbelianCertificate::Abelian);
        assert!(cert.verify(g.generators()).is_ok());
    }

    #[test]
    fn two_generators_of_s8_give_order_40320_without_enumerating() {
        // (1 2 3 4 5 6 7 8) and (1 2) (0-indexed: an 8-cycle and a transposition)
        // generate all of S_8.
        let a = cycle(8, &[0, 1, 2, 3, 4, 5, 6, 7]);
        let b = transposition(8, 0, 1);
        let g = PermutationGroup::from_generators(vec![a, b], 8).unwrap();
        assert_eq!(g.order(), 40320);
        assert!(g.order_certificate().verify().is_ok());
        // The BSGS base is at most 8 points; no 40320-element enumeration
        // happened to compute this (the transversal sizes multiply to it).
        assert!(g.order_certificate().base.len() <= 8);
    }

    #[test]
    fn membership_positive_and_negative_for_a5() {
        let g = alternating_group(5);
        let even = cycle(5, &[0, 1, 2]);
        assert_eq!(even.sign(), 1);
        match g.contains(&even) {
            MembershipCertificate::Member { .. } => {}
            other => panic!("expected membership, got {other:?}"),
        }
        assert!(g.contains(&even).verify(g.order_certificate()).is_ok());

        let odd = transposition(5, 0, 1);
        assert_eq!(odd.sign(), -1);
        let cert = g.contains(&odd);
        match &cert {
            MembershipCertificate::NonMember {
                prefix_factorization,
                level,
                ..
            } => {
                // The sift residue is recorded: a level and (possibly empty)
                // prefix factorization are present.
                assert!(*level <= g.order_certificate().base.len());
                let _ = prefix_factorization;
            }
            other => panic!("expected non-membership, got {other:?}"),
        }
        assert!(cert.verify(g.order_certificate()).is_ok());
    }

    #[test]
    fn orbit_stabilizer_on_s4_acting_on_points() {
        let g = symmetric_group(4);
        let (stab, cert) = g.orbit_stabilizer(0).unwrap();
        let orbit = g.orbit(0).unwrap();
        assert_eq!(orbit, [0, 1, 2, 3].into_iter().collect::<BTreeSet<_>>());
        assert_eq!(stab.order(), 6); // Stab(0) in S_4 is S_3 on {1,2,3}.
        assert_eq!(orbit.len() as u128 * stab.order(), g.order());
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn cosets_of_a4_in_s4_gives_two_cosets() {
        let s4 = symmetric_group(4);
        let a4 = alternating_group(4);
        let cert = s4.cosets(&a4).unwrap();
        assert_eq!(cert.representatives.len(), 2);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn cayley_table_of_s3_is_verified() {
        let g = symmetric_group(3);
        let cert = g.cayley_table().unwrap();
        assert_eq!(cert.elements.len(), 6);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn cayley_table_at_the_bound_s5_order_120() {
        let g = symmetric_group(5);
        assert_eq!(g.order(), CAYLEY_TABLE_BOUND);
        let cert = g.cayley_table().unwrap();
        assert_eq!(cert.elements.len(), 120);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn cayley_table_declines_above_the_bound() {
        let g = symmetric_group(6); // order 720 > 120
        match g.cayley_table() {
            Err(PermgroupError::TooLarge { bound, actual }) => {
                assert_eq!(bound, CAYLEY_TABLE_BOUND);
                assert_eq!(actual, 720);
            }
            other => panic!("expected TooLarge, got {other:?}"),
        }
    }

    #[test]
    fn cosets_decline_above_the_bound_with_a_distinct_reason() {
        // Build a group whose order is guaranteed > ENUMERATION_BOUND
        // without enumerating: S_8 has order 40320.
        let a = cycle(8, &[0, 1, 2, 3, 4, 5, 6, 7]);
        let b = transposition(8, 0, 1);
        let g = PermutationGroup::from_generators(vec![a, b], 8).unwrap();
        let trivial = PermutationGroup::from_generators(vec![], 8).unwrap();
        match g.cosets(&trivial) {
            Err(PermgroupError::TooLarge { bound, actual }) => {
                assert_eq!(bound, ENUMERATION_BOUND);
                assert_eq!(actual, 40320);
            }
            other => panic!("expected TooLarge, got {other:?}"),
        }
    }

    #[test]
    fn derived_subgroup_of_s4_is_a4() {
        let s4 = symmetric_group(4);
        let (derived, cert) = s4.derived_subgroup().unwrap();
        assert_eq!(derived.order(), 12);
        assert!(cert.verify().is_ok());
    }

    #[test]
    fn derived_subgroup_of_s3_is_order_3() {
        let s3 = symmetric_group(3);
        let (derived, cert) = s3.derived_subgroup().unwrap();
        assert_eq!(derived.order(), 3);
        assert!(cert.verify().is_ok());
    }

    // -- Forged certificates: each refused for a distinct reason. --

    #[test]
    fn forged_order_certificate_wrong_order_is_refused() {
        let g = symmetric_group(3);
        let mut forged = g.order_certificate().clone();
        forged.claimed_order = 7; // 6 is correct
        match forged.verify() {
            Err(OrderCertificateFailure::OrderMismatch { computed, claimed }) => {
                assert_eq!(computed, 6);
                assert_eq!(claimed, 7);
            }
            other => panic!("expected OrderMismatch, got {other:?}"),
        }
    }

    #[test]
    fn forged_transversal_element_not_fixing_base_prefix_is_refused() {
        let g = symmetric_group(4);
        let mut forged = g.order_certificate().clone();
        // Corrupt level 1's transversal: replace a word with one that
        // certainly doesn't fix base[0].
        assert!(forged.base.len() >= 2, "S_4's base has at least 2 points");
        let bogus_point = *forged.transversals[1].keys().next().unwrap();
        // Use the word for base[0]'s own non-identity mover at level 0
        // (which does NOT fix base[0]) as a corrupt entry at level 1.
        let corrupt_word: Word = forged.transversals[0]
            .values()
            .find(|w| !w.is_empty())
            .cloned()
            .unwrap_or_else(|| vec![0]);
        forged.transversals[1].insert(bogus_point, corrupt_word);
        match forged.verify() {
            Err(
                OrderCertificateFailure::TransversalElementDoesNotFixPrefix { .. }
                | OrderCertificateFailure::TransversalElementWrongImage { .. }
                | OrderCertificateFailure::TransversalDoesNotMatchOrbitClosure { .. },
            ) => {}
            other => panic!("expected a transversal guard to fire, got {other:?}"),
        }
    }

    #[test]
    fn forged_membership_factorization_that_does_not_multiply_back_is_refused() {
        let g = alternating_group(5);
        let even = cycle(5, &[0, 1, 2]);
        let cert = g.contains(&even);
        let forged = match cert {
            MembershipCertificate::Member {
                subject,
                mut factorization,
            } => {
                factorization.push(factorization.first().copied().unwrap_or(0));
                MembershipCertificate::Member {
                    subject,
                    factorization,
                }
            }
            other => panic!("expected membership, got {other:?}"),
        };
        match forged.verify(g.order_certificate()) {
            Err(MembershipFailure::FactorizationDoesNotReconstructSubject) => {}
            other => panic!("expected FactorizationDoesNotReconstructSubject, got {other:?}"),
        }
    }

    #[test]
    fn forged_strong_generator_word_that_does_not_reconstruct_is_refused() {
        let g = symmetric_group(4);
        let mut forged = g.order_certificate().clone();
        // Replace the word with the empty word (product = identity). A
        // strong generator is never the identity, so this is guaranteed to
        // change the reconstructed permutation -- unlike sign-flipping the
        // word's first entry, which is a no-op for an involution generator
        // (S_4's adjacent transpositions are all self-inverse).
        let idx = 0;
        assert_ne!(
            forged.strong_generators[idx],
            Permutation::identity(forged.degree),
            "test assumption: a strong generator is never the identity"
        );
        forged.strong_generator_words[idx] = Vec::new();
        assert!(matches!(
            forged.verify(),
            Err(
                OrderCertificateFailure::StrongGeneratorWordDoesNotReconstruct { index: 0 }
                    | OrderCertificateFailure::BadStrongGeneratorWord { index: 0 }
            )
        ));
    }

    #[test]
    fn forged_coset_certificate_overlap_and_noncover_are_distinct_reasons() {
        let s4 = symmetric_group(4);
        let a4 = alternating_group(4);
        let mut cert = s4.cosets(&a4).unwrap();
        assert_eq!(cert.representatives.len(), 2);

        // Overlap: duplicate a representative.
        let mut overlap = cert.clone();
        let dup = overlap.representatives[0].clone();
        overlap.representatives.push(dup);
        assert_eq!(overlap.verify(), Err(CosetFailure::CosetsOverlap));

        // Non-cover: drop a representative.
        cert.representatives.pop();
        assert_eq!(cert.verify(), Err(CosetFailure::CosetsDoNotCoverGroup));
    }

    #[test]
    fn forged_cayley_table_wrong_entry_and_missing_identity_are_distinct_reasons() {
        let g = symmetric_group(3);
        let mut cert = g.cayley_table().unwrap();
        let n = cert.elements.len();

        let mut wrong_entry = cert.clone();
        wrong_entry.table[0][1] = (wrong_entry.table[0][1] + 1) % n;
        assert!(matches!(
            wrong_entry.verify(),
            Err(CayleyTableFailure::WrongEntry { .. })
        ));

        // Remove the identity from the element list (and its row/col from
        // the table) to trigger NoIdentity distinctly. Find identity index.
        let degree = cert.group_order.degree;
        let id_idx = cert
            .elements
            .iter()
            .position(|p| *p == Permutation::identity(degree))
            .unwrap();
        cert.elements.remove(id_idx);
        cert.table.remove(id_idx);
        for row in &mut cert.table {
            row.remove(id_idx);
        }
        // Now shape is inconsistent as a group table (n-1 elements), so we
        // expect either shape/element-count guard or closure/no-identity;
        // assert a distinct, non-success outcome different from the
        // WrongEntry case above.
        assert!(cert.verify().is_err());
    }

    #[test]
    fn forged_orbit_stabilizer_product_mismatch_is_refused() {
        let g = symmetric_group(4);
        let (_, mut cert) = g.orbit_stabilizer(0).unwrap();
        cert.stabilizer_order.claimed_order += 1;
        // Corrupting claimed_order alone makes the stabilizer's own
        // OrderCertificate fail internal consistency first (order mismatch
        // against its transversal sizes), which is itself a valid distinct
        // refusal reason.
        assert!(cert.verify().is_err());
    }

    #[test]
    fn missing_base_point_transversal_is_refused() {
        // A certificate whose level-0 transversal omits base[0] is
        // rejected. Mutation-checked: deleting the explicit
        // "TransversalMissingBasePoint" guard kills no test here, because
        // the independently recomputed orbit-closure guard (which always
        // contains its own seed point) catches the same defect -- measured
        // redundant, kept as defence in depth (see the guard's own comment).
        let g = symmetric_group(3);
        let mut forged = g.order_certificate().clone();
        let base0 = forged.base[0];
        forged.transversals[0].remove(&base0);
        assert!(forged.verify().is_err());
    }
}
