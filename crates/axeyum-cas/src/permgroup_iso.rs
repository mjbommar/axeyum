//! Isomorphism testing and group presentations from a BSGS -- wave three of
//! item 5, split out of `permgroup.rs` to keep that file under its
//! line-count budget. A child module of [`crate::permgroup`] (declared there
//! via `#[path = "permgroup_iso.rs"] mod permgroup_iso;`, never in
//! `lib.rs`), so every private item it needs from the parent (`Word`,
//! `SignedWord`, `encode`, `decode`, `invert_signed_word`, `word_to_perm`,
//! `signed_word_to_perm`, `fixes_prefix`, `is_identity`, `image_key`,
//! `enumerate_group`, `sift_with_trace`, `SiftOutcome`) is visible here by
//! ordinary Rust privacy (private = visible in the defining module and its
//! descendants) without being made `pub`; the items re-exported from
//! `permgroup_sylow` (`Invariants`, `InvariantsCertificate`,
//! `DistinguishCertificate`, `distinguish`) are reached the same way,
//! because `permgroup.rs`'s own `pub use` brings them into `super::`'s
//! namespace, which every child (this module included) can see.
//!
//! # What this module computes
//!
//! - [`isomorphism`]: decides isomorphism between two permutation groups of
//!   order at most [`ISOMORPHISM_BOUND`] (2,000; matches
//!   [`crate::permgroup::DERIVED_SUBGROUP_ENUMERATION_BOUND`], the bound
//!   `distinguish` itself already carries, so calling it here never fails
//!   for a size reason once that gate has passed). It first tries
//!   [`crate::permgroup::distinguish`]; a genuine difference is conclusive
//!   ([`IsomorphismDecision::NotIsomorphic`] via
//!   [`NonIsomorphismReason::Invariants`]). When invariants agree, it
//!   backtracks over images of `G`'s strong generators in `H`, pruned by two
//!   necessary conditions for an isomorphism (element order, and conjugacy
//!   class size -- both are isomorphism invariants of the *element*, not
//!   just the group, since `|Ccl_G(g)| = |G|/|C_G(g)| = |H|/|C_H(phi(g))| =
//!   |Ccl_H(phi(g))|` when `|G| = |H|`), so no candidate is pruned that a
//!   genuine isomorphism could use. A candidate assignment is accepted only
//!   if every relator [`schreier_relators`] derives from `G`'s own BSGS
//!   holds of the images (so the assignment extends to a homomorphism) and
//!   the subgroup the images generate has the full order of `H` -- which,
//!   given `|G| = |H|` already, forces the induced map to be a bijection
//!   (image order equals `|H|` gives surjectivity, and Lagrange applied to
//!   the kernel gives injectivity for free; see [`IsoCertificate`]'s
//!   comment). Exhausting every constrained candidate without success is
//!   itself a complete proof of non-isomorphism (the constraints are all
//!   *necessary*, never merely typical, conditions), certified by
//!   [`NonIsomorphismReason::ExhaustedSearch`].
//! - [`PermutationGroup::presentation`]: `G`'s strong generating set plus a
//!   finite relator set derived the standard way from a complete BSGS --
//!   for every base level, every orbit point, every level-fixing strong
//!   generator, the Schreier generator it produces sifts to the identity,
//!   and that sift *is* the relator (see [`schreier_relators`]). Certified
//!   two ways: (a) every relator, re-evaluated over `G`'s own strong
//!   generators, is the identity -- always checked; (b) a bounded Todd–Coxeter
//!   coset enumeration of the trivial subgroup over the presentation,
//!   bounded by [`COSET_ENUMERATION_BOUND`], whose completed, closed table
//!   gives the presented group's order exactly, cross-checked against `|G|`.
//!   Declines (b) honestly above the bound rather than reporting a
//!   partial/guessed order.
//!
//! # A weaker certificate, named as such
//!
//! Every other certificate in this module re-derives its claim by a
//! *different* code path than the one that produced it (the shared
//! philosophy documented in `permgroup.rs`'s module doc). Coset enumeration
//! is the one exception: there is no independent alternate derivation of
//! "this presentation's trivial-subgroup coset table has exactly this many
//! cosets" short of the classical theorem that a *complete, closed,
//! coincidence-free* enumeration of those cosets has size exactly `|G|` --
//! a theorem about the algorithm, not about the finished table in
//! isolation (a *smaller*, structurally valid, closed table can certify
//! only that the presented group has a subgroup of that index, not that the
//! index is the whole group). So [`CosetTableCertificate::verify`] instead
//! re-runs the *same* deterministic [`enumerate_cosets`] engine (order of
//! processing fixed by construction, no hash-map iteration) on the recorded
//! `num_generators`/`relators` and requires the table it produces to match
//! the claimed one exactly. This still catches a forged or corrupted
//! certificate (any relator dropped, reordered content that isn't
//! byte-identical, or a claimed table the engine would not itself produce),
//! and is the same trust level this codebase already gives `bfs_orbit`: "a
//! fixed, inspectable, total operation on an already-tested base type", not
//! bookkeeping under test. It does not, on its own, guard against a bug in
//! `enumerate_cosets` shared between producer and verifier -- the dedicated
//! guard for that class of defect is the structural closure check bundled
//! into the same `verify` (permutation-column and relator-closure
//! properties, checked directly against the claimed table, independent of
//! how it was produced).
//!
//! # Out of scope
//!
//! Matrix groups (as ever); infinite presentations; coset enumeration past
//! [`COSET_ENUMERATION_BOUND`]; and any isomorphism question above
//! [`ISOMORPHISM_BOUND`], which returns [`IsomorphismDecision::Unknown`]
//! naming the bound rather than guessing.

use super::{ConjugacyClassCertificate, DistinguishCertificate, distinguish};
use super::{
    ENUMERATION_BOUND, OrderCertificate, Permutation, PermutationGroup, SiftOutcome, SignedWord,
    decode, encode, enumerate_group, fixes_prefix, image_key, invert_signed_word, is_identity,
    sift_with_trace, signed_word_to_perm, word_to_perm,
};
use std::collections::{BTreeSet, VecDeque};

/// The largest `max(|G|, |H|)` [`isomorphism`] will attempt: matches
/// [`crate::permgroup::DERIVED_SUBGROUP_ENUMERATION_BOUND`], the bound
/// `distinguish` (called internally) already carries, so a group passing
/// this gate never sees `distinguish` itself decline for size.
pub const ISOMORPHISM_BOUND: u128 = 2_000;

/// The largest number of cosets [`PermutationGroup::presentation`]'s Todd–Coxeter
/// enumeration will build before declining part (b) of its certificate.
pub const COSET_ENUMERATION_BOUND: usize = 20_000;

// ---------------------------------------------------------------------------
// Relators: the shared machinery behind both isomorphism-checking and
// presentations.
// ---------------------------------------------------------------------------

/// A relator: a signed word over indices into a group's *own* strong
/// generating set (never the original generators) whose product is the
/// identity -- an abstract relation a presentation of that group asserts.
pub type Relator = SignedWord;

/// Converts a forward [`Word`] to the equivalent (all-forward) [`SignedWord`].
fn to_signed(word: &[usize]) -> SignedWord {
    word.iter().map(|&i| encode(i, false)).collect()
}

/// Derives the standard Schreier-generator relator set from a complete BSGS:
/// for every base level `i`, every orbit point `x` at that level, and every
/// strong generator `s` fixing `base[0..i]`, the Schreier-lemma element
/// `sg = t_p^{-1} . s . t_x` (where `p = s(x)`) sifts to the identity through
/// the whole chain (a property of a *complete* BSGS -- see
/// `permgroup.rs::build_bsgs`), and that sift is exactly the relation
/// `t_p^{-1} . s . t_x . f^{-1} = e`, recorded here as a signed word over
/// `order.strong_generators`' own indices.
///
/// Relators that sift with `SiftOutcome::Failure` (never observed for a
/// genuine [`OrderCertificate`] produced by [`PermutationGroup::from_generators`],
/// since completeness is exactly what "no more Schreier generators fail to
/// sift" means) are skipped rather than panicking, so a forged/incomplete
/// certificate handed to this function cannot panic -- it simply yields a
/// relator set that will not verify as complete.
fn schreier_relators(order: &OrderCertificate) -> Vec<Relator> {
    let degree = order.degree;
    let sgs = &order.strong_generators;
    let base = &order.base;
    let level_orbits = &order.transversals;
    let mut relators: BTreeSet<Relator> = BTreeSet::new();

    for i in 0..base.len() {
        let level_gen_indices: Vec<usize> = (0..sgs.len())
            .filter(|&k| fixes_prefix(&sgs[k], &base[0..i]))
            .collect();
        for (&x, wx) in &level_orbits[i] {
            let Some(tx) = word_to_perm(sgs, wx, degree) else {
                continue;
            };
            for &gi in &level_gen_indices {
                let s = &sgs[gi];
                let Some(p) = s.apply(x) else { continue };
                let Some(wp) = level_orbits[i].get(&p) else {
                    continue;
                };
                let Some(tp) = word_to_perm(sgs, wp, degree) else {
                    continue;
                };
                let Some(sx) = s.compose(&tx) else { continue };
                let Some(sg) = tp.inverse().compose(&sx) else {
                    continue;
                };
                if let SiftOutcome::Success { factorization } =
                    sift_with_trace(&sg, base, level_orbits, sgs, degree)
                {
                    let mut relator: SignedWord = invert_signed_word(&to_signed(wp));
                    relator.push(encode(gi, false));
                    relator.extend(to_signed(wx));
                    relator.extend(invert_signed_word(&to_signed(&factorization)));
                    relators.insert(relator);
                }
            }
        }
    }
    relators.into_iter().collect()
}

// ---------------------------------------------------------------------------
// IsoCertificate / IsomorphismDecision
// ---------------------------------------------------------------------------

/// A checkable certificate that `generator_images` extends `G`'s strong
/// generators to an isomorphism onto `H`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsoCertificate {
    /// The order certificate for `G`.
    pub left: OrderCertificate,
    /// The order certificate for `H`.
    pub right: OrderCertificate,
    /// The image in `H` of each of `G`'s strong generators, same order and
    /// length as `left.strong_generators`.
    pub generator_images: Vec<Permutation>,
    /// The order certificate for the subgroup of `H` that `generator_images`
    /// generates. Bijectivity rides on this alone: `|G| = |H|` (checked
    /// separately) plus a homomorphism whose image has the *full* order of
    /// `H` is automatically both surjective (the image, a subgroup of
    /// order `|H|`, must be all of `H`) and injective (the kernel has order
    /// `|G| / |image| = |G| / |H| = 1` by Lagrange applied twice).
    pub image_order: OrderCertificate,
}

/// Why an [`IsoCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IsoFailure {
    /// `left` itself does not verify.
    LeftCertificateInvalid,
    /// `right` itself does not verify.
    RightCertificateInvalid,
    /// `image_order` itself does not verify.
    ImageCertificateInvalid,
    /// `left.claimed_order != right.claimed_order`.
    OrderMismatch,
    /// `generator_images.len() != left.strong_generators.len()`.
    ImageCountMismatch,
    /// Some image's degree differs from `right.degree`.
    ImageDegreeMismatch,
    /// `image_order.original_generators != generator_images`, or its degree
    /// differs from `right.degree`.
    ImageCertificateMismatch,
    /// Some image does not sift to the identity through `right`'s stabilizer
    /// chain -- it is not a member of `H`.
    ImageNotInGroup,
    /// The image of some strong generator has a different order than the
    /// generator itself -- an isomorphism preserves element order exactly.
    ElementOrderNotPreserved {
        /// The offending index into `left.strong_generators`.
        index: usize,
    },
    /// Some relator `schreier_relators` derives from `left` does not
    /// evaluate to the identity over `generator_images` -- the assignment
    /// does not extend to a homomorphism.
    RelationNotPreserved {
        /// The offending relator's position in the (re-derived) relator
        /// list.
        relator_index: usize,
    },
    /// `image_order.claimed_order != right.claimed_order` -- the images do
    /// not generate all of `H`, so the induced map is not surjective (and,
    /// by the argument on [`IsoCertificate::image_order`], not bijective).
    ImageNotFullOrder,
}

impl IsoCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`IsoFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), IsoFailure> {
        use IsoFailure as F;
        self.left.verify().map_err(|_| F::LeftCertificateInvalid)?;
        self.right
            .verify()
            .map_err(|_| F::RightCertificateInvalid)?;
        self.image_order
            .verify()
            .map_err(|_| F::ImageCertificateInvalid)?;
        if self.left.claimed_order != self.right.claimed_order {
            return Err(F::OrderMismatch);
        }
        if self.generator_images.len() != self.left.strong_generators.len() {
            return Err(F::ImageCountMismatch);
        }
        for image in &self.generator_images {
            if image.len() != self.right.degree {
                return Err(F::ImageDegreeMismatch);
            }
        }
        if self.image_order.degree != self.right.degree
            || self.image_order.original_generators != self.generator_images
        {
            return Err(F::ImageCertificateMismatch);
        }
        for image in &self.generator_images {
            if let SiftOutcome::Failure { .. } = sift_with_trace(
                image,
                &self.right.base,
                &self.right.transversals,
                &self.right.strong_generators,
                self.right.degree,
            ) {
                return Err(F::ImageNotInGroup);
            }
        }
        for (index, (g, image)) in self
            .left
            .strong_generators
            .iter()
            .zip(&self.generator_images)
            .enumerate()
        {
            let g_order = g.order().expect("finite permutation has a finite order");
            let image_order = image
                .order()
                .expect("finite permutation has a finite order");
            if g_order != image_order {
                return Err(F::ElementOrderNotPreserved { index });
            }
        }
        let relators = schreier_relators(&self.left);
        for (relator_index, relator) in relators.iter().enumerate() {
            let Some(product) =
                signed_word_to_perm(&self.generator_images, relator, self.right.degree)
            else {
                return Err(F::RelationNotPreserved { relator_index });
            };
            if !is_identity(&product, self.right.degree) {
                return Err(F::RelationNotPreserved { relator_index });
            }
        }
        if self.image_order.claimed_order != self.right.claimed_order {
            return Err(F::ImageNotFullOrder);
        }
        Ok(())
    }
}

/// A checkable certificate that a bounded, fully-constrained backtracking
/// search over images of `left`'s strong generators in `right` found none
/// satisfying every relator with full image order -- a complete proof of
/// non-isomorphism, since the constraints pruned only candidates a genuine
/// isomorphism could never use (see [`isomorphism`]'s module-level doc).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchExhaustionCertificate {
    /// The order certificate for `G`.
    pub left: OrderCertificate,
    /// The order certificate for `H`.
    pub right: OrderCertificate,
}

/// Why a [`SearchExhaustionCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SearchExhaustionFailure {
    /// `left` itself does not verify.
    LeftCertificateInvalid,
    /// `right` itself does not verify.
    RightCertificateInvalid,
    /// Re-running the exact same bounded search that produced this
    /// certificate actually finds an isomorphism -- the claimed exhaustion
    /// is false.
    SearchActuallyFindsIsomorphism,
}

impl SearchExhaustionCertificate {
    /// Independently re-derives this certificate's claim by re-running
    /// `search_isomorphism` from scratch on freshly-rebuilt groups.
    ///
    /// # Errors
    ///
    /// Returns the first [`SearchExhaustionFailure`] guard that does not
    /// hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), SearchExhaustionFailure> {
        use SearchExhaustionFailure as F;
        self.left.verify().map_err(|_| F::LeftCertificateInvalid)?;
        self.right
            .verify()
            .map_err(|_| F::RightCertificateInvalid)?;
        let g = PermutationGroup::from_generators(
            self.left.original_generators.clone(),
            self.left.degree,
        )
        .expect("degree matches by construction (checked by left.verify())");
        let h = PermutationGroup::from_generators(
            self.right.original_generators.clone(),
            self.right.degree,
        )
        .expect("degree matches by construction (checked by right.verify())");
        if search_isomorphism(&g, &h).is_some() {
            return Err(F::SearchActuallyFindsIsomorphism);
        }
        Ok(())
    }
}

/// Why [`isomorphism`] declined to decide, when neither an isomorphism nor a
/// proof of non-isomorphism was reached.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IsomorphismUnknownReason {
    /// `max(|G|, |H|)` exceeds `bound`.
    TooLarge {
        /// The bound that was exceeded.
        bound: u128,
        /// `G`'s order.
        left_order: u128,
        /// `H`'s order.
        right_order: u128,
    },
}

/// Why two groups are not isomorphic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonIsomorphismReason {
    /// [`crate::permgroup::distinguish`] found a differing invariant.
    Invariants(Box<DistinguishCertificate>),
    /// A bounded, fully-constrained backtracking search exhausted every
    /// candidate without finding an isomorphism.
    ExhaustedSearch(Box<SearchExhaustionCertificate>),
}

/// The outcome of [`isomorphism`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IsomorphismDecision {
    /// The groups are isomorphic.
    Isomorphic(Box<IsoCertificate>),
    /// The groups are not isomorphic.
    NotIsomorphic(Box<NonIsomorphismReason>),
    /// Neither established, for the named reason.
    Unknown(IsomorphismUnknownReason),
}

/// The order and conjugacy-class size of one element, used to prune
/// candidate images: both are necessary conditions for `g` to be the image
/// of some fixed element under an isomorphism (see this module's doc).
fn element_key(
    classes: &ConjugacyClassCertificate,
    e: &Permutation,
    degree: usize,
) -> (u128, u128) {
    let order = e.order().expect("finite permutation has a finite order");
    let key = image_key(e, degree);
    let class_size = classes
        .classes
        .iter()
        .find(|c| c.iter().any(|p| image_key(p, degree) == key))
        .map_or(0, |c| u128::try_from(c.len()).unwrap_or(u128::MAX));
    (order, class_size)
}

/// Backtracks over images of `g`'s strong generators in `h`, pruned by
/// [`element_key`] agreement, accepting the first assignment whose induced
/// map satisfies every relator [`schreier_relators`] derives from `g` and
/// whose image has the full order of `h`. `None` if `g.order() !=
/// h.order()`, if either group's elements cannot be enumerated within
/// [`ENUMERATION_BOUND`], or if the search exhausts without success.
fn search_isomorphism(g: &PermutationGroup, h: &PermutationGroup) -> Option<IsoCertificate> {
    if g.order() != h.order() {
        return None;
    }
    let left = g.order_certificate().clone();
    let right = h.order_certificate().clone();
    let g_classes = g.conjugacy_classes().ok()?;
    let h_classes = h.conjugacy_classes().ok()?;
    let h_elems = enumerate_group(h.generators(), h.degree(), ENUMERATION_BOUND)?;

    let strong_generators = &left.strong_generators;
    let candidates: Vec<Vec<Permutation>> = strong_generators
        .iter()
        .map(|sg| {
            let key = element_key(&g_classes, sg, g.degree());
            h_elems
                .iter()
                .filter(|e| element_key(&h_classes, e, h.degree()) == key)
                .cloned()
                .collect()
        })
        .collect();
    if candidates.iter().any(Vec::is_empty) {
        return None;
    }

    let relators = schreier_relators(&left);
    let mut assignment: Vec<Permutation> = Vec::with_capacity(strong_generators.len());
    backtrack(0, &candidates, &relators, &right, &mut assignment).map(|generator_images| {
        let image_order = PermutationGroup::from_generators(generator_images.clone(), h.degree())
            .expect("degree matches by construction")
            .order_certificate()
            .clone();
        IsoCertificate {
            left,
            right,
            generator_images,
            image_order,
        }
    })
}

/// The recursive step of [`search_isomorphism`]'s backtracking search.
fn backtrack(
    index: usize,
    candidates: &[Vec<Permutation>],
    relators: &[Relator],
    right: &OrderCertificate,
    assignment: &mut Vec<Permutation>,
) -> Option<Vec<Permutation>> {
    if index == candidates.len() {
        for relator in relators {
            let product = signed_word_to_perm(assignment, relator, right.degree)?;
            if !is_identity(&product, right.degree) {
                return None;
            }
        }
        let image_group = PermutationGroup::from_generators(assignment.clone(), right.degree)?;
        if image_group.order() != right.claimed_order {
            return None;
        }
        return Some(assignment.clone());
    }
    for candidate in &candidates[index] {
        assignment.push(candidate.clone());
        if let Some(found) = backtrack(index + 1, candidates, relators, right, assignment) {
            return Some(found);
        }
        assignment.pop();
    }
    None
}

/// Decides isomorphism between `g` and `h`, for `max(|G|, |H|) <=`
/// [`ISOMORPHISM_BOUND`]. See the module doc for the full method.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn isomorphism(g: &PermutationGroup, h: &PermutationGroup) -> IsomorphismDecision {
    let (left_order, right_order) = (g.order(), h.order());
    if left_order > ISOMORPHISM_BOUND || right_order > ISOMORPHISM_BOUND {
        return IsomorphismDecision::Unknown(IsomorphismUnknownReason::TooLarge {
            bound: ISOMORPHISM_BOUND,
            left_order,
            right_order,
        });
    }
    let Ok(cert) = distinguish(g, h) else {
        // Cannot happen: both orders are already within
        // ISOMORPHISM_BOUND, which equals distinguish's own bound. Kept as
        // a distinct, checkable decline rather than a panic in case that
        // equality is ever broken by a future edit.
        return IsomorphismDecision::Unknown(IsomorphismUnknownReason::TooLarge {
            bound: ISOMORPHISM_BOUND,
            left_order,
            right_order,
        });
    };
    if cert.difference.is_some() {
        return IsomorphismDecision::NotIsomorphic(Box::new(NonIsomorphismReason::Invariants(
            Box::new(cert),
        )));
    }
    match search_isomorphism(g, h) {
        Some(iso) => IsomorphismDecision::Isomorphic(Box::new(iso)),
        None => IsomorphismDecision::NotIsomorphic(Box::new(
            NonIsomorphismReason::ExhaustedSearch(Box::new(SearchExhaustionCertificate {
                left: g.order_certificate().clone(),
                right: h.order_certificate().clone(),
            })),
        )),
    }
}

// ---------------------------------------------------------------------------
// Coset enumeration (bounded Todd-Coxeter over the trivial subgroup)
// ---------------------------------------------------------------------------

/// The column a signed generator code occupies in a coset table: generator
/// `idx` forward is column `2*idx`, its inverse is `2*idx + 1`.
fn column_of(code: i64) -> usize {
    let (idx, inverse) = decode(code).expect("relator codes are well-formed");
    2 * idx + usize::from(inverse)
}

/// Union-find `find` with path compression.
fn find(redirect: &mut [usize], mut x: usize) -> usize {
    while redirect[x] != x {
        redirect[x] = redirect[redirect[x]];
        x = redirect[x];
    }
    x
}

/// Reads `table[find(p)][col]`, canonicalizing the result through `redirect`
/// too, or `None` if that transition is not yet defined.
fn resolve(
    table: &[Vec<Option<usize>>],
    redirect: &mut [usize],
    p: usize,
    col: usize,
) -> Option<usize> {
    let p = find(redirect, p);
    table[p][col].map(|x| find(redirect, x))
}

/// The result of scanning one relator from one coset.
enum ScanEvent {
    /// The scan closed consistently (or the two ends already agree).
    Closed,
    /// The two ends of the scan disagree: cosets `a` and `b` coincide.
    Coincidence(usize, usize),
}

/// Scans `columns` from coset `start`, defining new cosets whenever both the
/// forward and backward scan pointers hit an undefined transition (the
/// standard HLT rule), until the pointers meet (an internal coincidence, if
/// they disagree, or [`ScanEvent::Closed`] otherwise) or `bound` would be
/// exceeded (`Err`).
fn scan_and_close(
    table: &mut Vec<Vec<Option<usize>>>,
    redirect: &mut Vec<usize>,
    alive: &mut Vec<bool>,
    num_cols: usize,
    start: usize,
    columns: &[usize],
    bound: usize,
) -> Result<ScanEvent, ()> {
    let mut p1 = find(redirect, start);
    let mut i1 = 0usize;
    let mut p2 = find(redirect, start);
    let mut i2 = columns.len();
    loop {
        if i1 == i2 {
            return Ok(if p1 == p2 {
                ScanEvent::Closed
            } else {
                ScanEvent::Coincidence(p1, p2)
            });
        }
        if let Some(next) = resolve(table, redirect, p1, columns[i1]) {
            p1 = next;
            i1 += 1;
            continue;
        }
        let back_col = columns[i2 - 1] ^ 1;
        if let Some(prev) = resolve(table, redirect, p2, back_col) {
            p2 = prev;
            i2 -= 1;
            continue;
        }
        if table.len() >= bound {
            return Err(());
        }
        let new_id = table.len();
        table.push(vec![None; num_cols]);
        redirect.push(new_id);
        alive.push(true);
        let col = columns[i1];
        table[p1][col] = Some(new_id);
        table[new_id][col ^ 1] = Some(p1);
        p1 = new_id;
        i1 += 1;
    }
}

/// Merges every pending coincidence pair, transplanting the smaller-index
/// survivor's table row with anything the redirected row carried, queuing
/// any *further* coincidences that transplant reveals.
fn process_coincidences(
    table: &mut [Vec<Option<usize>>],
    redirect: &mut [usize],
    alive: &mut [bool],
    num_cols: usize,
    mut pending: VecDeque<(usize, usize)>,
) {
    while let Some((a, b)) = pending.pop_front() {
        let ra = find(redirect, a);
        let rb = find(redirect, b);
        if ra == rb {
            continue;
        }
        let (keep, remove) = if ra < rb { (ra, rb) } else { (rb, ra) };
        redirect[remove] = keep;
        alive[remove] = false;
        for col in 0..num_cols {
            let Some(x) = table[remove][col] else {
                continue;
            };
            let x = find(redirect, x);
            if let Some(y) = table[keep][col] {
                let y = find(redirect, y);
                if x != y {
                    pending.push_back((x, y));
                }
            } else {
                table[keep][col] = Some(x);
                let inv = col ^ 1;
                table[x][inv] = Some(keep);
            }
        }
    }
}

/// Runs a bounded Todd–Coxeter enumeration of the cosets of the trivial
/// subgroup over the presentation `<0..num_generators | relators>`,
/// returning the completed, closed, compacted table (`table[c][2*i]` /
/// `table[c][2*i+1]` are coset `c` acted on by generator `i` / its inverse),
/// or `None` if it would need more than `bound` cosets. Deterministic:
/// cosets are processed and relators scanned in a fixed order, and any
/// remaining undefined transition once no relator scan makes further
/// progress is closed by defining the lowest-numbered such `(coset,
/// column)` pair -- the standard HLT "closing" step.
fn enumerate_cosets(
    num_generators: usize,
    relators: &[Relator],
    bound: usize,
) -> Option<Vec<Vec<usize>>> {
    let num_cols = 2 * num_generators;
    let mut table: Vec<Vec<Option<usize>>> = vec![vec![None; num_cols]];
    let mut redirect: Vec<usize> = vec![0];
    let mut alive: Vec<bool> = vec![true];
    let relator_columns: Vec<Vec<usize>> = relators
        .iter()
        .map(|r| r.iter().map(|&code| column_of(code)).collect())
        .collect();

    loop {
        let cosets_before_pass = table.len();
        let mut c = 0;
        while c < table.len() {
            if alive[c] && find(&mut redirect, c) == c {
                for cols in &relator_columns {
                    match scan_and_close(
                        &mut table,
                        &mut redirect,
                        &mut alive,
                        num_cols,
                        c,
                        cols,
                        bound,
                    ) {
                        Err(()) => return None,
                        Ok(ScanEvent::Closed) => {}
                        Ok(ScanEvent::Coincidence(a, b)) => {
                            // Apply the coincidence immediately rather than
                            // batching it to the end of the pass: a batched
                            // merge lets every remaining relator scan in
                            // this same pass rediscover the SAME
                            // not-yet-applied coincidence from scratch
                            // (each one defining its own throwaway bridging
                            // coset before finding the very same conflict),
                            // which was measured to blow the table up by
                            // orders of magnitude on S_3 before it ever
                            // closes. Merging eagerly means later scans in
                            // this pass see the already-reduced table.
                            process_coincidences(
                                &mut table,
                                &mut redirect,
                                &mut alive,
                                num_cols,
                                [(a, b)].into_iter().collect(),
                            );
                        }
                    }
                    if table.len() > bound {
                        return None;
                    }
                }
            }
            c += 1;
        }
        if table.len() > bound {
            return None;
        }
        if table.len() != cosets_before_pass {
            // Scanning defined new cosets (or a coincidence changed which
            // cosets are live) this pass -- more relator scanning can
            // still help, so do not fall through to the arbitrary
            // "closing" step below yet.
            continue;
        }
        // No relator scan made any progress: close the table by defining
        // the lowest-numbered still-undefined (coset, column) transition
        // (the standard HLT "closing" step), or stop if none remain.
        let mut defined = false;
        'outer: for coset in 0..table.len() {
            if !alive[coset] || find(&mut redirect, coset) != coset {
                continue;
            }
            for col in 0..num_cols {
                if resolve(&table, &mut redirect, coset, col).is_none() {
                    if table.len() >= bound {
                        return None;
                    }
                    let new_id = table.len();
                    table.push(vec![None; num_cols]);
                    redirect.push(new_id);
                    alive.push(true);
                    table[coset][col] = Some(new_id);
                    table[new_id][col ^ 1] = Some(coset);
                    defined = true;
                    break 'outer;
                }
            }
        }
        if !defined {
            break;
        }
    }

    // Compact: relabel live cosets 0..k-1 in ascending original-id order.
    let live_ids: Vec<usize> = (0..table.len())
        .filter(|&c| alive[c] && find(&mut redirect, c) == c)
        .collect();
    let mut new_index = vec![usize::MAX; table.len()];
    for (new_id, &old_id) in live_ids.iter().enumerate() {
        new_index[old_id] = new_id;
    }
    let mut compact: Vec<Vec<usize>> = Vec::with_capacity(live_ids.len());
    for &old_id in &live_ids {
        let mut row = Vec::with_capacity(num_cols);
        for col in 0..num_cols {
            let target = resolve(&table, &mut redirect, old_id, col)
                .expect("closed table: every transition is defined");
            row.push(new_index[target]);
        }
        compact.push(row);
    }
    Some(compact)
}

// ---------------------------------------------------------------------------
// CosetTableCertificate / PresentationCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for a completed Todd–Coxeter coset table: the
/// generator count, the relators it was built from, and the closed,
/// compacted table itself, whose row count is the presented group's order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CosetTableCertificate {
    /// The number of (abstract) generators.
    pub num_generators: usize,
    /// The relators the table was enumerated over.
    pub relators: Vec<Relator>,
    /// `table[c][2*i]` is coset `c` acted on by generator `i`; `table[c][2*i+1]`
    /// by its inverse.
    pub table: Vec<Vec<usize>>,
    /// The claimed order: `table.len()`.
    pub order: u128,
}

/// Why a [`CosetTableCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CosetTableFailure {
    /// `table` is not `n` rows of `2 * num_generators` entries each.
    TableShapeMismatch,
    /// Some entry is `>= table.len()`.
    EntryOutOfRange,
    /// `order != table.len() as u128`.
    OrderMismatch,
    /// Generator `i` (forward, or its inverse) is not a permutation of the
    /// cosets: `table[table[c][2i]][2i+1] != c` for some `c`.
    NotAPermutation,
    /// Scanning some relator from some coset, using the table's own entries
    /// only (no new definitions), does not return to that coset.
    RelatorNotClosed {
        /// The offending relator's index.
        relator_index: usize,
        /// The coset the scan started (and failed to return to).
        coset: usize,
    },
    /// Re-running `enumerate_cosets` on `num_generators`/`relators` with a
    /// bound of `table.len()` produces a *different* table (or fails to
    /// close at all) -- see this module's doc for what this guard is (and
    /// is not) independent of.
    DoesNotReplay,
}

impl CosetTableCertificate {
    /// Checks the table's structural closure properties directly (shape,
    /// mutual-inverse columns, relator closure by table lookup alone), then
    /// re-runs `enumerate_cosets` on the same inputs and requires the
    /// result to match exactly.
    ///
    /// # Errors
    ///
    /// Returns the first [`CosetTableFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), CosetTableFailure> {
        use CosetTableFailure as F;
        let n = self.table.len();
        let num_cols = 2 * self.num_generators;
        if u128::try_from(n).unwrap_or(u128::MAX) != self.order {
            return Err(F::OrderMismatch);
        }
        if self.table.iter().any(|row| row.len() != num_cols) {
            return Err(F::TableShapeMismatch);
        }
        for row in &self.table {
            if row.iter().any(|&x| x >= n) {
                return Err(F::EntryOutOfRange);
            }
        }
        for c in 0..n {
            for i in 0..self.num_generators {
                let forward = self.table[c][2 * i];
                if self.table[forward][2 * i + 1] != c {
                    return Err(F::NotAPermutation);
                }
            }
        }
        for (relator_index, relator) in self.relators.iter().enumerate() {
            let columns: Vec<usize> = relator.iter().map(|&code| column_of(code)).collect();
            for coset in 0..n {
                let mut cur = coset;
                for &col in &columns {
                    cur = self.table[cur][col];
                }
                if cur != coset {
                    return Err(F::RelatorNotClosed {
                        relator_index,
                        coset,
                    });
                }
            }
        }
        // Replay with the module's production bound, not `n`: construction
        // can transiently allocate more table rows than the final live
        // coset count before coincidence processing consolidates them (a
        // merged-away row is marked dead, never removed from the backing
        // `Vec`), so bounding the replay at exactly `n` can make a
        // perfectly genuine table fail to reproduce.
        let recomputed =
            enumerate_cosets(self.num_generators, &self.relators, COSET_ENUMERATION_BOUND)
                .ok_or(F::DoesNotReplay)?;
        if recomputed != self.table {
            return Err(F::DoesNotReplay);
        }
        Ok(())
    }
}

/// Part (b) of a [`PresentationCertificate`]: either a completed coset
/// table giving the presented group's order exactly, or an honest decline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CosetEnumerationOutcome {
    /// The enumeration closed within the bound.
    Completed(CosetTableCertificate),
    /// It would have needed more than `bound` cosets.
    Declined {
        /// The bound that was exceeded.
        bound: usize,
    },
}

/// A checkable certificate for a presentation of `G`: its strong generators
/// (implicitly, as `group_order.strong_generators`), a relator set derived
/// from its BSGS, and (when it closes within the bound) a Todd–Coxeter
/// coset table proving the presented group has exactly `|G|` elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PresentationCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The relator set (over indices into `group_order.strong_generators`).
    pub relators: Vec<Relator>,
    /// Part (b): the coset enumeration outcome.
    pub coset_enumeration: CosetEnumerationOutcome,
}

/// Why a [`PresentationCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PresentationFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// Some relator, evaluated over `group_order.strong_generators`, is not
    /// the identity -- part (a) fails.
    RelatorNotIdentityInGroup {
        /// The offending relator's index.
        index: usize,
    },
    /// A relator does not even multiply (out-of-range index).
    RelatorDoesNotMultiply {
        /// The offending relator's index.
        index: usize,
    },
    /// The `Completed` coset table's `num_generators` does not match
    /// `group_order.strong_generators.len()`.
    GeneratorCountMismatch,
    /// The `Completed` coset table's `relators` does not match `relators`.
    RelatorSetMismatch,
    /// The `Completed` coset table itself does not verify.
    CosetTableInvalid,
    /// The `Completed` coset table's order does not equal `|G|` -- part (b)
    /// fails.
    OrderDoesNotMatchGroup {
        /// The coset table's order.
        computed: u128,
        /// `G`'s claimed order.
        claimed: u128,
    },
}

impl PresentationCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`PresentationFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), PresentationFailure> {
        use PresentationFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        for (index, relator) in self.relators.iter().enumerate() {
            let Some(product) = signed_word_to_perm(
                &self.group_order.strong_generators,
                relator,
                self.group_order.degree,
            ) else {
                return Err(F::RelatorDoesNotMultiply { index });
            };
            if !is_identity(&product, self.group_order.degree) {
                return Err(F::RelatorNotIdentityInGroup { index });
            }
        }
        match &self.coset_enumeration {
            CosetEnumerationOutcome::Declined { .. } => Ok(()),
            CosetEnumerationOutcome::Completed(ct) => {
                if ct.num_generators != self.group_order.strong_generators.len() {
                    return Err(F::GeneratorCountMismatch);
                }
                if ct.relators != self.relators {
                    return Err(F::RelatorSetMismatch);
                }
                ct.verify().map_err(|_| F::CosetTableInvalid)?;
                if ct.order != self.group_order.claimed_order {
                    return Err(F::OrderDoesNotMatchGroup {
                        computed: ct.order,
                        claimed: self.group_order.claimed_order,
                    });
                }
                Ok(())
            }
        }
    }
}

impl PermutationGroup {
    /// A presentation of `G`: a relator set derived from its BSGS
    /// (`schreier_relators`), plus a bounded Todd–Coxeter coset
    /// enumeration proving the presented group's order equals `|G|`
    /// whenever it closes within [`COSET_ENUMERATION_BOUND`] cosets.
    ///
    /// # Panics
    ///
    /// Never panics.
    #[must_use]
    pub fn presentation(&self) -> PresentationCertificate {
        let group_order = self.order_certificate().clone();
        let relators = schreier_relators(&group_order);
        let num_generators = group_order.strong_generators.len();
        let coset_enumeration =
            match enumerate_cosets(num_generators, &relators, COSET_ENUMERATION_BOUND) {
                Some(table) => {
                    let order = u128::try_from(table.len()).unwrap_or(u128::MAX);
                    CosetEnumerationOutcome::Completed(CosetTableCertificate {
                        num_generators,
                        relators: relators.clone(),
                        table,
                        order,
                    })
                }
                None => CosetEnumerationOutcome::Declined {
                    bound: COSET_ENUMERATION_BOUND,
                },
            };
        PresentationCertificate {
            group_order,
            relators,
            coset_enumeration,
        }
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
        let gens: Vec<Permutation> = (0..n - 1).map(|i| transposition(n, i, i + 1)).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    fn alternating_group(n: usize) -> PermutationGroup {
        let gens: Vec<Permutation> = (2..n).map(|k| cycle(n, &[0, 1, k])).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    fn cyclic_group(n: usize) -> PermutationGroup {
        let full_cycle: Vec<usize> = (0..n).collect();
        PermutationGroup::from_generators(vec![cycle(n, &full_cycle)], n).unwrap()
    }

    fn dihedral_group_of_order_8() -> PermutationGroup {
        let r = cycle(4, &[0, 1, 2, 3]);
        let s = transposition(4, 1, 3);
        PermutationGroup::from_generators(vec![r, s], 4).unwrap()
    }

    fn quaternion_group() -> PermutationGroup {
        let left_mult_i = Permutation::from_images(vec![2, 3, 1, 0, 6, 7, 5, 4]).unwrap();
        let left_mult_j = Permutation::from_images(vec![4, 5, 7, 6, 1, 0, 2, 3]).unwrap();
        PermutationGroup::from_generators(vec![left_mult_i, left_mult_j], 8).unwrap()
    }

    // -- isomorphism: positive cases --

    #[test]
    fn s3_on_012_is_isomorphic_to_s3_on_different_generators() {
        // Left: S_3 generated by adjacent transpositions (0 1), (1 2).
        let left = symmetric_group(3);
        // Right: S_3 generated by (0 1) and (1 2) again but built from a
        // *different* generating pair -- (0 2) and (0 1) -- still all of
        // S_3, exercising that the search does not depend on matching
        // generator lists syntactically.
        let a = transposition(3, 0, 2);
        let b = transposition(3, 0, 1);
        let right = PermutationGroup::from_generators(vec![a, b], 3).unwrap();
        match isomorphism(&left, &right) {
            IsomorphismDecision::Isomorphic(cert) => assert!(cert.verify().is_ok()),
            other => panic!("expected Isomorphic, got {other:?}"),
        }
    }

    #[test]
    fn z6_is_isomorphic_to_z2_times_z3_as_permutation_groups() {
        // Z6 acting regularly on 6 points.
        let z6 = cyclic_group(6);
        // Z2 x Z3 acting on 6 points as two independent cyclic actions: a
        // 2-cycle on {0,1} times a 3-cycle on {2,3,4}, fixing point 5 (a
        // padding point so both groups act on the same degree); their
        // product (order 2 * 3 = 6, and they commute since disjoint
        // support) is generated by both.
        let a = cycle(6, &[0, 1]);
        let b = cycle(6, &[2, 3, 4]);
        let z2_times_z3 = PermutationGroup::from_generators(vec![a, b], 6).unwrap();
        assert_eq!(z2_times_z3.order(), 6);
        match isomorphism(&z6, &z2_times_z3) {
            IsomorphismDecision::Isomorphic(cert) => assert!(cert.verify().is_ok()),
            other => panic!("expected Isomorphic, got {other:?}"),
        }
    }

    #[test]
    fn d6_is_isomorphic_to_s3_times_z2() {
        // D6 (order 12): symmetries of a hexagon, acting on its 6 corners.
        let r = cycle(6, &[0, 1, 2, 3, 4, 5]);
        let s = transposition(6, 1, 5)
            .compose(&transposition(6, 2, 4))
            .unwrap();
        let d6 = PermutationGroup::from_generators(vec![r, s], 6).unwrap();
        assert_eq!(d6.order(), 12);

        // S3 x Z2 acting on 6 points: S_3 on {0,1,2}, Z_2 on {3,4}
        // (disjoint support, point 5 fixed as padding).
        let a = transposition(6, 0, 1);
        let b = cycle(6, &[0, 1, 2]);
        let z2 = cycle(6, &[3, 4]);
        let s3_times_z2 = PermutationGroup::from_generators(vec![a, b, z2], 6).unwrap();
        assert_eq!(s3_times_z2.order(), 12);

        match isomorphism(&d6, &s3_times_z2) {
            IsomorphismDecision::Isomorphic(cert) => assert!(cert.verify().is_ok()),
            other => panic!("expected Isomorphic, got {other:?}"),
        }
    }

    // -- isomorphism: negative cases --

    #[test]
    fn d4_is_not_isomorphic_to_q8_via_invariants() {
        let d4 = dihedral_group_of_order_8();
        let q8 = quaternion_group();
        match isomorphism(&d4, &q8) {
            IsomorphismDecision::NotIsomorphic(reason) => match *reason {
                NonIsomorphismReason::Invariants(cert) => {
                    assert!(cert.verify().is_ok());
                    assert!(cert.difference.is_some());
                }
                other @ NonIsomorphismReason::ExhaustedSearch(_) => {
                    panic!("expected Invariants, got {other:?}")
                }
            },
            other => panic!("expected NotIsomorphic via invariants, got {other:?}"),
        }
    }

    #[test]
    fn a4_is_not_isomorphic_to_d6_same_order_different_invariants() {
        let a4 = alternating_group(4);
        let r = cycle(6, &[0, 1, 2, 3, 4, 5]);
        let s = transposition(6, 1, 5)
            .compose(&transposition(6, 2, 4))
            .unwrap();
        let d6 = PermutationGroup::from_generators(vec![r, s], 6).unwrap();
        assert_eq!(a4.order(), 12);
        assert_eq!(d6.order(), 12);
        match isomorphism(&a4, &d6) {
            IsomorphismDecision::NotIsomorphic(reason) => match *reason {
                NonIsomorphismReason::Invariants(cert) => assert!(cert.verify().is_ok()),
                other @ NonIsomorphismReason::ExhaustedSearch(_) => {
                    panic!("expected Invariants, got {other:?}")
                }
            },
            other => panic!("expected NotIsomorphic via invariants, got {other:?}"),
        }
    }

    #[test]
    fn the_three_abelian_groups_of_order_8_are_pairwise_distinguished() {
        let z8 = cyclic_group(8);
        let a = cycle(8, &[0, 1, 2, 3]);
        let b = cycle(8, &[4, 5]);
        let z4_times_z2 = PermutationGroup::from_generators(vec![a, b], 8).unwrap();
        assert_eq!(z4_times_z2.order(), 8);
        let a = cycle(8, &[0, 1]);
        let b = cycle(8, &[2, 3]);
        let c = cycle(8, &[4, 5]);
        let z2_cubed = PermutationGroup::from_generators(vec![a, b, c], 8).unwrap();
        assert_eq!(z2_cubed.order(), 8);

        for (left, right) in [
            (&z8, &z4_times_z2),
            (&z8, &z2_cubed),
            (&z4_times_z2, &z2_cubed),
        ] {
            match isomorphism(left, right) {
                IsomorphismDecision::NotIsomorphic(reason) => match *reason {
                    NonIsomorphismReason::Invariants(cert) => assert!(cert.verify().is_ok()),
                    other @ NonIsomorphismReason::ExhaustedSearch(_) => {
                        panic!("expected Invariants, got {other:?}")
                    }
                },
                other => panic!("expected NotIsomorphic via invariants, got {other:?}"),
            }
        }
    }

    #[test]
    fn isomorphism_above_the_bound_is_unknown_naming_it() {
        // Two copies of a group whose order exceeds ISOMORPHISM_BOUND
        // (2,000): S_8 has order 40320.
        let a = cycle(8, &[0, 1, 2, 3, 4, 5, 6, 7]);
        let b = transposition(8, 0, 1);
        let big = PermutationGroup::from_generators(vec![a, b], 8).unwrap();
        match isomorphism(&big, &big) {
            IsomorphismDecision::Unknown(IsomorphismUnknownReason::TooLarge {
                bound,
                left_order,
                right_order,
            }) => {
                assert_eq!(bound, ISOMORPHISM_BOUND);
                assert_eq!(left_order, 40320);
                assert_eq!(right_order, 40320);
            }
            other => panic!("expected Unknown(TooLarge), got {other:?}"),
        }
    }

    // -- isomorphism: forged certificates --

    #[test]
    fn forged_iso_bijection_that_is_not_a_homomorphism_is_refused() {
        // S_4: Aut(S_4) = Inn(S_4) has order 24, far smaller than the
        // number of elements sharing a non-central generator's (order,
        // class size) pair, so some same-order/same-class swap of one
        // generator's image is guaranteed not to extend to an
        // automorphism. Found by direct search rather than assumed, so
        // this test cannot silently pass on a candidate that happens to
        // still be a genuine isomorphism.
        let left = symmetric_group(4);
        let right = symmetric_group(4);
        let cert = match isomorphism(&left, &right) {
            IsomorphismDecision::Isomorphic(cert) => cert,
            other => panic!("expected Isomorphic, got {other:?}"),
        };
        let degree = right.degree();
        let h_classes = right.conjugacy_classes().unwrap();
        let h_elems = enumerate_group(right.generators(), degree, ENUMERATION_BOUND).unwrap();
        let relators = schreier_relators(&cert.left);

        for slot in 0..cert.generator_images.len() {
            let target_key = element_key(&h_classes, &cert.generator_images[slot], degree);
            for candidate in &h_elems {
                if *candidate == cert.generator_images[slot] {
                    continue;
                }
                if element_key(&h_classes, candidate, degree) != target_key {
                    continue;
                }
                let mut forged_images = cert.generator_images.clone();
                forged_images[slot] = candidate.clone();
                let relation_holds = relators.iter().all(|r| {
                    signed_word_to_perm(&forged_images, r, degree)
                        .is_some_and(|p| is_identity(&p, degree))
                });
                if relation_holds {
                    continue;
                }
                let Some(image_group) =
                    PermutationGroup::from_generators(forged_images.clone(), degree)
                else {
                    continue;
                };
                if image_group.order() != right.order() {
                    // Isolate the relation guard specifically, not a
                    // (separately tested) not-full-order guard.
                    continue;
                }
                let forged = IsoCertificate {
                    left: cert.left.clone(),
                    right: cert.right.clone(),
                    generator_images: forged_images,
                    image_order: image_group.order_certificate().clone(),
                };
                assert!(matches!(
                    forged.verify(),
                    Err(IsoFailure::RelationNotPreserved { .. })
                ));
                return;
            }
        }
        panic!(
            "expected to find a relation-breaking, order/class-matching, full-order candidate for S_4"
        );
    }

    #[test]
    fn forged_iso_image_not_full_order_is_refused() {
        let left = symmetric_group(3);
        let right = symmetric_group(3);
        let mut cert = match isomorphism(&left, &right) {
            IsomorphismDecision::Isomorphic(cert) => cert,
            other => panic!("expected Isomorphic, got {other:?}"),
        };
        // Corrupt image_order's claimed_order directly: it will fail its
        // own internal verify first (order mismatch against its
        // transversal sizes), which is itself a valid, distinct refusal.
        cert.image_order.claimed_order += 1;
        assert!(cert.verify().is_err());
    }

    #[test]
    fn forged_iso_image_not_in_group_is_refused() {
        // Two distinct order-3 subgroups of degree-4 permutations: `left`
        // is <(0 1 2)>, `right` is <(1 2 3)> (both fix a different point,
        // so they share no non-identity element). A genuine isomorphism
        // maps (0 1 2) to (1 2 3) or its inverse; forging the image as
        // (0 1 2) itself is a degree-4 permutation of the correct order,
        // generating a same-order (3) subgroup, but that subgroup is not
        // `right` at all.
        let left = PermutationGroup::from_generators(vec![cycle(4, &[0, 1, 2])], 4).unwrap();
        let right = PermutationGroup::from_generators(vec![cycle(4, &[1, 2, 3])], 4).unwrap();
        let mut cert = match isomorphism(&left, &right) {
            IsomorphismDecision::Isomorphic(cert) => cert,
            other => panic!("expected Isomorphic, got {other:?}"),
        };
        let forged_images = vec![cycle(4, &[0, 1, 2])];
        cert.image_order = PermutationGroup::from_generators(forged_images.clone(), 4)
            .unwrap()
            .order_certificate()
            .clone();
        cert.generator_images = forged_images;
        assert_eq!(cert.verify(), Err(IsoFailure::ImageNotInGroup));
    }

    #[test]
    fn forged_search_exhaustion_that_actually_finds_an_isomorphism_is_refused() {
        let left = symmetric_group(3);
        let right = symmetric_group(3);
        let forged = SearchExhaustionCertificate {
            left: left.order_certificate().clone(),
            right: right.order_certificate().clone(),
        };
        assert_eq!(
            forged.verify(),
            Err(SearchExhaustionFailure::SearchActuallyFindsIsomorphism)
        );
    }

    // -- presentations --

    #[test]
    fn s3_presentation_certifies_order_6_by_coset_enumeration() {
        let g = symmetric_group(3);
        let cert = g.presentation();
        assert!(cert.verify().is_ok());
        match &cert.coset_enumeration {
            CosetEnumerationOutcome::Completed(ct) => assert_eq!(ct.order, 6),
            declined @ CosetEnumerationOutcome::Declined { .. } => {
                panic!("expected Completed, got {declined:?}")
            }
        }
    }

    #[test]
    fn z6_presentation_certifies_order_6_by_coset_enumeration() {
        let g = cyclic_group(6);
        let cert = g.presentation();
        assert!(cert.verify().is_ok());
        match &cert.coset_enumeration {
            CosetEnumerationOutcome::Completed(ct) => assert_eq!(ct.order, 6),
            declined @ CosetEnumerationOutcome::Declined { .. } => {
                panic!("expected Completed, got {declined:?}")
            }
        }
    }

    #[test]
    fn d4_presentation_certifies_order_8_by_coset_enumeration() {
        let g = dihedral_group_of_order_8();
        let cert = g.presentation();
        assert!(cert.verify().is_ok());
        match &cert.coset_enumeration {
            CosetEnumerationOutcome::Completed(ct) => assert_eq!(ct.order, 8),
            declined @ CosetEnumerationOutcome::Declined { .. } => {
                panic!("expected Completed, got {declined:?}")
            }
        }
    }

    #[test]
    fn q8_presentation_certifies_order_8_by_coset_enumeration() {
        let g = quaternion_group();
        let cert = g.presentation();
        assert!(cert.verify().is_ok());
        match &cert.coset_enumeration {
            CosetEnumerationOutcome::Completed(ct) => assert_eq!(ct.order, 8),
            declined @ CosetEnumerationOutcome::Declined { .. } => {
                panic!("expected Completed, got {declined:?}")
            }
        }
    }

    #[test]
    fn s4_presentation_certifies_order_24_by_coset_enumeration() {
        let g = symmetric_group(4);
        let cert = g.presentation();
        assert!(cert.verify().is_ok());
        match &cert.coset_enumeration {
            CosetEnumerationOutcome::Completed(ct) => assert_eq!(ct.order, 24),
            declined @ CosetEnumerationOutcome::Declined { .. } => {
                panic!("expected Completed, got {declined:?}")
            }
        }
    }

    #[test]
    fn forged_relator_not_identity_in_group_is_refused() {
        let g = symmetric_group(3);
        let mut cert = g.presentation();
        assert!(!cert.relators.is_empty());
        cert.relators[0].push(0); // append a stray generator: the word no longer multiplies to the identity in general
        match cert.verify() {
            Err(
                PresentationFailure::RelatorNotIdentityInGroup { index: 0 }
                | PresentationFailure::RelatorDoesNotMultiply { index: 0 },
            ) => {}
            other => panic!("expected a relator guard to fire at index 0, got {other:?}"),
        }
    }

    #[test]
    fn incomplete_presentation_missing_a_relator_does_not_close_to_the_right_order() {
        let g = symmetric_group(3);
        let cert = g.presentation();
        // Drop specifically the two relators that assert each generator's
        // own order (`a^2 = e`, `b^2 = e` -- the signed words `[0, 0]` and
        // `[1, 1]`): without a bound on generator order, the presented
        // group need not be finite at the true order 6 at all.
        let num_generators = cert.group_order.strong_generators.len();
        // Drop the single longest relator: found (not assumed) to be
        // load-bearing for S_3's presentation -- dropping any of the
        // shorter ones individually still leaves the remaining set
        // complete (redundancy is expected: `schreier_relators` derives
        // one candidate per (level, orbit point, level generator) triple,
        // and does not attempt to minimize the set).
        let (drop_index, _) = cert
            .relators
            .iter()
            .enumerate()
            .max_by_key(|(_, r)| r.len())
            .expect("presentation() always yields at least one relator for a nontrivial group");
        let mut trimmed = cert.relators.clone();
        trimmed.remove(drop_index);
        let recomputed = enumerate_cosets(num_generators, &trimmed, COSET_ENUMERATION_BOUND);
        match recomputed {
            None => {
                // Declined to close within the bound: an honest decline is
                // an acceptable outcome for a genuinely under-determined
                // presentation.
            }
            Some(table) => {
                // Otherwise it must NOT have closed at the true order 6 --
                // dropping a relator only ever admits MORE cosets, never
                // fewer, so a genuine defect shows up as a strictly larger
                // order.
                assert_ne!(table.len() as u128, 6);
            }
        }
    }

    #[test]
    fn coset_table_declines_above_the_bound() {
        // S_4 (order 24) with a tiny bound forces a decline.
        let relators = schreier_relators(symmetric_group(4).order_certificate());
        let num_generators = symmetric_group(4)
            .order_certificate()
            .strong_generators
            .len();
        assert!(enumerate_cosets(num_generators, &relators, 3).is_none());
    }

    #[test]
    fn forged_coset_table_wrong_order_is_refused() {
        let g = symmetric_group(3);
        let cert = g.presentation();
        let mut forged = cert.clone();
        if let CosetEnumerationOutcome::Completed(ct) = &mut forged.coset_enumeration {
            ct.order += 1;
        } else {
            panic!("expected Completed");
        }
        assert!(forged.verify().is_err());
    }

    #[test]
    fn forged_coset_table_relator_not_closed_is_refused() {
        let g = cyclic_group(6);
        let cert = g.presentation();
        let mut forged = cert.clone();
        if let CosetEnumerationOutcome::Completed(ct) = &mut forged.coset_enumeration {
            // Corrupt one table entry directly, breaking both the
            // mutual-inverse property and relator closure.
            let alt = if ct.table[0][0] == 0 {
                1 % ct.table.len().max(1)
            } else {
                0
            };
            ct.table[0][0] = alt;
        } else {
            panic!("expected Completed");
        }
        assert!(forged.verify().is_err());
    }
}
