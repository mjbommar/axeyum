//! T-C.1 property tests for the symbolic character-predicate algebra.
//!
//! Over the house LCG we check the Boolean-algebra laws (De Morgan,
//! involution, absorption), the **canonical-form uniqueness invariant**
//! (structural equality is semantic equality — differently-built but equal
//! predicates intern to identical `CharPred`s), and **mintermization
//! correctness** (returned atoms are pairwise disjoint, cover the alphabet, and
//! every input predicate is exactly the union of the atoms it contains).

use axeyum_strings::regex::predicate::{ALPHABET_MAX, CharPred};

/// Deterministic linear-congruential generator (the repo's house constant).
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u32) -> u32 {
        u32::try_from((self.next_u64() >> 33) % u64::from(n.max(1))).expect("fits u32")
    }
}

/// A random predicate built from a handful of small ranges over `0..=cap`,
/// occasionally reordered/overlapping to stress the coalescing canonicalizer.
fn random_pred(rng: &mut Lcg, cap: u32) -> CharPred {
    let n = rng.below(4); // 0..=3 ranges
    let mut ranges = Vec::new();
    for _ in 0..n {
        let a = rng.below(cap + 1);
        let b = rng.below(cap + 1);
        ranges.push((a.min(b), a.max(b)));
    }
    CharPred::from_ranges(ranges)
}

/// The canonical-form invariant: a predicate built from ranges in one order
/// equals the same predicate built from the reversed, duplicated ranges.
#[test]
fn canonical_form_is_unique() {
    let mut rng = Lcg(0x0CA1_0F0E_D15E_A5E1);
    for _ in 0..20_000 {
        let p = random_pred(&mut rng, 120);
        // Rebuild from its own (already-canonical) ranges, reversed and doubled.
        let mut raw: Vec<(u32, u32)> = p.ranges().to_vec();
        raw.extend_from_slice(p.ranges());
        raw.reverse();
        let q = CharPred::from_ranges(raw);
        assert_eq!(p, q, "canonical form must be order/duplication independent");
        // Structural equality must agree with pointwise membership.
        for c in [0u32, 1, 60, 119, 120, 121, ALPHABET_MAX] {
            assert_eq!(p.contains(c), q.contains(c));
        }
    }
}

#[test]
fn boolean_algebra_laws() {
    let mut rng = Lcg(0xB001_EA0A_1234_5678);
    for _ in 0..20_000 {
        let a = random_pred(&mut rng, 120);
        let b = random_pred(&mut rng, 120);

        // Involution: ¬¬a = a.
        assert_eq!(a.not().not(), a, "double complement");

        // De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b and ¬(a ∨ b) = ¬a ∧ ¬b.
        assert_eq!(a.and(&b).not(), a.not().or(&b.not()), "De Morgan ∧");
        assert_eq!(a.or(&b).not(), a.not().and(&b.not()), "De Morgan ∨");

        // Absorption: a ∨ (a ∧ b) = a and a ∧ (a ∨ b) = a.
        assert_eq!(a.or(&a.and(&b)), a, "absorption ∨");
        assert_eq!(a.and(&a.or(&b)), a, "absorption ∧");

        // Complement laws: a ∧ ¬a = ∅, a ∨ ¬a = Σ.
        assert!(a.and(&a.not()).is_empty(), "a ∧ ¬a = ∅");
        assert!(a.or(&a.not()).is_all(), "a ∨ ¬a = Σ");

        // Commutativity / idempotence.
        assert_eq!(a.and(&b), b.and(&a));
        assert_eq!(a.or(&b), b.or(&a));
        assert_eq!(a.and(&a), a);
        assert_eq!(a.or(&a), a);

        // Witness soundness: a non-empty predicate's witness is a member.
        match a.witness() {
            Some(w) => assert!(a.contains(w), "witness must be a member"),
            None => assert!(a.is_empty(), "no witness iff empty"),
        }
    }
}

#[test]
fn mintermization_correctness() {
    let mut rng = Lcg(0x3EA7_C0DE_FEED_0001);
    for _ in 0..5_000 {
        let k = 1 + rng.below(5); // 1..=5 input predicates
        let preds: Vec<CharPred> = (0..k).map(|_| random_pred(&mut rng, 90)).collect();
        let atoms = CharPred::mintermize(&preds);

        // (1) Atoms are non-empty.
        for atom in &atoms {
            assert!(!atom.is_empty(), "atoms must be non-empty");
        }

        // (2) Atoms are pairwise disjoint.
        for i in 0..atoms.len() {
            for j in (i + 1)..atoms.len() {
                assert!(
                    atoms[i].and(&atoms[j]).is_empty(),
                    "atoms must be pairwise disjoint"
                );
            }
        }

        // (3) Atoms cover the whole alphabet.
        let mut union = CharPred::none();
        for atom in &atoms {
            union = union.or(atom);
        }
        assert!(union.is_all(), "atoms must cover the alphabet");

        // (4) Every input predicate is exactly the union of the atoms it
        //     contains (each such atom is a subset of the predicate).
        for p in &preds {
            let mut rebuilt = CharPred::none();
            for atom in &atoms {
                if p.and(atom) == *atom {
                    // atom ⊆ p
                    rebuilt = rebuilt.or(atom);
                } else {
                    assert!(
                        p.and(atom).is_empty(),
                        "an atom must be wholly inside or outside each predicate"
                    );
                }
            }
            assert_eq!(&rebuilt, p, "predicate must be the union of its atoms");
        }
    }
}

#[test]
fn constructors_and_boundaries() {
    assert!(CharPred::none().is_empty());
    assert!(CharPred::all().is_all());
    assert!(CharPred::all().contains(ALPHABET_MAX));
    assert!(!CharPred::all().contains(ALPHABET_MAX + 1));

    // Out-of-range constructors clamp to the alphabet / empty.
    assert!(CharPred::singleton(ALPHABET_MAX + 1).is_empty());
    assert!(CharPred::range(5, 3).is_empty());
    assert_eq!(CharPred::range(0, ALPHABET_MAX + 100), CharPred::all());

    // Complement of the empty predicate is the full alphabet and vice versa.
    assert!(CharPred::none().not().is_all());
    assert!(CharPred::all().not().is_empty());
}
