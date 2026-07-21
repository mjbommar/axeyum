//! Permutations of `{0, 1, …, n−1}` as first-class objects — the computational
//! substrate for symmetric groups.
//!
//! A [`Permutation`] stores its one-line image vector (`images[i]` is where `i`
//! maps). It supports composition, inverse, order, sign (parity), and cycle
//! decomposition — all exact and total. Every constructor validates that the image
//! vector is a genuine bijection, so a `Permutation` is always a valid group
//! element; the group laws (`p · p⁻¹ = id`, associativity) are checked in tests by
//! direct computation, which is the certificate.

/// A permutation of `{0, …, n−1}` in one-line notation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Permutation {
    /// `images[i]` is the image of `i`; a bijection of `0..images.len()`.
    images: Vec<usize>,
}

impl Permutation {
    /// A permutation from a one-line image vector `images` (where `i ↦ images[i]`),
    /// or `None` if `images` is not a permutation of `0..images.len()`.
    #[must_use]
    pub fn from_images(images: Vec<usize>) -> Option<Permutation> {
        let n = images.len();
        let mut seen = vec![false; n];
        for &image in &images {
            if image >= n || seen[image] {
                return None; // out of range or repeated ⇒ not a bijection
            }
            seen[image] = true;
        }
        Some(Permutation { images })
    }

    /// A permutation from disjoint cycles over `0..n` (e.g. `[[0, 2, 1]]` sends
    /// `0→2→1→0`). Points not mentioned are fixed. `None` if any index is `≥ n` or
    /// appears more than once across the cycles.
    #[must_use]
    pub fn from_cycles(cycles: &[Vec<usize>], n: usize) -> Option<Permutation> {
        let mut images: Vec<usize> = (0..n).collect();
        let mut seen = vec![false; n];
        for cycle in cycles {
            for &point in cycle {
                if point >= n || seen[point] {
                    return None;
                }
                seen[point] = true;
            }
            for window in cycle.windows(2) {
                images[window[0]] = window[1];
            }
            if let (Some(&last), Some(&first)) = (cycle.last(), cycle.first()) {
                images[last] = first;
            }
        }
        Some(Permutation { images })
    }

    /// The identity permutation on `n` points.
    #[must_use]
    pub fn identity(n: usize) -> Permutation {
        Permutation {
            images: (0..n).collect(),
        }
    }

    /// The number of points `n` this permutation acts on.
    #[must_use]
    pub fn len(&self) -> usize {
        self.images.len()
    }

    /// Whether this permutation acts on zero points.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.images.is_empty()
    }

    /// The image of `point` under this permutation, or `None` if out of range.
    #[must_use]
    pub fn apply(&self, point: usize) -> Option<usize> {
        self.images.get(point).copied()
    }

    /// The composition `self ∘ other` (apply `other` first, then `self`). `None` if
    /// the two permutations act on different numbers of points.
    #[must_use]
    pub fn compose(&self, other: &Permutation) -> Option<Permutation> {
        if self.len() != other.len() {
            return None;
        }
        let images = other
            .images
            .iter()
            .map(|&point| self.images[point])
            .collect();
        Some(Permutation { images })
    }

    /// The inverse permutation `self⁻¹`.
    #[must_use]
    pub fn inverse(&self) -> Permutation {
        let mut images = vec![0usize; self.len()];
        for (point, &image) in self.images.iter().enumerate() {
            images[image] = point;
        }
        Permutation { images }
    }

    /// The disjoint-cycle decomposition, omitting fixed points (1-cycles). The
    /// identity yields an empty list.
    #[must_use]
    pub fn cycles(&self) -> Vec<Vec<usize>> {
        let mut visited = vec![false; self.len()];
        let mut cycles = Vec::new();
        for start in 0..self.len() {
            if visited[start] || self.images[start] == start {
                visited[start] = true;
                continue;
            }
            let mut cycle = Vec::new();
            let mut current = start;
            while !visited[current] {
                visited[current] = true;
                cycle.push(current);
                current = self.images[current];
            }
            cycles.push(cycle);
        }
        cycles
    }

    /// The order of the permutation — the least `k ≥ 1` with `selfᵏ = id` — equal to
    /// the LCM of its cycle lengths. The identity has order `1`. `None` on overflow.
    #[must_use]
    pub fn order(&self) -> Option<u128> {
        let mut result: u128 = 1;
        for cycle in self.cycles() {
            let length = u128::try_from(cycle.len()).ok()?;
            result = lcm_u128(result, length)?;
        }
        Some(result)
    }

    /// The sign (parity) of the permutation: `+1` for an even permutation, `−1` for
    /// an odd one. A cycle of length `ℓ` contributes parity `ℓ − 1`.
    #[must_use]
    pub fn sign(&self) -> i32 {
        let transpositions: usize = self.cycles().iter().map(|cycle| cycle.len() - 1).sum();
        if transpositions.is_multiple_of(2) {
            1
        } else {
            -1
        }
    }
}

/// The least common multiple of two `u128` values, or `None` on overflow.
fn lcm_u128(a: u128, b: u128) -> Option<u128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let mut x = a;
    let mut y = b;
    while y != 0 {
        (x, y) = (y, x % y);
    }
    (a / x).checked_mul(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composition_and_inverse_obey_the_group_laws() {
        let p = Permutation::from_images(vec![1, 2, 0]).unwrap(); // 0→1→2→0
        let q = Permutation::from_images(vec![0, 2, 1]).unwrap(); // swap 1,2
        // p ∘ p⁻¹ = identity (the group-inverse certificate).
        assert_eq!(p.compose(&p.inverse()).unwrap(), Permutation::identity(3));
        assert_eq!(p.inverse().compose(&p).unwrap(), Permutation::identity(3));
        // Associativity: (p∘q)∘p = p∘(q∘p).
        let left = p.compose(&q).unwrap().compose(&p).unwrap();
        let right = p.compose(&q.compose(&p).unwrap()).unwrap();
        assert_eq!(left, right);
    }

    #[test]
    fn cycles_round_trip() {
        // (0 2 1) on 4 points: 0→2, 2→1, 1→0, 3 fixed.
        let p = Permutation::from_cycles(&[vec![0, 2, 1]], 4).unwrap();
        assert_eq!(p.apply(0), Some(2));
        assert_eq!(p.apply(2), Some(1));
        assert_eq!(p.apply(1), Some(0));
        assert_eq!(p.apply(3), Some(3));
        // Reconstructing from the reported cycles gives the same permutation.
        let cycles = p.cycles();
        assert_eq!(Permutation::from_cycles(&cycles, 4).unwrap(), p);
    }

    #[test]
    fn order_is_lcm_of_cycle_lengths() {
        // A 2-cycle and a 3-cycle on 5 points ⇒ order lcm(2,3) = 6.
        let p = Permutation::from_cycles(&[vec![0, 1], vec![2, 3, 4]], 5).unwrap();
        assert_eq!(p.order(), Some(6));
        // Verify directly: p⁶ = id and no smaller power is.
        let mut power = Permutation::identity(5);
        for step in 1..=6 {
            power = p.compose(&power).unwrap();
            if step < 6 {
                assert_ne!(power, Permutation::identity(5));
            }
        }
        assert_eq!(power, Permutation::identity(5));
        assert_eq!(Permutation::identity(5).order(), Some(1));
    }

    #[test]
    fn sign_matches_transposition_parity() {
        // A single transposition is odd.
        assert_eq!(
            Permutation::from_cycles(&[vec![0, 1]], 3).unwrap().sign(),
            -1
        );
        // A 3-cycle is even (two transpositions).
        assert_eq!(
            Permutation::from_cycles(&[vec![0, 1, 2]], 3)
                .unwrap()
                .sign(),
            1
        );
        // The identity is even.
        assert_eq!(Permutation::identity(4).sign(), 1);
        // sign is a homomorphism: sign(p∘q) = sign(p)·sign(q).
        let p = Permutation::from_cycles(&[vec![0, 1]], 4).unwrap();
        let q = Permutation::from_cycles(&[vec![2, 3, 0]], 4).unwrap();
        assert_eq!(p.compose(&q).unwrap().sign(), p.sign() * q.sign());
    }

    #[test]
    fn invalid_image_vectors_are_rejected() {
        assert!(Permutation::from_images(vec![0, 0, 1]).is_none()); // repeated
        assert!(Permutation::from_images(vec![0, 1, 3]).is_none()); // out of range
        assert!(Permutation::from_cycles(&[vec![0, 5]], 3).is_none()); // index ≥ n
    }
}
