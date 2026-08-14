//! Generalized **off-diagonal** Schur numbers `S(r; k_1, …, k_r)`.
//!
//! For `k >= 3` write `L(k)` for the equation
//!
//! ```text
//! x_1 + x_2 + … + x_{k-1} = x_k
//! ```
//!
//! over the positive integers (`L(3)` is Schur's `x + y = z`). The generalized
//! off-diagonal Schur number `S(r; k_1, …, k_r)` is the least `N` such that
//! **every** `r`-colouring of `[1, N]` contains a monochromatic solution of
//! `L(k_c)` in *some* colour `c`. Each colour forbids its **own** equation,
//! which is what "off-diagonal" means and what makes this family the first one
//! in this crate that is not colour-symmetric.
//!
//! # The conjecture this family exists to test
//!
//! Ahmed and Schaal (2015) conjectured
//!
//! ```text
//! S(3; s, t, u) = s·t·u − t·u − u − 1        for 4 ≤ s ≤ t ≤ u,
//! ```
//!
//! still open as of arXiv:2604.11030 (Song and Mao, April 2026). The `≥`
//! direction is a theorem (Ahmed–Schaal Thm 2.11); the eleven values known
//! exactly — `(4,4,4)=43`, `(4,4,5)=54`, `(4,4,6)=65`, `(4,4,7)=76`,
//! `(4,5,5)=69`, `(4,5,6)=83`, `(4,5,7)=97`, `(4,6,6)=101`, `(5,5,5)=94`,
//! `(5,5,6)=113`, `(6,6,6)=173` — all match it. Deciding one open cell means
//! satisfying `n = N − 1` and refuting `n = N`.
//!
//! # Two facts that shape the encoding
//!
//! For `k >= 4` a solution has `k − 1 >= 3` positive parts, so the sum strictly
//! exceeds every part. Hence
//!
//! * a solution's distinct-value set has size `(#distinct parts) + 1`, and
//! * the only **two-element** sets are `{a, (k−1)a}`, from all-equal parts.
//!
//! The second fact is worth a lot. Every solution set containing both `a` and
//! `(k−1)a` is subsumed by that binary clause, and subsumption cascades. On
//! `L(8)` over `[1,87]` the 2,576,807 solution multisets collapse to a
//! 77,314-set antichain — a 33× reduction — which is the difference between an
//! instance that fits in memory and one that does not. See
//! [`OffDiagonalSchur::minimal_solution_sets`].
//!
//! **The reduction is sound in both directions and needs no extra argument.**
//! The retained sets are a subset of the full list, so a refutation of the
//! reduced formula refutes the full one; and every dropped clause is implied by
//! a retained one (a clause over a superset is implied by the clause over its
//! subset), so the two formulas have exactly the same models.
//!
//! # Symmetry breaking is not free here
//!
//! [`ColouringProblem`]'s default symmetry breaking orders colour classes by
//! least element, which is justified only by colour names being
//! interchangeable. Colours `c` and `c'` of this family are interchangeable
//! exactly when `k_c == k_{c'}`, so [`OffDiagonalSchur::symmetry_blocks`]
//! groups the colours by parameter and the encoder breaks symmetry only inside
//! a group. For `S(3;4,5,6)` there is no symmetry to break at all. Applying the
//! whole-palette ordering to such an instance removes genuine colourings and
//! yields a **wrong `unsat`**; `tests/offdiag_schur.rs` demonstrates that on an
//! instance whose answer is known independently, so the restriction is a
//! measured requirement rather than a stated one.

use std::collections::HashSet;

use crate::SearchError;
use crate::colouring::ColouringProblem;
use crate::family::ColouringFamily;

/// The largest point index this module's bitset arithmetic supports.
///
/// 255 is comfortably above every instance the conjecture's open cells need
/// (the largest is `n = 160`), and keeping a set in four words rather than
/// sixteen is worth a factor of three in the subsumption pass, which is the
/// only step that runs tens of millions of times.
const MAX_POINTS: usize = 256;

/// A set of points in `1..MAX_POINTS`, as a fixed bitmask.
type Mask = [u64; MAX_POINTS / 64];

fn mask_of(members: &[usize]) -> Mask {
    let mut mask = [0u64; MAX_POINTS / 64];
    for &member in members {
        mask[member >> 6] |= 1u64 << (member & 63);
    }
    mask
}

/// Whether `small` is a subset of `large`. Only the antichain property test
/// needs this directly; the reduction itself probes a hash table instead.
#[cfg(test)]
fn mask_subset(small: &Mask, large: &Mask) -> bool {
    small.iter().zip(large.iter()).all(|(&s, &l)| s & !l == 0)
}

/// A deterministic multiply-xor hasher for [`Mask`] keys.
///
/// `SipHash` is the right default for untrusted keys and the wrong one for
/// hundreds of millions of lookups against four words of our own bits. This is
/// a fixed function of the bytes — no seeds, no randomness — so the reduction
/// stays reproducible, which is a public API promise here.
#[derive(Debug, Clone, Copy, Default)]
struct MaskHasher(u64);

impl core::hash::Hasher for MaskHasher {
    fn finish(&self) -> u64 {
        let mut hash = self.0;
        hash ^= hash >> 33;
        hash = hash.wrapping_mul(0xff51_afd7_ed55_8ccd);
        hash ^= hash >> 33;
        hash
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.0 = (self.0 ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3);
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = (self.0 ^ value)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(31);
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct MaskHasherBuilder;

impl core::hash::BuildHasher for MaskHasherBuilder {
    type Hasher = MaskHasher;

    fn build_hasher(&self) -> MaskHasher {
        MaskHasher(0xcbf2_9ce4_8422_2325)
    }
}

/// The mask table wide retained sets live in.
type MaskSet = HashSet<Mask, MaskHasherBuilder>;

/// The retained-set table the subsumption pass probes.
///
/// Sets of size two and three get dense bitmaps rather than hash entries.
/// They are where essentially all subsumption comes from — every solution set
/// containing `{a, (k-1)a}` dies to one binary — and they are probed against
/// tens of millions of candidates, so a 2 MB table that answers in one shift
/// and one load beats a hash probe by an order of magnitude. Everything wider
/// falls back to the mask table.
#[derive(Debug, Default)]
struct Subsumers {
    /// Bit `a * MAX_POINTS + b` set when `{a, b}` (`a < b`) is retained.
    pairs: Vec<u64>,
    /// Bit `(a * MAX_POINTS + b) * MAX_POINTS + c` set for retained `{a,b,c}`.
    triples: Vec<u64>,
    /// Retained sets of size four and up.
    wide: MaskSet,
}

impl Subsumers {
    fn new() -> Self {
        Self {
            pairs: vec![0u64; MAX_POINTS * MAX_POINTS / 64],
            triples: vec![0u64; MAX_POINTS * MAX_POINTS * MAX_POINTS / 64],
            wide: MaskSet::default(),
        }
    }

    fn pair_bit(a: usize, b: usize) -> usize {
        a * MAX_POINTS + b
    }

    fn triple_bit(a: usize, b: usize, c: usize) -> usize {
        (a * MAX_POINTS + b) * MAX_POINTS + c
    }

    fn has_pair(&self, a: usize, b: usize) -> bool {
        let bit = Self::pair_bit(a, b);
        self.pairs[bit >> 6] & (1u64 << (bit & 63)) != 0
    }

    fn has_triple(&self, a: usize, b: usize, c: usize) -> bool {
        let bit = Self::triple_bit(a, b, c);
        self.triples[bit >> 6] & (1u64 << (bit & 63)) != 0
    }

    /// Records `set` (ascending, duplicate-free) as retained.
    fn insert(&mut self, set: &[usize]) {
        match set {
            [a, b] => {
                let bit = Self::pair_bit(*a, *b);
                self.pairs[bit >> 6] |= 1u64 << (bit & 63);
            }
            [a, b, c] => {
                let bit = Self::triple_bit(*a, *b, *c);
                self.triples[bit >> 6] |= 1u64 << (bit & 63);
            }
            wider => {
                self.wide.insert(mask_of(wider));
            }
        }
    }

    /// Whether some retained set is a subset of `set` — including `set` itself,
    /// which is how duplicates are dropped.
    fn subsumes(&self, set: &[usize]) -> bool {
        let len = set.len();
        for i in 0..len {
            for j in (i + 1)..len {
                if self.has_pair(set[i], set[j]) {
                    return true;
                }
                for slot in set.iter().take(len).skip(j + 1) {
                    if self.has_triple(set[i], set[j], *slot) {
                        return true;
                    }
                }
            }
        }
        if len >= 4 && self.wide.contains(&mask_of(set)) {
            return true;
        }
        (4..len).any(|size| subsumed_at_size(set, size, &self.wide))
    }
}

/// The off-diagonal generalized Schur family: colour `c` forbids monochromatic
/// solutions of `L(k[c - 1])`.
///
/// With every `k_c` equal this is the ordinary generalized Schur number
/// `S(r; k, …, k)`, and `k = 3` everywhere is the Schur number itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OffDiagonalSchur {
    k: Vec<usize>,
}

impl OffDiagonalSchur {
    /// Builds the family from one equation index per colour.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for an empty list or any
    /// `k_c < 3` — `L(2)` would be `x_1 = x_2`, monochromatic for every point,
    /// which is not the family this module is about.
    pub fn new(k: Vec<usize>) -> Result<Self, SearchError> {
        if k.is_empty() {
            return Err(SearchError::InvalidParameter {
                what: "offdiag-schur needs at least one colour".to_string(),
            });
        }
        if let Some(&bad) = k.iter().find(|&&value| value < 3) {
            return Err(SearchError::InvalidParameter {
                what: format!("offdiag-schur needs every k >= 3, got {bad}"),
            });
        }
        Ok(Self { k })
    }

    /// Builds the three-colour family `S(3; s, t, u)`.
    ///
    /// # Errors
    ///
    /// As [`OffDiagonalSchur::new`].
    pub fn triple(s: usize, t: usize, u: usize) -> Result<Self, SearchError> {
        Self::new(vec![s, t, u])
    }

    /// The equation index of each colour, `k()[c - 1]` for colour `c`.
    pub fn k(&self) -> &[usize] {
        &self.k
    }

    /// The Ahmed–Schaal conjectured value `s·t·u − t·u − u − 1` for the sorted
    /// parameters, or `None` outside `4 <= s <= t <= u` with three colours.
    ///
    /// This is a *prediction*, never evidence. It exists so a run can say which
    /// side of the conjecture it landed on without the caller re-deriving the
    /// arithmetic.
    pub fn conjectured_value(&self) -> Option<usize> {
        if self.k.len() != 3 {
            return None;
        }
        let mut sorted = self.k.clone();
        sorted.sort_unstable();
        let [s, t, u] = [sorted[0], sorted[1], sorted[2]];
        if s < 4 {
            return None;
        }
        Some(s * t * u - t * u - u - 1)
    }

    /// Visits every solution set of `L(k)` inside `1..=points`.
    ///
    /// Parts are enumerated non-decreasing in lexicographic order and the
    /// visitor receives the ascending, duplicate-free set of values appearing
    /// in the solution — the `k - 1` parts together with their sum. That order
    /// is the encoding contract.
    ///
    /// Nothing is materialised, which is the point: `L(7)` over `[1,160]` has
    /// 38,761,647 solution multisets and a `Vec<Vec<usize>>` of them costs
    /// gigabytes.
    pub fn visit_solution_sets(k: usize, points: usize, visit: &mut dyn FnMut(&[usize])) {
        if k < 3 || points == 0 {
            return;
        }
        let mut parts: Vec<usize> = Vec::with_capacity(k - 1);
        let mut set: Vec<usize> = Vec::with_capacity(k);
        descend(k - 1, 1, points, 0, &mut parts, &mut set, visit);
    }

    /// Every solution set of `L(k)` inside `1..=points`, in encoding order.
    ///
    /// Duplicates are possible and are kept: two different part multisets can
    /// share a distinct-value set and a sum (`1+1+1+2+3+3 = 11` and
    /// `1+1+2+2+2+3 = 11` both give `{1,2,3,11}`). Use
    /// [`OffDiagonalSchur::minimal_solution_sets`] for the deduplicated,
    /// subsumption-reduced list.
    ///
    /// This materialises the whole list; see
    /// [`OffDiagonalSchur::visit_solution_sets`] for the streaming form.
    pub fn solution_sets(k: usize, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        Self::visit_solution_sets(k, points, &mut |set| sets.push(set.to_vec()));
        sets
    }

    /// The subsumption-minimal antichain of `L(k)`'s solution sets inside
    /// `1..=points`: no retained set contains another, and every dropped set
    /// contains a retained one.
    ///
    /// Logically equivalent to [`OffDiagonalSchur::solution_sets`] as a set of
    /// clauses, and a subset of it, so it is sound for both the `sat` and the
    /// `unsat` side. Sets are returned ascending by size, then
    /// lexicographically, so the result is deterministic.
    ///
    /// The waves are processed in increasing size, so a candidate is dropped
    /// exactly when one of its proper subsets was already retained; a candidate
    /// equal to a retained set is dropped as a duplicate.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for `k < 3` and
    /// [`SearchError::PointOutOfRange`] for `points` outside `1..MAX_POINTS`.
    /// Neither returns an empty list: a silently empty constraint set encodes a
    /// formula that is satisfiable for every `n`, which reads exactly like a
    /// genuine `sat`.
    pub fn minimal_solution_sets(k: usize, points: usize) -> Result<Vec<Vec<usize>>, SearchError> {
        if k < 3 {
            return Err(SearchError::InvalidParameter {
                what: format!("L({k}) is not a generalized Schur equation; need k >= 3"),
            });
        }
        if points == 0 || points > MAX_POINTS - 1 {
            // Returning an empty list here would encode a formula with no
            // constraints at all, which is satisfiable for every n and would
            // read exactly like a genuine `sat`. Refuse instead.
            return Err(SearchError::PointOutOfRange {
                point: points,
                points: MAX_POINTS - 1,
            });
        }
        // Wave 0: the sets of size <= 3. There are O(points^2) of them, they
        // are the cheapest possible subsumers, and filtering the full stream
        // with them first is what keeps the buckets below small enough to hold.
        let mut small: Vec<Vec<usize>> = Vec::new();
        Self::visit_solution_sets(k, points, &mut |set| {
            if set.len() <= 3 {
                small.push(set.to_vec());
            }
        });
        small.sort_unstable_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        small.dedup();
        let mut retained = Subsumers::new();
        let mut kept: Vec<Vec<usize>> = Vec::new();
        for set in small {
            if !retained.subsumes(&set) {
                retained.insert(&set);
                kept.push(set);
            }
        }

        // Waves 1..: everything larger, bucketed by size, filtered by the small
        // sets on the way in so the buckets never hold the full stream. The
        // filter is a table probe of the candidate's own pairs and triples, not
        // a scan of the retained list — the scan is O(retained) per candidate
        // and there are tens of millions of candidates.
        let mut buckets: Vec<Vec<Vec<usize>>> = vec![Vec::new(); k + 2];
        Self::visit_solution_sets(k, points, &mut |set| {
            if set.len() <= 3 || retained.subsumes(set) {
                return;
            }
            buckets[set.len()].push(set.to_vec());
        });
        for slot in buckets.iter_mut().skip(4) {
            let mut bucket = std::mem::take(slot);
            bucket.sort_unstable();
            for set in bucket {
                // Inserted as we go, not in a batch: two candidates of the same
                // size can only subsume each other by being equal, and that is
                // exactly the duplicate we want the second one to lose to.
                if retained.subsumes(&set) {
                    continue;
                }
                retained.insert(&set);
                kept.push(set);
            }
        }
        Ok(kept)
    }

    /// The colours grouped by equation index: colours `c` and `c'` land in the
    /// same block exactly when `k_c == k_{c'}`, and only those are
    /// interchangeable.
    ///
    /// Blocks are ordered by their least colour and each block is ascending.
    pub fn parameter_blocks(&self) -> Vec<Vec<usize>> {
        let mut blocks: Vec<(usize, Vec<usize>)> = Vec::new();
        for (index, &value) in self.k.iter().enumerate() {
            let colour = index + 1;
            match blocks.iter_mut().find(|(parameter, _)| *parameter == value) {
                Some((_, members)) => members.push(colour),
                None => blocks.push((value, vec![colour])),
            }
        }
        blocks.into_iter().map(|(_, members)| members).collect()
    }

    /// The problem built from the **minimal** solution sets rather than the
    /// full enumeration.
    ///
    /// Same models as [`ColouringFamily::problem`], far fewer clauses, and the
    /// clause list is a subset of the full one. This is the constructor the
    /// large instances need.
    ///
    /// # Errors
    ///
    /// As [`ColouringProblem::per_colour`].
    pub fn minimal_problem(&self, points: usize) -> Result<ColouringProblem, SearchError> {
        // Colours sharing a parameter share their constraint list, and the
        // reduction is the expensive step: on `S(3;6,6,6)` at n = 173 it is
        // ~40 s per colour, so recomputing it three times is 80 s of nothing.
        let mut cache: Vec<(usize, Vec<Vec<usize>>)> = Vec::new();
        let mut per_colour = Vec::with_capacity(self.k.len());
        for &k in &self.k {
            let sets = if let Some((_, sets)) = cache.iter().find(|(cached, _)| *cached == k) {
                sets.clone()
            } else {
                let sets = Self::minimal_solution_sets(k, points)?;
                cache.push((k, sets.clone()));
                sets
            };
            per_colour.push(sets);
        }
        ColouringProblem::per_colour(points, self.k.len(), per_colour, self.parameter_blocks())
    }
}

/// The widest solution set this module will subsume against, and so the widest
/// combination [`subsumed_at_size`] indexes.
const MAX_SET: usize = 24;

/// Whether some `size`-element subset of `set` is retained.
fn subsumed_at_size(set: &[usize], size: usize, retained: &MaskSet) -> bool {
    let len = set.len();
    debug_assert!(len <= MAX_SET, "solution sets stay small");
    if size >= len || len > MAX_SET {
        return false;
    }
    let mut choice = [0usize; MAX_SET];
    for (slot, entry) in choice.iter_mut().enumerate().take(size) {
        *entry = slot;
    }
    loop {
        let mut subset: Mask = [0u64; MAX_POINTS / 64];
        for &index in &choice[..size] {
            let member = set[index];
            subset[member >> 6] |= 1u64 << (member & 63);
        }
        if retained.contains(&subset) {
            return true;
        }
        // Next combination in lexicographic order; the loop ends when the
        // last one has been visited.
        let mut slot = size;
        loop {
            if slot == 0 {
                return false;
            }
            slot -= 1;
            if choice[slot] != slot + len - size {
                break;
            }
        }
        choice[slot] += 1;
        for follow in (slot + 1)..size {
            choice[follow] = choice[follow - 1] + 1;
        }
    }
}

/// Recursive non-decreasing part enumeration behind
/// [`OffDiagonalSchur::visit_solution_sets`].
fn descend(
    remaining: usize,
    min: usize,
    budget: usize,
    total: usize,
    parts: &mut Vec<usize>,
    set: &mut Vec<usize>,
    visit: &mut dyn FnMut(&[usize]),
) {
    if remaining == 0 {
        set.clear();
        for &part in parts.iter() {
            if set.last() != Some(&part) {
                set.push(part);
            }
        }
        // Every part is positive and there are at least two of them, so the sum
        // strictly exceeds each part and belongs at the end.
        set.push(total);
        visit(set);
        return;
    }
    let top = budget / remaining;
    for value in min..=top {
        parts.push(value);
        descend(
            remaining - 1,
            value,
            budget - value,
            total + value,
            parts,
            set,
            visit,
        );
        parts.pop();
    }
}

impl ColouringFamily for OffDiagonalSchur {
    fn name(&self) -> &'static str {
        "offdiag-schur"
    }

    fn label(&self) -> String {
        let mut parameters = String::new();
        for (position, value) in self.k.iter().enumerate() {
            if position > 0 {
                parameters.push(',');
            }
            parameters.push_str(&value.to_string());
        }
        format!("S({};{parameters})", self.k.len())
    }

    fn colours(&self) -> usize {
        self.k.len()
    }

    /// The sets forbidden in **every** colour: the intersection over the
    /// colours' relations.
    ///
    /// For a genuinely off-diagonal instance this is a *relaxation*, not the
    /// encoding — [`ColouringFamily::colour_dependent`] is `true`, so
    /// `problem()` never routes through here. It is deliberately the weak
    /// direction: a caller that ignores the per-colour split gets a formula
    /// with fewer constraints, whose `unsat` still implies the real `unsat`.
    fn constraints(&self, points: usize) -> Vec<Vec<usize>> {
        let mut shared: Option<HashSet<Vec<usize>>> = None;
        for &k in &self.k {
            let sets: HashSet<Vec<usize>> = Self::solution_sets(k, points).into_iter().collect();
            shared = Some(match shared {
                None => sets,
                Some(previous) => previous.intersection(&sets).cloned().collect(),
            });
        }
        let mut sets: Vec<Vec<usize>> = shared.unwrap_or_default().into_iter().collect();
        sets.sort_unstable_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        sets
    }

    fn constraints_for_colour(&self, colour: usize, points: usize) -> Vec<Vec<usize>> {
        match self.k.get(colour - 1) {
            Some(&k) => Self::solution_sets(k, points),
            None => Vec::new(),
        }
    }

    fn colour_dependent(&self) -> bool {
        true
    }

    fn symmetry_blocks(&self) -> Vec<Vec<usize>> {
        self.parameter_blocks()
    }

    /// Brute force straight off `x_1 + … + x_{k-1} = x_k`, per colour.
    ///
    /// For each colour `c` this asks, by reachability over the colour class
    /// itself, whether some member of the class is a sum of exactly `k_c - 1`
    /// members of the class. It shares no code with
    /// [`OffDiagonalSchur::visit_solution_sets`] — no partitions, no
    /// non-decreasing enumeration, no subsumption — which is the whole reason
    /// it exists.
    ///
    /// The reported violation is deterministic: the lowest colour, then the
    /// smallest right-hand side, then the parts recovered greedily from the
    /// smallest reachable predecessor.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for (index, &k) in self.k.iter().enumerate() {
            let colour = index + 1;
            let class: Vec<usize> = (1..=points)
                .filter(|&point| colouring[point - 1] == colour)
                .collect();
            if class.is_empty() {
                continue;
            }
            let parts = k - 1;
            // reach[j][v]: v is a sum of exactly j members of the class.
            let mut reach = vec![vec![false; points + 1]; parts + 1];
            reach[0][0] = true;
            for count in 1..=parts {
                for &member in &class {
                    for value in member..=points {
                        if reach[count - 1][value - member] {
                            reach[count][value] = true;
                        }
                    }
                }
            }
            let Some(&target) = class.iter().find(|&&value| reach[parts][value]) else {
                continue;
            };
            // Recover the parts by walking the table back down.
            let mut members = Vec::with_capacity(k);
            let mut value = target;
            for count in (1..=parts).rev() {
                let part = *class
                    .iter()
                    .find(|&&member| member <= value && reach[count - 1][value - member])
                    .expect("reachability table is consistent with itself");
                members.push(part);
                value -= part;
            }
            debug_assert_eq!(value, 0, "the parts sum to the target");
            members.push(target);
            members.sort_unstable();
            members.dedup();
            return Some((members, colour));
        }
        None
    }

    /// Low points first. There is no colour symmetry to lean on here, and the
    /// small integers are where the binary clauses `{a, (k−1)a}` bite, so
    /// branching on `2, 3, 4, …` splits the search far better than the default
    /// every-other-point plan.
    fn branch_points(&self, depth: usize) -> Vec<usize> {
        (1..=depth).map(|slot| slot + 1).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solution_sets_are_the_partitions_of_the_right_arity() {
        // L(4) on [1..6]: partitions of s <= 6 into exactly 3 parts.
        let sets = OffDiagonalSchur::solution_sets(4, 6);
        assert_eq!(
            sets,
            vec![
                vec![1, 3],       // 1+1+1 = 3
                vec![1, 2, 4],    // 1+1+2 = 4
                vec![1, 3, 5],    // 1+1+3 = 5
                vec![1, 4, 6],    // 1+1+4 = 6
                vec![1, 2, 5],    // 1+2+2 = 5
                vec![1, 2, 3, 6], // 1+2+3 = 6
                vec![2, 6],       // 2+2+2 = 6
            ]
        );
    }

    #[test]
    fn l3_is_schur() {
        // L(3) is x + y = z, so the sets are {x, z-x, z}.
        let sets = OffDiagonalSchur::solution_sets(3, 5);
        assert_eq!(
            sets,
            vec![
                vec![1, 2],    // 1+1 = 2
                vec![1, 2, 3], // 1+2 = 3
                vec![1, 3, 4], // 1+3 = 4
                vec![1, 4, 5], // 1+4 = 5
                vec![2, 4],    // 2+2 = 4
                vec![2, 3, 5], // 2+3 = 5
            ]
        );
        // Same sets — in a different order — as the crate's own Schur family,
        // which enumerates by right-hand side rather than by parts. Two
        // independent enumerations of `x + y = z` agreeing is a real check.
        let mut ours = OffDiagonalSchur::solution_sets(3, 24);
        let mut theirs = crate::family::Schur::new(3)
            .expect("family")
            .constraints(24);
        ours.sort_unstable();
        ours.dedup();
        theirs.sort_unstable();
        theirs.dedup();
        assert_eq!(ours, theirs);
        assert!(
            ours.len() >= 100,
            "{} sets is too few to mean much",
            ours.len()
        );
    }

    #[test]
    fn minimal_sets_are_an_antichain_that_covers_the_full_list() {
        for k in 3..=6 {
            for points in [8usize, 20, 31] {
                let full = OffDiagonalSchur::solution_sets(k, points);
                let minimal = OffDiagonalSchur::minimal_solution_sets(k, points).expect("minimal");
                let retained: HashSet<Vec<usize>> = minimal.iter().cloned().collect();
                assert_eq!(retained.len(), minimal.len(), "k={k} n={points} duplicates");
                // Antichain: no retained set contains another.
                for (i, a) in minimal.iter().enumerate() {
                    for (j, b) in minimal.iter().enumerate() {
                        if i != j {
                            assert!(
                                !mask_subset(&mask_of(a), &mask_of(b)),
                                "k={k} n={points}: {a:?} subsumes retained {b:?}"
                            );
                        }
                    }
                }
                // Covering: every full set contains a retained one, and every
                // retained set is a full set.
                let full_set: HashSet<Vec<usize>> = full.iter().cloned().collect();
                for set in &minimal {
                    assert!(full_set.contains(set), "k={k} n={points}: {set:?} invented");
                }
                for set in &full {
                    let mask = mask_of(set);
                    assert!(
                        minimal
                            .iter()
                            .any(|kept| mask_subset(&mask_of(kept), &mask)),
                        "k={k} n={points}: {set:?} is not implied by any retained set"
                    );
                }
                assert!(!minimal.is_empty(), "k={k} n={points} produced nothing");
            }
        }
    }

    #[test]
    fn first_violation_finds_a_monochromatic_solution_per_colour() {
        let family = OffDiagonalSchur::triple(4, 4, 5).expect("family");
        // Colour 3 forbids L(5): 1+1+1+1 = 4, so {1,4} all in colour 3.
        let colouring = vec![3, 1, 2, 3, 1];
        assert_eq!(
            family.first_violation(&colouring),
            Some((vec![1, 4], 3)),
            "colour 3 forbids x1+x2+x3+x4=x5"
        );
        // The same {1,4} in colour 1 is NOT a violation: colour 1 forbids L(4),
        // and 1+1+1 = 3 != 4.
        let colouring = vec![1, 2, 3, 1, 2];
        assert_eq!(family.first_violation(&colouring), None);
    }

    #[test]
    fn first_violation_is_colour_scoped_not_colour_blind() {
        // S(3;3,4,4): colour 1 forbids x+y=z, colours 2 and 3 forbid
        // x1+x2+x3=x4. {1,2} monochromatic is a violation in colour 1 only.
        let family = OffDiagonalSchur::triple(3, 4, 4).expect("family");
        assert_eq!(family.first_violation(&[1, 1, 2, 2]), Some((vec![1, 2], 1)));
        assert_eq!(family.first_violation(&[2, 2, 1, 3]), None);
    }

    #[test]
    fn independent_enumerator_and_encoder_view_agree_on_random_colourings() {
        for k in [vec![3, 4, 4], vec![4, 4, 5], vec![4, 5, 6], vec![3, 3, 3]] {
            let family = OffDiagonalSchur::new(k.clone()).expect("family");
            let points = 22usize;
            let problem = family.problem(points).expect("problem");
            let minimal = family.minimal_problem(points).expect("minimal problem");
            let mut state = 0x2026_0813_u64;
            let mut compared = 0usize;
            for _ in 0..128 {
                let colouring: Vec<usize> = (0..points)
                    .map(|_| {
                        state = state
                            .wrapping_mul(6_364_136_223_846_793_005)
                            .wrapping_add(1);
                        ((state >> 33) % 3) as usize + 1
                    })
                    .collect();
                let independent = family.first_violation(&colouring).is_none();
                assert_eq!(
                    independent,
                    problem.first_monochromatic(&colouring).is_none(),
                    "k={k:?}: independent and encoder views disagree on {colouring:?}"
                );
                assert_eq!(
                    independent,
                    minimal.first_monochromatic(&colouring).is_none(),
                    "k={k:?}: minimal encoding disagrees on {colouring:?}"
                );
                compared += 1;
            }
            assert_eq!(compared, 128);
        }
    }

    #[test]
    fn parameter_blocks_group_only_equal_equations() {
        assert_eq!(
            OffDiagonalSchur::triple(4, 4, 8)
                .expect("family")
                .parameter_blocks(),
            vec![vec![1, 2], vec![3]]
        );
        assert_eq!(
            OffDiagonalSchur::triple(4, 5, 6)
                .expect("family")
                .parameter_blocks(),
            vec![vec![1], vec![2], vec![3]]
        );
        assert_eq!(
            OffDiagonalSchur::triple(6, 6, 6)
                .expect("family")
                .parameter_blocks(),
            vec![vec![1, 2, 3]]
        );
        // Equal parameters need not be adjacent.
        assert_eq!(
            OffDiagonalSchur::triple(4, 5, 4)
                .expect("family")
                .parameter_blocks(),
            vec![vec![1, 3], vec![2]]
        );
    }

    #[test]
    fn conjectured_values_reproduce_the_eleven_known_ones() {
        let known = [
            (4, 4, 4, 43),
            (4, 4, 5, 54),
            (4, 4, 6, 65),
            (4, 4, 7, 76),
            (4, 5, 5, 69),
            (4, 5, 6, 83),
            (4, 5, 7, 97),
            (4, 6, 6, 101),
            (5, 5, 5, 94),
            (5, 5, 6, 113),
            (6, 6, 6, 173),
        ];
        let mut checked = 0usize;
        for (s, t, u, value) in known {
            let family = OffDiagonalSchur::triple(s, t, u).expect("family");
            assert_eq!(
                family.conjectured_value(),
                Some(value),
                "Ahmed-Schaal formula misses S(3;{s},{t},{u})"
            );
            checked += 1;
        }
        assert_eq!(checked, 11);
        // Outside the conjecture's range there is no prediction to offer.
        assert_eq!(
            OffDiagonalSchur::triple(3, 4, 5)
                .expect("family")
                .conjectured_value(),
            None
        );
    }

    #[test]
    fn labels_and_shape() {
        let family = OffDiagonalSchur::triple(4, 4, 8).expect("family");
        assert_eq!(family.label(), "S(3;4,4,8)");
        assert_eq!(family.colours(), 3);
        assert!(family.colour_dependent());
        assert!(OffDiagonalSchur::new(vec![2, 4, 4]).is_err());
        assert!(OffDiagonalSchur::new(Vec::new()).is_err());
    }

    #[test]
    fn the_encoded_problem_scopes_every_set_to_one_colour() {
        let family = OffDiagonalSchur::triple(3, 4, 4).expect("family");
        let problem = family.problem(6).expect("problem");
        assert!(problem.is_off_diagonal());
        let colour_one = OffDiagonalSchur::solution_sets(3, 6).len();
        let colour_two = OffDiagonalSchur::solution_sets(4, 6).len();
        assert_eq!(
            problem.forbidden().len(),
            colour_one + 2 * colour_two,
            "flattened colour-major"
        );
        assert_eq!(problem.scope(0), Some(1));
        assert_eq!(problem.scope(colour_one), Some(2));
        assert_eq!(problem.scope(colour_one + colour_two), Some(3));
        assert_eq!(
            problem.symmetry_blocks().map(<[Vec<usize>]>::to_vec),
            Some(vec![vec![1], vec![2, 3]])
        );
    }
}
