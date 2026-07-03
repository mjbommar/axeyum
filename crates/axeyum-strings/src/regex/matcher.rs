//! The independent reference matcher — the replay trust anchor (ADR-0054).
//!
//! [`matches()`] decides `s ∈ L(R)` by **direct structural recursion over the
//! regex on the concrete string**, sharing *no code* with the derivative engine
//! ([`derivative`](mod@super::derivative)). This independence is the whole point:
//! it mirrors `check_derivation` in the word-equation core — every `sat` the
//! derivative engine reports must replay through this matcher, and the
//! fundamental-derivative-theorem property test pits the two engines against
//! each other. Keep it simple and obviously correct.
//!
//! ## Method and totality
//!
//! We compute, for each sub-regex `r` and start index `i`, the set of end
//! indices `j` such that `s[i..j] ∈ L(r)` (the "reach set"). `matches` is then
//! `s.len() ∈ reach(root, 0)`. Every case is total:
//!
//! * [`Empty`](Regex::Empty) ⇒ `{i}`; [`None`](Regex::None) ⇒ `∅`;
//!   [`Pred`](Regex::Pred) ⇒ `{i+1}` iff `s[i]` satisfies the predicate.
//! * [`Concat`](Regex::Concat) ⇒ `⋃_{j ∈ reach(a,i)} reach(b,j)` (all split
//!   points).
//! * [`Union`](Regex::Union)/[`Inter`](Regex::Inter) ⇒ set union / intersection.
//! * [`Comp`](Regex::Comp) ⇒ `{i..=len} \ reach(a,i)` — a *specific* string
//!   `s[i..j]` is in `Σ* \ L(a)` iff it is not in `L(a)`; total because the
//!   candidate end set is the finite range `i..=len`.
//! * [`Star`](Regex::Star)/[`Loop`](Regex::Loop) ⇒ a bounded fixpoint over
//!   `(position, count)` states; positions live in `0..=len` and counts are
//!   capped, so the worklist terminates even when the body matches `ε`.
//!
//! Results are memoized on `(sub-regex-id, start)` via a structural node arena,
//! keeping the matcher polynomial.

use std::collections::BTreeSet;
use std::collections::HashMap;

use super::ast::Regex;
use super::predicate::CharPred;

/// Whether the whole string `cs` (a slice of Unicode code points) is in `L(r)`.
#[must_use]
pub fn matches(r: &Regex, cs: &[u32]) -> bool {
    let mut arena = Arena::new();
    let root = arena.intern(r);
    let mut memo: HashMap<(usize, usize), BTreeSet<usize>> = HashMap::new();
    arena.reach(root, cs, 0, &mut memo).contains(&cs.len())
}

/// A node in the structural arena: children referenced by index. Interning
/// dedups identical sub-trees so memoization keys `(node, start)` are shared.
enum Node {
    Empty,
    None,
    Pred(CharPred),
    Concat(usize, usize),
    Union(usize, usize),
    Inter(usize, usize),
    Comp(usize),
    Star(usize),
    Loop(usize, u32, Option<u32>),
}

struct Arena {
    nodes: Vec<Node>,
    dedup: HashMap<Regex, usize>,
}

impl Arena {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            dedup: HashMap::new(),
        }
    }

    fn intern(&mut self, r: &Regex) -> usize {
        if let Some(&id) = self.dedup.get(r) {
            return id;
        }
        let node = match r {
            Regex::Empty => Node::Empty,
            Regex::None => Node::None,
            Regex::Pred(p) => Node::Pred(p.clone()),
            Regex::Concat(a, b) => Node::Concat(self.intern(a), self.intern(b)),
            Regex::Union(a, b) => Node::Union(self.intern(a), self.intern(b)),
            Regex::Inter(a, b) => Node::Inter(self.intern(a), self.intern(b)),
            Regex::Comp(a) => Node::Comp(self.intern(a)),
            Regex::Star(a) => Node::Star(self.intern(a)),
            Regex::Loop { inner, lo, hi } => Node::Loop(self.intern(inner), *lo, *hi),
        };
        let id = self.nodes.len();
        self.nodes.push(node);
        self.dedup.insert(r.clone(), id);
        id
    }

    /// End indices `j` with `cs[start..j] ∈ L(node)`.
    fn reach(
        &self,
        node: usize,
        cs: &[u32],
        start: usize,
        memo: &mut HashMap<(usize, usize), BTreeSet<usize>>,
    ) -> BTreeSet<usize> {
        if let Some(cached) = memo.get(&(node, start)) {
            return cached.clone();
        }
        let result = self.reach_uncached(node, cs, start, memo);
        memo.insert((node, start), result.clone());
        result
    }

    fn reach_uncached(
        &self,
        node: usize,
        cs: &[u32],
        start: usize,
        memo: &mut HashMap<(usize, usize), BTreeSet<usize>>,
    ) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        match &self.nodes[node] {
            Node::Empty => {
                out.insert(start);
            }
            Node::None => {}
            Node::Pred(p) => {
                if start < cs.len() && p.contains(cs[start]) {
                    out.insert(start + 1);
                }
            }
            Node::Concat(a, b) => {
                for j in self.reach(*a, cs, start, memo) {
                    out.extend(self.reach(*b, cs, j, memo));
                }
            }
            Node::Union(a, b) => {
                out.extend(self.reach(*a, cs, start, memo));
                out.extend(self.reach(*b, cs, start, memo));
            }
            Node::Inter(a, b) => {
                let ra = self.reach(*a, cs, start, memo);
                let rb = self.reach(*b, cs, start, memo);
                out.extend(ra.intersection(&rb).copied());
            }
            Node::Comp(a) => {
                // A concrete string s[start..j] is in Σ*\L(a) iff not in L(a).
                let ra = self.reach(*a, cs, start, memo);
                for j in start..=cs.len() {
                    if !ra.contains(&j) {
                        out.insert(j);
                    }
                }
            }
            Node::Star(a) => {
                // Reachable end positions of ⋃_{k>=0} (body)^k. BFS over
                // positions; ε-iterations (j == p) add nothing new.
                let mut worklist = vec![start];
                out.insert(start);
                while let Some(p) = worklist.pop() {
                    for j in self.reach(*a, cs, p, memo) {
                        if out.insert(j) {
                            worklist.push(j);
                        }
                    }
                }
            }
            Node::Loop(a, lo, hi) => {
                out = self.reach_loop(*a, *lo, *hi, cs, start, memo);
            }
        }
        out
    }

    /// End positions of `body{lo,hi}`: BFS over `(position, count)` states.
    /// `hi = None` is `ω`; a position is collected once it is reachable with a
    /// count in `[lo, hi]`. To make the state set finite even when the body
    /// matches `ε` — and to keep advancing the position past `lo` copies when
    /// `hi = None` — the count is **saturated at `lo`** in the unbounded case
    /// (any copies beyond `lo` neither change acceptance nor need distinguishing)
    /// and bounded by `hi` in the finite case.
    fn reach_loop(
        &self,
        body: usize,
        lo: u32,
        hi: Option<u32>,
        cs: &[u32],
        start: usize,
        memo: &mut HashMap<(usize, usize), BTreeSet<usize>>,
    ) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
        let mut worklist = vec![(start, 0u32)];
        seen.insert((start, 0));
        while let Some((pos, count)) = worklist.pop() {
            // In the unbounded case a saturated count of `lo` means "≥ lo".
            let in_range = count >= lo && hi.is_none_or(|h| count <= h);
            if in_range {
                out.insert(pos);
            }
            // Stop taking further copies only when a finite `hi` is reached;
            // when `hi = None` we keep advancing the position, with the count
            // saturated at `lo` so ε-bodies cannot loop forever.
            if hi.is_some_and(|h| count >= h) {
                continue;
            }
            let next_count = match hi {
                Some(_) => count + 1,
                None => (count + 1).min(lo),
            };
            for j in self.reach(body, cs, pos, memo) {
                let next = (j, next_count);
                if seen.insert(next) {
                    worklist.push(next);
                }
            }
        }
        out
    }
}
