//! Certified optimal-size sorting networks, as SAT.
//!
//! # What this decides
//!
//! `S(n)` is the minimum number of comparators in a sorting network on `n`
//! channels. Optimality of a value `S` is two claims, and neither of them needs
//! an optimizer:
//!
//! * **upper bound** — an explicit network of size `S` sorts. By the 0-1
//!   principle it is enough to run all `2^n` binary inputs through it, which
//!   this example does in plain Rust, sharing no code with the encoder.
//! * **lower bound** — *no* network of size `S - 1` sorts. That is a plain
//!   UNSAT over a propositional encoding, and its DRAT certificate is checked
//!   by this repository's own backward checker.
//!
//! So "optimality" is decided without any `MaxSAT` / optimization search: the
//! encoder is parameterised by `(n, size)` and answers sat/unsat.
//!
//! # The encoding
//!
//! Fix `n` and a comparator count `k`.
//!
//! * `c[t][p]` for each step `t < k` and each channel pair `p = (a, b)`,
//!   `a < b`: "step `t` is the comparator on channels `a` and `b`". Exactly one
//!   per step (at-least-one + pairwise at-most-one).
//! * `used[t][i]`: "step `t` touches channel `i`". Functionally determined by
//!   the one-hot `c`, and present only so the *unchanged-channel* constraints
//!   cost `2` clauses per channel instead of `2(n-2)` per pair.
//! * `v[x][t][i]` for each binary input `x`, step `0..=k`, channel `i`: the
//!   value on channel `i` after `t` comparators when the input was `x`.
//!
//! Clauses: `v[x][0]` pinned to `x`; the comparator acts as `min = AND` on the
//! low channel and `max = OR` on the high channel; untouched channels copy
//! forward; and `v[x][k]` is ascending (`v[k][i] -> v[k][i + 1]`).
//!
//! **Only comparators with `a < b` exist in the encoding.** That is already a
//! symmetry break — the restriction to *standard* networks — and it is sound by
//! Knuth's untangling theorem: every generalized comparator network that sorts
//! can be converted into a standard one with the same size and depth
//! (TAOCP vol. 3, 5.3.4, exercise 16).
//!
//! Inputs already ascending (`0^a 1^b`, `n + 1` of them) are dropped. Every
//! standard comparator fixes such a vector — on `0^a 1^b` and `a < b` we have
//! `x[a] <= x[b]`, so `min` stays put — hence they are invariant under every
//! network the encoding can express and impose no constraint. Dropping them
//! removes clauses that are satisfied by construction; it removes no solution
//! and admits none.
//!
//! # Symmetry breaking (`--sym`)
//!
//! An unsound symmetry break yields a *wrong UNSAT*, so each one carries its
//! argument, and `--sym none` exists so every verdict can be re-derived without
//! any of them.
//!
//! * `first` — the first comparator is `(0, 1)`. Sound: let `C` be a standard
//!   sorting network of size `k` whose first comparator is `(a, b)`, and let
//!   `pi` map `a -> 0`, `b -> 1`. Relabelling channels by `pi` gives a
//!   *generalized* network whose every state is the `pi`-image of `C`'s, so it
//!   drives every input into the fixed order `pi(ascending)`, and its first
//!   comparator is the standard `(0, 1)`. Untangling (same citation as above)
//!   rewrites it into a standard sorting network of the same size, and
//!   untangling only ever touches comparators at or after the first *reversed*
//!   one — which here is at position `>= 2`. So the leading `(0, 1)` survives.
//! * `commute` — adjacent comparators on disjoint channels are lexicographically
//!   ordered. Sound: comparators on disjoint channel sets commute, so swapping
//!   an adjacent out-of-order disjoint pair preserves the computed function and
//!   the size while strictly decreasing the comparator sequence in
//!   lexicographic order; that order is well-founded on fixed-length words, so
//!   repeated swaps terminate in a network satisfying the constraint.
//! * `full` (default) = `first` + `commute`. The two compose: `(0, 1)` is the
//!   lexicographic minimum of all pairs, so no `commute` swap can ever displace
//!   it from position 0, and `commute` swaps never change the multiset of
//!   comparators that `first` reasoned about.
//! * `second` — with the first comparator pinned to `(0, 1)`, the *residual*
//!   relabelling group is `Sym({2, ..., n-1})`: a relabelling must send `{0, 1}`
//!   to itself, and if it swaps them the untangling step composes with that
//!   transposition, so what acts on the rest of the network fixes `0` and `1`
//!   pointwise. Its orbits on unordered pairs are `{0,1}`, `{0,j}`, `{1,j}` and
//!   `{i,j}` for `2 <= i < j`, so the second comparator may be restricted to the
//!   four representatives `(0,1) (0,2) (1,2) (2,3)`. Relabelling by such a `pi`
//!   and untangling leaves the first comparator alone, because untangling only
//!   rewrites comparators from the first *reversed* one onward and `(0, 1)` under
//!   a `pi` that stabilizes `{0, 1}` is either already standard or is the very
//!   comparator untangling normalizes back to `(0, 1)`.
//! * `max` = `first` + `second` + `commute` **restricted to steps `>= 2`**. The
//!   restriction is load-bearing and is exactly where naive composition would be
//!   **unsound**: with `commute` active at step 1, a network with
//!   `c_1 = (1,2), c_2 = (0,3)` is out of lexicographic order on a disjoint pair,
//!   so the canonical form swaps them and leaves `c_1 = (0,3)`, which is not an
//!   orbit representative. Confining commutation swaps to positions `>= 2` freezes
//!   `c_0` and `c_1`, so the bubble-sort argument runs on the suffix alone and the
//!   two breaks compose.
//!
//! Empirically, `--sweep` runs every `n` with a known `S(n)` at both `S(n) - 1`
//! and `S(n)`, under `--sym max`, `--sym full` **and** `--sym none`, and requires
//! every verdict to agree with ground truth. A symmetry break that excluded a
//! real network would turn a `sat` cell `unsat` and fail that sweep.
//!
//! # Usage
//!
//! ```text
//! sorting_network --n 6 --size 11              # one instance
//! sorting_network --n 6 --size 12 --model      # print + independently verify the network
//! sorting_network --n 5 --size 8 --drat        # UNSAT with a checked DRAT certificate
//! sorting_network --n 6 --size 11 --dimacs f.cnf   # emit for an external solver
//! sorting_network --sweep                      # negative control: both directions, both sym modes
//! sorting_network --verify                     # the ledger checker: re-derive the committed facts
//! ```

use std::time::Instant;

use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, SatResult,
    StreamingProofOutcome, TextProofSink, check_drat_backward, check_drat_backward_reader,
    solve_with_drat_proof_streaming, solve_with_drat_proof_with_limits, solve_with_native_core,
};

/// `S(n)` for `n = 1..=10`, indexed by `n`. Entry `0` is a placeholder.
///
/// `S(1..=8) = 0, 1, 3, 5, 9, 12, 16, 19` is Floyd and Knuth (1966); `S(9) = 25`
/// and `S(10) = 29` are Codish, Cruz-Filipe, Frank and Schneider-Kamp (2014).
///
/// The table stops at 10 because that is where *this* encoder's reach is being
/// measured, **not** because the literature stops there: `S(11) = 35` and
/// `S(12) = 39` were settled by Harder (2020, arXiv:2012.04400), with the lower
/// bounds formally verified in Isabelle/HOL. The smallest genuinely open cell
/// for optimal *size* is therefore `S(13)`. Do not restate a stale "S(11) is
/// open" here — that claim was in this comment and was wrong.
const KNOWN_S: [Option<usize>; 11] = [
    None,
    Some(0),
    Some(1),
    Some(3),
    Some(5),
    Some(9),
    Some(12),
    Some(16),
    Some(19),
    Some(25),
    Some(29),
];

// ---------------------------------------------------------------------------
// encoding
// ---------------------------------------------------------------------------

/// Which symmetry breaks are enabled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Sym {
    /// Force the first comparator to be `(0, 1)`.
    first: bool,
    /// Restrict the SECOND comparator to one representative per orbit of the
    /// residual relabelling group. Requires `first`.
    second: bool,
    /// Lexicographically order adjacent comparators on disjoint channels. When
    /// `second` is on this starts at position `from_step` = 2 rather than 0, so
    /// that a commutation swap can never move the normalized second comparator.
    commute: bool,
    /// First step index at which the `commute` constraint applies.
    commute_from: usize,
}

impl Sym {
    const NONE: Self = Self {
        first: false,
        second: false,
        commute: false,
        commute_from: 0,
    };
    const FULL: Self = Self {
        first: true,
        second: false,
        commute: true,
        commute_from: 0,
    };
    const COMMUTE: Self = Self {
        first: false,
        second: false,
        commute: true,
        commute_from: 0,
    };
    /// `first` + `second` + `commute` restricted to steps `>= 2`.
    const MAX: Self = Self {
        first: true,
        second: true,
        commute: true,
        commute_from: 2,
    };

    fn parse(s: &str) -> Option<Self> {
        match s {
            "none" => Some(Self::NONE),
            "first" => Some(Self {
                first: true,
                ..Self::NONE
            }),
            "commute" => Some(Self::COMMUTE),
            "full" => Some(Self::FULL),
            "max" => Some(Self::MAX),
            _ => None,
        }
    }

    fn label(self) -> &'static str {
        match (self.first, self.second, self.commute) {
            (false, false, false) => "none",
            (true, false, false) => "first",
            (false, false, true) => "commute",
            (true, true, true) => "max",
            (true, false, true) => "full",
            _ => "custom",
        }
    }
}

/// Representatives of the orbits of unordered channel pairs under the residual
/// relabelling group once the first comparator is fixed to `(0, 1)`.
///
/// That residual group is `Sym({2, ..., n-1})`: a relabelling `pi` must map
/// `{0, 1}` to itself to keep the first comparator on those channels, and if it
/// swaps them the untangling step composes with the transposition, so the
/// permutation effectively acting on the *rest* of the network fixes `0` and `1`
/// pointwise. Its orbits on pairs are `{0,1}`, `{0,j}`, `{1,j}` and `{i,j}` with
/// `2 <= i < j`, whose representatives are the four below.
fn second_orbit_reps(n: usize) -> Vec<(usize, usize)> {
    let mut reps = vec![(0, 1)];
    if n > 2 {
        reps.push((0, 2));
        reps.push((1, 2));
    }
    if n > 3 {
        reps.push((2, 3));
    }
    reps
}

/// The comparators the encoding may choose from, as ordered pairs `(a, b)`
/// meaning "minimum to channel `a`, maximum to channel `b`".
///
/// Standard mode keeps only `a < b`. Generalized mode keeps every ordered pair,
/// so the search also ranges over comparators that send the maximum to the lower
/// channel — which is what removes Knuth's untangling theorem from the trust
/// base of a lower bound.
fn comparators(n: usize, generalized: bool) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for a in 0..n {
        for b in 0..n {
            if a < b || (generalized && a != b) {
                out.push((a, b));
            }
        }
    }
    out.sort_unstable();
    out
}

/// `true` when the length-`n` bit vector `x` (bit `i` = channel `i`) is already
/// ascending, i.e. of the form `0^a 1^b`.
fn is_ascending(x: u32, n: usize) -> bool {
    (1..n).all(|i| !bit(x, i - 1) || bit(x, i))
}

fn bit(x: u32, i: usize) -> bool {
    (x >> i) & 1 == 1
}

/// The binary inputs the encoding constrains.
///
/// In standard mode the already-ascending vectors are dropped: every standard
/// comparator fixes `0^a 1^b`, so those inputs are invariant under every network
/// the encoding can express and their constraints hold by construction.
///
/// **That reasoning fails in generalized mode** — a comparator sending the
/// maximum to a lower channel unsorts an ascending input (on `x[1] = 0`,
/// `x[3] = 1`, the comparator `min -> 3, max -> 1` produces `x[1] = 1`,
/// `x[3] = 0`) — so generalized mode keeps all `2^n`.
fn encoded_inputs(n: usize, generalized: bool) -> Vec<u32> {
    (0..(1u32 << n))
        .filter(|&x| generalized || !is_ascending(x, n))
        .collect()
}

/// The variable layout: `n`, `k`, and the pair list are all it needs to name
/// every variable, so it is shared by the encoder and the model reader.
struct Layout {
    n: usize,
    k: usize,
    pairs: Vec<(usize, usize)>,
}

impl Layout {
    /// `c[t][p]`.
    fn comparator_var(&self, t: usize, p: usize) -> CnfVar {
        CnfVar::new(t * self.pairs.len() + p).expect("variable index fits")
    }

    /// `used[t][i]`.
    fn used_var(&self, t: usize, i: usize) -> CnfVar {
        let base = self.k * self.pairs.len();
        CnfVar::new(base + t * self.n + i).expect("variable index fits")
    }

    /// `v[x][t][i]`, where `xi` indexes into the interesting-input list.
    fn value_var(&self, xi: usize, t: usize, i: usize) -> CnfVar {
        let base = self.k * self.pairs.len() + self.k * self.n;
        CnfVar::new(base + (xi * (self.k + 1) + t) * self.n + i).expect("variable index fits")
    }
}

/// The CNF instance plus the layout needed to read a model back.
struct Encoding {
    layout: Layout,
    formula: CnfFormula,
}

fn pos(v: CnfVar) -> CnfLit {
    CnfLit::positive(v)
}

fn neg(v: CnfVar) -> CnfLit {
    CnfLit::positive(v).negated()
}

/// Builds the CNF asserting "there is a standard sorting network on `n`
/// channels with exactly `k` comparators".
fn encode(n: usize, k: usize, sym: Sym) -> Encoding {
    encode_with(n, k, sym, false)
}

/// As [`encode`], but `generalized` widens the comparator alphabet to every
/// ordered pair of distinct channels.
fn encode_with(n: usize, k: usize, sym: Sym, generalized: bool) -> Encoding {
    assert!((2..=12).contains(&n), "n out of supported range");
    assert!(
        !(generalized && (sym.first || sym.second)),
        "the `first` and `second` breaks are derived from untangling, which is \
         exactly the assumption generalized mode exists to drop"
    );
    let inputs = encoded_inputs(n, generalized);
    encode_core(n, k, sym, generalized, &inputs)
}

/// The clauses that implement `sym`. Split out of [`encode_core`] only for
/// length; the soundness argument for each break is in the module header.
fn symmetry_clauses(lay: &Layout, n: usize, k: usize, sym: Sym) -> Vec<Vec<CnfLit>> {
    let mut cs: Vec<Vec<CnfLit>> = Vec::new();
    if sym.first && k > 0 {
        // pairs[0] is (0, 1) by construction of `pairs`.
        cs.push(vec![pos(lay.comparator_var(0, 0))]);
    }
    if sym.second && k > 1 {
        let reps = second_orbit_reps(n);
        for (p, pair) in lay.pairs.iter().enumerate() {
            if !reps.contains(pair) {
                cs.push(vec![neg(lay.comparator_var(1, p))]);
            }
        }
    }
    if sym.commute {
        for t in sym.commute_from..k.saturating_sub(1) {
            for (p, &(a, b)) in lay.pairs.iter().enumerate() {
                for (q, &(x, y)) in lay.pairs.iter().enumerate() {
                    let disjoint = a != x && a != y && b != x && b != y;
                    // Forbid a strictly lex-decreasing adjacent disjoint pair.
                    if disjoint && (x, y) < (a, b) {
                        cs.push(vec![
                            neg(lay.comparator_var(t, p)),
                            neg(lay.comparator_var(t + 1, q)),
                        ]);
                    }
                }
            }
        }
    }
    cs
}

/// The shared encoder. `inputs` is the set of binary vectors the network must
/// sort; the callers differ only in what that set is.
fn encode_core(n: usize, k: usize, sym: Sym, generalized: bool, inputs: &[u32]) -> Encoding {
    let lay = Layout {
        n,
        k,
        pairs: comparators(n, generalized),
    };
    let n_vars = k * lay.pairs.len() + k * n + inputs.len() * (k + 1) * n;

    let mut cs: Vec<Vec<CnfLit>> = Vec::new();

    // --- exactly one comparator per step ---
    for t in 0..k {
        cs.push(
            (0..lay.pairs.len())
                .map(|p| pos(lay.comparator_var(t, p)))
                .collect(),
        );
        for p in 0..lay.pairs.len() {
            for q in (p + 1)..lay.pairs.len() {
                cs.push(vec![
                    neg(lay.comparator_var(t, p)),
                    neg(lay.comparator_var(t, q)),
                ]);
            }
        }
    }

    // --- `used` is functionally determined by the one-hot `c` ---
    for t in 0..k {
        for (p, &(a, b)) in lay.pairs.iter().enumerate() {
            let c = neg(lay.comparator_var(t, p));
            cs.push(vec![c, pos(lay.used_var(t, a))]);
            cs.push(vec![c, pos(lay.used_var(t, b))]);
            for i in 0..n {
                if i != a && i != b {
                    cs.push(vec![c, neg(lay.used_var(t, i))]);
                }
            }
        }
    }

    // --- symmetry breaking ---
    cs.extend(symmetry_clauses(&lay, n, k, sym));

    // --- the 0-1 semantics of the network, per input ---
    for (xi, &x) in inputs.iter().enumerate() {
        // pin step 0 to the input
        for i in 0..n {
            let v = lay.value_var(xi, 0, i);
            cs.push(vec![if bit(x, i) { pos(v) } else { neg(v) }]);
        }

        for t in 0..k {
            // untouched channels copy forward
            for i in 0..n {
                let u = pos(lay.used_var(t, i));
                let before = lay.value_var(xi, t, i);
                let after = lay.value_var(xi, t + 1, i);
                cs.push(vec![u, neg(before), pos(after)]);
                cs.push(vec![u, pos(before), neg(after)]);
            }
            // the comparator: min = AND on the low channel, max = OR on the high one
            for (p, &(a, b)) in lay.pairs.iter().enumerate() {
                let c = neg(lay.comparator_var(t, p));
                let (va, vb) = (lay.value_var(xi, t, a), lay.value_var(xi, t, b));
                let (wa, wb) = (lay.value_var(xi, t + 1, a), lay.value_var(xi, t + 1, b));
                // wa <-> va AND vb
                cs.push(vec![c, neg(wa), pos(va)]);
                cs.push(vec![c, neg(wa), pos(vb)]);
                cs.push(vec![c, pos(wa), neg(va), neg(vb)]);
                // wb <-> va OR vb
                cs.push(vec![c, pos(wb), neg(va)]);
                cs.push(vec![c, pos(wb), neg(vb)]);
                cs.push(vec![c, neg(wb), pos(va), pos(vb)]);
            }
        }

        // the output must be ascending
        for i in 0..(n - 1) {
            cs.push(vec![
                neg(lay.value_var(xi, k, i)),
                pos(lay.value_var(xi, k, i + 1)),
            ]);
        }
    }

    let mut formula = CnfFormula::new(n_vars);
    for lits in cs {
        formula
            .add_clause(CnfClause::new(lits))
            .expect("literal in range");
    }
    Encoding {
        layout: lay,
        formula,
    }
}

/// The set a suffix still has to sort after `prefix` has run: the distinct,
/// not-yet-ascending images of all `2^n` binary inputs.
///
/// This is the standard prefix reduction. A network `prefix ++ suffix` sorts
/// every input exactly when `suffix` sorts `outputs(prefix)`, so fixing a prefix
/// both removes its comparator variables and **collapses** inputs that the
/// prefix has already mapped together — for `n = 6` the 57 constrained vectors
/// fall to a little over half that after two comparators.
fn prefix_outputs(prefix: &[(usize, usize)], n: usize) -> Vec<u32> {
    let mut out: Vec<u32> = (0..(1u32 << n))
        .map(|x| apply(prefix, x))
        .filter(|&y| !is_ascending(y, n))
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

// ---------------------------------------------------------------------------
// permutation subsumption between prefix output sets
// ---------------------------------------------------------------------------

/// A set of `n`-bit vectors as a bitmask over `0..2^n`. `n <= 7` fits a `u128`,
/// which makes "is this permuted set a subset of that one" a single `&`.
type OutSet = u128;

/// The largest `n` for which an output set fits [`OutSet`].
const SUBSUME_MAX_N: usize = 7;

fn outputs_mask(vectors: &[u32]) -> OutSet {
    vectors.iter().fold(0, |m, &x| m | (1u128 << x))
}

/// Every permutation of `0..n`, in a deterministic order.
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur: Vec<usize> = (0..n).collect();
    permute_into(&mut cur, 0, &mut out);
    out
}

fn permute_into(cur: &mut Vec<usize>, at: usize, out: &mut Vec<Vec<usize>>) {
    if at == cur.len() {
        out.push(cur.clone());
        return;
    }
    for i in at..cur.len() {
        cur.swap(at, i);
        permute_into(cur, at + 1, out);
        cur.swap(at, i);
    }
}

/// The image of `mask` under the channel relabelling `perm` (channel `i` of the
/// input becomes channel `perm[i]` of the output).
fn permute_mask(mask: OutSet, perm: &[usize], n: usize) -> OutSet {
    let mut out: OutSet = 0;
    for x in 0..(1u32 << n) {
        if mask & (1u128 << x) == 0 {
            continue;
        }
        let mut y = 0u32;
        for (i, &p) in perm.iter().enumerate() {
            if bit(x, i) {
                y |= 1 << p;
            }
        }
        out |= 1u128 << y;
    }
    out
}

/// Reduces a prefix list by **permutation subsumption**, the reduction that
/// makes the lower-bound search tractable past `n = 6`.
///
/// Write `R(P)` for [`prefix_outputs`] of a prefix `P`, and call `R` *`k`-sortable*
/// when some standard network of `k` comparators sorts every vector in `R`. Say
/// `R1` **subsumes** `R2` when there is a channel relabelling `pi` with
/// `pi(R1) subset-of R2`.
///
/// **Lemma.** If `R1` subsumes `R2` and `R2` is `k`-sortable, then `R1` is
/// `k`-sortable. Let `C` be a standard `k`-network sorting `R2`. For `x` in `R1`
/// we have `pi(x)` in `R2`, so `C(pi(x))` is ascending; hence the *generalized*
/// network `pi^-1 . C . pi` drives every `x` in `R1` into the one fixed order
/// `pi^-1(ascending)`. Untangling (Knuth TAOCP vol. 3, 5.3.4 exercise 16, in the
/// form Codish, Cruz-Filipe and Schneider-Kamp state it for arbitrary input sets)
/// rewrites that into a *standard* network of the same size that genuinely sorts
/// `R1`.
///
/// The contrapositive is what a lower bound uses: **refuting `R1` refutes every
/// `R2` it subsumes.** So it is enough to refute a set of prefixes that subsumes
/// all of them, and since `pi` preserves cardinality only a `R1` with
/// `|R1| <= |R2|` can subsume `R2` — the surviving branches are the *easiest*
/// ones, and their UNSAT is the strongest statement.
///
/// This rests on the same untangling step the `first`/`second` symmetry breaks
/// do, so it belongs to the same `sortnet.symmetry-breaking-soundness`
/// assumption and is **off by default**: `--subsume` opts in, and any verdict it
/// produces must be reproduced without it.
fn subsumption_reduce(prefixes: &[Vec<(usize, usize)>], n: usize) -> Vec<Vec<(usize, usize)>> {
    assert!(
        n <= SUBSUME_MAX_N,
        "subsumption needs an output set to fit u128, so n <= {SUBSUME_MAX_N}"
    );
    let perms = permutations(n);
    // For each prefix: its own output mask, its cardinality, and every
    // relabelled image of that mask.
    let entries: Vec<(OutSet, u32, Vec<OutSet>)> = prefixes
        .iter()
        .map(|p| {
            let mask = outputs_mask(&prefix_outputs(p, n));
            let images: Vec<OutSet> = perms.iter().map(|pi| permute_mask(mask, pi, n)).collect();
            (mask, mask.count_ones(), images)
        })
        .collect();

    // `a` subsumes `b` when some relabelled image of `a` is a subset of `b`.
    let subsumes = |a: usize, b: usize| -> bool {
        if entries[a].1 > entries[b].1 {
            return false;
        }
        let target = entries[b].0;
        entries[a].2.iter().any(|&img| img & !target == 0)
    };

    // Greedy antichain: keep `c` unless something already kept subsumes it, and
    // drop anything kept that `c` subsumes. Subsumption is transitive (compose
    // the relabellings), so nothing is lost when a keeper is later displaced.
    let mut kept: Vec<usize> = Vec::new();
    for c in 0..prefixes.len() {
        if kept.iter().any(|&k| subsumes(k, c)) {
            continue;
        }
        kept.retain(|&k| !subsumes(c, k));
        kept.push(c);
    }
    kept.sort_unstable();
    kept.into_iter().map(|i| prefixes[i].clone()).collect()
}

// ---------------------------------------------------------------------------
// certificates on disk (ADR-0426 route: stream out, check back in)
// ---------------------------------------------------------------------------

/// Refutes one instance, streaming its DRAT proof to `path` rather than holding
/// it in memory, then re-checks it by reading the file back.
///
/// Returns `Ok((steps, bytes))` on a refutation the backward checker accepts.
///
/// `keep` decides whether the certificate survives its own check. At `n = 7` a
/// single branch's proof reaches a gigabyte and a run has thousands of branches,
/// so the default deletes each one **after** the backward checker has accepted
/// it: what the run is claiming is that every branch was refuted *and
/// re-checked*, and that claim is already discharged by the time the bytes are
/// dropped. Pass `--keep-proofs` when the artifacts are wanted for offline
/// re-validation, and budget the terabytes.
fn refute_to_file(
    formula: &CnfFormula,
    path: &std::path::Path,
    conflicts: usize,
    keep: bool,
) -> Result<(usize, u64), CubeOutcome> {
    use std::io::BufReader;

    let fail = |e: String| CubeOutcome::Failed(e);
    let file = match std::fs::File::create(path) {
        Ok(f) => f,
        Err(e) => return Err(fail(format!("create {}: {e}", path.display()))),
    };
    // A refutation branch's proof can run to gigabytes; drop its pages from
    // the OS page cache as they are written rather than evicting whatever
    // else is resident on the box (refactor-2026-08 item 05.1).
    #[cfg(unix)]
    let mut sink = TextProofSink::new(axeyum_cnf::CacheDroppingWriter::new(file));
    #[cfg(not(unix))]
    let mut sink = TextProofSink::new(file);
    let outcome = solve_with_drat_proof_streaming(formula, None, conflicts, &mut sink);
    if let Err(e) = sink.flush() {
        return Err(fail(format!("flush: {e}")));
    }
    drop(sink);
    match outcome {
        StreamingProofOutcome::Unsat => {}
        StreamingProofOutcome::Sat(model) => return Err(CubeOutcome::Sat(model)),
        other => return Err(fail(format!("expected unsat, got {other:?}"))),
    }
    let bytes = match std::fs::metadata(path) {
        Ok(m) => m.len(),
        Err(e) => return Err(fail(format!("stat: {e}"))),
    };
    let open = || std::fs::File::open(path).map(BufReader::new);
    let steps = match open() {
        Ok(reader) => std::io::BufRead::lines(reader).count(),
        Err(e) => return Err(fail(format!("reopen {}: {e}", path.display()))),
    };
    let reader = match open() {
        Ok(reader) => reader,
        Err(e) => return Err(fail(format!("reopen {}: {e}", path.display()))),
    };
    let verdict = check_drat_backward_reader(formula, reader);
    // Only ever removed on the accepting path, so a rejected or unfinished
    // certificate is always left on disk to be looked at.
    if keep || !matches!(verdict, Ok(true)) {
        // keep the bytes
    } else if let Err(e) = std::fs::remove_file(path) {
        return Err(fail(format!("remove {}: {e}", path.display())));
    }
    match verdict {
        Ok(true) => Ok((steps, bytes)),
        Ok(false) => Err(fail(
            "backward checker found no refutation in the proof".into(),
        )),
        Err(e) => Err(fail(format!("backward checker rejected the proof: {e}"))),
    }
}

/// Why a cube did not come back refuted.
enum CubeOutcome {
    /// The branch is satisfiable — with `k = S(n) - 1` this would be a wrong
    /// lower bound, so the model is decoded and independently 0-1 checked
    /// rather than merely reported.
    Sat(CnfAssignment),
    /// Anything else: a resource-out, an I/O failure, or a rejected proof.
    Failed(String),
}

/// How hard the cube route is allowed to lean on relabelling arguments.
///
/// This is the cube route's `--sym`, and it exists for the same reason: an
/// unsound reduction of the prefix set manufactures a **wrong UNSAT**, so every
/// verdict must be reproducible at a weaker setting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CubeSym {
    /// No relabelling argument at all. Every position of the prefix ranges over
    /// every comparator, and the suffix gets no symmetry break either. The only
    /// reduction is output-set **equality**, which needs no argument: two
    /// prefixes with the same output set pose a literally identical question.
    None,
    /// Position 0 is `(0, 1)`, position 1 an orbit representative, and the
    /// suffix is commutation-ordered — the `first`, `second` and `commute`
    /// arguments from the module header.
    Full,
    /// [`CubeSym::Full`] plus permutation subsumption between prefix output sets
    /// ([`subsumption_reduce`]).
    Subsume,
}

impl CubeSym {
    fn parse(s: &str) -> Option<Self> {
        match s {
            "none" => Some(Self::None),
            "full" => Some(Self::Full),
            "subsume" => Some(Self::Subsume),
            _ => None,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Full => "full",
            Self::Subsume => "subsume",
        }
    }

    /// The symmetry break applied to each branch's suffix encoding.
    ///
    /// `commute` is sound on the suffix alone: the bubble-sort argument runs
    /// inside the suffix and never moves a comparator across the fixed prefix.
    fn suffix_sym(self) -> Sym {
        match self {
            Self::None => Sym::NONE,
            Self::Full | Self::Subsume => Sym::COMMUTE,
        }
    }
}

/// Enumerates the prefixes the cube split ranges over, deduplicated by output
/// set.
///
/// Under [`CubeSym::None`] every position ranges over every comparator, so the
/// enumeration is exhaustive with no relabelling argument. Otherwise position 0
/// is `(0, 1)` and position 1 an orbit representative — the `first` and `second`
/// symmetry arguments — while positions `2..depth` still range over **every**
/// comparator, so the enumeration stays complete however deep it goes.
///
/// Two prefixes with the *same* output set pose the same remaining question, so
/// only one of each is kept. That is equality, not subsumption up to
/// permutation; it is weaker and needs no extra argument. [`CubeSym::Subsume`]
/// then adds the permutation reduction on top.
fn cube_prefixes(n: usize, depth: usize, sym: CubeSym) -> Vec<Vec<(usize, usize)>> {
    let all = comparators(n, false);
    let reps = second_orbit_reps(n);
    let mut prefixes: Vec<Vec<(usize, usize)>> = match sym {
        CubeSym::None => all.iter().map(|&c| vec![c]).collect(),
        CubeSym::Full | CubeSym::Subsume => vec![vec![(0, 1)]],
    };
    for pos in 1..depth {
        let choices: &[(usize, usize)] = match (sym, pos) {
            (CubeSym::Full | CubeSym::Subsume, 1) => &reps,
            _ => &all,
        };
        let mut next = Vec::new();
        for base in &prefixes {
            for &c in choices {
                let mut p = base.clone();
                p.push(c);
                next.push(p);
            }
        }
        prefixes = next;
    }
    let mut seen = std::collections::BTreeSet::new();
    prefixes.retain(|p| seen.insert(prefix_outputs(p, n)));
    if sym == CubeSym::Subsume {
        prefixes = subsumption_reduce(&prefixes, n);
    }
    prefixes
}

/// One branch's result, so the worker threads can report without interleaving.
struct CubeResult {
    prefix: Vec<(usize, usize)>,
    line: String,
    ok: bool,
}

/// Everything one cube run needs, so the worker closure can borrow it whole.
struct CubeRun {
    n: usize,
    k: usize,
    dir: String,
    conflicts: usize,
    depth: usize,
    jobs: usize,
    sym: CubeSym,
    keep_proofs: bool,
    /// `(index, count)`: run only the branches with
    /// `branch_index % count == index`. `(0, 1)` is the whole run.
    ///
    /// A shard's exit status covers **its own** branches only. The lower bound
    /// is established when every shard of a partition has reported success, and
    /// nothing in one shard's output claims more than that.
    shard: (usize, usize),
}

impl CubeRun {
    /// Refutes one branch: fix `prefix`, encode the remaining `k - |prefix|`
    /// comparators against the prefix's output set, and require a DRAT proof the
    /// backward checker accepts.
    fn branch(&self, prefix: &[(usize, usize)]) -> CubeResult {
        let (n, k) = (self.n, self.k);
        let tag = prefix
            .iter()
            .map(|&(a, b)| format!("{a}_{b}"))
            .collect::<Vec<_>>()
            .join("-");
        let inputs = prefix_outputs(prefix, n);
        let enc = encode_core(n, k - prefix.len(), self.sym.suffix_sym(), false, &inputs);
        let path = std::path::Path::new(&self.dir).join(format!("n{n}-k{k}-{tag}.drat"));
        let t0 = Instant::now();
        match refute_to_file(&enc.formula, &path, self.conflicts, self.keep_proofs) {
            Ok((steps, bytes)) => CubeResult {
                prefix: prefix.to_vec(),
                line: format!(
                    "  cube {}  {} vectors, {} clauses -> UNSAT, {steps} step(s), \
                     {bytes} bytes, backward-checked, {:.2}s",
                    render(prefix),
                    inputs.len(),
                    enc.formula.clauses().len(),
                    t0.elapsed().as_secs_f64()
                ),
                ok: true,
            },
            Err(CubeOutcome::Sat(model)) => {
                // The negative control for the cube route: a satisfiable branch
                // must yield a network that really sorts, or the encoding is
                // wrong in the direction that also produces a wrong UNSAT.
                let line = match decode(&enc, &model) {
                    Ok(suffix) => {
                        let mut whole = prefix.to_vec();
                        whole.extend(suffix);
                        format!(
                            "  cube {}  SAT: {} -- independent 0-1 check: {}",
                            render(prefix),
                            render(&whole),
                            if sorts_all(&whole, n) {
                                "SORTS"
                            } else {
                                "DOES NOT SORT"
                            }
                        )
                    }
                    Err(e) => format!(
                        "  cube {}  SAT but the model does not decode: {e}",
                        render(prefix)
                    ),
                };
                CubeResult {
                    prefix: prefix.to_vec(),
                    line,
                    ok: false,
                }
            }
            Err(CubeOutcome::Failed(e)) => CubeResult {
                prefix: prefix.to_vec(),
                line: format!("  cube {}  FAILED: {e}", render(prefix)),
                ok: false,
            },
        }
    }
}

/// The cube split: fix a prefix, replace the network's first `depth` steps by
/// that prefix's output set, and refute the remaining `k - depth` comparators on
/// its own.
///
/// Completeness is [`cube_prefixes`]'s: some size-`k` sorting network has
/// `c_0 = (0, 1)` and, after relabelling, `c_1` on an orbit representative, and
/// every deeper position is enumerated exhaustively. So if every branch is
/// UNSAT, no size-`k` sorting network exists.
///
/// Each branch gets its own DRAT certificate, streamed to disk and read back for
/// checking, which is what keeps the peak footprint bounded.
fn cubes(run: &CubeRun) -> i32 {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let all_prefixes = cube_prefixes(run.n, run.depth, run.sym);
    let (shard, shards) = run.shard;
    assert!(shards >= 1 && shard < shards, "bad --shard");
    let total_branches = all_prefixes.len();
    let prefixes: Vec<Vec<(usize, usize)>> = all_prefixes
        .into_iter()
        .enumerate()
        .filter(|(i, _)| i % shards == shard)
        .map(|(_, p)| p)
        .collect();
    std::fs::create_dir_all(&run.dir).expect("create proof dir");
    println!(
        "cube split at depth {}, cube-sym {}: {total_branches} branch(es){}, {} worker(s)",
        run.depth,
        run.sym.label(),
        if shards > 1 {
            format!(
                " -- THIS IS SHARD {shard} OF {shards}, covering {} of them; the bound needs every shard",
                prefixes.len()
            )
        } else {
            String::new()
        },
        run.jobs
    );
    let started = Instant::now();
    let next = AtomicUsize::new(0);
    let done = AtomicUsize::new(0);
    let total = prefixes.len();
    let results: Mutex<Vec<CubeResult>> = Mutex::new(Vec::new());

    std::thread::scope(|scope| {
        for _ in 0..run.jobs.max(1) {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    let Some(prefix) = prefixes.get(i) else { break };
                    let res = run.branch(prefix);
                    // Progress goes to stderr so stdout stays the deterministic,
                    // prefix-sorted report. A multi-hour run that prints nothing
                    // until it finishes cannot be told from a hung one.
                    let seen = done.fetch_add(1, Ordering::SeqCst) + 1;
                    eprintln!(
                        "[{seen}/{total}] {} {} after {:.1}s",
                        render(&res.prefix),
                        if res.ok { "ok" } else { "NOT REFUTED" },
                        started.elapsed().as_secs_f64()
                    );
                    results.lock().expect("results lock").push(res);
                }
            });
        }
    });

    let mut rows = results.into_inner().expect("results lock");
    rows.sort_by(|a, b| a.prefix.cmp(&b.prefix));
    let bad = rows.iter().filter(|r| !r.ok).count();
    for r in &rows {
        if r.ok {
            println!("{}", r.line);
        } else {
            eprintln!("{}", r.line);
        }
    }
    let (n, k) = (run.n, run.k);
    if bad == 0 {
        // A shard says only what a shard can say. The unsharded wording is
        // load-bearing: fact checker_commands match on it exactly, and it must
        // never appear for a run that covered part of the space.
        if shards > 1 {
            println!(
                "n={n} size={k}: shard {shard}/{shards} refuted and re-checked its {} of \
                 {total_branches} cubes in {:.2}s -- NOT a bound on its own",
                rows.len(),
                started.elapsed().as_secs_f64()
            );
        } else {
            println!(
                "n={n} size={k}: all {} cubes refuted and re-checked in {:.2}s",
                rows.len(),
                started.elapsed().as_secs_f64()
            );
        }
        0
    } else {
        eprintln!("n={n} size={k}: {bad} of {} cube(s) unrefuted", rows.len());
        1
    }
}

// ---------------------------------------------------------------------------
// independent checking (shares no code with the encoder)
// ---------------------------------------------------------------------------

/// Runs `x` through `net` and returns the resulting bit vector.
fn apply(net: &[(usize, usize)], mut x: u32) -> u32 {
    for &(a, b) in net {
        let (va, vb) = (bit(x, a), bit(x, b));
        let (lo, hi) = (va && vb, va || vb);
        x = (x & !(1 << a) & !(1 << b)) | (u32::from(lo) << a) | (u32::from(hi) << b);
    }
    x
}

/// `true` when `net` sorts every one of the `2^n` binary inputs.
///
/// This is the 0-1 principle applied directly, in code that never sees the CNF.
fn sorts_all(net: &[(usize, usize)], n: usize) -> bool {
    (0..(1u32 << n)).all(|x| {
        let y = apply(net, x);
        is_ascending(y, n) && y.count_ones() == x.count_ones()
    })
}

/// Reads the comparator sequence out of a SAT model.
fn decode(enc: &Encoding, model: &CnfAssignment) -> Result<Vec<(usize, usize)>, String> {
    let lay = &enc.layout;
    let mut net = Vec::with_capacity(lay.k);
    for t in 0..lay.k {
        let chosen: Vec<usize> = (0..lay.pairs.len())
            .filter(|&p| model.value(lay.comparator_var(t, p)) == Some(true))
            .collect();
        match chosen.as_slice() {
            [p] => net.push(lay.pairs[*p]),
            other => {
                return Err(format!(
                    "step {t}: model selects {} comparators, expected exactly 1",
                    other.len()
                ));
            }
        }
    }
    Ok(net)
}

// ---------------------------------------------------------------------------
// driver
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

struct RunReport {
    verdict: Verdict,
    vars: usize,
    clauses: usize,
    seconds: f64,
    network: Option<Vec<(usize, usize)>>,
}

fn run(
    n: usize,
    k: usize,
    sym: Sym,
    want_drat: bool,
    conflicts: usize,
    generalized: bool,
) -> RunReport {
    let enc = encode_with(n, k, sym, generalized);
    let vars = enc.formula.variable_count();
    let clauses = enc.formula.clauses().len();
    let started = Instant::now();

    if want_drat {
        // The proof-producing core: `unsat` comes back with a DRAT certificate
        // that this repository's own backward checker re-derives.
        let outcome = solve_with_drat_proof_with_limits(&enc.formula, None, conflicts);
        let seconds = started.elapsed().as_secs_f64();
        return match outcome {
            ProofSolveOutcome::Unsat(proof) => {
                let ok = check_drat_backward(&enc.formula, &proof).expect("DRAT checker ran");
                println!("  drat: {} steps, backward-checked = {ok}", proof.len());
                assert!(ok, "the CDCL core emitted a DRAT proof the checker rejects");
                RunReport {
                    verdict: Verdict::Unsat,
                    vars,
                    clauses,
                    seconds,
                    network: None,
                }
            }
            ProofSolveOutcome::Sat(model) => {
                let net = decode(&enc, &model).expect("model decodes");
                RunReport {
                    verdict: Verdict::Sat,
                    vars,
                    clauses,
                    seconds,
                    network: Some(net),
                }
            }
            _ => RunReport {
                verdict: Verdict::Unknown,
                vars,
                clauses,
                seconds,
                network: None,
            },
        };
    }

    let result = solve_with_native_core(&enc.formula).expect("SAT solver ran");
    let seconds = started.elapsed().as_secs_f64();
    match result {
        SatResult::Sat(model) => {
            let net = decode(&enc, &model).expect("model decodes");
            RunReport {
                verdict: Verdict::Sat,
                vars,
                clauses,
                seconds,
                network: Some(net),
            }
        }
        SatResult::Unsat(_) => RunReport {
            verdict: Verdict::Unsat,
            vars,
            clauses,
            seconds,
            network: None,
        },
        SatResult::Unknown(_) => RunReport {
            verdict: Verdict::Unknown,
            vars,
            clauses,
            seconds,
            network: None,
        },
    }
}

fn render(net: &[(usize, usize)]) -> String {
    net.iter()
        .map(|&(a, b)| format!("{a}:{b}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The negative control. For every `n` with a known `S(n)`, both directions and
/// both symmetry modes must agree with ground truth.
fn sweep(max_n: usize, want_drat: bool, generalized: bool) -> i32 {
    let mut failures = 0;
    println!("negative control: sat at S(n), unsat at S(n)-1, under two symmetry modes\n");
    println!(
        "{:>3} {:>5} {:>4} {:>8} {:>9} {:>9} {:>8}  sec",
        "n", "size", "sym", "expect", "verdict", "vars", "clauses"
    );
    for (n, known) in KNOWN_S.iter().enumerate().take(max_n + 1).skip(2) {
        let Some(s) = *known else { continue };
        let modes: &[Sym] = if generalized {
            &[Sym::COMMUTE, Sym::NONE]
        } else {
            &[Sym::MAX, Sym::FULL, Sym::NONE]
        };
        for &sym in modes {
            for (k, expect) in [(s, Verdict::Sat), (s.saturating_sub(1), Verdict::Unsat)] {
                if s == 0 {
                    continue;
                }
                let r = run(n, k, sym, want_drat, 200_000_000, generalized);
                let ok = r.verdict == expect;
                let mut extra = String::new();
                if let Some(net) = &r.network {
                    if sorts_all(net, n) {
                        extra = format!("  verified: {}", render(net));
                    } else {
                        failures += 1;
                        extra = "  MODEL DOES NOT SORT".into();
                    }
                }
                if !ok {
                    failures += 1;
                    extra.push_str("  <== MISMATCH");
                }
                println!(
                    "{n:>3} {k:>5} {:>4} {:>8} {:>9} {:>9} {:>8}  {:.2}{extra}",
                    sym.label(),
                    format!("{expect:?}").to_lowercase(),
                    format!("{:?}", r.verdict).to_lowercase(),
                    r.vars,
                    r.clauses,
                    r.seconds,
                );
            }
        }
    }
    if failures == 0 {
        println!("\nsweep: all cells agree with the published S(n)");
        0
    } else {
        eprintln!("\nsweep: {failures} FAILURE(S)");
        1
    }
}

fn usage() -> ! {
    eprintln!(
        "usage: sorting_network [--n N --size K] [--sym none|first|commute|full] [--drat]\n\
         \x20                     [--model] [--dimacs PATH] [--conflicts N]\n\
         \x20      sorting_network --n N --size K --cubes DIR [--depth D] [--jobs J]\n\
         \x20                     [--cube-sym none|full|subsume] [--keep-proofs]\n\
         \x20                     [--shard I/N]   (shard I only; the bound needs every shard)\n\
         \x20      sorting_network --sweep [--max-n N] [--drat]\n\
         \x20      sorting_network --verify"
    );
    std::process::exit(2)
}

/// The parsed command line. Split out of [`main`] only for length.
#[allow(clippy::struct_excessive_bools)] // one field per flag, which is what a flag is
struct Cli {
    n: Option<usize>,
    size: Option<usize>,
    sym: Sym,
    want_drat: bool,
    want_model: bool,
    dimacs: Option<String>,
    cube_dir: Option<String>,
    cube_sym: CubeSym,
    keep_proofs: bool,
    shard: (usize, usize),
    generalized: bool,
    depth: usize,
    jobs: usize,
    do_sweep: bool,
    do_verify: bool,
    max_n: usize,
    conflicts: usize,
}

impl Cli {
    #[allow(clippy::too_many_lines)] // a flat flag table: one arm per option
    fn parse(args: &[String]) -> Self {
        let mut cli = Self {
            n: None,
            size: None,
            sym: Sym::FULL,
            want_drat: false,
            want_model: false,
            dimacs: None,
            cube_dir: None,
            cube_sym: CubeSym::Full,
            keep_proofs: false,
            shard: (0, 1),
            generalized: false,
            depth: 2,
            jobs: 1,
            do_sweep: false,
            do_verify: false,
            max_n: 6,
            conflicts: 200_000_000,
        };
        let mut i = 0;
        while i < args.len() {
            match args[i].as_str() {
                "--n" => {
                    i += 1;
                    cli.n = Some(
                        args.get(i)
                            .and_then(|s| s.parse().ok())
                            .unwrap_or_else(|| usage()),
                    );
                }
                "--size" => {
                    i += 1;
                    cli.size = Some(
                        args.get(i)
                            .and_then(|s| s.parse().ok())
                            .unwrap_or_else(|| usage()),
                    );
                }
                "--sym" => {
                    i += 1;
                    cli.sym = args
                        .get(i)
                        .and_then(|s| Sym::parse(s))
                        .unwrap_or_else(|| usage());
                }
                "--max-n" => {
                    i += 1;
                    cli.max_n = args
                        .get(i)
                        .and_then(|s| s.parse().ok())
                        .unwrap_or_else(|| usage());
                }
                "--conflicts" => {
                    i += 1;
                    cli.conflicts = args
                        .get(i)
                        .and_then(|s| s.parse().ok())
                        .unwrap_or_else(|| usage());
                }
                "--dimacs" => {
                    i += 1;
                    cli.dimacs = Some(args.get(i).cloned().unwrap_or_else(|| usage()));
                }
                "--depth" => {
                    i += 1;
                    cli.depth = args
                        .get(i)
                        .and_then(|s| s.parse().ok())
                        .unwrap_or_else(|| usage());
                }
                "--jobs" => {
                    i += 1;
                    cli.jobs = args
                        .get(i)
                        .and_then(|s| s.parse().ok())
                        .unwrap_or_else(|| usage());
                }
                "--cubes" => {
                    i += 1;
                    cli.cube_dir = Some(args.get(i).cloned().unwrap_or_else(|| usage()));
                }
                "--cube-sym" => {
                    i += 1;
                    cli.cube_sym = args
                        .get(i)
                        .and_then(|s| CubeSym::parse(s))
                        .unwrap_or_else(|| usage());
                }
                "--generalized" => {
                    cli.generalized = true;
                    if cli.sym.first || cli.sym.second {
                        cli.sym = Sym::COMMUTE;
                    }
                }
                "--shard" => {
                    i += 1;
                    cli.shard = args
                        .get(i)
                        .and_then(|s| s.split_once('/'))
                        .and_then(|(a, b)| Some((a.parse().ok()?, b.parse().ok()?)))
                        .filter(|&(a, b): &(usize, usize)| b >= 1 && a < b)
                        .unwrap_or_else(|| usage());
                }
                "--keep-proofs" => cli.keep_proofs = true,
                "--drat" => cli.want_drat = true,
                "--model" => cli.want_model = true,
                "--sweep" => cli.do_sweep = true,
                "--verify" => cli.do_verify = true,
                _ => usage(),
            }
            i += 1;
        }
        cli
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Cli {
        n,
        size,
        sym,
        want_drat,
        want_model,
        dimacs,
        cube_dir,
        cube_sym,
        keep_proofs,
        shard,
        generalized,
        depth,
        jobs,
        do_sweep,
        do_verify,
        max_n,
        conflicts,
    } = Cli::parse(&args);

    if do_verify {
        std::process::exit(verify());
    }
    if do_sweep {
        std::process::exit(sweep(max_n, want_drat, generalized));
    }

    let (Some(n), Some(k)) = (n, size) else {
        usage()
    };

    if let Some(dir) = cube_dir {
        std::process::exit(cubes(&CubeRun {
            n,
            k,
            dir,
            conflicts,
            depth,
            jobs,
            sym: cube_sym,
            keep_proofs,
            shard,
        }));
    }

    if let Some(path) = dimacs {
        let enc = encode_with(n, k, sym, generalized);
        std::fs::write(&path, enc.formula.to_dimacs()).expect("write DIMACS");
        println!(
            "wrote {path}: n={n} size={k} sym={} vars={} clauses={}",
            sym.label(),
            enc.formula.variable_count(),
            enc.formula.clauses().len()
        );
        return;
    }

    let r = run(n, k, sym, want_drat, conflicts, generalized);
    println!(
        "n={n} size={k} sym={} vars={} clauses={} -> {:?} in {:.2}s",
        sym.label(),
        r.vars,
        r.clauses,
        r.verdict,
        r.seconds
    );
    if let Some(net) = &r.network {
        let sorts = sorts_all(net, n);
        println!("network: {}", render(net));
        println!(
            "independent 0-1 check over all {} inputs: {}",
            1usize << n,
            if sorts { "SORTS" } else { "DOES NOT SORT" }
        );
        if !sorts {
            std::process::exit(1);
        }
        if want_model {
            for &(a, b) in net {
                println!("  compare {a} {b}");
            }
        }
    }
    if r.verdict == Verdict::Unknown {
        std::process::exit(3);
    }
}

// ---------------------------------------------------------------------------
// the ledger checker
// ---------------------------------------------------------------------------

/// Explicit witness networks for the upper bounds, so `--verify` does not
/// depend on a SAT search finding one.
const WITNESS: [(usize, &[(usize, usize)]); 5] = [
    (2, &[(0, 1)]),
    (3, &[(0, 1), (0, 2), (1, 2)]),
    (4, &[(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]),
    (
        5,
        &[
            (0, 1),
            (3, 4),
            (2, 4),
            (2, 3),
            (0, 3),
            (0, 2),
            (1, 4),
            (1, 3),
            (1, 2),
        ],
    ),
    (
        6,
        &[
            (0, 1),
            (2, 3),
            (4, 5),
            (0, 2),
            (3, 5),
            (1, 4),
            (0, 1),
            (2, 3),
            (4, 5),
            (1, 2),
            (3, 4),
            (2, 3),
        ],
    ),
];

/// Re-derives every committed fact: for `n = 2..=6`, the witness network of
/// size `S(n)` sorts all `2^n` inputs, and the encoding at `S(n) - 1` is UNSAT
/// with a DRAT certificate this repository's backward checker accepts.
fn verify() -> i32 {
    let mut bad = 0;

    for (n, net) in WITNESS {
        let s = KNOWN_S[n].expect("known S(n)");
        if net.len() != s {
            eprintln!(
                "verify: witness for n={n} has {} comparators, S(n)={s}",
                net.len()
            );
            bad += 1;
            continue;
        }
        if sorts_all(net, n) {
            println!(
                "  upper bound n={n}: {s} comparators sort all {} inputs",
                1usize << n
            );
        } else {
            eprintln!("  upper bound n={n}: WITNESS DOES NOT SORT");
            bad += 1;
        }
    }

    for (n, known) in KNOWN_S.iter().enumerate().take(7).skip(2) {
        let s = known.expect("known S(n)");
        let k = s - 1;
        let enc = encode(n, k, Sym::FULL);
        match solve_with_drat_proof_with_limits(&enc.formula, None, 200_000_000) {
            ProofSolveOutcome::Unsat(proof) => {
                if matches!(check_drat_backward(&enc.formula, &proof), Ok(true)) {
                    println!(
                        "  lower bound n={n}: size {k} UNSAT, DRAT ({} steps) backward-checked",
                        proof.len()
                    );
                } else {
                    eprintln!("  lower bound n={n}: DRAT REJECTED");
                    bad += 1;
                }
            }
            other => {
                eprintln!("  lower bound n={n}: expected unsat, got {other:?}");
                bad += 1;
            }
        }
    }

    if bad == 0 {
        println!("sorting-network facts: re-derived, 0 failures");
        0
    } else {
        eprintln!("sorting-network facts: {bad} FAILURE(S)");
        1
    }
}
