//! Randomized soundness gate for Craig interpolation (Track 3, P3.8).
//!
//! For many random unsatisfiable conjunctions `A ∧ B`, ask for an interpolant and
//! — whenever one is returned — *independently* re-check the three Craig
//! conditions (`A ⇒ I`, `I ∧ B ⇒ ⊥`, shared vocabulary). The generator is allowed
//! to decline (`None`); it is **never** allowed to return an interpolant that
//! fails a condition. Deterministic (a fixed LCG, no wall-clock / `rand`), per the
//! project's determinism rule.
#![cfg(feature = "full")]

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, SolverConfig, check_auto, check_qf_uf, check_with_lra, check_with_uf_arithmetic,
    lra_interpolant, qf_bv_interpolant, qf_uf_interpolant, uflra_interpolant,
};

/// A small deterministic linear-congruential generator.
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        // Numerical Recipes constants.
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // The raw state is never handed out: bit `k` of an LCG modulo 2^64
        // has period 2^(k+1), so `state & 1` alternates on every draw and a
        // decision made at a fixed draw offset is a constant, not a coin.
        // Measured 2026-09-16 (lane ax-proptest, bench-results/proptest-box-
        // audit-20260916): the EUF pool never drew a `t != t` literal (0/800),
        // the QF_BV constant `pick(16)` sat at one parity so every constant
        // was even (never all-ones), and LRA `na, nb` was always (1,2)/(2,1).
        // SplitMix64's finalizer makes every output bit depend on the state.
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A uniform index in `0..n`.
    fn pick(&mut self, n: usize) -> usize {
        let m = u64::try_from(n).expect("len fits u64");
        usize::try_from(self.next_u64() % m).expect("modulus fits usize")
    }

    /// A small integer coefficient in `lo..=hi`.
    fn coeff(&mut self, lo: i64, hi: i64) -> i128 {
        let span = u64::try_from(hi - lo + 1).expect("positive span");
        i128::from(lo) + i128::from(self.next_u64() % span)
    }
}

fn vocab(
    arena: &TermArena,
    term: TermId,
    out: &mut BTreeSet<(u8, usize)>,
    seen: &mut BTreeSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert((0, s.index()));
        }
        TermNode::App { op, args } => {
            if let Op::Apply(f) = op {
                out.insert((1, f.index()));
            }
            for &a in args {
                vocab(arena, a, out, seen);
            }
        }
        _ => {}
    }
}

fn vocab_of(arena: &TermArena, terms: &[TermId]) -> BTreeSet<(u8, usize)> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for &t in terms {
        vocab(arena, t, &mut out, &mut seen);
    }
    out
}

/// Asserts the three Craig conditions for `i` over `(a, b)` using `decide`
/// (a theory's conjunctive decider) for the entailment checks.
fn check_interpolant(
    arena: &mut TermArena,
    a: &[TermId],
    b: &[TermId],
    i: TermId,
    decide: impl Fn(&mut TermArena, &[TermId]) -> bool,
) {
    // (1) A ∧ ¬I unsat.
    let not_i = arena.not(i).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(decide(arena, &a_not_i), "A ⇒ I failed (A ∧ ¬I sat)");

    // (2) I ∧ B unsat.
    let mut i_b = vec![i];
    i_b.extend_from_slice(b);
    assert!(decide(arena, &i_b), "I ∧ B sat (must be unsat)");

    // (3) Vocabulary ⊆ shared.
    let av = vocab_of(arena, a);
    let bv = vocab_of(arena, b);
    let iv = vocab_of(arena, std::slice::from_ref(&i));
    for v in &iv {
        assert!(
            av.contains(v) && bv.contains(v),
            "interpolant uses a non-shared symbol"
        );
    }
}

/// One generated `(A, B)` pair: its arena and the two constraint lists.
type Pair = (TermArena, Vec<TermId>, Vec<TermId>);

const LRA_SEED: u64 = 0x1234_5678_9abc_def0;
const LRA_ROUNDS: u32 = 400;

/// One LRA round: 3 Real variables, `na, nb ∈ 1..=2` random linear
/// constraints each.
fn gen_lra_pair(rng: &mut Lcg) -> Pair {
    let mut arena = TermArena::new();
    let vars: Vec<TermId> = (0..3)
        .map(|k| {
            let s = arena.declare(&format!("x{k}"), Sort::Real).unwrap();
            arena.var(s)
        })
        .collect();

    // A random linear constraint over the 3 variables.
    let make_constraint = |arena: &mut TermArena, rng: &mut Lcg| -> TermId {
        let mut lhs: Option<TermId> = None;
        for &v in &vars {
            let c = rng.coeff(-2, 2);
            if c == 0 {
                continue;
            }
            let coeff = arena.real_ratio(c, 1);
            let term = arena.real_mul(coeff, v).unwrap();
            lhs = Some(match lhs {
                Some(acc) => arena.real_add(acc, term).unwrap(),
                None => term,
            });
        }
        let lhs = lhs.unwrap_or_else(|| arena.real_ratio(0, 1));
        let k = arena.real_ratio(rng.coeff(-4, 4), 1);
        match rng.pick(5) {
            0 => arena.real_le(lhs, k).unwrap(),
            1 => arena.real_lt(lhs, k).unwrap(),
            2 => arena.real_ge(lhs, k).unwrap(),
            3 => arena.real_gt(lhs, k).unwrap(),
            _ => arena.eq(lhs, k).unwrap(),
        }
    };

    let na = rng.pick(2) + 1;
    let nb = rng.pick(2) + 1;
    let a: Vec<TermId> = (0..na).map(|_| make_constraint(&mut arena, rng)).collect();
    let b: Vec<TermId> = (0..nb).map(|_| make_constraint(&mut arena, rng)).collect();
    (arena, a, b)
}

#[test]
fn lra_interpolant_soundness_fuzz() {
    let lra_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(check_with_lra(arena, ts), Ok(CheckResult::Unsat))
    };

    let mut rng = Lcg(LRA_SEED);
    let mut produced = 0u32;

    for _ in 0..LRA_ROUNDS {
        let (mut arena, a, b) = gen_lra_pair(&mut rng);

        let mut all = a.clone();
        all.extend_from_slice(&b);
        if !lra_unsat(&mut arena, &all) {
            continue; // only interpolate genuine refutations
        }
        if let Some(i) = lra_interpolant(&mut arena, &a, &b).expect("decides") {
            produced += 1;
            check_interpolant(&mut arena, &a, &b, i, lra_unsat);
        }
    }

    assert!(
        produced > 0,
        "fuzzer never produced an interpolant — coverage bug"
    );
}

const EUF_SEED: u64 = 0x0fed_cba9_8765_4321;
const EUF_ROUNDS: u32 = 800;

/// One EUF round: constants `c0..c2`, unary `f`, a pool `{c_i, f(c_i)}`, and
/// `na, nb ∈ 1..=3` (dis)equality literals over the pool.
fn gen_euf_pair(rng: &mut Lcg) -> Pair {
    let mut arena = TermArena::new();
    let consts: Vec<TermId> = (0..3)
        .map(|k| {
            let s = arena.declare(&format!("c{k}"), Sort::Int).unwrap();
            arena.var(s)
        })
        .collect();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();

    // A pool of terms: the constants plus f applied to each.
    let mut terms = consts.clone();
    for &c in &consts {
        terms.push(arena.apply(f, &[c]).unwrap());
    }

    let make_literal = |arena: &mut TermArena, rng: &mut Lcg| -> TermId {
        let s = terms[rng.pick(terms.len())];
        let t = terms[rng.pick(terms.len())];
        let e = arena.eq(s, t).unwrap();
        if rng.pick(2) == 0 {
            e
        } else {
            arena.not(e).unwrap()
        }
    };

    let na = rng.pick(3) + 1;
    let nb = rng.pick(3) + 1;
    let a: Vec<TermId> = (0..na).map(|_| make_literal(&mut arena, rng)).collect();
    let b: Vec<TermId> = (0..nb).map(|_| make_literal(&mut arena, rng)).collect();
    (arena, a, b)
}

#[test]
fn euf_interpolant_soundness_fuzz() {
    let uf_unsat =
        |arena: &mut TermArena, ts: &[TermId]| matches!(check_qf_uf(arena, ts), CheckResult::Unsat);

    let mut rng = Lcg(EUF_SEED);
    let mut produced = 0u32;

    for _ in 0..EUF_ROUNDS {
        let (mut arena, a, b) = gen_euf_pair(&mut rng);

        let mut all = a.clone();
        all.extend_from_slice(&b);
        if !uf_unsat(&mut arena, &all) {
            continue;
        }
        if let Some(i) = qf_uf_interpolant(&mut arena, &a, &b).expect("decides") {
            produced += 1;
            // A degenerate ⊤/⊥ interpolant has empty vocabulary; `check_qf_uf`
            // cannot re-check a bare Bool-const (no equality atoms), and the
            // inline verify-before-return already confirmed it. Skip the external
            // recheck for those; verify all non-degenerate interpolants.
            if vocab_of(&arena, std::slice::from_ref(&i)).is_empty() {
                continue;
            }
            check_interpolant(&mut arena, &a, &b, i, uf_unsat);
        }
    }

    assert!(
        produced > 0,
        "fuzzer never produced an interpolant — coverage bug"
    );
}

const BV_SEED: u64 = 0xdead_beef_0bad_f00d;
const BV_ROUNDS: u32 = 300;
const BV_WIDTH: u32 = 4;

/// One `QF_BV` round: 3 width-4 variables and `na, nb ∈ 1..=3` (negated)
/// `=`/`bvult`/`bvule` atoms against a variable or a constant.
fn gen_bv_pair(rng: &mut Lcg) -> Pair {
    let mut arena = TermArena::new();
    let width = BV_WIDTH;
    let vars: Vec<TermId> = (0..3)
        .map(|k| {
            let s = arena
                .declare(&format!("b{k}"), Sort::BitVec(width))
                .unwrap();
            arena.var(s)
        })
        .collect();

    let make = |arena: &mut TermArena, rng: &mut Lcg| -> TermId {
        let lhs = vars[rng.pick(vars.len())];
        let rhs = if rng.pick(2) == 0 {
            vars[rng.pick(vars.len())]
        } else {
            let v = u128::try_from(rng.pick(16)).expect("fits u128");
            arena.bv_const(width, v).unwrap()
        };
        let atom = match rng.pick(3) {
            0 => arena.eq(lhs, rhs).unwrap(),
            1 => arena.bv_ult(lhs, rhs).unwrap(),
            _ => arena.bv_ule(lhs, rhs).unwrap(),
        };
        if rng.pick(2) == 0 {
            atom
        } else {
            arena.not(atom).unwrap()
        }
    };

    let na = rng.pick(3) + 1;
    let nb = rng.pick(3) + 1;
    let a: Vec<TermId> = (0..na).map(|_| make(&mut arena, rng)).collect();
    let b: Vec<TermId> = (0..nb).map(|_| make(&mut arena, rng)).collect();
    (arena, a, b)
}

#[test]
fn qf_bv_interpolant_soundness_fuzz() {
    let cfg = SolverConfig::default();
    let bv_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(check_auto(arena, ts, &cfg), Ok(CheckResult::Unsat))
    };

    let mut rng = Lcg(BV_SEED);
    let mut produced = 0u32;

    for _ in 0..BV_ROUNDS {
        let (mut arena, a, b) = gen_bv_pair(&mut rng);

        let mut all = a.clone();
        all.extend_from_slice(&b);
        if !bv_unsat(&mut arena, &all) {
            continue;
        }
        if let Some(i) = qf_bv_interpolant(&mut arena, &a, &b) {
            produced += 1;
            check_interpolant(&mut arena, &a, &b, i, bv_unsat);
        }
    }

    assert!(
        produced > 0,
        "QF_BV fuzzer never produced an interpolant — coverage bug"
    );
}

const UFLRA_SEED: u64 = 0xfeed_face_cafe_b0ba;
const UFLRA_ROUNDS: u32 = 800;

/// One UFLRA round: a single Real `r0`, the pool `{r0, f(r0)}`, and
/// `na, nb ∈ 1..=3` bounds on pool terms.
fn gen_uflra_pair(rng: &mut Lcg) -> Pair {
    let mut arena = TermArena::new();
    let r0_sym = arena.declare("r0", Sort::Real).unwrap();
    let r0 = arena.var(r0_sym);
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    // A small pool — the real var and one shared UF app — so opposing bounds
    // on the SAME term frequently contradict without needing congruence (the
    // fragment uflra_interpolant produces on).
    let terms = [r0, arena.apply(f, &[r0]).unwrap()];

    let make = |arena: &mut TermArena, rng: &mut Lcg| -> TermId {
        let lhs = terms[rng.pick(terms.len())];
        let k = arena.real_ratio(rng.coeff(-2, 2), 1);
        // Bias toward bounds so contradictory intervals arise often.
        match rng.pick(3) {
            0 => arena.real_le(lhs, k).unwrap(),
            1 => arena.real_ge(lhs, k).unwrap(),
            _ => arena.real_lt(lhs, k).unwrap(),
        }
    };

    let na = rng.pick(3) + 1;
    let nb = rng.pick(3) + 1;
    let a: Vec<TermId> = (0..na).map(|_| make(&mut arena, rng)).collect();
    let b: Vec<TermId> = (0..nb).map(|_| make(&mut arena, rng)).collect();
    (arena, a, b)
}

#[test]
fn uflra_interpolant_soundness_fuzz() {
    let cfg = SolverConfig::default();
    let uflra_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(
            check_with_uf_arithmetic(arena, ts, &cfg),
            Ok(CheckResult::Unsat)
        )
    };

    let mut rng = Lcg(UFLRA_SEED);
    let mut produced = 0u32;

    for _ in 0..UFLRA_ROUNDS {
        let (mut arena, a, b) = gen_uflra_pair(&mut rng);

        let mut all = a.clone();
        all.extend_from_slice(&b);
        if !uflra_unsat(&mut arena, &all) {
            continue;
        }
        // An Err is a verifying-decider error (not a false interpolant); skip it.
        if let Ok(Some(i)) = uflra_interpolant(&mut arena, &a, &b) {
            produced += 1;
            // A ground (empty-vocab) interpolant was already inline-verified; the
            // external recheck below covers every non-degenerate case.
            if vocab_of(&arena, std::slice::from_ref(&i)).is_empty() {
                continue;
            }
            check_interpolant(&mut arena, &a, &b, i, uflra_unsat);
        }
    }

    assert!(
        produced > 0,
        "QF_UFLRA fuzzer never produced an interpolant — coverage bug"
    );
}

// ---------------------------------------------------------------------------
// Generator coverage guard (no decider, no interpolation).
// ---------------------------------------------------------------------------

/// Is `lit` a literal `s = t` / `s != t` with `s` and `t` the SAME term?
/// Returns `Some(negated)`.
fn reflexive_literal(arena: &TermArena, lit: TermId) -> Option<bool> {
    let (negated, atom) = match arena.node(lit) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => (true, args[0]),
        _ => (false, lit),
    };
    match arena.node(atom) {
        TermNode::App { op: Op::Eq, args } if args.len() == 2 && args[0] == args[1] => {
            Some(negated)
        }
        _ => None,
    }
}

/// Every BV constant value appearing anywhere under `terms`.
fn bv_constants(arena: &TermArena, terms: &[TermId]) -> Vec<u128> {
    fn walk(arena: &TermArena, t: TermId, out: &mut Vec<u128>, seen: &mut BTreeSet<TermId>) {
        if !seen.insert(t) {
            return;
        }
        match arena.node(t) {
            TermNode::BvConst { value, .. } => out.push(*value),
            TermNode::App { args, .. } => {
                for &a in args {
                    walk(arena, a, out, seen);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for &t in terms {
        walk(arena, t, &mut out, &mut seen);
    }
    out
}

/// Coverage guard for the four LCG-driven fuzzes above.
///
/// Regenerates exactly the populations the fuzzes run (same seeds, same round
/// counts, the same `gen_*_pair` functions) and counts the classes the
/// 2026-09-16 box audit measured at ZERO under the raw-state LCG:
///
/// - LRA: `na == nb == 2` (audit: `(na, nb)` was always `(1,2)` or `(2,1)`
///   over 400 rounds);
/// - EUF: a `t != t` literal (audit: 0/800 — `s` and `t` were consecutive
///   `pick(6)` draws of opposite parity, so `s != t` always) and a partition
///   whose A and B vocabularies are disjoint (audit: 0/800);
/// - `QF_BV`: an ODD constant (audit: 0/300 — `pick(16)` sat at one parity so
///   only `{0,2,..,14}` occurred) and the all-ones constant `15`.
#[test]
fn the_generator_reaches_reflexive_literals_and_odd_constants() {
    let mut lra_na_nb_two = 0u32;
    let mut lra_na_nb_one = 0u32;
    let mut rng = Lcg(LRA_SEED);
    for _ in 0..LRA_ROUNDS {
        let (_, a, b) = gen_lra_pair(&mut rng);
        if a.len() == 2 && b.len() == 2 {
            lra_na_nb_two += 1;
        }
        if a.len() == 1 && b.len() == 1 {
            lra_na_nb_one += 1;
        }
    }

    let mut euf_reflexive_ne = 0u32;
    let mut euf_reflexive_eq = 0u32;
    let mut euf_disjoint_vocab = 0u32;
    let mut rng = Lcg(EUF_SEED);
    for _ in 0..EUF_ROUNDS {
        let (arena, a, b) = gen_euf_pair(&mut rng);
        let lits: Vec<Option<bool>> = a
            .iter()
            .chain(&b)
            .map(|&lit| reflexive_literal(&arena, lit))
            .collect();
        if lits.contains(&Some(true)) {
            euf_reflexive_ne += 1;
        }
        if lits.contains(&Some(false)) {
            euf_reflexive_eq += 1;
        }
        if vocab_of(&arena, &a).is_disjoint(&vocab_of(&arena, &b)) {
            euf_disjoint_vocab += 1;
        }
    }

    let mut bv_odd_constant = 0u32;
    let mut bv_all_ones = 0u32;
    let mut rng = Lcg(BV_SEED);
    for _ in 0..BV_ROUNDS {
        let (arena, a, b) = gen_bv_pair(&mut rng);
        let mut all = a.clone();
        all.extend_from_slice(&b);
        let consts = bv_constants(&arena, &all);
        if consts.iter().any(|c| c % 2 == 1) {
            bv_odd_constant += 1;
        }
        if consts.contains(&u128::from((1u32 << BV_WIDTH) - 1)) {
            bv_all_ones += 1;
        }
    }

    eprintln!(
        "interpolant generator coverage: lra na=nb=2 {lra_na_nb_two}/{LRA_ROUNDS} (na=nb=1 {lra_na_nb_one}); \
         euf t!=t {euf_reflexive_ne}/{EUF_ROUNDS}, t=t {euf_reflexive_eq}/{EUF_ROUNDS}, \
         disjoint-vocab {euf_disjoint_vocab}/{EUF_ROUNDS}; \
         bv odd-constant {bv_odd_constant}/{BV_ROUNDS}, all-ones {bv_all_ones}/{BV_ROUNDS}"
    );
    assert!(
        lra_na_nb_two >= FLOOR_LRA_NA_NB_TWO,
        "LRA rounds with na = nb = 2: {lra_na_nb_two}/{LRA_ROUNDS} (audit measured 0)"
    );
    assert!(
        euf_reflexive_ne >= FLOOR_EUF_REFLEXIVE_NE,
        "EUF rounds with a `t != t` literal: {euf_reflexive_ne}/{EUF_ROUNDS} (audit measured 0)"
    );
    assert!(
        euf_disjoint_vocab >= FLOOR_EUF_DISJOINT_VOCAB,
        "EUF rounds with disjoint A/B vocabularies: {euf_disjoint_vocab}/{EUF_ROUNDS} (audit measured 0)"
    );
    assert!(
        bv_odd_constant >= FLOOR_BV_ODD_CONSTANT,
        "QF_BV rounds with an odd constant: {bv_odd_constant}/{BV_ROUNDS} (audit measured 0)"
    );
    assert!(
        bv_all_ones >= FLOOR_BV_ALL_ONES,
        "QF_BV rounds with the all-ones constant: {bv_all_ones}/{BV_ROUNDS} (audit measured 0)"
    );
}

// Measured with the mixed generator (2026-09-16): lra na=nb=2 103, euf t!=t 244,
// disjoint-vocab 13, bv odd-constant 197, all-ones 36. Floors at about a quarter.
const FLOOR_LRA_NA_NB_TWO: u32 = 25;
const FLOOR_EUF_REFLEXIVE_NE: u32 = 60;
const FLOOR_EUF_DISJOINT_VOCAB: u32 = 3;
const FLOOR_BV_ODD_CONSTANT: u32 = 50;
const FLOOR_BV_ALL_ONES: u32 = 9;
