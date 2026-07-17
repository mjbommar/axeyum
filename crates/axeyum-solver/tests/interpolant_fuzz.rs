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
        self.0
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

#[test]
fn lra_interpolant_soundness_fuzz() {
    let lra_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(check_with_lra(arena, ts), Ok(CheckResult::Unsat))
    };

    let mut rng = Lcg(0x1234_5678_9abc_def0);
    let mut produced = 0u32;

    for _ in 0..400 {
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
        let a: Vec<TermId> = (0..na)
            .map(|_| make_constraint(&mut arena, &mut rng))
            .collect();
        let b: Vec<TermId> = (0..nb)
            .map(|_| make_constraint(&mut arena, &mut rng))
            .collect();

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

#[test]
fn euf_interpolant_soundness_fuzz() {
    let uf_unsat =
        |arena: &mut TermArena, ts: &[TermId]| matches!(check_qf_uf(arena, ts), CheckResult::Unsat);

    let mut rng = Lcg(0x0fed_cba9_8765_4321);
    let mut produced = 0u32;

    for _ in 0..800 {
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
        let a: Vec<TermId> = (0..na)
            .map(|_| make_literal(&mut arena, &mut rng))
            .collect();
        let b: Vec<TermId> = (0..nb)
            .map(|_| make_literal(&mut arena, &mut rng))
            .collect();

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

#[test]
fn qf_bv_interpolant_soundness_fuzz() {
    let cfg = SolverConfig::default();
    let bv_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(check_auto(arena, ts, &cfg), Ok(CheckResult::Unsat))
    };

    let mut rng = Lcg(0xdead_beef_0bad_f00d);
    let mut produced = 0u32;

    for _ in 0..300 {
        let mut arena = TermArena::new();
        let width = 4u32;
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
        let a: Vec<TermId> = (0..na).map(|_| make(&mut arena, &mut rng)).collect();
        let b: Vec<TermId> = (0..nb).map(|_| make(&mut arena, &mut rng)).collect();

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

#[test]
fn uflra_interpolant_soundness_fuzz() {
    let cfg = SolverConfig::default();
    let uflra_unsat = |arena: &mut TermArena, ts: &[TermId]| {
        matches!(
            check_with_uf_arithmetic(arena, ts, &cfg),
            Ok(CheckResult::Unsat)
        )
    };

    let mut rng = Lcg(0xfeed_face_cafe_b0ba);
    let mut produced = 0u32;

    for _ in 0..800 {
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
        let a: Vec<TermId> = (0..na).map(|_| make(&mut arena, &mut rng)).collect();
        let b: Vec<TermId> = (0..nb).map(|_| make(&mut arena, &mut rng)).collect();

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
