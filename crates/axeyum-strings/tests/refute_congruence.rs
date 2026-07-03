//! Slice-3 refutation: **concat-congruence / affix-cancellation** disequality
//! `unsat`, behind the independent [`check_congruence_equality`] re-check. Concrete
//! tests pin the census `str002` shape and the cancellation generalizations; the
//! honest-decline test pins that a bare quadratic word *equation* is NOT closed
//! here; and two adversarial properties confirm both directions:
//!
//! 1. **soundness** — a premise + a disequality that HOLD under a random model are
//!    never refuted (≥1000 model-consistent systems);
//! 2. **certified refutations are genuinely unsat** — every congruence refutation's
//!    cited premises + the disequality are jointly unsatisfiable by brute-force
//!    small-model enumeration (≥1000 refutations).
#![allow(clippy::many_single_char_names, clippy::similar_names)]

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};
use common::{cat, seq_var, unit};

fn budget() -> SearchBudget {
    SearchBudget::new(1_000_000)
}

/// A constant sequence from a byte string (each byte a `seq.unit` of a char const).
fn konst(arena: &mut TermArena, bytes: &[u8]) -> TermId {
    assert!(!bytes.is_empty(), "konst on non-empty bytes");
    let parts: Vec<TermId> = bytes
        .iter()
        .map(|&c| {
            let e = arena.bv_const(8, u128::from(c)).expect("char const");
            unit(arena, e)
        })
        .collect();
    parts
        .iter()
        .copied()
        .reduce(|acc, p| cat(arena, acc, p))
        .expect("non-empty")
}

// ----- concrete census shapes -------------------------------------------------

#[test]
fn str002_congruence_certifies() {
    // The census `r1_QF_S_str002` leaf, one disjunct branch:
    //   premise  xx ≈ yy ++ "aa"
    //   diseq    xx ++ "bb"  ≠  yy ++ "aa" ++ "bb"
    // From the premise, xx ++ "bb" ≈ (yy ++ "aa") ++ "bb" — a congruence contradiction.
    let mut arena = TermArena::new();
    let xx = seq_var(&mut arena, "xx");
    let yy = seq_var(&mut arena, "yy");
    let aa = konst(&mut arena, b"aa");
    let bb = konst(&mut arena, b"bb");

    let yy_aa = cat(&mut arena, yy, aa);
    let eqs = vec![(xx, yy_aa)];

    let lhs = cat(&mut arena, xx, bb); // xx ++ "bb"
    let rhs = cat(&mut arena, yy_aa, bb); // (yy ++ "aa") ++ "bb"
    let diseqs = vec![(lhs, rhs)];

    let outcome = refute_word_equations(&mut arena, &eqs, &diseqs, &budget());
    let RefuteOutcome::Unsat { premises } = outcome else {
        panic!("str002 congruence shape was not refuted: {outcome:?}");
    };
    assert_eq!(
        premises,
        BTreeSet::from([0]),
        "cites exactly the sole premise"
    );
    assert!(
        congruence_unsat(&arena, &[eqs[0]], diseqs[0]),
        "cited premises + diseq are not brute-force unsat"
    );
}

#[test]
fn suffix_cancellation_certifies() {
    // premise xx ≈ yy ; diseq xx ++ "cc" ≠ yy ++ "cc" (common constant suffix).
    let mut arena = TermArena::new();
    let xx = seq_var(&mut arena, "xx");
    let yy = seq_var(&mut arena, "yy");
    let cc = konst(&mut arena, b"cc");
    let eqs = vec![(xx, yy)];
    let lhs = cat(&mut arena, xx, cc);
    let rhs = cat(&mut arena, yy, cc);
    let diseqs = vec![(lhs, rhs)];
    assert!(matches!(
        refute_word_equations(&mut arena, &eqs, &diseqs, &budget()),
        RefuteOutcome::Unsat { .. }
    ));
}

#[test]
fn prefix_cancellation_certifies() {
    // premise xx ≈ yy ; diseq "pp" ++ xx ≠ "pp" ++ yy (common constant prefix).
    let mut arena = TermArena::new();
    let xx = seq_var(&mut arena, "xx");
    let yy = seq_var(&mut arena, "yy");
    let pp = konst(&mut arena, b"pp");
    let eqs = vec![(xx, yy)];
    let lhs = cat(&mut arena, pp, xx);
    let rhs = cat(&mut arena, pp, yy);
    let diseqs = vec![(lhs, rhs)];
    assert!(matches!(
        refute_word_equations(&mut arena, &eqs, &diseqs, &budget()),
        RefuteOutcome::Unsat { .. }
    ));
}

#[test]
fn chained_substitution_certifies() {
    // A two-step substitution chain: xx ≈ yy ++ "a", yy ≈ zz.
    //   diseq  xx ++ "b" ≠ zz ++ "a" ++ "b"
    // xx → (zz ++ "a"), so xx ++ "b" ≈ zz ++ "ab" ≈ zz ++ "a" ++ "b".
    let mut arena = TermArena::new();
    let xx = seq_var(&mut arena, "xx");
    let yy = seq_var(&mut arena, "yy");
    let zz = seq_var(&mut arena, "zz");
    let a = konst(&mut arena, b"a");
    let b = konst(&mut arena, b"b");
    let yy_a = cat(&mut arena, yy, a);
    let eqs = vec![(xx, yy_a), (yy, zz)];
    let lhs = cat(&mut arena, xx, b);
    let za = cat(&mut arena, zz, a);
    let rhs = cat(&mut arena, za, b);
    let diseqs = vec![(lhs, rhs)];
    let outcome = refute_word_equations(&mut arena, &eqs, &diseqs, &budget());
    let RefuteOutcome::Unsat { premises } = outcome else {
        panic!("chained substitution not refuted: {outcome:?}");
    };
    assert!(
        congruence_unsat(
            &arena,
            &premises.iter().map(|&i| eqs[i]).collect::<Vec<_>>(),
            diseqs[0]
        ),
        "cited premises + diseq not brute-force unsat"
    );
}

#[test]
fn bare_quadratic_word_equation_declines() {
    // The `quad-028-2-2-unsat` shape as a bare *equation* (no disequality):
    //   x1 ++ "abc" ++ x2 ++ z  =  x2 ++ "bab" ++ x1 ++ t
    // It IS unsat, but only by a Nielsen/length case analysis — NOT a word-level
    // constant clash or congruence/cancellation. The refuter must honestly DECLINE
    // it to `unknown` (a wrong `unsat` is impossible; an *unknown* is correct here).
    let mut arena = TermArena::new();
    let x1 = seq_var(&mut arena, "x1");
    let x2 = seq_var(&mut arena, "x2");
    let z = seq_var(&mut arena, "z");
    let t = seq_var(&mut arena, "t");
    let abc = konst(&mut arena, b"abc");
    let bab = konst(&mut arena, b"bab");

    let l = {
        let a = cat(&mut arena, x1, abc);
        let a = cat(&mut arena, a, x2);
        cat(&mut arena, a, z)
    };
    let r = {
        let a = cat(&mut arena, x2, bab);
        let a = cat(&mut arena, a, x1);
        cat(&mut arena, a, t)
    };
    let eqs = vec![(l, r)];
    assert_eq!(
        refute_word_equations(&mut arena, &eqs, &[], &budget()),
        RefuteOutcome::Unknown,
        "a bare quadratic word equation must decline, not certify"
    );
}

// ----- adversarial properties -------------------------------------------------

/// The repo's house LCG.
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        (self.next_u64() >> 33) % n
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & (1 << 40) != 0
    }
}

/// A short random constant of 1-2 chars over `{a, b}`.
fn rand_konst(arena: &mut TermArena, rng: &mut Lcg) -> TermId {
    let len = 1 + rng.below(2);
    let bytes: Vec<u8> = (0..len)
        .map(|_| if rng.coin() { b'a' } else { b'b' })
        .collect();
    konst(arena, &bytes)
}

/// Builds a congruence-UNSAT instance: `xx ≈ yy ++ C` and a disequality whose two
/// sides are `xx`-vs-`(yy ++ C)` wrapped in a shared constant prefix/suffix, so the
/// premise forces them equal. Returns `(eqs, (a, b))`.
fn congruence_seed(
    arena: &mut TermArena,
    rng: &mut Lcg,
    id: u64,
) -> (Vec<(TermId, TermId)>, (TermId, TermId)) {
    let xx = seq_var(arena, &format!("cx{id}"));
    let yy = seq_var(arena, &format!("cy{id}"));
    let c = rand_konst(arena, rng);
    let rhs = cat(arena, yy, c); // yy ++ C
    let mut eqs = vec![(xx, rhs)];

    // Optional satisfiable noise premise over two fresh variables.
    if rng.coin() {
        let p = seq_var(arena, &format!("np{id}"));
        let q = seq_var(arena, &format!("nq{id}"));
        eqs.push((p, q));
    }

    // Wrap both sides in a shared affix. `xx` and `rhs` are premise-equal, so the
    // two wrapped sides are equal.
    let d = rand_konst(arena, rng);
    let (a, b) = if rng.coin() {
        (cat(arena, xx, d), cat(arena, rhs, d)) // suffix
    } else {
        (cat(arena, d, xx), cat(arena, d, rhs)) // prefix
    };
    (eqs, (a, b))
}

#[test]
fn certified_congruence_refutations_are_brute_force_unsat() {
    let mut rng = Lcg(0xC01D_CAFE_5EED_1111);
    let mut refuted = 0u64;
    for id in 0..1500 {
        let mut arena = TermArena::new();
        let (eqs, diseq) = congruence_seed(&mut arena, &mut rng, id);
        let outcome = refute_word_equations(&mut arena, &eqs, &[diseq], &budget());
        let RefuteOutcome::Unsat { premises } = outcome else {
            continue;
        };
        let cited: Vec<(TermId, TermId)> = premises.iter().map(|&i| eqs[i]).collect();
        assert!(!cited.is_empty(), "an unsat must cite at least one premise");
        assert!(
            congruence_unsat(&arena, &cited, diseq),
            "cited premises {premises:?} + diseq are NOT unsat by brute force (wrong refutation)"
        );
        refuted += 1;
    }
    assert!(
        refuted >= 1000,
        "expected ≥1000 certified congruence refutations (did {refuted})"
    );
}

#[test]
fn model_consistent_congruence_never_refuted() {
    let mut rng = Lcg(0x5AFE_1234_9876_ABCD);
    let mut checked = 0u64;
    for id in 0..1600 {
        let mut arena = TermArena::new();
        // A pool of variables and short constants; build equalities/disequalities
        // that all HOLD under a random ground model.
        let vars: Vec<TermId> = (0..3)
            .map(|i| seq_var(&mut arena, &format!("mc{id}_{i}")))
            .collect();
        let consts = [
            rand_konst(&mut arena, &mut rng),
            rand_konst(&mut arena, &mut rng),
        ];
        let mut pool: Vec<TermId> = vars.clone();
        pool.extend_from_slice(&consts);
        for _ in 0..4 {
            let a = pool[usize::try_from(rng.below(pool.len() as u64)).unwrap()];
            let b = pool[usize::try_from(rng.below(pool.len() as u64)).unwrap()];
            pool.push(cat(&mut arena, a, b));
        }

        // Random ground assignment.
        let mut asg = Assignment::new();
        let mut sv: BTreeSet<SymbolId> = BTreeSet::new();
        for &t in &pool {
            collect_vars(&arena, t, &mut sv);
        }
        for s in &sv {
            let len = rng.below(3);
            let elems = (0..len)
                .map(|_| Value::Bv {
                    width: 8,
                    value: u128::from(b'a') + u128::from(rng.below(2)),
                })
                .collect();
            asg.set(*s, Value::Seq(elems));
        }
        let vals: Vec<Value> = pool
            .iter()
            .map(|&t| eval(&arena, t, &asg).unwrap())
            .collect();

        let mut eqs = Vec::new();
        let mut diseqs = Vec::new();
        for i in 0..pool.len() {
            for j in (i + 1)..pool.len() {
                if vals[i] == vals[j] {
                    if rng.coin() {
                        eqs.push((pool[i], pool[j]));
                    }
                } else if rng.coin() {
                    diseqs.push((pool[i], pool[j]));
                }
            }
        }
        if eqs.is_empty() || diseqs.is_empty() {
            continue;
        }
        checked += 1;
        let outcome = refute_word_equations(&mut arena, &eqs, &diseqs, &budget());
        assert_eq!(
            outcome,
            RefuteOutcome::Unknown,
            "a model-consistent system was refuted (wrong unsat)\neqs {eqs:?}\ndiseqs {diseqs:?}"
        );
    }
    assert!(
        checked >= 1000,
        "expected ≥1000 non-trivial model-consistent systems (did {checked})"
    );
}

// ----- brute-force small-model enumeration -----------------------------------

/// Whether `eqs ∧ (a ≠ b)` is unsatisfiable over strings of length ≤ 2 on `{a,b}`:
/// i.e. every assignment that satisfies all `eqs` forces `a == b`.
fn congruence_unsat(arena: &TermArena, eqs: &[(TermId, TermId)], diseq: (TermId, TermId)) -> bool {
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for &(a, b) in eqs {
        collect_vars(arena, a, &mut vars);
        collect_vars(arena, b, &mut vars);
    }
    collect_vars(arena, diseq.0, &mut vars);
    collect_vars(arena, diseq.1, &mut vars);
    let vars: Vec<SymbolId> = vars.into_iter().collect();

    let mut values: Vec<Value> = Vec::new();
    for len in 0..=2usize {
        enumerate_strings(b"ab", len, &mut Vec::new(), &mut values);
    }
    let base = values.len();
    let Some(total) = base.checked_pow(u32::try_from(vars.len()).unwrap()) else {
        return false;
    };
    for combo in 0..total {
        let mut asg = Assignment::new();
        let mut rem = combo;
        for &v in &vars {
            asg.set(v, values[rem % base].clone());
            rem /= base;
        }
        let eqs_hold = eqs.iter().all(|&(a, b)| {
            matches!((eval(arena, a, &asg), eval(arena, b, &asg)), (Ok(x), Ok(y)) if x == y)
        });
        if !eqs_hold {
            continue;
        }
        // Premises hold; for unsat the diseq must be impossible, i.e. sides equal.
        let sides_equal = matches!(
            (eval(arena, diseq.0, &asg), eval(arena, diseq.1, &asg)),
            (Ok(x), Ok(y)) if x == y
        );
        if !sides_equal {
            return false; // a model with premises holding and sides differing → SAT
        }
    }
    true
}

fn collect_vars(arena: &TermArena, t: TermId, out: &mut BTreeSet<SymbolId>) {
    use axeyum_ir::TermNode;
    match arena.node(t) {
        TermNode::Symbol(s) => {
            if matches!(arena.sort_of(t), axeyum_ir::Sort::Seq(_)) {
                out.insert(*s);
            }
        }
        TermNode::App { args, .. } => {
            for &a in args {
                collect_vars(arena, a, out);
            }
        }
        _ => {}
    }
}

fn enumerate_strings(alphabet: &[u8], len: usize, acc: &mut Vec<Value>, out: &mut Vec<Value>) {
    if len == 0 {
        out.push(Value::Seq(acc.clone()));
        return;
    }
    for &c in alphabet {
        acc.push(Value::Bv {
            width: 8,
            value: u128::from(c),
        });
        enumerate_strings(alphabet, len - 1, acc, out);
        acc.pop();
    }
}
