//! The trust anchor for T-B.7 refutation. Two adversarial properties over the
//! house LCG, mirroring `infer_property.rs`:
//!
//! 1. **soundness on model-consistent input** — from a random ground assignment
//!    we build an equality set (and disequality set) that HOLD under it; the
//!    refuter must then **never** return `Unsat` (a satisfiable system may only be
//!    `unknown`);
//! 2. **certified conflicts are genuinely unsat** — from adversarial UNSAT seeds
//!    (a variable forced to two distinct constants through a chain) any `Unsat`
//!    the refuter returns must cite a premise subset that is **jointly
//!    unsatisfiable by brute-force small-model enumeration**. A wrong `unsat`
//!    fails this — but it cannot happen, because the `unsat` is gated by the
//!    independent re-checker.

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};
use common::{cat, seq_sort, unit};

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
    fn below(&mut self, n: u64) -> u64 {
        (self.next_u64() >> 33) % n
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & (1 << 40) != 0
    }
}

/// A generous, deadline-free budget — refutation is non-recursive, so this only
/// exercises the API shape.
fn budget() -> SearchBudget {
    SearchBudget::new(1_000_000)
}

// ----- shared term pool -------------------------------------------------------

struct Pool {
    terms: Vec<TermId>,
}

impl Pool {
    fn new(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Self {
        let seq_vars: Vec<TermId> = (0..4)
            .map(|i| {
                let s = arena
                    .declare(&format!("p{id}_{i}"), seq_sort())
                    .expect("declare seq var");
                arena.var(s)
            })
            .collect();
        let chars: Vec<TermId> = [b'a', b'b']
            .iter()
            .map(|&c| {
                let ce = arena.bv_const(8, u128::from(c)).expect("char const");
                unit(arena, ce)
            })
            .collect();

        let mut terms: Vec<TermId> = seq_vars;
        terms.extend_from_slice(&chars);
        for _ in 0..7 {
            let a = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            let b = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            terms.push(cat(arena, a, b));
        }
        Self { terms }
    }
}

fn gen_assignment(arena: &TermArena, rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for &t in &pool.terms {
        collect_vars(arena, t, &mut vars);
    }
    for s in vars {
        let len = rng.below(3);
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: u128::from(b'a') + u128::from(rng.below(2)),
            })
            .collect();
        asg.set(s, Value::Seq(elems));
    }
    asg
}

// ----- (1) soundness on model-consistent input -------------------------------

#[test]
fn model_consistent_systems_are_never_refuted() {
    let mut rng = Lcg(0x0BAD_F00D_1234_5678);
    let mut checked = 0u64;

    for id in 0..1600 {
        let mut arena = TermArena::new();
        let pool = Pool::new(&mut arena, &mut rng, id);
        let asg = gen_assignment(&arena, &mut rng, &pool);

        let vals: Vec<Value> = pool
            .terms
            .iter()
            .map(|&t| eval(&arena, t, &asg).expect("closed pool term"))
            .collect();

        // Equalities that HOLD under `asg`, and disequalities that HOLD (pairs
        // that genuinely differ) — a fully model-consistent system.
        let mut eqs = Vec::new();
        let mut diseqs = Vec::new();
        for i in 0..pool.terms.len() {
            for j in (i + 1)..pool.terms.len() {
                if vals[i] == vals[j] {
                    if rng.coin() {
                        eqs.push((pool.terms[i], pool.terms[j]));
                    }
                } else if rng.coin() {
                    diseqs.push((pool.terms[i], pool.terms[j]));
                }
            }
        }
        if eqs.is_empty() {
            continue;
        }
        checked += 1;

        let outcome = refute_word_equations(&mut arena, &eqs, &diseqs, &budget());
        assert_eq!(
            outcome,
            RefuteOutcome::Unknown,
            "a model-consistent system was refuted (wrong unsat).\neqs: {eqs:?}\ndiseqs: {diseqs:?}"
        );
    }

    assert!(
        checked >= 1000,
        "expected at least 1000 non-empty model-consistent systems (did {checked})"
    );
}

// ----- (2) certified conflicts are genuinely unsat ---------------------------

/// An UNSAT seed: a variable chain forcing one class to contain two distinct
/// constants, plus a satisfiable noise equality among fresh variables.
fn adversarial_seed(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Vec<(TermId, TermId)> {
    let ca = {
        let e = arena.bv_const(8, u128::from(b'a')).expect("a");
        unit(arena, e)
    };
    let cb = {
        let e = arena.bv_const(8, u128::from(b'b')).expect("b");
        unit(arena, e)
    };

    let k = 1 + rng.below(3); // 1..3 links
    let vars: Vec<TermId> = (0..=k)
        .map(|i| {
            let s = arena
                .declare(&format!("c{id}_{i}"), seq_sort())
                .expect("var");
            arena.var(s)
        })
        .collect();

    let mut eqs = Vec::new();
    eqs.push((vars[0], ca));
    for w in vars.windows(2) {
        eqs.push((w[0], w[1]));
    }
    eqs.push((*vars.last().expect("nonempty"), cb));

    if rng.coin() {
        let s1 = arena.declare(&format!("n{id}_0"), seq_sort()).expect("n0");
        let s2 = arena.declare(&format!("n{id}_1"), seq_sort()).expect("n1");
        eqs.push((arena.var(s1), arena.var(s2)));
    }
    eqs
}

#[test]
fn certified_unsat_premises_are_brute_force_unsat() {
    let mut rng = Lcg(0xC0FF_EE00_DEAD_BEEF);
    let mut refuted = 0u64;

    for id in 0..1400 {
        let mut arena = TermArena::new();
        let eqs = adversarial_seed(&mut arena, &mut rng, id);

        let outcome = refute_word_equations(&mut arena, &eqs, &[], &budget());
        let RefuteOutcome::Unsat { premises } = outcome else {
            // Refutation may decline (conservative), but for these direct
            // constant-chain clashes it should certify; either way, no wrong unsat.
            continue;
        };

        // The cited premise subset must be genuinely unsatisfiable.
        let cited: Vec<(TermId, TermId)> = premises.iter().map(|&i| eqs[i]).collect();
        assert!(!cited.is_empty(), "an unsat must cite at least one premise");
        assert!(
            brute_force_unsat(&arena, &cited),
            "cited premises {premises:?} are NOT unsat by brute force (wrong refutation)"
        );
        refuted += 1;
    }

    assert!(
        refuted >= 1000,
        "expected at least 1000 certified refutations (did {refuted})"
    );
}

// ----- brute-force small-model enumeration -----------------------------------

fn brute_force_unsat(arena: &TermArena, eqs: &[(TermId, TermId)]) -> bool {
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for &(a, b) in eqs {
        collect_vars(arena, a, &mut vars);
        collect_vars(arena, b, &mut vars);
    }
    let vars: Vec<SymbolId> = vars.into_iter().collect();

    let alphabet = [b'a', b'b'];
    let mut values: Vec<Value> = Vec::new();
    for len in 0..=2usize {
        enumerate_strings(&alphabet, len, &mut Vec::new(), &mut values);
    }

    let base = values.len();
    let Some(total) = base.checked_pow(u32::try_from(vars.len()).expect("few vars")) else {
        return false;
    };
    for combo in 0..total {
        let mut asg = Assignment::new();
        let mut rem = combo;
        for &v in &vars {
            asg.set(v, values[rem % base].clone());
            rem /= base;
        }
        let sat = eqs.iter().all(|&(a, b)| {
            matches!(
                (eval(arena, a, &asg), eval(arena, b, &asg)),
                (Ok(va), Ok(vb)) if va == vb
            )
        });
        if sat {
            return false;
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
