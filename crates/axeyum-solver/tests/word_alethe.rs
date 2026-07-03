//! Trust anchor for the word-conflict Alethe emitter: a house-LCG property sweep
//! (every certified refutation emits a self-checking certificate) plus a
//! front-door demonstration (a system refuted through the public
//! [`refute_word_equations`] API carries an Alethe certificate).
//!
//! Mirrors `axeyum-strings/tests/refute_property.rs`: adversarial UNSAT seeds
//! (a variable chain forcing one class to two distinct constants, and self-loops)
//! must each yield a certificate that self-checks; model-consistent systems must
//! never produce one (a certificate is only ever emitted behind the independent
//! T-B.7 re-check, and `word_conflict_alethe` verifies before recording).

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_solver::{WordAletheError, word_conflict_alethe};
use axeyum_strings::{RefuteOutcome, SearchBudget, refute_word_equations};

const ELEM: axeyum_ir::ArraySortKey = axeyum_ir::ArraySortKey::BitVec(8);

fn seq_sort() -> Sort {
    Sort::Seq(ELEM)
}

fn seq_var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, seq_sort()).expect("seq var");
    arena.var(s)
}

fn ch(arena: &mut TermArena, c: u8) -> TermId {
    let e = arena.bv_const(8, u128::from(c)).expect("char");
    arena.seq_unit(e).expect("unit")
}

fn cat(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.seq_concat(a, b).expect("concat")
}

fn budget() -> SearchBudget {
    SearchBudget::new(50_000_000)
}

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

// ----- (1) property: certified refutations emit self-checking certificates ----

/// An UNSAT seed: a variable chain forcing one class to contain two distinct
/// constants, plus optional satisfiable noise (mirrors `refute_property`).
fn constant_chain_seed(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Vec<(TermId, TermId)> {
    let ca = ch(arena, b'a');
    let cb = ch(arena, b'b');
    let k = 1 + rng.below(3); // 1..3 links
    let vars: Vec<TermId> = (0..=k)
        .map(|i| seq_var(arena, &format!("c{id}_{i}")))
        .collect();

    let mut eqs = Vec::new();
    eqs.push((vars[0], ca));
    for w in vars.windows(2) {
        eqs.push((w[0], w[1]));
    }
    eqs.push((*vars.last().expect("nonempty"), cb));
    if rng.coin() {
        let n0 = seq_var(arena, &format!("n{id}_0"));
        let n1 = seq_var(arena, &format!("n{id}_1"));
        eqs.push((n0, n1));
    }
    eqs
}

/// A self-loop seed forcing a nonempty constant to ε (`x = pre ++ x ++ post`).
fn self_loop_seed(arena: &mut TermArena, rng: &mut Lcg, id: u64) -> Vec<(TermId, TermId)> {
    let x = seq_var(arena, &format!("s{id}"));
    let c = ch(arena, if rng.coin() { b'a' } else { b'b' });
    let rhs = if rng.coin() {
        cat(arena, c, x) // "a" ++ x
    } else {
        cat(arena, x, c) // x ++ "a"
    };
    vec![(x, rhs)]
}

#[test]
fn certified_refutations_emit_self_checking_certificates() {
    let mut rng = Lcg(0xA1E7_4E00_D00D_F00D);
    let mut certified = 0u64;

    for id in 0..900 {
        let mut arena = TermArena::new();
        let eqs = if id % 3 == 0 {
            self_loop_seed(&mut arena, &mut rng, id)
        } else {
            constant_chain_seed(&mut arena, &mut rng, id)
        };

        match word_conflict_alethe(&mut arena, &eqs, &[]) {
            Ok(cert) => {
                // Self-checks and derives the empty clause.
                assert!(
                    cert.check(),
                    "emitted certificate must self-check (id {id})"
                );
                // The cited premises must be a genuine unsat core: re-refuting the
                // cited subset alone is still Unsat.
                let cited: Vec<(TermId, TermId)> = cert.premises.iter().map(|&i| eqs[i]).collect();
                assert!(!cited.is_empty(), "unsat cites at least one premise");
                let mut check_arena = clone_system(&arena, &cited);
                assert!(
                    matches!(
                        refute_word_equations(&mut check_arena.0, &check_arena.1, &[], &budget()),
                        RefuteOutcome::Unsat { .. }
                    ),
                    "cited premises {:?} are not independently unsat (id {id})",
                    cert.premises
                );
                certified += 1;
            }
            // Conservative declines are allowed (never a wrong certificate), but the
            // direct constant chains / self-loops here should certify.
            Err(WordAletheError::NotRefuted) => {}
            Err(e) => panic!("unexpected emitter error {e:?} (id {id})"),
        }
    }

    assert!(
        certified >= 500,
        "expected >= 500 certified refutations (did {certified})"
    );
}

/// Rebuild the cited equalities in a fresh arena (structurally) so the re-check is
/// independent of the emitter's arena. Returns the arena + the rebuilt pairs.
fn clone_system(arena: &TermArena, eqs: &[(TermId, TermId)]) -> (TermArena, Vec<(TermId, TermId)>) {
    let mut out = TermArena::new();
    let mut memo = std::collections::HashMap::new();
    let pairs = eqs
        .iter()
        .map(|&(a, b)| {
            (
                rebuild(arena, &mut out, &mut memo, a),
                rebuild(arena, &mut out, &mut memo, b),
            )
        })
        .collect();
    (out, pairs)
}

fn rebuild(
    src: &TermArena,
    dst: &mut TermArena,
    memo: &mut std::collections::HashMap<TermId, TermId>,
    t: TermId,
) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let r = match src.node(t) {
        TermNode::Symbol(s) => {
            let (name, sort) = src.symbol(*s);
            let sym = dst.declare(name, sort).expect("declare");
            dst.var(sym)
        }
        TermNode::BvConst { width, value } => dst.bv_const(*width, *value).expect("bv const"),
        TermNode::App { op, args } => {
            let a: Vec<TermId> = args.iter().map(|&x| rebuild(src, dst, memo, x)).collect();
            match op {
                Op::SeqConcat => dst.seq_concat(a[0], a[1]).expect("concat"),
                Op::SeqUnit => dst.seq_unit(a[0]).expect("unit"),
                Op::SeqEmpty(k) => dst.seq_empty(*k),
                other => panic!("unexpected op {other:?} in seq system"),
            }
        }
        other => panic!("unexpected node {other:?}"),
    };
    memo.insert(t, r);
    r
}

// ----- (2) soundness: model-consistent systems never emit a certificate -------

#[test]
fn model_consistent_systems_never_certify() {
    let mut rng = Lcg(0x0BAD_F00D_5151_2323);
    let mut checked = 0u64;

    for id in 0..600 {
        let mut arena = TermArena::new();
        // A small pool of variables and characters + a few concatenations.
        let vars: Vec<TermId> = (0..4)
            .map(|i| seq_var(&mut arena, &format!("m{id}_{i}")))
            .collect();
        let chars = [ch(&mut arena, b'a'), ch(&mut arena, b'b')];
        let mut pool: Vec<TermId> = vars.clone();
        pool.extend_from_slice(&chars);
        for _ in 0..5 {
            let a = pool[usize::try_from(rng.below(pool.len() as u64)).unwrap()];
            let b = pool[usize::try_from(rng.below(pool.len() as u64)).unwrap()];
            pool.push(cat(&mut arena, a, b));
        }

        // A ground assignment, then equalities that HOLD under it.
        let mut asg = Assignment::new();
        let mut syms: BTreeSet<SymbolId> = BTreeSet::new();
        for &t in &pool {
            collect_vars(&arena, t, &mut syms);
        }
        for s in syms {
            let len = rng.below(3);
            let elems = (0..len)
                .map(|_| Value::Bv {
                    width: 8,
                    value: u128::from(b'a') + u128::from(rng.below(2)),
                })
                .collect();
            asg.set(s, Value::Seq(elems));
        }
        let vals: Vec<Value> = pool
            .iter()
            .map(|&t| eval(&arena, t, &asg).expect("closed"))
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
        if eqs.is_empty() {
            continue;
        }
        checked += 1;

        // A model-consistent system is satisfiable: the emitter must decline.
        assert!(
            matches!(
                word_conflict_alethe(&mut arena, &eqs, &diseqs),
                Err(WordAletheError::NotRefuted)
            ),
            "a model-consistent system produced a certificate (wrong).\neqs {eqs:?}\ndiseqs {diseqs:?}"
        );
    }

    assert!(
        checked >= 300,
        "expected >= 300 non-empty model-consistent systems (did {checked})"
    );
}

fn collect_vars(arena: &TermArena, t: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            for &a in args {
                collect_vars(arena, a, out);
            }
        }
        _ => {}
    }
}

// ----- (3) front-door demonstration ------------------------------------------

#[test]
fn front_door_word_unsat_carries_certificate() {
    // Construct a word unsat through the public refute API (the front door), then
    // show the same system carries an Alethe certificate that self-checks.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let eqs = [(x, a), (x, y), (y, b)];

    // Front door: the independent refuter reports unsat with a premise core.
    let RefuteOutcome::Unsat { premises } = refute_word_equations(&mut arena, &eqs, &[], &budget())
    else {
        panic!("front-door refute must report unsat");
    };
    assert!(!premises.is_empty());

    // The same system now carries a self-checking Alethe certificate whose cited
    // core matches the front-door refutation.
    let cert = word_conflict_alethe(&mut arena, &eqs, &[]).expect("emits a certificate");
    assert!(cert.check(), "front-door certificate must self-check");
    assert_eq!(cert.premises, premises, "cited core matches the refutation");
}
