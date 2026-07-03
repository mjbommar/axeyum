//! The trust anchor for T-B.2. With the house LCG we generate random ground
//! assignments and, from them, **model-consistent** equality sets (only
//! equalities whose two sides actually evaluate equal are kept). Then we assert
//! the three soundness invariants of the flat/normal-form substrate:
//!
//! 1. **class soundness** — every member of an equivalence class evaluates to
//!    the same value (the union-find never merges unequal terms);
//! 2. **normal-form soundness** — each class's normal-form vector, evaluated and
//!    concatenated, equals every member's value;
//! 3. **explanation sufficiency** — recomputing a class's normal form from
//!    *only* the premises the explanation cites re-derives the same vector.
//!
//! Cycle / unreconciled declines are legitimate incompleteness on a
//! model-consistent input (a `y ≈ ε` loop, or a decomposition only T-B.4 could
//! align); those cases are counted and skipped, and the run still verifies well
//! over 1000 fully-decided cases.

mod common;

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::{Classes, Declined, NormalForm};
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

/// The shared term pool: seq variables plus a batch of random concat terms.
struct Pool {
    seq_vars: Vec<(SymbolId, TermId)>,
    /// Every candidate term (variables and concats) equalities may relate.
    terms: Vec<TermId>,
}

impl Pool {
    fn new(arena: &mut TermArena, rng: &mut Lcg) -> Self {
        let seq_vars: Vec<(SymbolId, TermId)> = (0..4)
            .map(|i| {
                let s = arena
                    .declare(&format!("s{i}"), seq_sort())
                    .expect("declare seq var");
                (s, arena.var(s))
            })
            .collect();
        // A couple of constant single-char sequences to exercise fusion.
        let chars: Vec<TermId> = [b'a', b'b']
            .iter()
            .map(|&c| {
                let ce = arena.bv_const(8, u128::from(c)).expect("char const");
                unit(arena, ce)
            })
            .collect();

        let mut terms: Vec<TermId> = seq_vars.iter().map(|&(_, t)| t).collect();
        terms.extend_from_slice(&chars);
        // Grow with random concatenations of existing terms.
        for _ in 0..6 {
            let a = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            let b = terms[usize::try_from(rng.below(terms.len() as u64)).expect("fits")];
            terms.push(cat(arena, a, b));
        }
        Self { seq_vars, terms }
    }
}

/// Binds every sequence variable to a random short `Bv(8)` sequence.
fn gen_assignment(rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    for &(s, _) in &pool.seq_vars {
        let len = rng.below(3); // 0..2 characters
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: u128::from(b'a') + u128::from(rng.below(2)), // 'a' or 'b'
            })
            .collect();
        asg.set(s, Value::Seq(elems));
    }
    asg
}

/// The model-consistent equality set: every pool pair that evaluates equal
/// under `asg` is included with probability ~1/2, so classes are non-trivial
/// yet always sound.
fn consistent_equalities(
    arena: &TermArena,
    pool: &Pool,
    asg: &Assignment,
    rng: &mut Lcg,
) -> Vec<(TermId, TermId)> {
    let vals: Vec<Value> = pool
        .terms
        .iter()
        .map(|&t| eval(arena, t, asg).expect("closed pool term"))
        .collect();
    let mut eqs = Vec::new();
    for i in 0..pool.terms.len() {
        for j in (i + 1)..pool.terms.len() {
            if vals[i] == vals[j] && rng.coin() {
                eqs.push((pool.terms[i], pool.terms[j]));
            }
        }
    }
    eqs
}

/// Right-associated concatenation of `components` (ε when empty), evaluated
/// under `asg`.
fn eval_components(arena: &mut TermArena, components: &[TermId], asg: &Assignment) -> Value {
    if components.is_empty() {
        return Value::Seq(Vec::new());
    }
    let mut acc = *components.last().expect("non-empty");
    for &p in components[..components.len() - 1].iter().rev() {
        acc = cat(arena, p, acc);
    }
    eval(arena, acc, asg).expect("eval component concat")
}

/// Terminal-vector equality: identical handles, or both closed constants of
/// equal value.
fn terminal_vectors_equal(arena: &TermArena, a: &[TermId], b: &[TermId]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b).all(|(&x, &y)| {
        x == y
            || matches!(
                (
                    eval(arena, x, &Assignment::new()),
                    eval(arena, y, &Assignment::new())
                ),
                (Ok(vx), Ok(vy)) if vx == vy
            )
    })
}

#[test]
fn normal_forms_are_sound_and_explanations_sufficient() {
    let mut rng = Lcg(0xDEAD_BEEF_1234_5678);

    let mut verified_classes = 0u64;
    let mut decided_iters = 0u64;
    let mut declined_iters = 0u64;

    for _ in 0..4000 {
        let mut arena = TermArena::new();
        let pool = Pool::new(&mut arena, &mut rng);
        let asg = gen_assignment(&mut rng, &pool);
        let eqs = consistent_equalities(&arena, &pool, &asg, &mut rng);

        let classes = Classes::new(&eqs);

        // (1) Class soundness — always holds, decline or not.
        for &(a, _) in &eqs {
            let rep = classes.representative(a);
            let rep_val = eval(&arena, rep, &asg).expect("eval rep");
            for m in classes.class_members(a) {
                let mv = eval(&arena, m, &asg).expect("eval member");
                assert_eq!(mv, rep_val, "class member disagrees with representative");
            }
        }

        let forms = match classes.normal_forms(&mut arena) {
            Ok(f) => f,
            Err(Declined::Cycle { .. } | Declined::Unreconciled { .. }) => {
                declined_iters += 1;
                continue;
            }
        };
        decided_iters += 1;

        // Collect the (rep, nf) pairs up front (nf borrows would collide with
        // the &mut arena needed to build concat terms).
        let snapshot: Vec<(TermId, NormalForm)> =
            forms.iter().map(|(r, nf)| (r, nf.clone())).collect();

        for (rep, nf) in &snapshot {
            // (2) Normal-form soundness.
            let rep_val = eval(&arena, *rep, &asg).expect("eval rep");
            let nf_val = eval_components(&mut arena, &nf.components, &asg);
            assert_eq!(
                nf_val, rep_val,
                "normal form does not denote its class representative"
            );

            // (3) Explanation sufficiency: recompute from the cited premises
            // only and re-derive the same vector.
            let mut sub: Vec<(TermId, TermId)> = nf
                .premises
                .iter()
                .map(|&i| eqs[i])
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            // A reflexive pair (no connectivity effect) guarantees `base` is a
            // seeded endpoint, so its class is recomputed even when the cited
            // premise set is empty (a concat-representative class decomposes by
            // pure normalization).
            sub.push((nf.base, nf.base));
            let sub_classes = Classes::new(&sub);
            let sub_forms = sub_classes
                .normal_forms(&mut arena)
                .expect("a subset of a decided, consistent set stays decidable");
            let sub_rep = sub_classes.representative(nf.base);
            let sub_nf = sub_forms
                .get(sub_rep)
                .expect("base's class recomputed under its own premises");
            assert!(
                terminal_vectors_equal(&arena, &nf.components, &sub_nf.components),
                "cited premises are not sufficient to re-derive the normal form"
            );

            verified_classes += 1;
        }
    }

    assert!(
        decided_iters >= 1000,
        "property test must fully decide at least 1000 cases (did {decided_iters}, declined {declined_iters})"
    );
    assert!(
        verified_classes >= 1000,
        "expected at least 1000 verified classes (did {verified_classes})"
    );
}
