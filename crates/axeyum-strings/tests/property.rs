//! The trust anchor for T-B.1: random `Seq`-sorted terms under random
//! assignments must evaluate identically before and after normalization, the
//! rewrite must be idempotent, and the output must satisfy the structural
//! normal-form invariant.
//!
//! Randomness is a deterministic hand-rolled LCG (the house pattern:
//! `wrapping_mul(6364136223846793005)`) — no external dependency.

mod common;

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_strings::normalize;
use common::{assert_normal_form, seq_sort};

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

    /// A value in `0..n` (n > 0), taken from the high bits for better spread.
    fn below(&mut self, n: u64) -> u64 {
        (self.next_u64() >> 33) % n
    }

    /// A uniformly-chosen element of a non-empty slice.
    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        let bits = usize::try_from(self.next_u64() >> 33).expect("31-bit index fits usize");
        items[bits % items.len()]
    }
}

/// The variable pool shared by every generated term (so a single assignment
/// interprets any of them).
struct Pool {
    seq_vars: Vec<(SymbolId, TermId)>,
    elem_vars: Vec<(SymbolId, TermId)>,
    chars: Vec<TermId>,
}

impl Pool {
    fn new(arena: &mut TermArena) -> Self {
        let seq_vars = (0..3)
            .map(|i| {
                let sid = arena
                    .declare(&format!("s{i}"), seq_sort())
                    .expect("declare seq var");
                (sid, arena.var(sid))
            })
            .collect();
        let elem_vars = (0..3)
            .map(|i| {
                let sid = arena
                    .declare(&format!("e{i}"), Sort::BitVec(8))
                    .expect("declare elem var");
                (sid, arena.var(sid))
            })
            .collect();
        let chars = (0..3u128)
            .map(|v| arena.bv_const(8, v).expect("char const"))
            .collect();
        Self {
            seq_vars,
            elem_vars,
            chars,
        }
    }
}

/// Generates a random `Seq(BitVec 8)` term of the given depth budget.
fn gen_seq(arena: &mut TermArena, rng: &mut Lcg, pool: &Pool, depth: u32) -> TermId {
    // At depth 0 (or ~1/3 of the time) emit a leaf; otherwise a concatenation.
    if depth == 0 || rng.below(3) == 0 {
        match rng.below(4) {
            0 => arena.seq_empty(common::ELEM),
            1 => {
                let c = rng.pick(&pool.chars);
                arena.seq_unit(c).expect("unit of const char")
            }
            2 => {
                let e = rng.pick(&pool.elem_vars).1;
                arena.seq_unit(e).expect("unit of var elem")
            }
            _ => rng.pick(&pool.seq_vars).1,
        }
    } else {
        let a = gen_seq(arena, rng, pool, depth - 1);
        let b = gen_seq(arena, rng, pool, depth - 1);
        arena.seq_concat(a, b).expect("concat")
    }
}

/// A random assignment binding every pool variable (sequences to random small
/// `Bv(8)` sequences, elements to random `Bv(8)`s).
fn gen_assignment(rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    for (sid, _) in &pool.seq_vars {
        let len = rng.below(4); // 0..3 characters
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: u128::from(rng.below(4)),
            })
            .collect();
        asg.set(*sid, Value::Seq(elems));
    }
    for (sid, _) in &pool.elem_vars {
        asg.set(
            *sid,
            Value::Bv {
                width: 8,
                value: u128::from(rng.below(4)),
            },
        );
    }
    asg
}

#[test]
fn normalize_preserves_denotation_and_invariant() {
    let mut arena = TermArena::new();
    let pool = Pool::new(&mut arena);
    let mut rng = Lcg(0x9E37_79B9_7F4A_7C15);

    let iterations = 2400;
    let mut compared = 0u64;

    for _ in 0..iterations {
        let asg = gen_assignment(&mut rng, &pool);
        let t = gen_seq(&mut arena, &mut rng, &pool, 3);

        // (1) The sequence term itself: denotation preserved.
        let seq_norm = normalize(&mut arena, t);
        let seq_before = eval(&arena, t, &asg).expect("eval original seq term");
        let seq_after = eval(&arena, seq_norm, &asg).expect("eval normalized seq term");
        assert_eq!(
            seq_before, seq_after,
            "normalization changed the sequence denotation"
        );
        assert_normal_form(&arena, seq_norm);
        // Idempotence: interned equality.
        let seq_norm_again = normalize(&mut arena, seq_norm);
        assert_eq!(
            seq_norm, seq_norm_again,
            "normalize is not idempotent on a sequence term"
        );
        compared += 1;

        // (2) A length term under arithmetic: exercises rule 4's push.
        let len = arena.seq_len(t).expect("str.len");
        let bias = i128::from(rng.below(5));
        let bias_term = arena.int_const(bias);
        let sum = arena.int_add(len, bias_term).expect("int add");

        let len_norm = normalize(&mut arena, sum);
        let len_before = eval(&arena, sum, &asg).expect("eval original len term");
        let len_after = eval(&arena, len_norm, &asg).expect("eval normalized len term");
        assert_eq!(
            len_before, len_after,
            "normalization changed the length denotation"
        );
        let len_norm_again = normalize(&mut arena, len_norm);
        assert_eq!(
            len_norm, len_norm_again,
            "normalize is not idempotent on a length term"
        );
        compared += 1;
    }

    assert!(
        compared >= 2000,
        "property test must compare at least 2000 term/assignment pairs (did {compared})"
    );
}
