//! **Dedicated adversarial denotation-preservation fuzz for T-B.1 `normalize`.**
//!
//! `normalize` is the one primitive the otherwise-independent T-B.7 derivation
//! re-checker ([`check_conflict`](axeyum_strings::check_conflict) /
//! [`check_fact`](axeyum_strings::check_fact)) *shares* with the untrusted
//! inference engine (`check_derivation` calls
//! [`normalize`](axeyum_strings::normalize) to recover each member's component
//! vector). A `normalize` that silently changed a term's denotation would be
//! invisible to the checker — a corrupted derivation could ride an unsound
//! rewrite straight past the "trusted small check". This suite is the guard on
//! that trust hole: on tens of thousands of adversarially-shaped `Seq` terms and
//! random assignments it asserts, for **every** case,
//!
//! * **denotation preservation** — `eval(t) == eval(normalize(t))` under the same
//!   assignment, for `Seq`, `Int` (`str.len` under arithmetic), and `Bool`
//!   (equalities / length comparisons over `Seq` subterms) roots;
//! * **the structural normal-form invariant** on every `str.++` subterm of the
//!   result ([`assert_normal_form`]); and
//! * **idempotence** — `normalize(normalize(t))` interns to `normalize(t)`.
//!
//! On any failure it dumps the offending term tree (a shrink-free but fully
//! diagnosable print) before panicking, so a future red is actionable.
//!
//! # Why a *separate* suite from `property.rs`
//!
//! `property.rs` is the trust anchor but deliberately shallow: fixed depth 3,
//! balanced binary concats, three char constants, and a single `+ bias` on top of
//! `str.len`. This generator is aimed squarely at the edges that leaves
//! under-covered:
//!
//! * **deep, unbalanced nesting** — up to depth 8, folded **left**-nested as often
//!   as right-nested (property only builds balanced trees), to stress the flatten
//!   rule's re-association across long spines;
//! * **ε in every position** — ε is injected as the left operand, the right
//!   operand, both operands, and sprinkled between spine components, not merely
//!   sampled as an occasional leaf;
//! * **long constant runs** — explicit runs of 2..8 adjacent constant units (same
//!   char and mixed chars), the fusion rule's stress case, which a depth-3 tree
//!   almost never produces;
//! * **unit-of-variable** alongside unit-of-constant, so fusion boundaries fall
//!   next to opaque cells;
//! * **`str.len` under real arithmetic** — nested `+`/`-`/`*` mixing several
//!   `str.len` terms and constants (property does only a single `+ bias`), driving
//!   rule 4's push through arbitrary `Int` structure;
//! * **mixed sorts wrapped around `Seq` subterms** — `Bool` equalities between two
//!   sequences, `Int` `<`/`≤` between length terms, `and`/`not`, and `ite`
//!   selecting between sequences, so normalization is reached through non-`Seq`
//!   structure and its denotation checked there;
//! * **empty / singleton edge shapes** — bare ε, a lone unit, ε-only concats.
//!
//! Randomness is the repo's house LCG (`wrapping_mul(6364136223846793005)`), no
//! external dependency.

#![allow(clippy::many_single_char_names)]

mod common;

use axeyum_ir::{Assignment, IrError, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_strings::normalize;
use common::{assert_normal_form, seq_sort};

/// Deterministic linear-congruential generator (the repo's house constants).
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

    /// A `u32` value in `0..n` (n > 0). Kept as its own helper so callers never
    /// need a truncating `as` cast (the pedantic lint set forbids those).
    fn below_u32(&mut self, n: u32) -> u32 {
        u32::try_from(self.below(u64::from(n))).expect("value < n fits u32")
    }

    fn coin(&mut self) -> bool {
        self.below(2) == 0
    }

    /// A uniformly-chosen element of a non-empty slice.
    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        let bits = usize::try_from(self.next_u64() >> 33).expect("31-bit index fits usize");
        items[bits % items.len()]
    }
}

/// The fixed variable / constant pool shared by every generated term, so one
/// assignment interprets any of them.
struct Pool {
    seq_vars: Vec<(SymbolId, TermId)>,
    elem_vars: Vec<(SymbolId, TermId)>,
    /// Distinct 8-bit "characters" — enough distinct values that fused constant
    /// blocks are genuinely different sequences.
    chars: Vec<TermId>,
    /// The distinct char *values*, parallel to `chars`.
    char_vals: Vec<u128>,
}

impl Pool {
    fn new(arena: &mut TermArena) -> Self {
        let seq_vars = (0..5)
            .map(|i| {
                let sid = arena
                    .declare(&format!("s{i}"), seq_sort())
                    .expect("declare seq var");
                (sid, arena.var(sid))
            })
            .collect();
        let elem_vars = (0..4)
            .map(|i| {
                let sid = arena
                    .declare(&format!("e{i}"), Sort::BitVec(8))
                    .expect("declare elem var");
                (sid, arena.var(sid))
            })
            .collect();
        let char_vals: Vec<u128> = vec![0, 1, 2, 7, u128::from(b'a'), u128::from(b'b')];
        let chars = char_vals
            .iter()
            .map(|&v| arena.bv_const(8, v).expect("char const"))
            .collect();
        Self {
            seq_vars,
            elem_vars,
            chars,
            char_vals,
        }
    }
}

// ----- Seq generation ---------------------------------------------------------

/// A single constant unit `seq.unit(c)` for a randomly-chosen char constant.
fn const_unit(arena: &mut TermArena, rng: &mut Lcg, pool: &Pool) -> TermId {
    let c = rng.pick(&pool.chars);
    arena.seq_unit(c).expect("unit of const char")
}

/// A single variable unit `seq.unit(e)` for a randomly-chosen element variable.
fn var_unit(arena: &mut TermArena, rng: &mut Lcg, pool: &Pool) -> TermId {
    let e = rng.pick(&pool.elem_vars).1;
    arena.seq_unit(e).expect("unit of var elem")
}

/// A **long constant run**: `k` (2..=8) adjacent constant units, folded left- or
/// right-nested. This is the fusion rule's stress case — a depth-3 balanced tree
/// almost never produces a run this long.
fn constant_run(arena: &mut TermArena, rng: &mut Lcg, pool: &Pool) -> TermId {
    let k = 2 + rng.below(7); // 2..=8
    // Half the runs are a single repeated char, half are mixed chars.
    let single = rng.coin();
    let fixed = rng.pick(&pool.chars);
    let units: Vec<TermId> = (0..k)
        .map(|_| {
            if single {
                arena.seq_unit(fixed).expect("unit")
            } else {
                const_unit(arena, rng, pool)
            }
        })
        .collect();
    fold_concat(arena, rng, &units)
}

/// Folds a non-empty slice of components into a concatenation, choosing left- or
/// right-nesting at random (property.rs only ever builds balanced trees, so the
/// deep left-nested spines here are new coverage for the flatten rule).
fn fold_concat(arena: &mut TermArena, rng: &mut Lcg, parts: &[TermId]) -> TermId {
    assert!(!parts.is_empty(), "fold_concat on empty slice");
    if rng.coin() {
        // Left-nested: ((p0 ++ p1) ++ p2) ...
        let mut acc = parts[0];
        for &p in &parts[1..] {
            acc = arena.seq_concat(acc, p).expect("concat");
        }
        acc
    } else {
        // Right-nested: p0 ++ (p1 ++ (p2 ...))
        let mut acc = *parts.last().expect("non-empty");
        for &p in parts[..parts.len() - 1].iter().rev() {
            acc = arena.seq_concat(p, acc).expect("concat");
        }
        acc
    }
}

/// Generates an adversarial `Seq(BitVec 8)` term with the given depth budget.
///
/// `budget` is a **shared node budget** decremented once per internal node across
/// the whole term (all recursive calls share the same counter). It bounds total
/// term size so wide spines at deep `depth` cannot blow up exponentially — deep
/// *linear* shapes (left-nested spines, single-child ε chains, constant runs) are
/// preserved, only unbounded fan-out is curbed.
fn gen_seq(
    arena: &mut TermArena,
    rng: &mut Lcg,
    pool: &Pool,
    depth: u32,
    budget: &mut u32,
) -> TermId {
    if depth == 0 || *budget == 0 {
        return gen_seq_leaf(arena, rng, pool);
    }
    *budget -= 1;
    match rng.below(8) {
        // A leaf even with budget left (keeps some subtrees shallow / singleton).
        0 => gen_seq_leaf(arena, rng, pool),
        // A long constant run (fusion stress).
        1 => constant_run(arena, rng, pool),
        // ε injected into a concat: cover every operand position.
        2 => {
            let e = arena.seq_empty(common::ELEM);
            let sub = gen_seq(arena, rng, pool, depth - 1, budget);
            match rng.below(3) {
                0 => arena.seq_concat(e, sub).expect("ε ++ sub"),
                1 => arena.seq_concat(sub, e).expect("sub ++ ε"),
                _ => {
                    let e2 = arena.seq_empty(common::ELEM);
                    arena.seq_concat(e, e2).expect("ε ++ ε")
                }
            }
        }
        // A spine of 2..=5 components, ε sprinkled between them, random assoc.
        3 | 4 => {
            let n = 2 + rng.below(4); // 2..=5 components
            let mut parts = Vec::new();
            for _ in 0..n {
                if rng.below(3) == 0 {
                    parts.push(arena.seq_empty(common::ELEM)); // ε between components
                }
                parts.push(gen_seq(arena, rng, pool, depth - 1, budget));
            }
            if rng.coin() {
                parts.push(arena.seq_empty(common::ELEM)); // trailing ε
            }
            fold_concat(arena, rng, &parts)
        }
        // A plain binary concat of two recursive subterms.
        _ => {
            let a = gen_seq(arena, rng, pool, depth - 1, budget);
            let b = gen_seq(arena, rng, pool, depth - 1, budget);
            arena.seq_concat(a, b).expect("concat")
        }
    }
}

/// A `Seq` leaf: ε, constant unit, variable unit, a bare sequence variable, or a
/// short constant run — ε and constant shapes are weighted up relative to
/// property.rs.
fn gen_seq_leaf(arena: &mut TermArena, rng: &mut Lcg, pool: &Pool) -> TermId {
    match rng.below(6) {
        0 | 1 => arena.seq_empty(common::ELEM),
        2 => const_unit(arena, rng, pool),
        3 => var_unit(arena, rng, pool),
        4 => rng.pick(&pool.seq_vars).1,
        _ => constant_run(arena, rng, pool),
    }
}

// ----- Int generation (str.len under real arithmetic) -------------------------

/// Generates an `Int` term mixing `str.len` of adversarial sequences with nested
/// `+`/`-`/`*` and small constants — rule 4's push through arbitrary arithmetic.
/// Magnitudes stay tiny (small constants, shallow trees, sequences ≤ a few dozen
/// elements) so the ground evaluator never overflows.
fn gen_int(
    arena: &mut TermArena,
    rng: &mut Lcg,
    pool: &Pool,
    depth: u32,
    budget: &mut u32,
) -> TermId {
    if depth == 0 || *budget == 0 {
        return if rng.below(2) == 0 {
            arena.int_const(i128::from(rng.below(5)))
        } else {
            let d = 2 + rng.below_u32(4);
            let s = gen_seq(arena, rng, pool, d, budget);
            arena.seq_len(s).expect("str.len")
        };
    }
    *budget -= 1;
    let a = gen_int(arena, rng, pool, depth - 1, budget);
    let b = gen_int(arena, rng, pool, depth - 1, budget);
    match rng.below(3) {
        0 => arena.int_add(a, b).expect("int add"),
        1 => arena.int_sub(a, b).expect("int sub"),
        _ => arena.int_mul(a, b).expect("int mul"),
    }
}

// ----- Bool generation (Seq subterms behind non-Seq structure) ----------------

/// Generates a `Bool` term wrapping `Seq` subterms: sequence equalities, length
/// comparisons, `ite` selecting sequences, and `and`/`not` combinators.
fn gen_bool(
    arena: &mut TermArena,
    rng: &mut Lcg,
    pool: &Pool,
    depth: u32,
    budget: &mut u32,
) -> TermId {
    if depth == 0 || *budget == 0 {
        return match rng.below(3) {
            0 => {
                let (da, db) = (2 + rng.below_u32(4), 2 + rng.below_u32(4));
                let a = gen_seq(arena, rng, pool, da, budget);
                let b = gen_seq(arena, rng, pool, db, budget);
                arena.eq(a, b).expect("seq eq")
            }
            1 => {
                let (da, db) = (1 + rng.below_u32(2), 1 + rng.below_u32(2));
                let a = gen_int(arena, rng, pool, da, budget);
                let b = gen_int(arena, rng, pool, db, budget);
                arena.int_le(a, b).expect("int le")
            }
            _ => {
                let (da, db) = (1 + rng.below_u32(2), 1 + rng.below_u32(2));
                let a = gen_int(arena, rng, pool, da, budget);
                let b = gen_int(arena, rng, pool, db, budget);
                arena.int_lt(a, b).expect("int lt")
            }
        };
    }
    *budget -= 1;
    match rng.below(4) {
        0 => {
            let a = gen_bool(arena, rng, pool, depth - 1, budget);
            let b = gen_bool(arena, rng, pool, depth - 1, budget);
            arena.and(a, b).expect("and")
        }
        1 => {
            let a = gen_bool(arena, rng, pool, depth - 1, budget);
            arena.not(a).expect("not")
        }
        // ite over two sequences, compared for equality — a Seq subterm reached
        // through a Bool-selecting `ite`.
        2 => {
            let c = gen_bool(arena, rng, pool, depth - 1, budget);
            let (dt, de, do_) = (
                2 + rng.below_u32(3),
                2 + rng.below_u32(3),
                2 + rng.below_u32(3),
            );
            let t = gen_seq(arena, rng, pool, dt, budget);
            let e = gen_seq(arena, rng, pool, de, budget);
            let chosen = arena.ite(c, t, e).expect("ite seq");
            let other = gen_seq(arena, rng, pool, do_, budget);
            arena.eq(chosen, other).expect("eq of ite-seq")
        }
        _ => {
            let (da, db) = (2 + rng.below_u32(4), 2 + rng.below_u32(4));
            let a = gen_seq(arena, rng, pool, da, budget);
            let b = gen_seq(arena, rng, pool, db, budget);
            arena.eq(a, b).expect("seq eq")
        }
    }
}

// ----- assignment -------------------------------------------------------------

/// A random assignment binding every pool variable (sequences to random small
/// `Bv(8)` sequences, elements to random `Bv(8)`s).
fn gen_assignment(rng: &mut Lcg, pool: &Pool) -> Assignment {
    let mut asg = Assignment::new();
    for (sid, _) in &pool.seq_vars {
        let len = rng.below(5); // 0..=4 characters — includes the empty edge
        let elems = (0..len)
            .map(|_| Value::Bv {
                width: 8,
                value: rng.pick(&pool.char_vals),
            })
            .collect();
        asg.set(*sid, Value::Seq(elems));
    }
    for (sid, _) in &pool.elem_vars {
        asg.set(
            *sid,
            Value::Bv {
                width: 8,
                value: rng.pick(&pool.char_vals),
            },
        );
    }
    asg
}

// ----- term dump (diagnosable failure) ----------------------------------------

/// A recursive, indented dump of a term tree — printed before a panic so a future
/// red is diagnosable without a debugger.
fn dump_term(arena: &TermArena, t: TermId, indent: usize, out: &mut String) {
    use std::fmt::Write;
    let pad = "  ".repeat(indent);
    match arena.node(t) {
        TermNode::App { op, args } => {
            let _ = writeln!(out, "{pad}{op:?}  [{t:?}]");
            let kids: Vec<TermId> = args.to_vec();
            for k in kids {
                dump_term(arena, k, indent + 1, out);
            }
        }
        leaf => {
            let _ = writeln!(out, "{pad}{leaf:?}  [{t:?}]");
        }
    }
}

/// Builds the failure report: the original tree, the normalized tree, and the
/// two evaluations.
fn report(
    arena: &TermArena,
    label: &str,
    orig: TermId,
    norm: TermId,
    before: &Result<Value, IrError>,
    after: &Result<Value, IrError>,
    asg: &Assignment,
) -> String {
    use std::fmt::Write;
    let mut s = format!("\n=== normalize denotation FUZZ FAILURE ({label}) ===\n");
    let _ = writeln!(s, "assignment: {asg:?}");
    let _ = writeln!(s, "eval(original)   = {before:?}");
    let _ = writeln!(s, "eval(normalized) = {after:?}");
    s.push_str("--- ORIGINAL term tree ---\n");
    dump_term(arena, orig, 0, &mut s);
    s.push_str("--- NORMALIZED term tree ---\n");
    dump_term(arena, norm, 0, &mut s);
    s
}

// ----- the fuzz ---------------------------------------------------------------

/// Runs one case: normalize `orig`, then assert denotation preservation, the
/// structural invariant, and idempotence — dumping the trees on any failure.
fn check_case(arena: &mut TermArena, label: &str, orig: TermId, asg: &Assignment) {
    let before = eval(arena, orig, asg);
    let norm = normalize(arena, orig);
    let after = eval(arena, norm, asg);

    // Denotation preservation. We keep magnitudes tiny so `eval` never errors;
    // treat a before/after Result mismatch (or any Err) as a failure to surface.
    let ok = match (&before, &after) {
        (Ok(vb), Ok(va)) => vb == va,
        _ => false,
    };
    assert!(
        ok,
        "{}",
        report(arena, label, orig, norm, &before, &after, asg)
    );

    // Structural normal-form invariant on every str.++ subterm of the result.
    assert_normal_form(arena, norm);

    // Idempotence: normalize(normalize(t)) interns to normalize(t).
    let norm2 = normalize(arena, norm);
    assert!(norm == norm2, "normalize not idempotent ({label}):\n{}", {
        let mut s = String::new();
        s.push_str("--- normalize once ---\n");
        dump_term(arena, norm, 0, &mut s);
        s.push_str("--- normalize twice ---\n");
        dump_term(arena, norm2, 0, &mut s);
        s
    });
}

#[test]
fn normalize_denotation_adversarial_fuzz() {
    let mut arena = TermArena::new();
    let pool = Pool::new(&mut arena);
    // A different seed from property.rs so the two suites explore disjoint streams.
    let mut rng = Lcg(0xD1B5_4A32_D192_ED03);

    let iterations = 24_000usize;
    let mut pairs = 0u64;

    for _ in 0..iterations {
        let asg = gen_assignment(&mut rng, &pool);
        // Depth 0..=8 (property.rs is fixed depth 3); most are moderate, a healthy
        // tail reaches the full depth-8 budget.
        let depth = rng.below_u32(9);

        // A generous per-term node budget: enough for a full depth-8 term of
        // ordinary width, but a hard cap that keeps wide spines from blowing up.
        let mut budget = 160u32;

        match rng.below(3) {
            // Seq root — the primary denotation + invariant + idempotence case.
            0 => {
                let t = gen_seq(&mut arena, &mut rng, &pool, depth, &mut budget);
                check_case(&mut arena, "seq", t, &asg);
            }
            // Int root — str.len pushed through nested arithmetic.
            1 => {
                let d = 1 + (depth % 4); // 1..=4 arithmetic depth
                let t = gen_int(&mut arena, &mut rng, &pool, d, &mut budget);
                check_case(&mut arena, "int/len", t, &asg);
            }
            // Bool root — Seq subterms behind eq / comparisons / ite.
            _ => {
                let d = 1 + (depth % 4);
                let t = gen_bool(&mut arena, &mut rng, &pool, d, &mut budget);
                check_case(&mut arena, "bool", t, &asg);
            }
        }
        pairs += 1;
    }

    assert!(
        pairs >= 20_000,
        "fuzz must exercise at least 20,000 term/assignment pairs (did {pairs})"
    );
}

/// A focused battery of hand-built edge shapes that the random stream hits only
/// rarely — bare ε, a lone unit, ε-only concats, a maximal constant run, and a
/// deep left-nested spine — each asserted under a spread of assignments.
#[test]
fn normalize_denotation_edge_shapes() {
    let mut arena = TermArena::new();
    let pool = Pool::new(&mut arena);
    let mut rng = Lcg(0x0BAD_F00D_1234_5678);

    // Deterministic edge terms.
    let e = arena.seq_empty(common::ELEM);
    let eps_only = arena.seq_concat(e, e).expect("ε ++ ε");
    let lone = const_unit(&mut arena, &mut rng, &pool);
    let var_lone = rng.pick(&pool.seq_vars).1;
    let big_run = {
        // A run longer than any depth-8 tree is likely to produce.
        let units: Vec<TermId> = (0..12)
            .map(|_| const_unit(&mut arena, &mut rng, &pool))
            .collect();
        fold_concat(&mut arena, &mut rng, &units)
    };
    let deep_left = {
        // ((((s0 ++ ε) ++ s1) ++ ε) ++ s2) ... left-nested with ε interleaved.
        let mut acc = rng.pick(&pool.seq_vars).1;
        for _ in 0..10 {
            let e = arena.seq_empty(common::ELEM);
            acc = arena.seq_concat(acc, e).expect("++ ε");
            let v = rng.pick(&pool.seq_vars).1;
            acc = arena.seq_concat(acc, v).expect("++ v");
        }
        acc
    };
    let len_of_run = arena.seq_len(big_run).expect("len of run");

    let edges = [
        ("bare-ε", e),
        ("ε-only-concat", eps_only),
        ("lone-const-unit", lone),
        ("lone-var", var_lone),
        ("12-const-run", big_run),
        ("deep-left-ε-spine", deep_left),
        ("len-of-run", len_of_run),
    ];

    for _ in 0..50 {
        let asg = gen_assignment(&mut rng, &pool);
        for (label, t) in edges {
            check_case(&mut arena, label, t, &asg);
        }
    }
}
