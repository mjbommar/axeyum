//! A wide randomized hunt for a rewrite rule that fires outside its
//! precondition.
//!
//! The unit suite drives each default rule on one focused example. That proves
//! each rule *can* fire correctly; it does not probe the shapes where a
//! precondition is most likely to be wrong — operand widths at their
//! boundaries, degenerate divisors, extracts that straddle a `concat` or an
//! extension seam, and deep nestings where one rule's output becomes another
//! rule's input.
//!
//! Two independent judges run on every generated term:
//!
//! 1. the **precondition guard** inside the canonicalizer, which refuses any
//!    rule that leaves its declared operator scope or changes denotation on its
//!    own 4 fixed samples; and
//! 2. this file's **replay**, which evaluates the original and the canonical
//!    term against many more assignments than the guard samples, using the
//!    `axeyum-ir` ground evaluator directly.
//!
//! The second judge exists because the first one samples sparsely on purpose
//! (it runs on the default path and must stay linear). A defect that hides from
//! 4 samples but not from 40 is exactly the kind this file is here to find.
//!
//! Per the repository's hard rule on partial operators, the generator
//! **deliberately emits the degenerate arguments**: constant-zero divisors for
//! `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod` and for integer `div`/`mod`,
//! shift amounts at and beyond the operand width, rotates by a full width, and
//! extends by zero bits. A generator that only ever produced *variable* divisors
//! is how the `a946f925` wrong-`unsat` survived its differential gate.

use std::cmp::Ordering;

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_rewrite::{Canonicalizer, PreconditionPolicy, default_manifest};

const BV_WIDTH: u32 = 4;
const WIDE_WIDTH: u32 = 8;

struct Leaves {
    bv: Vec<TermId>,
    wide: Vec<TermId>,
    bools: Vec<TermId>,
    ints: Vec<TermId>,
    bv_syms: Vec<SymbolId>,
    wide_syms: Vec<SymbolId>,
    bool_syms: Vec<SymbolId>,
    int_syms: Vec<SymbolId>,
}

fn splitmix(seed: u64) -> u64 {
    let mut x = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// Derives an independent child seed. A salt keeps sibling subterms from
/// collapsing to the same shape, which would narrow the sweep silently.
fn mix(seed: u64, salt: u64) -> u64 {
    splitmix(seed.wrapping_add(salt.wrapping_mul(0x9e37_79b9_7f4a_7c15)))
}

fn build_leaves(arena: &mut TermArena) -> Leaves {
    let mut bv_syms = Vec::new();
    let mut bv = Vec::new();
    for name in ["fz_x", "fz_y", "fz_z"] {
        let sym = arena.declare(name, Sort::BitVec(BV_WIDTH)).unwrap();
        bv_syms.push(sym);
        bv.push(arena.var(sym));
    }
    // Constants that sit exactly on the rules' corners: zero and all-ones drive
    // the identity/annihilator/saturation rules, one drives `bvmul` identity,
    // and the powers of two drive the strength-reduction rules.
    for value in [0u128, 1, 2, 4, 8, 15] {
        bv.push(arena.bv_const(BV_WIDTH, value).unwrap());
    }

    let mut wide_syms = Vec::new();
    let mut wide = Vec::new();
    for name in ["fz_a", "fz_b"] {
        let sym = arena.declare(name, Sort::BitVec(WIDE_WIDTH)).unwrap();
        wide_syms.push(sym);
        wide.push(arena.var(sym));
    }
    for value in [0u128, 1, 8, 128, 255] {
        wide.push(arena.bv_const(WIDE_WIDTH, value).unwrap());
    }

    let mut bool_syms = Vec::new();
    let mut bools = Vec::new();
    for name in ["fz_p", "fz_q"] {
        let sym = arena.declare(name, Sort::Bool).unwrap();
        bool_syms.push(sym);
        bools.push(arena.var(sym));
    }
    bools.push(arena.bool_const(true));
    bools.push(arena.bool_const(false));

    let mut int_syms = Vec::new();
    let mut ints = Vec::new();
    for name in ["fz_i", "fz_j"] {
        let sym = arena.declare(name, Sort::Int).unwrap();
        int_syms.push(sym);
        ints.push(arena.var(sym));
    }
    // A literal ZERO among the integer leaves is mandatory, not incidental: it
    // is what lets the generator produce `(div t 0)` and `(mod t 0)`.
    for value in [0i128, 1, -1, 2, 7] {
        ints.push(arena.int_const(value));
    }

    Leaves {
        bv,
        wide,
        bools,
        ints,
        bv_syms,
        wide_syms,
        bool_syms,
        int_syms,
    }
}

/// Rotation amounts include 0 and a full width, both of which are rule corners.
fn rotate_amount(seed: u64) -> u32 {
    u32::try_from((seed >> 8) % u64::from(BV_WIDTH + 1)).expect("modulus bounds this by BV_WIDTH")
}

fn pick(items: &[TermId], seed: u64) -> TermId {
    let len = u64::try_from(items.len()).expect("leaf lists are small");
    items[usize::try_from(seed % len).expect("index is below the list length")]
}

#[allow(clippy::too_many_lines)]
fn build_bv(arena: &mut TermArena, seed: u64, depth: u8, leaves: &Leaves) -> TermId {
    if depth == 0 {
        return pick(&leaves.bv, seed);
    }
    let lhs = build_bv(arena, mix(seed, 1), depth - 1, leaves);
    let rhs = build_bv(arena, mix(seed, 2), depth - 1, leaves);
    let cond = build_bool(arena, mix(seed, 3), depth - 1, leaves);
    let wide = build_wide(arena, mix(seed, 4), depth - 1, leaves);

    match seed % 30 {
        0 => arena.bv_add(lhs, rhs),
        1 => arena.bv_sub(lhs, rhs),
        2 => arena.bv_mul(lhs, rhs),
        3 => arena.bv_and(lhs, rhs),
        4 => arena.bv_or(lhs, rhs),
        5 => arena.bv_xor(lhs, rhs),
        6 => arena.bv_nand(lhs, rhs),
        7 => arena.bv_nor(lhs, rhs),
        8 => arena.bv_xnor(lhs, rhs),
        9 => arena.bv_not(lhs),
        10 => arena.bv_neg(lhs),
        // Divisors here are whatever the generator produced, INCLUDING the
        // constant zero that sits in `leaves.bv`.
        11 => arena.bv_udiv(lhs, rhs),
        12 => arena.bv_urem(lhs, rhs),
        13 => arena.bv_sdiv(lhs, rhs),
        14 => arena.bv_srem(lhs, rhs),
        15 => arena.bv_smod(lhs, rhs),
        16 => arena.bv_shl(lhs, rhs),
        17 => arena.bv_lshr(lhs, rhs),
        18 => arena.bv_ashr(lhs, rhs),
        19 => arena.ite(cond, lhs, rhs),
        // Extracts of a wider term, so the range can land inside one side of a
        // concat, inside the original bits of an extend, or across either seam.
        20..=23 => {
            let hi = u32::try_from((seed >> 8) % u64::from(WIDE_WIDTH))
                .expect("modulus keeps this below WIDE_WIDTH");
            let lo = u32::try_from((seed >> 16) % u64::from(hi + 1))
                .expect("modulus keeps this at or below hi");
            let sliced = arena.extract(hi, lo, wide).unwrap();
            let want = hi - lo + 1;
            return match want.cmp(&BV_WIDTH) {
                Ordering::Equal => sliced,
                Ordering::Less => arena.zero_ext(BV_WIDTH - want, sliced).unwrap(),
                Ordering::Greater => arena.extract(BV_WIDTH - 1, 0, sliced).unwrap(),
            };
        }
        24 => arena.extract(BV_WIDTH - 1, 0, wide),
        25 => arena.extract(WIDE_WIDTH - 1, WIDE_WIDTH - BV_WIDTH, wide),
        // Rotate by 0 and by a full width are both boundary cases.
        26 => arena.rotate_left(rotate_amount(seed), lhs),
        27 => arena.rotate_right(rotate_amount(seed), lhs),
        28 => arena.zero_ext(0, lhs),
        _ => arena.sign_ext(0, lhs),
    }
    .unwrap()
}

fn build_wide(arena: &mut TermArena, seed: u64, depth: u8, leaves: &Leaves) -> TermId {
    if depth == 0 {
        return pick(&leaves.wide, seed);
    }
    let lhs = build_wide(arena, mix(seed, 5), depth - 1, leaves);
    let rhs = build_wide(arena, mix(seed, 6), depth - 1, leaves);
    let narrow_a = build_bv(arena, mix(seed, 7), depth - 1, leaves);
    let narrow_b = build_bv(arena, mix(seed, 8), depth - 1, leaves);
    let cond = build_bool(arena, mix(seed, 9), depth - 1, leaves);

    match seed % 10 {
        0 => arena.bv_add(lhs, rhs),
        1 => arena.bv_and(lhs, rhs),
        2 => arena.bv_or(lhs, rhs),
        3 => arena.bv_xor(lhs, rhs),
        4 => arena.bv_mul(lhs, rhs),
        5 => arena.ite(cond, lhs, rhs),
        // `concat` of two 4-bit terms is the shape `bv.extract_concat*` and
        // `bv.concat_extract` are about.
        6 | 7 => arena.concat(narrow_a, narrow_b),
        8 => arena.zero_ext(BV_WIDTH, narrow_a),
        _ => arena.sign_ext(BV_WIDTH, narrow_a),
    }
    .unwrap()
}

fn build_int(arena: &mut TermArena, seed: u64, depth: u8, leaves: &Leaves) -> TermId {
    if depth == 0 {
        return pick(&leaves.ints, seed);
    }
    let lhs = build_int(arena, mix(seed, 11), depth - 1, leaves);
    let rhs = build_int(arena, mix(seed, 12), depth - 1, leaves);

    match seed % 8 {
        0 => arena.int_add(lhs, rhs),
        1 => arena.int_sub(lhs, rhs),
        2 => arena.int_mul(lhs, rhs),
        3 => arena.int_neg(lhs),
        4 => arena.int_abs(lhs),
        // `div`/`mod` by whatever the generator produced, including the
        // constant `0` leaf. SMT-LIB leaves these underspecified, so a rule
        // that folds them is a wrong-`unsat`, not a wrong answer.
        5 => arena.int_div(lhs, rhs),
        6 => arena.int_mod(lhs, rhs),
        _ => arena.int_pow2(lhs),
    }
    .unwrap()
}

#[allow(clippy::too_many_lines)]
fn build_bool(arena: &mut TermArena, seed: u64, depth: u8, leaves: &Leaves) -> TermId {
    if depth == 0 {
        return pick(&leaves.bools, seed);
    }
    let lhs = build_bool(arena, mix(seed, 13), depth - 1, leaves);
    let rhs = build_bool(arena, mix(seed, 14), depth - 1, leaves);
    let bv_a = build_bv(arena, mix(seed, 15), depth - 1, leaves);
    let bv_b = build_bv(arena, mix(seed, 16), depth - 1, leaves);
    let int_a = build_int(arena, mix(seed, 17), depth - 1, leaves);
    let int_b = build_int(arena, mix(seed, 18), depth - 1, leaves);

    match seed % 24 {
        0 => arena.not(lhs),
        1 => arena.and(lhs, rhs),
        2 => arena.or(lhs, rhs),
        3 => arena.xor(lhs, rhs),
        4 => arena.implies(lhs, rhs),
        5 => arena.eq(lhs, rhs),
        6 => arena.eq(bv_a, bv_b),
        7 => arena.eq(int_a, int_b),
        8 => arena.bv_ult(bv_a, bv_b),
        9 => arena.bv_ule(bv_a, bv_b),
        10 => arena.bv_ugt(bv_a, bv_b),
        11 => arena.bv_uge(bv_a, bv_b),
        12 => arena.bv_slt(bv_a, bv_b),
        13 => arena.bv_sle(bv_a, bv_b),
        14 => arena.bv_sgt(bv_a, bv_b),
        15 => arena.bv_sge(bv_a, bv_b),
        16 => arena.int_lt(int_a, int_b),
        17 => arena.int_le(int_a, int_b),
        18 => arena.int_gt(int_a, int_b),
        19 => arena.int_ge(int_a, int_b),
        20 => arena.ite(lhs, rhs, lhs),
        21 => {
            let comp = arena.bv_comp(bv_a, bv_b).unwrap();
            let one = arena.bv_const(1, 1).unwrap();
            arena.eq(comp, one)
        }
        22 => arena.eq(bv_a, bv_a),
        _ => arena.bv_ult(bv_a, bv_a),
    }
    .unwrap()
}

fn replay_assignment(leaves: &Leaves, seed: u64) -> Assignment {
    let mut assignment = Assignment::new();
    let mut next = seed;
    for &sym in &leaves.bv_syms {
        next = splitmix(next);
        assignment.set(
            sym,
            Value::Bv {
                width: BV_WIDTH,
                value: u128::from(next % 16),
            },
        );
    }
    for &sym in &leaves.wide_syms {
        next = splitmix(next);
        assignment.set(
            sym,
            Value::Bv {
                width: WIDE_WIDTH,
                value: u128::from(next % 256),
            },
        );
    }
    for &sym in &leaves.bool_syms {
        next = splitmix(next);
        assignment.set(sym, Value::Bool(next & 1 == 1));
    }
    for &sym in &leaves.int_syms {
        next = splitmix(next);
        assignment.set(sym, Value::Int(i128::from(next % 21) - 10));
    }
    assignment
}

/// The hunt. Every generated term is canonicalized under the live guard, then
/// replayed against the ground evaluator on many more assignments than the
/// guard itself samples.
#[test]
fn wide_random_sweep_finds_no_rule_firing_outside_its_precondition() {
    let mut arena = TermArena::new();
    let leaves = build_leaves(&mut arena);
    let canonicalizer = Canonicalizer::new(default_manifest());

    let mut originals = Vec::new();
    for seed in 0..4096u64 {
        let mixed = splitmix(seed);
        let term = match seed % 3 {
            0 => build_bool(&mut arena, mixed, 4, &leaves),
            1 => build_bv(&mut arena, mixed, 4, &leaves),
            _ => build_int(&mut arena, mixed, 3, &leaves),
        };
        originals.push(term);
    }

    // A guard refusal here is the finding, so it must not be swallowed.
    let outcome = canonicalizer
        .canonicalize_terms(&mut arena, &originals)
        .expect("a precondition violation on generated input is a WRONG-UNSAT CLASS DEFECT");
    let audit = outcome.report.precondition_audit();

    // The sweep must actually exercise the rules. A generator that produced
    // nothing rewritable would pass this file while testing nothing at all --
    // the exact way a control can be vacuous.
    assert!(
        audit.applications() >= 2000,
        "sweep exercised only {} rule applications; it is too weak to be evidence",
        audit.applications()
    );
    assert!(
        audit.denotation_checked() * 10 >= audit.applications() * 9,
        "the semantic tier reached only {} of {} applications; a guard that \
         declines to check is not a guard",
        audit.denotation_checked(),
        audit.applications()
    );

    // Second, independent judge: replay on assignments the guard never saw.
    for replay in 0..40u64 {
        let assignment = replay_assignment(&leaves, splitmix(replay.wrapping_add(0xfeed)));
        for (index, (&original, &canonical)) in originals.iter().zip(&outcome.terms).enumerate() {
            let (Ok(before), Ok(after)) = (
                eval(&arena, original, &assignment),
                eval(&arena, canonical, &assignment),
            ) else {
                continue;
            };
            assert_eq!(
                before, after,
                "canonicalization changed denotation on generated term #{index} \
                 under replay assignment #{replay}"
            );
        }
    }
}

/// The same sweep with the semantic tier switched off, to establish what the
/// structural tier alone is worth.
///
/// This is a measurement, not a guard: it records that the operator-scope check
/// runs on every application even when the denotation check does not, so the
/// release fast path is not unprotected.
#[test]
fn structural_tier_alone_still_checks_every_application() {
    let mut arena = TermArena::new();
    let leaves = build_leaves(&mut arena);
    let canonicalizer =
        Canonicalizer::with_precondition_policy(default_manifest(), PreconditionPolicy::Structural);

    let mut originals = Vec::new();
    for seed in 0..1024u64 {
        let mixed = splitmix(seed);
        originals.push(match seed % 2 {
            0 => build_bool(&mut arena, mixed, 4, &leaves),
            _ => build_bv(&mut arena, mixed, 4, &leaves),
        });
    }

    let outcome = canonicalizer
        .canonicalize_terms(&mut arena, &originals)
        .expect("structural tier must not refuse a legitimate rewrite");
    let audit = outcome.report.precondition_audit();

    assert!(audit.applications() >= 500);
    assert_eq!(
        audit.applications(),
        audit.scope_checked() + audit.scope_unconstrained(),
        "every application is accounted for by the structural tier"
    );
    assert_eq!(
        audit.denotation_checked() + audit.denotation_unavailable(),
        0,
        "the semantic tier must be genuinely off, not silently on"
    );
}
