//! Unit and exhaustive small-width tests for the term IR and evaluator.
//!
//! Per the bv-semantics note, operators with edge cases are tested
//! exhaustively at small widths, not just on sampled inputs.

use axeyum_ir::{
    ArrayValue, Assignment, BIT_VECTOR_WIRE_ORDER, BitOrder, FuncValue, IrError, Rational, Sort,
    TermArena, Value, bv_value_to_lsb_bits, eval, lsb_bits_to_bv_value, lsb_bits_to_value,
    value_to_lsb_bits,
};

fn bv(width: u32, value: u128) -> Value {
    Value::Bv { width, value }
}

// ----- interning and determinism ----------------------------------------

#[test]
fn interning_dedups_structurally_equal_terms() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let one_a = a.bv_const(8, 1).unwrap();
    let one_b = a.bv_const(8, 1).unwrap();
    assert_eq!(one_a, one_b);
    let s1 = a.bv_add(x, one_a).unwrap();
    let s2 = a.bv_add(x, one_b).unwrap();
    assert_eq!(s1, s2);
    assert_eq!(a.len(), 3); // x, 1, x+1
}

#[test]
fn identical_construction_yields_identical_ids() {
    let build = || {
        let mut a = TermArena::new();
        let x = a.bv_var("x", 8).unwrap();
        let one = a.bv_const(8, 1).unwrap();
        let sum = a.bv_add(x, one).unwrap();
        let five = a.bv_const(8, 5).unwrap();
        let eq = a.eq(sum, five).unwrap();
        (x, one, sum, five, eq)
    };
    assert_eq!(build(), build());
}

#[test]
fn symbol_redeclaration_same_sort_is_idempotent() {
    let mut a = TermArena::new();
    let s1 = a.declare("x", Sort::BitVec(8)).unwrap();
    let s2 = a.declare("x", Sort::BitVec(8)).unwrap();
    assert_eq!(s1, s2);
    let err = a.declare("x", Sort::Bool).unwrap_err();
    assert!(matches!(err, IrError::SymbolSortConflict { .. }));
}

// ----- build-time validation ---------------------------------------------

#[test]
fn width_and_value_validation() {
    let mut a = TermArena::new();
    assert!(matches!(a.bv_const(0, 0), Err(IrError::InvalidWidth(0))));
    assert!(matches!(
        a.bv_const(129, 0),
        Err(IrError::InvalidWidth(129))
    ));
    assert!(matches!(
        a.bv_const(4, 16),
        Err(IrError::ValueOutOfRange {
            width: 4,
            value: 16
        })
    ));
    assert!(a.bv_const(128, u128::MAX).is_ok());
    assert!(a.bv_const(4, 15).is_ok());
}

#[test]
fn sort_checking_rejects_mixed_operands() {
    let mut a = TermArena::new();
    let p = a.bool_var("p").unwrap();
    let x = a.bv_var("x", 8).unwrap();
    let y = a.bv_var("y", 4).unwrap();
    assert!(matches!(a.and(p, x), Err(IrError::SortMismatch { .. })));
    assert!(matches!(a.bv_add(x, y), Err(IrError::SortsDiffer(..))));
    assert!(matches!(a.eq(p, x), Err(IrError::SortsDiffer(..))));
    assert!(matches!(a.ite(x, p, p), Err(IrError::SortMismatch { .. })));
    assert!(matches!(a.ite(p, p, x), Err(IrError::SortsDiffer(..))));
    assert!(matches!(a.bv_not(p), Err(IrError::SortMismatch { .. })));
}

#[test]
fn extract_and_concat_bounds_are_static_errors() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    assert!(matches!(
        a.extract(8, 0, x),
        Err(IrError::ExtractOutOfRange { .. })
    ));
    assert!(matches!(
        a.extract(2, 3, x),
        Err(IrError::ExtractOutOfRange { .. })
    ));
    let wide = a.bv_var("w", 128).unwrap();
    assert!(matches!(
        a.concat(wide, x),
        Err(IrError::ConcatTooWide(136))
    ));
    assert!(matches!(
        a.zero_ext(u32::MAX, x),
        Err(IrError::ConcatTooWide(u32::MAX))
    ));
    assert!(matches!(
        a.sign_ext(u32::MAX, x),
        Err(IrError::ConcatTooWide(u32::MAX))
    ));
}

#[test]
fn lsb_first_bit_conversion_uses_numeric_bit_indices() {
    assert_eq!(BIT_VECTOR_WIRE_ORDER, BitOrder::LsbFirst);
    assert_eq!(
        bv_value_to_lsb_bits(4, 0b1010).unwrap(),
        vec![false, true, false, true],
        "element i is SMT-LIB bit i with numeric weight 2^i"
    );
    assert_eq!(
        value_to_lsb_bits(Value::Bool(true)).unwrap(),
        vec![true],
        "Bool lowers to one Boolean wire"
    );
    assert_eq!(
        lsb_bits_to_bv_value(&[false, true, false, true]).unwrap(),
        bv(4, 0b1010)
    );
}

#[test]
fn lsb_first_bit_conversion_round_trips_values() {
    let cases = [
        bv(1, 0),
        bv(1, 1),
        bv(3, 5),
        bv(8, 0xa5),
        bv(64, 0x8000_0000_0000_0001),
        bv(128, u128::MAX),
    ];
    for value in cases {
        let sort = value.sort();
        let bits = value_to_lsb_bits(value.clone()).unwrap();
        assert_eq!(lsb_bits_to_value(sort, &bits).unwrap(), value);
    }
}

#[test]
fn lsb_first_bit_conversion_rejects_invalid_shapes() {
    assert!(matches!(
        bv_value_to_lsb_bits(0, 0),
        Err(IrError::InvalidWidth(0))
    ));
    assert!(matches!(
        bv_value_to_lsb_bits(4, 16),
        Err(IrError::ValueOutOfRange {
            width: 4,
            value: 16
        })
    ));
    assert!(matches!(
        lsb_bits_to_bv_value(&[]),
        Err(IrError::InvalidWidth(0))
    ));
    assert!(matches!(
        lsb_bits_to_value(Sort::Bool, &[true, false]),
        Err(IrError::BitCountMismatch {
            expected: 1,
            found: 2
        })
    ));
    assert!(matches!(
        lsb_bits_to_value(Sort::BitVec(4), &[true, false]),
        Err(IrError::BitCountMismatch {
            expected: 4,
            found: 2
        })
    ));
}

// ----- evaluator: Boolean operators --------------------------------------

#[test]
fn boolean_truth_tables() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    for p in [false, true] {
        let tp = a.bool_const(p);
        let np = a.not(tp).unwrap();
        assert_eq!(eval(&a, np, &asg).unwrap(), Value::Bool(!p));
        for q in [false, true] {
            let tq = a.bool_const(q);
            let cases = [
                (a.and(tp, tq).unwrap(), p && q),
                (a.or(tp, tq).unwrap(), p || q),
                (a.xor(tp, tq).unwrap(), p ^ q),
                (a.eq(tp, tq).unwrap(), p == q),
            ];
            for (term, expect) in cases {
                assert_eq!(eval(&a, term, &asg).unwrap(), Value::Bool(expect));
            }
        }
    }
}

// ----- evaluator: exhaustive small-width BV semantics ---------------------

#[test]
fn exhaustive_bv_binary_ops_small_widths() {
    for w in [1u32, 2, 3, 4, 8] {
        let count = 1u128 << w;
        let m = count - 1;
        let mut a = TermArena::new();
        let asg = Assignment::new();
        for x in 0..count {
            for y in 0..count {
                let tx = a.bv_const(w, x).unwrap();
                let ty = a.bv_const(w, y).unwrap();
                let cases = [
                    (a.bv_add(tx, ty).unwrap(), bv(w, (x + y) & m)),
                    (a.bv_and(tx, ty).unwrap(), bv(w, x & y)),
                    (a.bv_or(tx, ty).unwrap(), bv(w, x | y)),
                    (a.bv_xor(tx, ty).unwrap(), bv(w, x ^ y)),
                    (a.bv_ult(tx, ty).unwrap(), Value::Bool(x < y)),
                    (a.eq(tx, ty).unwrap(), Value::Bool(x == y)),
                ];
                for (term, expect) in cases {
                    assert_eq!(eval(&a, term, &asg).unwrap(), expect, "w={w} x={x} y={y}");
                }
            }
        }
    }
}

#[test]
fn exhaustive_bv_not_small_widths() {
    for w in [1u32, 4, 8] {
        let count = 1u128 << w;
        let mut a = TermArena::new();
        let asg = Assignment::new();
        for x in 0..count {
            let tx = a.bv_const(w, x).unwrap();
            let t = a.bv_not(tx).unwrap();
            assert_eq!(eval(&a, t, &asg).unwrap(), bv(w, !x & (count - 1)));
        }
    }
}

#[test]
fn exhaustive_extract_concat_roundtrip() {
    // Splitting at every position and re-concatenating restores the value.
    let w = 6u32;
    let mut a = TermArena::new();
    let asg = Assignment::new();
    for v in 0..(1u128 << w) {
        let tv = a.bv_const(w, v).unwrap();
        for split in 1..w {
            let hi = a.extract(w - 1, split, tv).unwrap();
            let lo = a.extract(split - 1, 0, tv).unwrap();
            let back = a.concat(hi, lo).unwrap();
            assert_eq!(
                eval(&a, back, &asg).unwrap(),
                bv(w, v),
                "v={v} split={split}"
            );
        }
    }
}

#[test]
fn ite_selects_branches() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let cond_t = a.bool_const(true);
    let cond_f = a.bool_const(false);
    let seven = a.bv_const(8, 7).unwrap();
    let nine = a.bv_const(8, 9).unwrap();
    let pick_x = a.ite(cond_t, seven, nine).unwrap();
    let pick_y = a.ite(cond_f, seven, nine).unwrap();
    assert_eq!(eval(&a, pick_x, &asg).unwrap(), bv(8, 7));
    assert_eq!(eval(&a, pick_y, &asg).unwrap(), bv(8, 9));
}

// ----- evaluator: width-128 boundary --------------------------------------

#[test]
fn width_128_wrapping_and_masking() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let max = a.bv_const(128, u128::MAX).unwrap();
    let one = a.bv_const(128, 1).unwrap();
    let sum = a.bv_add(max, one).unwrap();
    assert_eq!(eval(&a, sum, &asg).unwrap(), bv(128, 0));
    let n = a.bv_not(max).unwrap();
    assert_eq!(eval(&a, n, &asg).unwrap(), bv(128, 0));
}

// ----- evaluator: symbols and sharing -------------------------------------

#[test]
fn unbound_symbol_is_a_typed_error() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let err = eval(&a, x, &Assignment::new()).unwrap_err();
    assert!(matches!(err, IrError::UnboundSymbol(_)));
}

#[test]
fn deep_shared_term_evaluates_without_stack_overflow() {
    // 100k stacked additions over a shared DAG; iterative eval must hold.
    let mut a = TermArena::new();
    let sym = a.declare("x", Sort::BitVec(64)).unwrap();
    let x = a.var(sym);
    let one = a.bv_const(64, 1).unwrap();
    let mut t = x;
    for _ in 0..100_000 {
        t = a.bv_add(t, one).unwrap();
    }
    let mut asg = Assignment::new();
    asg.set(sym, bv(64, 5));
    assert_eq!(eval(&a, t, &asg).unwrap(), bv(64, 100_005));
}

// ----- Phase 1: exhaustive semantics for the extended operator set --------

/// Two's-complement interpretation for the i64-based test reference.
fn to_i(w: u32, v: u128) -> i64 {
    let v = i64::try_from(v).unwrap();
    if v >= 1i64 << (w - 1) {
        v - (1i64 << w)
    } else {
        v
    }
}

/// Masks an i64 reference result back to width bits.
fn from_i(w: u32, v: i64) -> u128 {
    u128::from(v.rem_euclid(1i64 << w) as u64)
}

#[test]
fn exhaustive_arithmetic_ops() {
    for w in [1u32, 2, 3, 4] {
        let count = 1u128 << w;
        let m = count - 1;
        let mut a = TermArena::new();
        let asg = Assignment::new();
        for x in 0..count {
            for y in 0..count {
                let tx = a.bv_const(w, x).unwrap();
                let ty = a.bv_const(w, y).unwrap();
                let cases = [
                    (a.bv_sub(tx, ty).unwrap(), x.wrapping_sub(y) & m),
                    (a.bv_mul(tx, ty).unwrap(), x.wrapping_mul(y) & m),
                    (
                        a.bv_udiv(tx, ty).unwrap(),
                        x.checked_div(y).unwrap_or(u128::MAX) & m,
                    ),
                    (a.bv_urem(tx, ty).unwrap(), x.checked_rem(y).unwrap_or(x)),
                    (a.bv_nand(tx, ty).unwrap(), !(x & y) & m),
                    (a.bv_nor(tx, ty).unwrap(), !(x | y) & m),
                    (a.bv_xnor(tx, ty).unwrap(), !(x ^ y) & m),
                ];
                for (term, expect) in cases {
                    assert_eq!(
                        eval(&a, term, &asg).unwrap(),
                        bv(w, expect),
                        "w={w} x={x} y={y}"
                    );
                }
            }
        }
    }
}

#[test]
fn exhaustive_signed_arithmetic() {
    for w in [1u32, 2, 3, 4, 8] {
        let count = 1u128 << w;
        let mut a = TermArena::new();
        let asg = Assignment::new();
        for x in 0..count {
            for y in 0..count {
                let (sx, sy) = (to_i(w, x), to_i(w, y));
                let tx = a.bv_const(w, x).unwrap();
                let ty = a.bv_const(w, y).unwrap();
                let sdiv = if sy == 0 {
                    if sx >= 0 { from_i(w, -1) } else { 1 }
                } else {
                    from_i(w, sx.wrapping_div(sy))
                };
                let srem = if sy == 0 { x } else { from_i(w, sx % sy) };
                let smod = if sy == 0 {
                    x
                } else {
                    let r = sx % sy;
                    if r != 0 && (r < 0) != (sy < 0) {
                        from_i(w, r + sy)
                    } else {
                        from_i(w, r)
                    }
                };
                let cases = [
                    (a.bv_sdiv(tx, ty).unwrap(), bv(w, sdiv)),
                    (a.bv_srem(tx, ty).unwrap(), bv(w, srem)),
                    (a.bv_smod(tx, ty).unwrap(), bv(w, smod)),
                    (a.bv_slt(tx, ty).unwrap(), Value::Bool(sx < sy)),
                    (a.bv_sle(tx, ty).unwrap(), Value::Bool(sx <= sy)),
                    (a.bv_sgt(tx, ty).unwrap(), Value::Bool(sx > sy)),
                    (a.bv_sge(tx, ty).unwrap(), Value::Bool(sx >= sy)),
                ];
                for (term, expect) in cases {
                    assert_eq!(eval(&a, term, &asg).unwrap(), expect, "w={w} x={x} y={y}");
                }
            }
        }
    }
}

#[test]
fn exhaustive_unsigned_comparisons() {
    let w = 4u32;
    let mut a = TermArena::new();
    let asg = Assignment::new();
    for x in 0..16u128 {
        for y in 0..16u128 {
            let tx = a.bv_const(w, x).unwrap();
            let ty = a.bv_const(w, y).unwrap();
            let cases = [
                (a.bv_ule(tx, ty).unwrap(), x <= y),
                (a.bv_ugt(tx, ty).unwrap(), x > y),
                (a.bv_uge(tx, ty).unwrap(), x >= y),
            ];
            for (term, expect) in cases {
                assert_eq!(eval(&a, term, &asg).unwrap(), Value::Bool(expect));
            }
        }
    }
}

#[test]
fn exhaustive_shifts_including_overshift() {
    for w in [1u32, 4, 8] {
        let count = 1u128 << w;
        let m = count - 1;
        let mut a = TermArena::new();
        let asg = Assignment::new();
        for x in 0..count {
            for k in 0..count {
                let tx = a.bv_const(w, x).unwrap();
                let tk = a.bv_const(w, k).unwrap();
                let shl = if k >= u128::from(w) { 0 } else { (x << k) & m };
                let lshr = if k >= u128::from(w) { 0 } else { x >> k };
                let sign = (x >> (w - 1)) & 1 == 1;
                let ashr = if k >= u128::from(w) {
                    if sign { m } else { 0 }
                } else {
                    from_i(w, to_i(w, x) >> k)
                };
                let cases = [
                    (a.bv_shl(tx, tk).unwrap(), shl),
                    (a.bv_lshr(tx, tk).unwrap(), lshr),
                    (a.bv_ashr(tx, tk).unwrap(), ashr),
                ];
                for (term, expect) in cases {
                    assert_eq!(
                        eval(&a, term, &asg).unwrap(),
                        bv(w, expect),
                        "w={w} x={x} k={k}"
                    );
                }
            }
        }
    }
}

#[test]
fn exhaustive_extensions_and_rotates() {
    let w = 4u32;
    let mut a = TermArena::new();
    let asg = Assignment::new();
    for x in 0..16u128 {
        let tx = a.bv_const(w, x).unwrap();
        let neg = a.bv_neg(tx).unwrap();
        assert_eq!(eval(&a, neg, &asg).unwrap(), bv(w, x.wrapping_neg() & 15));
        for by in 0..=3u32 {
            let z = a.zero_ext(by, tx).unwrap();
            assert_eq!(eval(&a, z, &asg).unwrap(), bv(w + by, x));
            let s = a.sign_ext(by, tx).unwrap();
            let sign = x >> 3 & 1 == 1;
            let expect = if sign {
                x | (((1u128 << (w + by)) - 1) ^ 15)
            } else {
                x
            };
            assert_eq!(
                eval(&a, s, &asg).unwrap(),
                bv(w + by, expect),
                "x={x} by={by}"
            );
        }
        for by in 0..=9u32 {
            let k = by % w;
            let rl = a.rotate_left(by, tx).unwrap();
            let expect_l = if k == 0 {
                x
            } else {
                ((x << k) | (x >> (w - k))) & 15
            };
            assert_eq!(
                eval(&a, rl, &asg).unwrap(),
                bv(w, expect_l),
                "x={x} by={by}"
            );
            let rr = a.rotate_right(by, tx).unwrap();
            let expect_r = if k == 0 {
                x
            } else {
                ((x >> k) | (x << (w - k))) & 15
            };
            assert_eq!(
                eval(&a, rr, &asg).unwrap(),
                bv(w, expect_r),
                "x={x} by={by}"
            );
        }
    }
}

#[test]
fn rotate_amounts_normalize_for_interning() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let r1 = a.rotate_left(1, x).unwrap();
    let r9 = a.rotate_left(9, x).unwrap();
    assert_eq!(r1, r9);
}

#[test]
fn implies_and_comp() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    for p in [false, true] {
        for q in [false, true] {
            let tp = a.bool_const(p);
            let tq = a.bool_const(q);
            let imp = a.implies(tp, tq).unwrap();
            assert_eq!(eval(&a, imp, &asg).unwrap(), Value::Bool(!p || q));
        }
    }
    let x = a.bv_const(8, 7).unwrap();
    let y = a.bv_const(8, 9).unwrap();
    let same = a.bv_comp(x, x).unwrap();
    let diff = a.bv_comp(x, y).unwrap();
    assert_eq!(eval(&a, same, &asg).unwrap(), bv(1, 1));
    assert_eq!(eval(&a, diff, &asg).unwrap(), bv(1, 0));
}

#[test]
fn render_produces_smtlib_syntax() {
    use axeyum_ir::render;
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let one = a.bv_const(8, 1).unwrap();
    let five = a.bv_const(8, 5).unwrap();
    let sum = a.bv_add(x, one).unwrap();
    let f = a.eq(sum, five).unwrap();
    assert_eq!(render(&a, f), "(= (bvadd x (_ bv1 8)) (_ bv5 8))");
    let sl = a.extract(7, 4, x).unwrap();
    let se = a.sign_ext(4, sl).unwrap();
    assert_eq!(render(&a, se), "((_ sign_extend 4) ((_ extract 7 4) x))");
}

// ----- term-shape metrics (query-cost-control note) ------------------------

#[test]
fn term_stats_detect_representational_blowup() {
    use axeyum_ir::TermStats;
    // The classic 2^k bomb: x doubled 200 times. DAG stays tiny; the tree
    // count saturates, which is exactly the alarm signal.
    let mut a = TermArena::new();
    let mut t = a.bv_var("x", 64).unwrap();
    for _ in 0..200 {
        t = a.bv_add(t, t).unwrap();
    }
    let stats = TermStats::compute(&a, &[t]);
    assert_eq!(stats.dag_nodes, 201);
    assert_eq!(stats.tree_nodes, u64::MAX, "tree count must saturate");
    assert_eq!(stats.max_depth, 201);
    assert_eq!(stats.distinct_symbols, 1);
    assert!(stats.sharing_ratio() > 1e15);
}

#[test]
fn term_stats_count_op_classes() {
    use axeyum_ir::TermStats;
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let y = a.bv_var("y", 8).unwrap();
    let p = a.bool_var("p").unwrap();
    let prod_term = a.bv_mul(x, y).unwrap();
    let div_term = a.bv_udiv(prod_term, y).unwrap();
    let picked = a.ite(p, div_term, x).unwrap();
    let stats = TermStats::compute(&a, &[picked]);
    assert_eq!(stats.mul_div_count, 2);
    assert_eq!(stats.ite_count, 1);
    assert_eq!(stats.distinct_symbols, 3);
    assert_eq!(stats.tree_nodes, 8); // ite(p, udiv(mul(x,y),y), x) as a tree
    assert_eq!(stats.dag_nodes, 6);
}

#[test]
fn array_select_over_store_is_read_over_write() {
    // select(store(a, i, e), j) == ite(i == j, e, select(a, j)), with `a` a
    // constant array. Checked exhaustively over a small index/element domain.
    let mut arena = TermArena::new();
    let a_sym = arena
        .declare(
            "a",
            Sort::Array {
                index: 3,
                element: 4,
            },
        )
        .unwrap();
    let a = arena.var(a_sym);
    let i_sym = arena.declare("i", Sort::BitVec(3)).unwrap();
    let j_sym = arena.declare("j", Sort::BitVec(3)).unwrap();
    let e_sym = arena.declare("e", Sort::BitVec(4)).unwrap();
    let i = arena.var(i_sym);
    let j = arena.var(j_sym);
    let e = arena.var(e_sym);
    let stored = arena.store(a, i, e).unwrap();
    let read = arena.select(stored, j).unwrap();
    assert_eq!(arena.sort_of(read), Sort::BitVec(4));

    let default = 0x5u128;
    for i_val in 0..8u128 {
        for j_val in 0..8u128 {
            for e_val in [0u128, 1, 7, 15] {
                let mut assignment = Assignment::new();
                assignment.set(a_sym, Value::Array(ArrayValue::constant(3, 4, default)));
                assignment.set(i_sym, bv(3, i_val));
                assignment.set(j_sym, bv(3, j_val));
                assignment.set(e_sym, bv(4, e_val));
                let expected = if i_val == j_val { e_val } else { default };
                assert_eq!(
                    eval(&arena, read, &assignment).unwrap(),
                    bv(4, expected),
                    "i={i_val} j={j_val} e={e_val}"
                );
            }
        }
    }
}

#[test]
fn array_store_is_last_write_wins_and_extensional() {
    // store(store(a, i, e1), i, e2) is extensionally equal to store(a, i, e2).
    let mut arena = TermArena::new();
    let a_sym = arena
        .declare(
            "a",
            Sort::Array {
                index: 4,
                element: 8,
            },
        )
        .unwrap();
    let a = arena.var(a_sym);
    let i = arena.bv_const(4, 3).unwrap();
    let e1 = arena.bv_const(8, 0xaa).unwrap();
    let e2 = arena.bv_const(8, 0xbb).unwrap();
    let inner = arena.store(a, i, e1).unwrap();
    let outer = arena.store(inner, i, e2).unwrap();
    let direct = arena.store(a, i, e2).unwrap();
    let equal = arena.eq(outer, direct).unwrap();

    let mut assignment = Assignment::new();
    assignment.set(a_sym, Value::Array(ArrayValue::constant(4, 8, 0)));
    assert_eq!(eval(&arena, equal, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn array_builders_reject_mismatched_widths() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let wrong_index = arena.bv_const(5, 0).unwrap();
    assert!(matches!(
        arena.select(a, wrong_index),
        Err(IrError::SortsDiffer(..))
    ));
    let idx = arena.bv_const(4, 0).unwrap();
    let wrong_elem = arena.bv_const(7, 0).unwrap();
    assert!(matches!(
        arena.store(a, idx, wrong_elem),
        Err(IrError::SortsDiffer(..))
    ));
    // select on a non-array is a sort mismatch.
    let bv8 = arena.bv_var("x", 8).unwrap();
    assert!(matches!(
        arena.select(bv8, idx),
        Err(IrError::SortMismatch {
            expected: "Array",
            ..
        })
    ));
}

// ----- uninterpreted functions (ADR-0013) -------------------------------

#[test]
fn apply_interns_and_carries_result_sort() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let a = arena.apply(f, &[x]).unwrap();
    let b = arena.apply(f, &[x]).unwrap();
    // Same function, same argument => the same interned term.
    assert_eq!(a, b);
    assert_eq!(arena.sort_of(a), Sort::BitVec(8));
    // Re-declaring with the identical signature returns the same FuncId.
    let f_again = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    assert_eq!(f, f_again);
}

#[test]
fn apply_rejects_bad_signatures_and_arguments() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    // Wrong arity.
    assert!(matches!(
        arena.apply(f, &[x, x]),
        Err(IrError::ArityMismatch {
            expected: 1,
            found: 2
        })
    ));
    // Wrong argument sort.
    assert!(matches!(
        arena.apply(f, &[y]),
        Err(IrError::SortsDiffer(..))
    ));
    // Array sort in a signature is rejected.
    assert!(matches!(
        arena.declare_fun(
            "g",
            &[Sort::Array {
                index: 4,
                element: 8
            }],
            Sort::Bool
        ),
        Err(IrError::SortMismatch {
            expected: "Bool or BitVec",
            ..
        })
    ));
    // Re-declaring a name with a different signature conflicts.
    assert!(matches!(
        arena.declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(8)),
        Err(IrError::FunctionSignatureConflict { .. })
    ));
}

#[test]
fn apply_evaluates_against_a_model_interpretation() {
    // F: f(x) where f is interpreted as a small table.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(8))
        .unwrap();
    let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_sym);
    let app = arena.apply(f, &[x]).unwrap();

    let interp = FuncValue::constant(vec![Sort::BitVec(4)], Sort::BitVec(8), 0xff)
        .define(&[1], 0xaa)
        .define(&[2], 0xbb);

    for x_val in 0..16u128 {
        let mut model = Assignment::new();
        model.set(x_sym, bv(4, x_val));
        model.set_function(f, interp.clone());
        let expected = match x_val {
            1 => 0xaa,
            2 => 0xbb,
            _ => 0xff,
        };
        assert_eq!(eval(&arena, app, &model).unwrap(), bv(8, expected));
    }
}

#[test]
fn apply_is_a_function_equal_arguments_give_equal_results() {
    // The defining EUF property (congruence): under any interpretation,
    // x == y implies f(x) == f(y). Checked exhaustively at width 3.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(3)], Sort::BitVec(3))
        .unwrap();
    let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_arg = arena.eq(x, y).unwrap();
    let same_res = arena.eq(fx, fy).unwrap();
    let congruence = arena.implies(same_arg, same_res).unwrap();

    // An arbitrary (deterministic) interpretation of f.
    let mut interp = FuncValue::constant(vec![Sort::BitVec(3)], Sort::BitVec(3), 0);
    for k in 0..8u128 {
        interp = interp.define(&[k], (k.wrapping_mul(5).wrapping_add(1)) & 0x7);
    }
    for x_val in 0..8u128 {
        for y_val in 0..8u128 {
            let mut model = Assignment::new();
            model.set(x_sym, bv(3, x_val));
            model.set(y_sym, bv(3, y_val));
            model.set_function(f, interp.clone());
            assert_eq!(
                eval(&arena, congruence, &model).unwrap(),
                Value::Bool(true),
                "congruence must hold for x={x_val} y={y_val}"
            );
        }
    }
}

#[test]
fn apply_without_interpretation_is_unbound_function() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Bool], Sort::Bool).unwrap();
    let p_sym = arena.declare("p", Sort::Bool).unwrap();
    let p = arena.var(p_sym);
    let app = arena.apply(f, &[p]).unwrap();
    let mut model = Assignment::new();
    model.set(p_sym, Value::Bool(true));
    assert!(matches!(
        eval(&arena, app, &model),
        Err(IrError::UnboundFunction(_))
    ));
}

#[test]
fn func_value_normalizes_to_default() {
    // Defining an entry equal to the default leaves no override (extensional).
    let interp = FuncValue::constant(vec![Sort::BitVec(4)], Sort::BitVec(4), 7)
        .define(&[1], 7)
        .define(&[2], 3);
    assert_eq!(interp.apply(&[1]), 7);
    assert_eq!(interp.apply(&[2]), 3);
    assert_eq!(interp.apply(&[9]), 7);
    // Only the genuinely-overriding entry remains.
    assert_eq!(interp.entries().count(), 1);
}

// ----- linear integer arithmetic (ADR-0014) -----------------------------

fn int(value: i128) -> Value {
    Value::Int(value)
}

#[test]
fn int_builders_sort_check_and_intern() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let sum_a = arena.int_add(x, one).unwrap();
    let sum_b = arena.int_add(x, one).unwrap();
    assert_eq!(sum_a, sum_b, "structurally equal int terms intern");
    assert_eq!(arena.sort_of(sum_a), Sort::Int);
    let lt = arena.int_lt(x, one).unwrap();
    assert_eq!(arena.sort_of(lt), Sort::Bool);
    // Mixing an integer with a bit-vector is a sort error.
    let bv8 = arena.bv_var("b", 8).unwrap();
    assert!(matches!(
        arena.int_add(x, bv8),
        Err(IrError::SortMismatch {
            expected: "Int",
            ..
        })
    ));
    // Integers are distinct from bit-vectors under equality.
    assert!(matches!(arena.eq(x, bv8), Err(IrError::SortsDiffer(..))));
}

#[test]
fn int_evaluator_matches_reference_arithmetic() {
    // Exhaustive small-range check of the linear operator semantics against
    // i128 reference arithmetic.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let neg = arena.int_neg(x).unwrap();
    let add = arena.int_add(x, y).unwrap();
    let sub = arena.int_sub(x, y).unwrap();
    let mul = arena.int_mul(x, y).unwrap();
    let lt = arena.int_lt(x, y).unwrap();
    let le = arena.int_le(x, y).unwrap();
    let gt = arena.int_gt(x, y).unwrap();
    let ge = arena.int_ge(x, y).unwrap();

    for xv in -6i128..=6 {
        for yv in -6i128..=6 {
            let mut m = Assignment::new();
            m.set(x_sym, int(xv));
            m.set(y_sym, int(yv));
            assert_eq!(eval(&arena, neg, &m).unwrap(), int(-xv));
            assert_eq!(eval(&arena, add, &m).unwrap(), int(xv + yv));
            assert_eq!(eval(&arena, sub, &m).unwrap(), int(xv - yv));
            assert_eq!(eval(&arena, mul, &m).unwrap(), int(xv * yv));
            assert_eq!(eval(&arena, lt, &m).unwrap(), Value::Bool(xv < yv));
            assert_eq!(eval(&arena, le, &m).unwrap(), Value::Bool(xv <= yv));
            assert_eq!(eval(&arena, gt, &m).unwrap(), Value::Bool(xv > yv));
            assert_eq!(eval(&arena, ge, &m).unwrap(), Value::Bool(xv >= yv));
        }
    }
}

#[test]
fn int_const_and_negative_evaluate() {
    let mut arena = TermArena::new();
    let a = arena.int_const(-5);
    let b = arena.int_const(8);
    let sum = arena.int_add(a, b).unwrap();
    let asg = Assignment::new();
    assert_eq!(eval(&arena, sum, &asg).unwrap(), int(3));
    // Distinct integer constants are not equal; equal ones intern.
    assert_eq!(arena.int_const(-5), a);
}

#[test]
fn int_is_not_a_function_argument_sort() {
    // Functions are finite scalar (Bool/BitVec); integers are rejected.
    let mut arena = TermArena::new();
    assert!(matches!(
        arena.declare_fun("f", &[Sort::Int], Sort::Bool),
        Err(IrError::SortMismatch { .. })
    ));
}

// ----- linear real arithmetic (ADR-0015) --------------------------------

fn real(num: i128, den: i128) -> Value {
    Value::Real(axeyum_ir::Rational::new(num, den))
}

#[test]
fn real_builders_sort_check_and_intern() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let half = arena.real_ratio(1, 2);
    let sum_a = arena.real_add(x, half).unwrap();
    let sum_b = arena.real_add(x, half).unwrap();
    assert_eq!(sum_a, sum_b, "structurally equal real terms intern");
    assert_eq!(arena.sort_of(sum_a), Sort::Real);
    let lt = arena.real_lt(x, half).unwrap();
    assert_eq!(arena.sort_of(lt), Sort::Bool);
    // Mixing a real with an integer or bit-vector is a sort error.
    let y = arena.int_var("y").unwrap();
    assert!(matches!(
        arena.real_add(x, y),
        Err(IrError::SortMismatch {
            expected: "Real",
            ..
        })
    ));
    assert!(matches!(arena.eq(x, y), Err(IrError::SortsDiffer(..))));
    // Equal rationals in lowest terms intern to the same constant term.
    assert_eq!(arena.real_ratio(2, 4), half);
}

#[test]
fn real_evaluator_matches_exact_rational_arithmetic() {
    // Check the linear operator semantics against exact rational reference
    // values over a small grid of fractions.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let neg = arena.real_neg(x).unwrap();
    let add = arena.real_add(x, y).unwrap();
    let sub = arena.real_sub(x, y).unwrap();
    let mul = arena.real_mul(x, y).unwrap();
    let lt = arena.real_lt(x, y).unwrap();
    let le = arena.real_le(x, y).unwrap();
    let gt = arena.real_gt(x, y).unwrap();
    let ge = arena.real_ge(x, y).unwrap();

    let grid = [
        Rational::new(-3, 2),
        Rational::new(-1, 3),
        Rational::zero(),
        Rational::new(1, 4),
        Rational::new(5, 3),
        Rational::integer(2),
    ];
    for &xv in &grid {
        for &yv in &grid {
            let mut m = Assignment::new();
            m.set(x_sym, Value::Real(xv));
            m.set(y_sym, Value::Real(yv));
            assert_eq!(eval(&arena, neg, &m).unwrap(), Value::Real(-xv));
            assert_eq!(eval(&arena, add, &m).unwrap(), Value::Real(xv + yv));
            assert_eq!(eval(&arena, sub, &m).unwrap(), Value::Real(xv - yv));
            assert_eq!(eval(&arena, mul, &m).unwrap(), Value::Real(xv * yv));
            assert_eq!(eval(&arena, lt, &m).unwrap(), Value::Bool(xv < yv));
            assert_eq!(eval(&arena, le, &m).unwrap(), Value::Bool(xv <= yv));
            assert_eq!(eval(&arena, gt, &m).unwrap(), Value::Bool(xv > yv));
            assert_eq!(eval(&arena, ge, &m).unwrap(), Value::Bool(xv >= yv));
        }
    }
}

// ----- quantifiers (ADR-0016) -------------------------------------------

#[test]
fn boolean_quantifiers_enumerate() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let p_sym = a.declare("p", Sort::Bool).unwrap();
    let p = a.var(p_sym);
    let np = a.not(p).unwrap();
    let tautology = a.or(p, np).unwrap();

    // forall p. (p or not p) is true; forall p. p is false.
    let all_taut = a.forall(p_sym, tautology).unwrap();
    assert_eq!(eval(&a, all_taut, &asg).unwrap(), Value::Bool(true));
    let all_p = a.forall(p_sym, p).unwrap();
    assert_eq!(eval(&a, all_p, &asg).unwrap(), Value::Bool(false));
    // exists p. p is true.
    let some_p = a.exists(p_sym, p).unwrap();
    assert_eq!(eval(&a, some_p, &asg).unwrap(), Value::Bool(true));
}

#[test]
fn bitvector_quantifiers_range_over_all_values() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let x_sym = a.declare("x", Sort::BitVec(3)).unwrap();
    let x = a.var(x_sym);
    let zero = a.bv_const(3, 0).unwrap();
    let three = a.bv_const(3, 3).unwrap();

    // forall x. x + 0 == x  (true for all 3-bit x).
    let sum = a.bv_add(x, zero).unwrap();
    let idem = a.eq(sum, x).unwrap();
    let all_idem = a.forall(x_sym, idem).unwrap();
    assert_eq!(eval(&a, all_idem, &asg).unwrap(), Value::Bool(true));

    // exists x. x == 3  (true); forall x. x == 3 (false).
    let is_three = a.eq(x, three).unwrap();
    let some_three = a.exists(x_sym, is_three).unwrap();
    assert_eq!(eval(&a, some_three, &asg).unwrap(), Value::Bool(true));
    let all_three = a.forall(x_sym, is_three).unwrap();
    assert_eq!(eval(&a, all_three, &asg).unwrap(), Value::Bool(false));
}

#[test]
fn nested_quantifiers_evaluate() {
    // forall x:BV2. exists y:BV2. x == y  is true.
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let x_sym = a.declare("x", Sort::BitVec(2)).unwrap();
    let y_sym = a.declare("y", Sort::BitVec(2)).unwrap();
    let x = a.var(x_sym);
    let y = a.var(y_sym);
    let eq = a.eq(x, y).unwrap();
    let inner = a.exists(y_sym, eq).unwrap();
    let outer = a.forall(x_sym, inner).unwrap();
    assert_eq!(eval(&a, outer, &asg).unwrap(), Value::Bool(true));

    // forall x. forall y. x == y  is false.
    let inner_all = a.forall(y_sym, eq).unwrap();
    let outer_all = a.forall(x_sym, inner_all).unwrap();
    assert_eq!(eval(&a, outer_all, &asg).unwrap(), Value::Bool(false));
}

#[test]
fn quantifier_over_infinite_domain_is_an_error() {
    // Reals cannot be enumerated by the evaluator.
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let r_sym = a.declare("r", Sort::Real).unwrap();
    let r = a.var(r_sym);
    let zero = a.real_ratio(0, 1);
    let ge = a.real_ge(r, zero).unwrap();
    let all = a.forall(r_sym, ge).unwrap();
    assert!(matches!(
        eval(&a, all, &asg),
        Err(IrError::UnsupportedQuantifierDomain(Sort::Real))
    ));
}

#[test]
fn real_constant_arithmetic_evaluates_exactly() {
    // 1/3 + 1/6 == 1/2, checked through the evaluator on constants.
    let mut arena = TermArena::new();
    let third = arena.real_ratio(1, 3);
    let sixth = arena.real_ratio(1, 6);
    let sum = arena.real_add(third, sixth).unwrap();
    let asg = Assignment::new();
    assert_eq!(eval(&arena, sum, &asg).unwrap(), real(1, 2));
}

// ----- integer Euclidean div/mod/abs (SMT-LIB semantics) -----------------

#[test]
fn int_div_mod_abs_euclidean_semantics() {
    let mut a = TermArena::new();
    let asg = Assignment::new();
    let eval_int = |a: &mut TermArena, t| match eval(a, t, &asg) {
        Ok(Value::Int(v)) => v,
        other => panic!("expected Int, got {other:?}"),
    };
    let int = |a: &mut TermArena, v: i128| a.int_const(v);
    // (dividend, divisor, expected_div, expected_mod) — SMT-LIB Euclidean: 0<=mod<|b|.
    let cases: [(i128, i128, i128, i128); 8] = [
        (7, 3, 2, 1),
        (-7, 3, -3, 2),
        (7, -3, -2, 1),
        (-7, -3, 3, 2),
        (6, 3, 2, 0),
        (0, 5, 0, 0),
        (5, 0, 0, 5),   // convention: div a 0 = 0, mod a 0 = a
        (-5, 0, 0, -5),
    ];
    for (x, y, ed, em) in cases {
        let xt = int(&mut a, x);
        let yt = int(&mut a, y);
        let d = a.int_div(xt, yt).unwrap();
        let m = a.int_mod(xt, yt).unwrap();
        assert_eq!(eval_int(&mut a, d), ed, "div({x},{y})");
        assert_eq!(eval_int(&mut a, m), em, "mod({x},{y})");
        // the defining identity a = b*div + mod holds
        if y != 0 {
            assert_eq!(y * ed + em, x, "identity for ({x},{y})");
            assert!((0..y.abs()).contains(&em), "0<=mod<|b| for ({x},{y})");
        }
    }
    // abs
    for v in [-5i128, 0, 7] {
        let vt = int(&mut a, v);
        let av = a.int_abs(vt).unwrap();
        assert_eq!(eval_int(&mut a, av), v.abs(), "abs({v})");
    }
}
