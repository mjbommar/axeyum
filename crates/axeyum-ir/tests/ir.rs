//! Unit and exhaustive small-width tests for the term IR and evaluator.
//!
//! Per the bv-semantics note, operators with edge cases are tested
//! exhaustively at small widths, not just on sampled inputs.

use axeyum_ir::{
    Assignment, BIT_VECTOR_WIRE_ORDER, BitOrder, IrError, Sort, TermArena, Value,
    bv_value_to_lsb_bits, eval, lsb_bits_to_bv_value, lsb_bits_to_value, value_to_lsb_bits,
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
        let bits = value_to_lsb_bits(value).unwrap();
        assert_eq!(lsb_bits_to_value(value.sort(), &bits).unwrap(), value);
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
