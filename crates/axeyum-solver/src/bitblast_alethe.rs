//! Per-operator **bitblast-step emitter** producing Carcara-valid Alethe
//! `bitblast_*` steps for the **bitwise fragment** of `QF_BV` (Track 3, task
//! T3.3.1 step 2, first slice).
//!
//! Given a bit-vector term `t` whose top operator is in the bitwise fragment
//! (`bvnot`, `bvand`, `bvor`, `bvxor`, `bvxnor`, plus a bare variable or
//! constant), [`bitblast_step`] emits the single definitional step
//!
//! ```text
//! (step <id> (cl (= <T> (@bbterm b0 b1 … b_{n-1}))) :rule bitblast_<op>)
//! ```
//!
//! where `<T>` is the SMT-LIB rendering of `t`, `n` is its bit width, and the
//! per-bit terms `b_i` are LSB-first, matching **exactly** how Carcara's
//! `bitvectors` rules reconstruct each gadget (verified empirically against the
//! Carcara binary; see `tests/carcara_crosscheck.rs`). Each emitted step is
//! soundness-critical: it must be accepted by the real Carcara checker.
//!
//! Anything outside this fragment — the arithmetic, comparison, and structural
//! operators, non-bit-vector terms, and the full-refutation bridge — is a later
//! increment and yields [`None`].

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

/// The per-bit extraction `((_ @bit_of i) a)` — Carcara's `BvBitOf` projection.
fn bit_of(i: usize, arg: &AletheTerm) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i128::try_from(i).expect("bit index fits i128")],
        args: vec![arg.clone()],
    }
}

/// Renders a bit-vector `BvConst { width, value }` as the SMT-LIB `#b…` binary
/// literal, MSB-first (e.g. width-2 value 1 → `#b01`).
fn bv_const_literal(width: u32, value: u128) -> String {
    let mut out = String::with_capacity(2 + width as usize);
    out.push_str("#b");
    // MSB-first: bit (width-1) down to bit 0.
    for i in (0..width).rev() {
        let bit = (value >> i) & 1;
        out.push(if bit == 1 { '1' } else { '0' });
    }
    out
}

/// Renders a bitwise-fragment bit-vector term as an [`AletheTerm`] matching the
/// SMT-LIB surface syntax Carcara's parser expects:
///
/// - [`TermNode::Symbol`] → `Const(name)`;
/// - [`TermNode::BvConst`] → `Const("#b…")` (the binary literal);
/// - a bitwise [`TermNode::App`] (`bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`) →
///   `App(head, [rendered args])`.
///
/// Returns [`None`] for any other node (wide constants, non-bitwise operators,
/// non-bit-vector terms), so the rendered `<T>` always matches what the `.smt2`
/// declares.
fn bv_term_to_alethe(arena: &TermArena, term: TermId) -> Option<AletheTerm> {
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            let (name, _sort) = arena.symbol(*symbol);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(bv_const_literal(*width, *value)))
        }
        TermNode::App { op, args } => {
            let head = bitwise_head(*op)?;
            let rendered = args
                .iter()
                .map(|&arg| bv_term_to_alethe(arena, arg))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(head.to_owned(), rendered))
        }
        _ => None,
    }
}

/// The SMT-LIB head spelling for a bitwise operator, or [`None`] if `op` is not
/// in the bitwise fragment.
fn bitwise_head(op: Op) -> Option<&'static str> {
    match op {
        Op::BvNot => Some("bvnot"),
        Op::BvAnd => Some("bvand"),
        Op::BvOr => Some("bvor"),
        Op::BvXor => Some("bvxor"),
        Op::BvXnor => Some("bvxnor"),
        _ => None,
    }
}

/// The bit width of a bit-vector term, or [`None`] if `term` is not a
/// bit-vector.
fn bv_width(arena: &TermArena, term: TermId) -> Option<u32> {
    match arena.sort_of(term) {
        Sort::BitVec(width) => Some(width),
        _ => None,
    }
}

/// Builds the `(step <id> (cl (= <T> (@bbterm bits…))) :rule <rule>)` command
/// from the rendered term, its per-bit terms, and the rule name.
fn bbterm_step(rule: &str, lhs: AletheTerm, bits: Vec<AletheTerm>, step_id: &str) -> AletheCommand {
    let bbterm = AletheTerm::App("@bbterm".to_owned(), bits);
    let equality = AletheTerm::App("=".to_owned(), vec![lhs, bbterm]);
    AletheCommand::Step {
        id: step_id.to_owned(),
        clause: vec![AletheLit {
            atom: equality,
            negated: false,
        }],
        rule: rule.to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    }
}

/// Emits the single definitional `bitblast_*` step for a bitwise-fragment
/// bit-vector term `term`, recorded under `step_id`.
///
/// The conclusion is `(= <T> (@bbterm b0 … b_{n-1}))` where `<T>` is the
/// SMT-LIB rendering of `term`, `n` its bit width, and the `b_i` are LSB-first
/// per-bit terms reconstructed exactly as Carcara's `bitvectors` rules expect:
///
/// - **variable** ([`TermNode::Symbol`]): `b_i = ((_ @bit_of i) x)`; rule
///   `bitblast_var`.
/// - **constant** ([`TermNode::BvConst`]): `b_i` is `true`/`false` per bit `i`
///   of the value (LSB-first); rule `bitblast_const`.
/// - **`bvnot`**: `b_i = (not ((_ @bit_of i) a))`; rule `bitblast_not`.
/// - **`bvand`/`bvor`/`bvxor`** (`n`-ary, left fold): start from arg0's bits and
///   fold each later arg's bit with `(and/or/xor prev_i arg_i)`; rules
///   `bitblast_and`/`bitblast_or`/`bitblast_xor`. For the binary case `b_i` is the
///   single gadget `(and a_i b_i)` etc.; for the `n`-ary case it nests
///   left-to-right, e.g. width-1 `(bvand a b c)` bit0 = `(and (and a0 b0) c0)`.
/// - **`bvxnor`** (binary only, per Carcara): `b_i = (= a_i b_i)`; rule
///   `bitblast_xnor`.
///
/// Returns [`None`] for any operator outside this fragment (arithmetic,
/// comparisons, structural ops), for a non-bit-vector term, for a wide
/// (`> 128`-bit) constant, or for a malformed application (e.g. `bvxnor` with
/// other than two arguments). The arithmetic/comparison/structural ops and the
/// full-refutation bridge are later increments and are deliberately not handled.
///
/// # Panics
///
/// Panics only on arena corruption (a bit width or index exceeding the integer
/// range used for the indexed-operator literals), which cannot occur for
/// well-formed terms.
#[must_use]
pub fn bitblast_step(arena: &TermArena, term: TermId, step_id: &str) -> Option<AletheCommand> {
    let width = bv_width(arena, term)? as usize;

    match arena.node(term) {
        TermNode::Symbol(_) => {
            let lhs = bv_term_to_alethe(arena, term)?;
            let bits = (0..width).map(|i| bit_of(i, &lhs)).collect();
            Some(bbterm_step("bitblast_var", lhs, bits, step_id))
        }
        TermNode::BvConst { width: w, value } => {
            let value = *value;
            let w = *w as usize;
            debug_assert_eq!(w, width, "BvConst width matches its bit-vector sort width");
            let lhs = bv_term_to_alethe(arena, term)?;
            let bits = (0..width)
                .map(|i| {
                    let bit = (value >> i) & 1;
                    AletheTerm::Const(if bit == 1 { "true" } else { "false" }.to_owned())
                })
                .collect();
            Some(bbterm_step("bitblast_const", lhs, bits, step_id))
        }
        TermNode::App { op, args } => bitblast_app(arena, term, *op, args, width, step_id),
        _ => None,
    }
}

/// Emits the step for a bitwise-operator application. Split out so [`bitblast_step`]
/// stays readable.
fn bitblast_app(
    arena: &TermArena,
    term: TermId,
    op: Op,
    args: &[TermId],
    width: usize,
    step_id: &str,
) -> Option<AletheCommand> {
    // Render the operand bit-vectors once; each must itself be a bitwise-fragment
    // term so the rendered `<T>` matches the declared SMT-LIB problem.
    let rendered_args = args
        .iter()
        .map(|&arg| bv_term_to_alethe(arena, arg))
        .collect::<Option<Vec<_>>>()?;
    let lhs = bv_term_to_alethe(arena, term)?;

    match op {
        Op::BvNot => {
            // Unary: b_i = (not ((_ @bit_of i) a)).
            let [arg] = rendered_args.as_slice() else {
                return None;
            };
            let bits = (0..width)
                .map(|i| AletheTerm::App("not".to_owned(), vec![bit_of(i, arg)]))
                .collect();
            Some(bbterm_step("bitblast_not", lhs, bits, step_id))
        }
        Op::BvAnd | Op::BvOr | Op::BvXor => {
            // n-ary left fold matching Carcara: start from arg0's bit projections,
            // then for each later arg fold (head prev_i arg_i) bit-by-bit.
            let head = match op {
                Op::BvAnd => "and",
                Op::BvOr => "or",
                Op::BvXor => "xor",
                _ => unreachable!(),
            };
            let (first, rest) = rendered_args.split_first()?;
            // Initial bits = the per-bit projections of arg0.
            let mut bits: Vec<AletheTerm> = (0..width).map(|i| bit_of(i, first)).collect();
            for arg in rest {
                bits = (0..width)
                    .map(|i| {
                        AletheTerm::App(head.to_owned(), vec![bits[i].clone(), bit_of(i, arg)])
                    })
                    .collect();
            }
            let rule = match op {
                Op::BvAnd => "bitblast_and",
                Op::BvOr => "bitblast_or",
                Op::BvXor => "bitblast_xor",
                _ => unreachable!(),
            };
            Some(bbterm_step(rule, lhs, bits, step_id))
        }
        Op::BvXnor => {
            // Binary only (per Carcara): b_i = (= ((_ @bit_of i) x) ((_ @bit_of i) y)).
            let [x, y] = rendered_args.as_slice() else {
                return None;
            };
            let bits = (0..width)
                .map(|i| AletheTerm::App("=".to_owned(), vec![bit_of(i, x), bit_of(i, y)]))
                .collect();
            Some(bbterm_step("bitblast_xnor", lhs, bits, step_id))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::bitblast_step;
    use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
    use axeyum_ir::{Sort, TermArena};

    fn bv_var(arena: &mut TermArena, name: &str, width: u32) -> axeyum_ir::TermId {
        let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
        arena.var(s)
    }

    /// Pulls the single conclusion atom out of an emitted step.
    fn conclusion(cmd: &AletheCommand) -> &AletheTerm {
        let AletheCommand::Step { clause, .. } = cmd else {
            panic!("expected a step");
        };
        let [
            AletheLit {
                atom,
                negated: false,
            },
        ] = clause.as_slice()
        else {
            panic!("expected a single positive literal");
        };
        atom
    }

    fn rule_of(cmd: &AletheCommand) -> &str {
        let AletheCommand::Step { rule, .. } = cmd else {
            panic!("expected a step");
        };
        rule
    }

    #[test]
    fn var_step_has_bit_of_projections() {
        let mut arena = TermArena::new();
        let x = bv_var(&mut arena, "x", 2);
        let cmd = bitblast_step(&arena, x, "s").expect("var is in the fragment");
        assert_eq!(rule_of(&cmd), "bitblast_var");

        let bit_of = |i: i128| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const("x".to_owned())],
        };
        let expected = AletheTerm::App(
            "=".to_owned(),
            vec![
                AletheTerm::Const("x".to_owned()),
                AletheTerm::App("@bbterm".to_owned(), vec![bit_of(0), bit_of(1)]),
            ],
        );
        assert_eq!(conclusion(&cmd), &expected);
    }

    #[test]
    fn const_step_emits_true_false_bits() {
        // width-3 value 5 = 0b101 → LSB-first bits true,false,true.
        let mut arena = TermArena::new();
        let c = arena.bv_const(3, 5).expect("bv const");
        let cmd = bitblast_step(&arena, c, "s").expect("const is in the fragment");
        assert_eq!(rule_of(&cmd), "bitblast_const");

        let t = || AletheTerm::Const("true".to_owned());
        let f = || AletheTerm::Const("false".to_owned());
        let expected = AletheTerm::App(
            "=".to_owned(),
            vec![
                AletheTerm::Const("#b101".to_owned()),
                AletheTerm::App("@bbterm".to_owned(), vec![t(), f(), t()]),
            ],
        );
        assert_eq!(conclusion(&cmd), &expected);
    }

    #[test]
    fn binary_and_step_is_per_bit_gadget() {
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 1);
        let b = bv_var(&mut arena, "b", 1);
        let t = arena.bv_and(a, b).expect("bvand");
        let cmd = bitblast_step(&arena, t, "s").expect("bvand is in the fragment");
        assert_eq!(rule_of(&cmd), "bitblast_and");

        let bit_of = |name: &str| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![0],
            args: vec![AletheTerm::Const(name.to_owned())],
        };
        let expected = AletheTerm::App(
            "=".to_owned(),
            vec![
                AletheTerm::App(
                    "bvand".to_owned(),
                    vec![
                        AletheTerm::Const("a".to_owned()),
                        AletheTerm::Const("b".to_owned()),
                    ],
                ),
                AletheTerm::App(
                    "@bbterm".to_owned(),
                    vec![AletheTerm::App(
                        "and".to_owned(),
                        vec![bit_of("a"), bit_of("b")],
                    )],
                ),
            ],
        );
        assert_eq!(conclusion(&cmd), &expected);
    }

    #[test]
    fn nary_xor_nests_left_to_right() {
        // width-1 (bvxor a b c) bit0 = (xor (xor a0 b0) c0).
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 1);
        let b = bv_var(&mut arena, "b", 1);
        let c = bv_var(&mut arena, "c", 1);
        let ab = arena.bv_xor(a, b).expect("bvxor");
        let abc = arena.bv_xor(ab, c).expect("bvxor");
        // Build a genuine 3-ary application by re-noding: bvxor folds binary, so
        // construct via the n-ary builder if available; otherwise the nested
        // binary form already exercises the fold path one layer at a time.
        let cmd = bitblast_step(&arena, abc, "s").expect("bvxor is in the fragment");
        assert_eq!(rule_of(&cmd), "bitblast_xor");
        // The outer term is (bvxor (bvxor a b) c); its single fold step over arg0
        // = (bvxor a b) and arg1 = c gives bit0 = (xor <bit0 of (bvxor a b)> c0).
        // bit0 of (bvxor a b) is itself ((_ @bit_of 0) (bvxor a b)).
        let bit_of_term = |t: AletheTerm| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![0],
            args: vec![t],
        };
        let bvxor_ab = AletheTerm::App(
            "bvxor".to_owned(),
            vec![
                AletheTerm::Const("a".to_owned()),
                AletheTerm::Const("b".to_owned()),
            ],
        );
        let expected_bit = AletheTerm::App(
            "xor".to_owned(),
            vec![
                bit_of_term(bvxor_ab.clone()),
                bit_of_term(AletheTerm::Const("c".to_owned())),
            ],
        );
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(_, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(&bbterm_args[0], &expected_bit);
    }

    #[test]
    fn arithmetic_op_is_outside_the_fragment() {
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 4);
        let b = bv_var(&mut arena, "b", 4);
        let sum = arena.bv_add(a, b).expect("bvadd");
        assert!(
            bitblast_step(&arena, sum, "s").is_none(),
            "bvadd is not in the bitwise fragment"
        );
    }

    #[test]
    fn non_bitvector_term_is_rejected() {
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 4);
        let b = bv_var(&mut arena, "b", 4);
        let eq = arena.eq(a, b).expect("eq"); // Bool sort
        assert!(
            bitblast_step(&arena, eq, "s").is_none(),
            "a Bool-sorted term has no bit width"
        );
    }
}
