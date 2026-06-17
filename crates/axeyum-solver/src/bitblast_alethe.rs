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
//! The emitter now also covers the **arithmetic-add** (`bvadd`, `bvneg`),
//! **comparison** (`bvult`, `bvslt`), and **equality** (`bvcomp`, plus
//! bit-vector `=`) operators. These produce three distinct conclusion shapes:
//!
//! 1. **Term op → `(= <t> (@bbterm b0 … b_{n-1}))`** — `bvadd`, `bvneg`, and the
//!    bitwise ops; the right-hand side is a `@bbterm` of per-bit Booleans.
//! 2. **Predicate op → `(= <pred> <bool>)`** — `bvult`, `bvslt`, and bit-vector
//!    `=`; the right-hand side is a single Boolean formula (no `@bbterm`).
//! 3. **`bvcomp` → `(= (bvcomp x y) (@bbterm <bool>))`** — a 1-bit BV result, so
//!    the single Boolean is wrapped in `@bbterm`.
//!
//! The emitter additionally covers the **multiplier** (`bvmul`, shift-add) and
//! the structural operators **`extract`**, **`concat`**, and **`sign_extend`** —
//! all of which produce conclusion shape 1 (`(= <t> (@bbterm …))`).
//!
//! Anything still outside this set — shifts (`bvshl`/`bvlshr`/`bvashr`),
//! division/remainder (`bvudiv`/`bvurem`/…), `zero_extend`, rotates, non-bit-vector
//! terms, and the full-refutation bridge — is a later increment and yields
//! [`None`]. The shift and div/rem reconstructions are Carcara holes, deferred to
//! the in-house miter certificate.

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

/// The literal Boolean constant `false`/`true`, emitted verbatim (Carcara
/// compares structurally and does not simplify these away).
fn bool_const(value: bool) -> AletheTerm {
    AletheTerm::Const(if value { "true" } else { "false" }.to_owned())
}

/// The size-`size` per-bit term vector for an operand, mirroring Carcara's
/// `build_term_vec`: if `term` is already a `(@bbterm …)` its argument bits are
/// returned directly; otherwise the `i`-th bit is the projection
/// `((_ @bit_of i) term)`.
fn build_term_vec(term: &AletheTerm, size: usize) -> Vec<AletheTerm> {
    if let AletheTerm::App(head, args) = term {
        if head == "@bbterm" {
            return args.clone();
        }
    }
    (0..size).map(|i| bit_of(i, term)).collect()
}

/// `(and a b)`.
fn and2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("and".to_owned(), vec![a, b])
}

/// `(or a b)`.
fn or2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("or".to_owned(), vec![a, b])
}

/// `(xor a b)`.
fn xor2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("xor".to_owned(), vec![a, b])
}

/// `(not a)`.
fn not1(a: AletheTerm) -> AletheTerm {
    AletheTerm::App("not".to_owned(), vec![a])
}

/// `(= a b)` (Boolean or per-bit equality, depending on operands).
fn eq2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![a, b])
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
            let rendered = args
                .iter()
                .map(|&arg| bv_term_to_alethe(arena, arg))
                .collect::<Option<Vec<_>>>()?;
            match op {
                // Indexed operators render with the `((_ op i…) args…)` surface
                // syntax Carcara's parser expects.
                Op::Extract { hi, lo } => Some(AletheTerm::Indexed {
                    op: "extract".to_owned(),
                    indices: vec![i128::from(*hi), i128::from(*lo)],
                    args: rendered,
                }),
                Op::SignExt { by } => Some(AletheTerm::Indexed {
                    op: "sign_extend".to_owned(),
                    indices: vec![i128::from(*by)],
                    args: rendered,
                }),
                _ => {
                    let head = covered_head(*op)?;
                    Some(AletheTerm::App(head.to_owned(), rendered))
                }
            }
        }
        _ => None,
    }
}

/// The SMT-LIB head spelling for an operator the emitter can render, or [`None`]
/// if `op` is outside the covered set. Covers the bitwise fragment plus the
/// arithmetic-add, comparison, and equality operators handled here; bit-vector
/// equality (`Op::Eq`) renders as `=`.
fn covered_head(op: Op) -> Option<&'static str> {
    match op {
        Op::BvNot => Some("bvnot"),
        Op::BvAnd => Some("bvand"),
        Op::BvOr => Some("bvor"),
        Op::BvXor => Some("bvxor"),
        Op::BvXnor => Some("bvxnor"),
        Op::BvAdd => Some("bvadd"),
        Op::BvNeg => Some("bvneg"),
        Op::BvUlt => Some("bvult"),
        Op::BvSlt => Some("bvslt"),
        Op::BvComp => Some("bvcomp"),
        Op::BvMul => Some("bvmul"),
        Op::Concat => Some("concat"),
        Op::Eq => Some("="),
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

/// Builds the `(step <id> (cl (= <pred> <bool>)) :rule <rule>)` command for a
/// predicate operator whose bit-blasting yields a single Boolean formula (no
/// `@bbterm` wrapper): `bvult`, `bvslt`, and bit-vector `=`.
fn predicate_step(rule: &str, lhs: AletheTerm, result: AletheTerm, step_id: &str) -> AletheCommand {
    let equality = eq2(lhs, result);
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
/// - **`bvadd`** (`n`-ary, left fold via ripple-carry): `b_i = (xor (xor x_i
///   y_i) c_i)` with `c_0 = false` and the recurrence `c_i = (or (and x_{i-1}
///   y_{i-1}) (and (xor x_{i-1} y_{i-1}) c_{i-1}))`; rule `bitblast_add`.
/// - **`bvneg`** (unary): the ripple-carry adder of `(bvnot x)` and `0` with
///   `c_0 = true`, emitted verbatim with literal `false` constants; rule
///   `bitblast_neg`.
/// - **`bvult`/`bvslt`** (predicates → `(= <pred> <bool>)`): the unsigned/signed
///   less-than ladder; rules `bitblast_ult`/`bitblast_slt`.
/// - **bit-vector `=`** (predicate → `(= (= x y) <bool>)`): the per-bit AND of
///   `(= x_i y_i)`; rule `bitblast_equal`.
/// - **`bvcomp`** (1-bit BV → `(= (bvcomp x y) (@bbterm <bool>))`): the same
///   per-bit AND, wrapped in `@bbterm`; rule `bitblast_comp`.
/// - **`bvmul`** (`n`-ary, left fold via the shift-add multiplier): rule
///   `bitblast_mult`. Width-1 yields `(@bbterm (and y0 x0))`.
/// - **`extract`** (`((_ extract i j) x)` → bits `j..=i` of `x`): rule
///   `bitblast_extract`.
/// - **`concat`** (`(concat a b)` with `a` high): the low operand's bits first,
///   then the high operand's; rule `bitblast_concat`.
/// - **`sign_extend`** (`((_ sign_extend i) x)`): `x`'s bits then `i` copies of
///   the sign bit; rule `bitblast_sign_extend`. For `i == 0` Carcara's rule
///   returns the operand `x` itself, so the conclusion is the plain
///   `(= ((_ sign_extend 0) x) x)` (no `@bbterm`).
///
/// Returns [`None`] for any operator still outside the covered set — the shifts
/// (`bvshl`/`bvlshr`/`bvashr`), division/remainder, `zero_extend`, rotates — for a
/// non-bit-vector, non-predicate term, for a wide (`> 128`-bit) constant, or for a
/// malformed application. Those are later increments and deliberately not handled.
///
/// # Panics
///
/// Panics only on arena corruption (a bit width or index exceeding the integer
/// range used for the indexed-operator literals), which cannot occur for
/// well-formed terms.
#[must_use]
pub fn bitblast_step(arena: &TermArena, term: TermId, step_id: &str) -> Option<AletheCommand> {
    match arena.node(term) {
        TermNode::Symbol(_) => {
            let width = bv_width(arena, term)? as usize;
            let lhs = bv_term_to_alethe(arena, term)?;
            let bits = (0..width).map(|i| bit_of(i, &lhs)).collect();
            Some(bbterm_step("bitblast_var", lhs, bits, step_id))
        }
        TermNode::BvConst { width: w, value } => {
            let value = *value;
            let width = *w as usize;
            let lhs = bv_term_to_alethe(arena, term)?;
            let bits = (0..width)
                .map(|i| bool_const((value >> i) & 1 == 1))
                .collect();
            Some(bbterm_step("bitblast_const", lhs, bits, step_id))
        }
        TermNode::App { op, args } => bitblast_app(arena, term, *op, args, step_id),
        _ => None,
    }
}

/// Emits the step for a covered-operator application. Split out so
/// [`bitblast_step`] stays readable. Dispatches into the three conclusion shapes:
/// term ops (`@bbterm` of bits), predicate ops (single Boolean), and `bvcomp`
/// (single Boolean wrapped in `@bbterm`).
fn bitblast_app(
    arena: &TermArena,
    term: TermId,
    op: Op,
    args: &[TermId],
    step_id: &str,
) -> Option<AletheCommand> {
    // Render the operand bit-vectors once; each must itself be a covered term so
    // the rendered `<T>` matches the declared SMT-LIB problem.
    let rendered_args = args
        .iter()
        .map(|&arg| bv_term_to_alethe(arena, arg))
        .collect::<Option<Vec<_>>>()?;
    let lhs = bv_term_to_alethe(arena, term)?;

    // The bit width comes from operand 0 (a bit-vector for every covered op,
    // including the predicates whose own result sort is Bool).
    let width = bv_width(arena, *args.first()?)? as usize;

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
        Op::BvAdd => add_step(&rendered_args, lhs, width, step_id),
        Op::BvMul => mult_step(&rendered_args, lhs, width, step_id),
        Op::BvNeg => neg_step(&rendered_args, lhs, width, step_id),
        Op::Extract { hi, lo } => extract_step(&rendered_args, lhs, hi, lo, step_id),
        Op::Concat => concat_step(arena, args, &rendered_args, lhs, step_id),
        Op::SignExt { by } => sign_extend_step(&rendered_args, lhs, width, by, step_id),
        Op::BvUlt => {
            let [x, y] = rendered_args.as_slice() else {
                return None;
            };
            let result = ult_ladder(x, y, width)?;
            Some(predicate_step("bitblast_ult", lhs, result, step_id))
        }
        Op::BvSlt => {
            let [x, y] = rendered_args.as_slice() else {
                return None;
            };
            let result = slt_ladder(x, y, width)?;
            Some(predicate_step("bitblast_slt", lhs, result, step_id))
        }
        Op::Eq => {
            // Bit-vector equality only: per-bit `(= x_i y_i)` AND-folded into a
            // single Boolean. Non-bit-vector equality is not a `bitblast_equal`.
            let [x, y] = rendered_args.as_slice() else {
                return None;
            };
            let result = bitwise_equal_and(x, y, width);
            Some(predicate_step("bitblast_equal", lhs, result, step_id))
        }
        Op::BvComp => {
            // Same per-bit AND as equality, but the 1-bit BV result wraps the
            // single Boolean in `@bbterm`.
            let [x, y] = rendered_args.as_slice() else {
                return None;
            };
            let result = bitwise_equal_and(x, y, width);
            Some(bbterm_step("bitblast_comp", lhs, vec![result], step_id))
        }
        _ => None,
    }
}

/// The `bitblast_add` step (shape 1): `(bvadd …)` folded left via ripple-carry.
/// The accumulator is a `@bbterm`, so each later fold's `build_term_vec` returns
/// its bits directly (no `@bit_of` projection), mirroring Carcara's `add` loop.
fn add_step(
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    width: usize,
    step_id: &str,
) -> Option<AletheCommand> {
    let (first, rest) = rendered_args.split_first()?;
    let mut acc = first.clone();
    for y in rest {
        let bits = ripple_carry_bits(&acc, y, width);
        acc = AletheTerm::App("@bbterm".to_owned(), bits);
    }
    // `acc` is now the final `@bbterm`; its args are the result bits. A
    // single-operand bvadd would leave `acc` as operand 0; the IR builders never
    // produce that, so reject defensively.
    let AletheTerm::App(_, bits) = acc else {
        return None;
    };
    Some(bbterm_step("bitblast_add", lhs, bits, step_id))
}

/// The `bitblast_mult` step (shape 1): `(bvmul …)` folded left via the
/// shift-add multiplier. Like `add_step`, the accumulator is a `@bbterm`, so
/// each later fold's `build_term_vec` returns its bits directly.
fn mult_step(
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    width: usize,
    step_id: &str,
) -> Option<AletheCommand> {
    let (first, rest) = rendered_args.split_first()?;
    let mut acc = first.clone();
    for y in rest {
        let bits = shift_add_multiplier_bits(&acc, y, width);
        acc = AletheTerm::App("@bbterm".to_owned(), bits);
    }
    // A single-operand bvmul cannot arise from the IR builders; reject defensively.
    let AletheTerm::App(_, bits) = acc else {
        return None;
    };
    Some(bbterm_step("bitblast_mult", lhs, bits, step_id))
}

/// The shift-add multiplier result bits for `(bvmul x y)` over `size` bits,
/// transcribing Carcara's `shift_add_multiplier` verbatim (bit order, the
/// literal `false` fill, and the nesting all match structurally):
///
/// - `shift[j][i] = (and y_j x_{i-j})` when `j <= i`, else `false`;
/// - `res[0][i] = shift[0][i]`;
/// - for `j` in `1..size`: `carry[j][0] = false`, then for `i` in `1..size`
///   `carry[j][i] = (or (and res[j-1][i-1] shift[j][i-1]) (and (xor …) carry[j][i-1]))`
///   when `j < i`, else `false`; and `res[j][i]` is `shift[0][0]` at `i == 0`,
///   `res[i][i]` when `j > i`, else `(xor (xor res[j-1][i] shift[j][i]) carry[j][i])`.
///
/// The result is `res[size-1]`.
fn shift_add_multiplier_bits(x: &AletheTerm, y: &AletheTerm, size: usize) -> Vec<AletheTerm> {
    let xb = build_term_vec(x, size);
    let yb = build_term_vec(y, size);

    let shift: Vec<Vec<AletheTerm>> = (0..size)
        .map(|j| {
            (0..size)
                .map(|i| {
                    if j <= i {
                        and2(yb[j].clone(), xb[i - j].clone())
                    } else {
                        bool_const(false)
                    }
                })
                .collect()
        })
        .collect();

    let mut res: Vec<Vec<AletheTerm>> = vec![(0..size).map(|i| shift[0][i].clone()).collect()];

    for j in 1..size {
        // Carry row for round j: index 0 is false, then i in 1..size.
        let mut carry_j = vec![bool_const(false)];
        for i in 1..size {
            let c = if j < i {
                or2(
                    and2(res[j - 1][i - 1].clone(), shift[j][i - 1].clone()),
                    and2(
                        xor2(res[j - 1][i - 1].clone(), shift[j][i - 1].clone()),
                        carry_j[i - 1].clone(),
                    ),
                )
            } else {
                bool_const(false)
            };
            carry_j.push(c);
        }
        // Result row for round j.
        let res_j: Vec<AletheTerm> = (0..size)
            .map(|i| {
                if i == 0 {
                    shift[0][0].clone()
                } else if j > i {
                    res[i][i].clone()
                } else {
                    xor2(
                        xor2(res[j - 1][i].clone(), shift[j][i].clone()),
                        carry_j[i].clone(),
                    )
                }
            })
            .collect();
        res.push(res_j);
    }

    res[size - 1].clone()
}

/// The `bitblast_extract` step (shape 1): `((_ extract i j) x)` bit-blasts to
/// `x`'s bits `j..=i`, LSB-first.
fn extract_step(
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    hi: u32,
    lo: u32,
    step_id: &str,
) -> Option<AletheCommand> {
    let [x] = rendered_args else {
        return None;
    };
    let bits = (lo..=hi).map(|i| bit_of(i as usize, x)).collect();
    Some(bbterm_step("bitblast_extract", lhs, bits, step_id))
}

/// The `bitblast_sign_extend` step: `((_ sign_extend i) x)` bit-blasts to `x`'s
/// bits then `i` copies of the sign bit. For `i == 0` Carcara's rule returns the
/// operand `x` itself (a plain `(= ((_ sign_extend 0) x) x)`, no `@bbterm`).
fn sign_extend_step(
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    width: usize,
    by: u32,
    step_id: &str,
) -> Option<AletheCommand> {
    let [x] = rendered_args else {
        return None;
    };
    if by == 0 {
        return Some(predicate_step(
            "bitblast_sign_extend",
            lhs,
            x.clone(),
            step_id,
        ));
    }
    let mut bits = build_term_vec(x, width);
    let sign = bits.last()?.clone();
    for _ in 0..by {
        bits.push(sign.clone());
    }
    Some(bbterm_step("bitblast_sign_extend", lhs, bits, step_id))
}

/// The `bitblast_concat` step (shape 1): `(concat a1 … an)` bit-blasts to the
/// per-bit concatenation built **last argument first** (the low/rightmost
/// operand), then each earlier operand, matching Carcara's `concat`. `args` are
/// the IR operand ids (for their widths); `rendered_args` their Alethe forms.
fn concat_step(
    arena: &TermArena,
    args: &[TermId],
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    step_id: &str,
) -> Option<AletheCommand> {
    if rendered_args.is_empty() {
        return None;
    }
    let mut bits = Vec::new();
    // Last operand (low bits) first, then towards the first (high bits).
    for (rendered, &arg) in rendered_args.iter().zip(args.iter()).rev() {
        let w = bv_width(arena, arg)? as usize;
        bits.extend(build_term_vec(rendered, w));
    }
    Some(bbterm_step("bitblast_concat", lhs, bits, step_id))
}

/// The `bitblast_neg` step (shape 1): the ripple-carry adder of `(not x)` and
/// `0` with carry-in `true`, emitted verbatim with literal `false` constants per
/// Carcara's `neg`. Carries: `c_0 = true`,
/// `c_i = (or (and (not x_{i-1}) false) (and (xor (not x_{i-1}) false) c_{i-1}))`;
/// result bit `b_i = (xor (xor (not x_i) false) c_i)`.
fn neg_step(
    rendered_args: &[AletheTerm],
    lhs: AletheTerm,
    width: usize,
    step_id: &str,
) -> Option<AletheCommand> {
    let [x] = rendered_args else {
        return None;
    };
    let xb = build_term_vec(x, width);
    let mut carries = vec![bool_const(true)];
    for i in 1..width {
        let nx = not1(xb[i - 1].clone());
        let carry = or2(
            and2(nx.clone(), bool_const(false)),
            and2(xor2(nx, bool_const(false)), carries[i - 1].clone()),
        );
        carries.push(carry);
    }
    let bits = (0..width)
        .map(|i| {
            xor2(
                xor2(not1(xb[i].clone()), bool_const(false)),
                carries[i].clone(),
            )
        })
        .collect();
    Some(bbterm_step("bitblast_neg", lhs, bits, step_id))
}

/// The ripple-carry adder result bits for `(bvadd x y)` over `size` bits,
/// matching Carcara's `ripple_carry_adder`: `c_0 = false`,
/// `c_i = (or (and x_{i-1} y_{i-1}) (and (xor x_{i-1} y_{i-1}) c_{i-1}))`, and
/// `b_i = (xor (xor x_i y_i) c_i)`.
fn ripple_carry_bits(x: &AletheTerm, y: &AletheTerm, size: usize) -> Vec<AletheTerm> {
    let xb = build_term_vec(x, size);
    let yb = build_term_vec(y, size);

    let mut carries = vec![bool_const(false)];
    for i in 1..size {
        let carry = or2(
            and2(xb[i - 1].clone(), yb[i - 1].clone()),
            and2(
                xor2(xb[i - 1].clone(), yb[i - 1].clone()),
                carries[i - 1].clone(),
            ),
        );
        carries.push(carry);
    }
    (0..size)
        .map(|i| xor2(xor2(xb[i].clone(), yb[i].clone()), carries[i].clone()))
        .collect()
}

/// The unsigned less-than ladder for `(bvult x y)` over `size` bits, matching
/// Carcara's `ult`: base `(and (not x0) y0)`, then for `i` in `1..size`
/// `(or (and (= x_i y_i) r) (and (not x_i) y_i))`. Returns [`None`] for the
/// degenerate `size == 0` (which cannot arise for a well-formed bit-vector).
fn ult_ladder(x: &AletheTerm, y: &AletheTerm, size: usize) -> Option<AletheTerm> {
    let xb = build_term_vec(x, size);
    let yb = build_term_vec(y, size);
    let mut r = and2(not1(xb.first()?.clone()), yb[0].clone());
    for i in 1..size {
        r = or2(
            and2(eq2(xb[i].clone(), yb[i].clone()), r),
            and2(not1(xb[i].clone()), yb[i].clone()),
        );
    }
    Some(r)
}

/// The signed less-than ladder for `(bvslt x y)` over `size` bits, matching
/// Carcara's `slt`: width-1 is `(and x0 (not y0))`; otherwise the unsigned
/// ladder runs over `1..size-1`, then the final sign step at `k = size-1` is
/// `(or (and (= x_k y_k) r) (and x_k (not y_k)))`.
fn slt_ladder(x: &AletheTerm, y: &AletheTerm, size: usize) -> Option<AletheTerm> {
    let xb = build_term_vec(x, size);
    let yb = build_term_vec(y, size);
    if size == 1 {
        return Some(and2(xb.first()?.clone(), not1(yb[0].clone())));
    }
    let mut r = and2(not1(xb[0].clone()), yb[0].clone());
    for i in 1..(size - 1) {
        r = or2(
            and2(eq2(xb[i].clone(), yb[i].clone()), r),
            and2(not1(xb[i].clone()), yb[i].clone()),
        );
    }
    let k = size - 1;
    r = or2(
        and2(eq2(xb[k].clone(), yb[k].clone()), r),
        and2(xb[k].clone(), not1(yb[k].clone())),
    );
    Some(r)
}

/// The per-bit-equality AND used by both `bitblast_equal` and `bitblast_comp`:
/// `e_i = (= x_i y_i)`; the result is `(and e0 e1 …)` for `size > 1`, else `e0`.
fn bitwise_equal_and(x: &AletheTerm, y: &AletheTerm, size: usize) -> AletheTerm {
    let xb = build_term_vec(x, size);
    let yb = build_term_vec(y, size);
    let es: Vec<AletheTerm> = (0..size)
        .map(|i| eq2(xb[i].clone(), yb[i].clone()))
        .collect();
    if es.len() > 1 {
        AletheTerm::App("and".to_owned(), es)
    } else {
        es.into_iter().next().expect("size >= 1 for a bit-vector")
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
    fn width1_mult_is_a_single_and_gadget() {
        // Width-1 (bvmul a b): the `for j in 1..n` loop is empty, so the result is
        // just res[0][0] = shift[0][0] = (and b0 a0).
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 1);
        let b = bv_var(&mut arena, "b", 1);
        let prod = arena.bv_mul(a, b).expect("bvmul");
        let cmd = bitblast_step(&arena, prod, "s").expect("bvmul width-1 is covered");
        assert_eq!(rule_of(&cmd), "bitblast_mult");

        let bit = |name: &str| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![0],
            args: vec![AletheTerm::Const(name.to_owned())],
        };
        // shift[0][0] = (and y0 x0) = (and b0 a0).
        let expected_bit = AletheTerm::App("and".to_owned(), vec![bit("b"), bit("a")]);
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(bbterm_args, &vec![expected_bit]);
    }

    #[test]
    fn extract_step_projects_the_requested_bit_range() {
        // ((_ extract 2 1) x) over width 4: bits 1, 2 of x, LSB-first.
        let mut arena = TermArena::new();
        let x = bv_var(&mut arena, "x", 4);
        let ex = arena.extract(2, 1, x).expect("extract");
        let cmd = bitblast_step(&arena, ex, "s").expect("extract is covered");
        assert_eq!(rule_of(&cmd), "bitblast_extract");

        let bit = |i: i128| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const("x".to_owned())],
        };
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(bbterm_args, &vec![bit(1), bit(2)]);
    }

    #[test]
    fn concat_step_puts_low_operand_bits_first() {
        // (concat a b): a is high (width 2), b is low (width 3). Bits = b0 b1 b2 a0 a1.
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 2);
        let b = bv_var(&mut arena, "b", 3);
        let cat = arena.concat(a, b).expect("concat");
        let cmd = bitblast_step(&arena, cat, "s").expect("concat is covered");
        assert_eq!(rule_of(&cmd), "bitblast_concat");

        let bit = |i: i128, name: &str| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const(name.to_owned())],
        };
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(
            bbterm_args,
            &vec![
                bit(0, "b"),
                bit(1, "b"),
                bit(2, "b"),
                bit(0, "a"),
                bit(1, "a"),
            ]
        );
    }

    #[test]
    fn sign_extend_repeats_the_sign_bit() {
        // ((_ sign_extend 2) x) over width 3: x0 x1 x2, then two copies of x2.
        let mut arena = TermArena::new();
        let x = bv_var(&mut arena, "x", 3);
        let se = arena.sign_ext(2, x).expect("sign_extend");
        let cmd = bitblast_step(&arena, se, "s").expect("sign_extend is covered");
        assert_eq!(rule_of(&cmd), "bitblast_sign_extend");

        let bit = |i: i128| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const("x".to_owned())],
        };
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(bbterm_args, &vec![bit(0), bit(1), bit(2), bit(2), bit(2)]);
    }

    #[test]
    fn shift_is_still_outside_the_covered_set() {
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 4);
        let b = bv_var(&mut arena, "b", 4);
        let shl = arena.bv_shl(a, b).expect("bvshl");
        assert!(
            bitblast_step(&arena, shl, "s").is_none(),
            "shifts are a Carcara hole, not handled here"
        );
    }

    #[test]
    fn bool_equality_is_not_a_bitblast_equal() {
        // Equality over Bool operands has no bit width, so it is not a
        // `bitblast_equal` and must yield `None`.
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 4);
        let b = bv_var(&mut arena, "b", 4);
        let eq_bv = arena.eq(a, b).expect("eq"); // Bool sort over BV operands
        let nested = arena.eq(eq_bv, eq_bv).expect("eq over Bool");
        assert!(
            bitblast_step(&arena, nested, "s").is_none(),
            "equality over Bool operands is not a bit-vector equality"
        );
    }

    #[test]
    fn bitblast_add_width2_bits_match_ripple_carry() {
        // (bvadd a b) over width 2: bit0 = (xor (xor a0 b0) false),
        // bit1 = (xor (xor a1 b1) (or (and a0 b0) (and (xor a0 b0) false))).
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 2);
        let b = bv_var(&mut arena, "b", 2);
        let sum = arena.bv_add(a, b).expect("bvadd");
        let cmd = bitblast_step(&arena, sum, "s").expect("bvadd is covered");
        assert_eq!(rule_of(&cmd), "bitblast_add");

        let bit = |i: i128, name: &str| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const(name.to_owned())],
        };
        let f = || AletheTerm::Const("false".to_owned());
        let app = |h: &str, args: Vec<AletheTerm>| AletheTerm::App(h.to_owned(), args);

        let a0 = bit(0, "a");
        let b0 = bit(0, "b");
        let a1 = bit(1, "a");
        let b1 = bit(1, "b");
        let bit0 = app("xor", vec![app("xor", vec![a0.clone(), b0.clone()]), f()]);
        let carry1 = app(
            "or",
            vec![
                app("and", vec![a0.clone(), b0.clone()]),
                app("and", vec![app("xor", vec![a0, b0]), f()]),
            ],
        );
        let bit1 = app("xor", vec![app("xor", vec![a1, b1]), carry1]);

        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(bbterm_args, &vec![bit0, bit1]);
    }

    #[test]
    fn bitblast_equal_is_per_bit_and() {
        // (= a b) over width 2 → (and (= a0 b0) (= a1 b1)); no @bbterm wrapper.
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 2);
        let b = bv_var(&mut arena, "b", 2);
        let eq = arena.eq(a, b).expect("eq");
        let cmd = bitblast_step(&arena, eq, "s").expect("BV equality is covered");
        assert_eq!(rule_of(&cmd), "bitblast_equal");

        let bit = |i: i128, name: &str| AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const(name.to_owned())],
        };
        let eq2 = |x: AletheTerm, y: AletheTerm| AletheTerm::App("=".to_owned(), vec![x, y]);
        let expected_result = AletheTerm::App(
            "and".to_owned(),
            vec![eq2(bit(0, "a"), bit(0, "b")), eq2(bit(1, "a"), bit(1, "b"))],
        );
        // Conclusion is (= (= a b) <expected_result>) — a Bool-equality with no
        // @bbterm on the right.
        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        assert_eq!(&eq_args[1], &expected_result);
        assert!(
            !matches!(&eq_args[1], AletheTerm::App(h, _) if h == "@bbterm"),
            "bitblast_equal must not wrap its result in @bbterm"
        );
    }

    #[test]
    fn bitblast_comp_wraps_the_and_in_bbterm() {
        // (bvcomp a b) over width 2 → (= (bvcomp a b) (@bbterm (and (= a0 b0) (= a1 b1)))).
        let mut arena = TermArena::new();
        let a = bv_var(&mut arena, "a", 2);
        let b = bv_var(&mut arena, "b", 2);
        let comp = arena.bv_comp(a, b).expect("bvcomp");
        let cmd = bitblast_step(&arena, comp, "s").expect("bvcomp is covered");
        assert_eq!(rule_of(&cmd), "bitblast_comp");

        let AletheTerm::App(_, eq_args) = conclusion(&cmd) else {
            panic!("expected eq app");
        };
        let AletheTerm::App(head, bbterm_args) = &eq_args[1] else {
            panic!("expected bbterm app");
        };
        assert_eq!(head, "@bbterm");
        assert_eq!(bbterm_args.len(), 1, "bvcomp wraps a single Boolean");
        assert!(
            matches!(&bbterm_args[0], AletheTerm::App(h, _) if h == "and"),
            "the wrapped bit is the per-bit AND"
        );
    }
}
