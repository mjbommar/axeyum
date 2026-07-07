//! SMT-LIB-style rendering of terms.
//!
//! This is the stable debug format (performance note: debug renderers are
//! separate from canonical serialization, which does not exist yet).

use std::collections::HashMap;

use crate::arena::TermArena;
use crate::term::{Op, TermId, TermNode};

/// Operator name in SMT-LIB concrete syntax.
fn op_name(op: Op) -> String {
    match op {
        Op::BoolNot => "not".into(),
        Op::BoolAnd => "and".into(),
        Op::BoolOr => "or".into(),
        Op::BoolXor => "xor".into(),
        Op::BoolImplies => "=>".into(),
        Op::BvNot => "bvnot".into(),
        Op::BvAnd => "bvand".into(),
        Op::BvOr => "bvor".into(),
        Op::BvXor => "bvxor".into(),
        Op::BvNand => "bvnand".into(),
        Op::BvNor => "bvnor".into(),
        Op::BvXnor => "bvxnor".into(),
        Op::BvNeg => "bvneg".into(),
        Op::BvAdd => "bvadd".into(),
        Op::BvSub => "bvsub".into(),
        Op::BvMul => "bvmul".into(),
        Op::BvUdiv => "bvudiv".into(),
        Op::BvUrem => "bvurem".into(),
        Op::BvSdiv => "bvsdiv".into(),
        Op::BvSrem => "bvsrem".into(),
        Op::BvSmod => "bvsmod".into(),
        Op::BvShl => "bvshl".into(),
        Op::BvLshr => "bvlshr".into(),
        Op::BvAshr => "bvashr".into(),
        Op::BvUlt => "bvult".into(),
        Op::BvUle => "bvule".into(),
        Op::BvUgt => "bvugt".into(),
        Op::BvUge => "bvuge".into(),
        Op::BvSlt => "bvslt".into(),
        Op::BvSle => "bvsle".into(),
        Op::BvSgt => "bvsgt".into(),
        Op::BvSge => "bvsge".into(),
        Op::Eq => "=".into(),
        Op::Ite => "ite".into(),
        Op::BvComp => "bvcomp".into(),
        Op::Extract { hi, lo } => format!("(_ extract {hi} {lo})"),
        Op::Concat => "concat".into(),
        Op::ZeroExt { by } => format!("(_ zero_extend {by})"),
        Op::SignExt { by } => format!("(_ sign_extend {by})"),
        Op::RotateLeft { by } => format!("(_ rotate_left {by})"),
        Op::RotateRight { by } => format!("(_ rotate_right {by})"),
        Op::Select => "select".into(),
        Op::Store => "store".into(),
        Op::ConstArray { .. } => "const".into(),
        Op::IntToReal => "to_real".into(),
        Op::RealToInt => "to_int".into(),
        Op::RealIsInt => "is_int".into(),
        Op::Bv2Nat => "bv2nat".into(),
        Op::Int2Bv { width } => format!("(_ int2bv {width})"),
        Op::FpFromBits { exp, sig } => format!("(_ to_fp {exp} {sig})"),
        // The function name needs the arena; handled in `render` directly.
        Op::Apply(func) => format!("!fn{}", func.index()),
        Op::IntNeg | Op::IntSub | Op::RealNeg | Op::RealSub => "-".into(),
        Op::IntAdd | Op::RealAdd => "+".into(),
        Op::IntMul | Op::RealMul => "*".into(),
        Op::RealDiv => "/".into(),
        Op::IntDiv => "div".into(),
        Op::IntMod => "mod".into(),
        Op::IntAbs => "abs".into(),
        Op::IntPow2 => "int.pow2".into(),
        Op::IntLt | Op::RealLt => "<".into(),
        Op::IntLe | Op::RealLe => "<=".into(),
        Op::IntGt | Op::RealGt => ">".into(),
        Op::IntGe | Op::RealGe => ">=".into(),
        // The bound variable name needs the arena; handled in `render`.
        Op::Forall(_) => "forall".into(),
        Op::Exists(_) => "exists".into(),
        // Datatype ops (ADR-0022).
        Op::DtConstruct { constructor, .. } => format!("!construct{}", constructor.index()),
        Op::DtSelect { constructor, index } => format!("!select{}_{index}", constructor.index()),
        Op::DtTest(constructor) => format!("!is{}", constructor.index()),
        // Sequences (ADR-0051, P2.7). `seq.empty` is a nullary constant; SMT-LIB
        // spells it `(as seq.empty (Seq ...))`, but the element sort needs the
        // whole term, so this operator-name view renders the bare `seq.empty`.
        Op::SeqLen => "str.len".into(),
        Op::SeqEmpty(_) => "seq.empty".into(),
        Op::SeqUnit => "seq.unit".into(),
        Op::SeqConcat => "str.++".into(),
    }
}

/// Renders `term` as an SMT-LIB-style s-expression.
///
/// Shared subterms are expanded in place (no `let`), so output size can be
/// exponential in pathological DAGs; this is a debug surface, not a
/// serializer.
///
/// # Panics
///
/// Panics if `term` does not belong to `arena`.
pub fn render(arena: &TermArena, term: TermId) -> String {
    // Iterative post-order with memoized strings, mirroring the evaluator.
    let mut memo: HashMap<TermId, String> = HashMap::new();
    let mut stack: Vec<(TermId, bool)> = vec![(term, false)];
    while let Some((t, children_ready)) = stack.pop() {
        if memo.contains_key(&t) {
            continue;
        }
        match arena.node(t) {
            TermNode::BoolConst(b) => {
                memo.insert(t, b.to_string());
            }
            TermNode::BvConst { width, value } => {
                memo.insert(t, format!("(_ bv{value} {width})"));
            }
            TermNode::WideBvConst(w) => {
                // MSB-first binary literal (the value may exceed u128).
                let mut s = String::from("#b");
                for i in (0..w.width()).rev() {
                    s.push(if w.bit(i) { '1' } else { '0' });
                }
                memo.insert(t, s);
            }
            TermNode::IntConst(value) => {
                // SMT-LIB renders negative integers as `(- n)`.
                if *value < 0 {
                    memo.insert(t, format!("(- {})", value.unsigned_abs()));
                } else {
                    memo.insert(t, value.to_string());
                }
            }
            TermNode::RealConst(value) => {
                // SMT-LIB rationals: `(/ n d)`, or `(- ...)` for negatives.
                let num = value.numerator();
                let den = value.denominator();
                let magnitude = if den == 1 {
                    num.unsigned_abs().to_string()
                } else {
                    format!("(/ {} {den})", num.unsigned_abs())
                };
                if num < 0 {
                    memo.insert(t, format!("(- {magnitude})"));
                } else {
                    memo.insert(t, magnitude);
                }
            }
            TermNode::Symbol(s) => {
                memo.insert(t, arena.symbol(*s).0.to_owned());
            }
            TermNode::App { op, args } => {
                if children_ready {
                    // Quantifiers render in SMT-LIB binder form:
                    // `(forall ((x Sort)) body)`.
                    if let Op::Forall(var) | Op::Exists(var) = op {
                        let (name, sort) = arena.symbol(*var);
                        let keyword = if matches!(op, Op::Forall(_)) {
                            "forall"
                        } else {
                            "exists"
                        };
                        memo.insert(
                            t,
                            format!("({keyword} (({name} {sort})) {})", memo[&args[0]]),
                        );
                        continue;
                    }
                    let mut out = String::from("(");
                    match op {
                        Op::Apply(func) => out.push_str(arena.function(*func).0),
                        _ => out.push_str(&op_name(*op)),
                    }
                    for a in args {
                        out.push(' ');
                        out.push_str(&memo[a]);
                    }
                    out.push(')');
                    memo.insert(t, out);
                } else {
                    stack.push((t, true));
                    for &a in &**args {
                        stack.push((a, false));
                    }
                }
            }
        }
    }
    memo.remove(&term).expect("root term rendered")
}
