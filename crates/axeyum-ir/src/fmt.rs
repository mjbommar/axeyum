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
            TermNode::Symbol(s) => {
                memo.insert(t, arena.symbol(*s).0.to_owned());
            }
            TermNode::App { op, args } => {
                if children_ready {
                    let mut out = String::from("(");
                    out.push_str(&op_name(*op));
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
