//! Sharing-preserving SMT-LIB 2 script export.
//!
//! Shared interior nodes (fan-in > 1) are emitted as 0-ary `define-fun`s,
//! so output size is linear in the DAG — never the unfolded tree
//! (query-cost-control hard rule). Children always intern before parents,
//! so ascending `TermId` order is a valid emission order.

use std::collections::HashMap;
use std::fmt::Write as _;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

/// Renders `assertions` as a complete SMT-LIB script
/// (`set-logic` … `check-sat`).
///
/// # Panics
///
/// Panics if any assertion does not belong to `arena`.
pub fn write_script(arena: &TermArena, assertions: &[TermId]) -> String {
    // Count uses to find shared interior nodes (iterative).
    let mut uses: HashMap<TermId, u32> = HashMap::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    let mut symbols: Vec<(String, Sort)> = Vec::new();
    while let Some(t) = stack.pop() {
        if seen.contains(&t) {
            continue;
        }
        seen.insert(t);
        match arena.node(t) {
            TermNode::Symbol(s) => {
                let (name, sort) = arena.symbol(*s);
                symbols.push((name.to_owned(), sort));
            }
            TermNode::App { args, .. } => {
                for &a in &**args {
                    *uses.entry(a).or_insert(0) += 1;
                    stack.push(a);
                }
            }
            TermNode::BoolConst(_) | TermNode::BvConst { .. } => {}
        }
    }
    symbols.sort_by(|a, b| a.0.cmp(&b.0));

    let mut out = String::from("(set-logic QF_BV)\n");
    for (name, sort) in &symbols {
        let _ = writeln!(out, "(declare-const {name} {})", sort_str(*sort));
    }

    // Emit shared App nodes as defs in ascending id order (children first).
    let mut names: HashMap<TermId, String> = HashMap::new();
    let mut ordered: Vec<TermId> = seen.iter().copied().collect();
    ordered.sort();
    for t in ordered {
        let shared_app =
            uses.get(&t).copied().unwrap_or(0) > 1 && matches!(arena.node(t), TermNode::App { .. });
        if shared_app {
            let name = format!("axy.t{}", t.index());
            let body = render_node(arena, t, &names);
            let _ = writeln!(
                out,
                "(define-fun {name} () {} {body})",
                sort_str(arena.sort_of(t))
            );
            names.insert(t, name);
        }
    }
    for &t in assertions {
        let _ = writeln!(out, "(assert {})", render_ref(arena, t, &names));
    }
    out.push_str("(check-sat)\n");
    out
}

fn sort_str(sort: Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_owned(),
        Sort::BitVec(w) => format!("(_ BitVec {w})"),
    }
}

/// Renders a reference to `t`: its def name if named, else inline.
fn render_ref(arena: &TermArena, t: TermId, names: &HashMap<TermId, String>) -> String {
    names
        .get(&t)
        .cloned()
        .unwrap_or_else(|| render_node(arena, t, names))
}

/// Renders `t` inline, with children as references. Iterative.
fn render_node(arena: &TermArena, root: TermId, names: &HashMap<TermId, String>) -> String {
    let mut memo: HashMap<TermId, String> = HashMap::new();
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
    while let Some((t, ready)) = stack.pop() {
        if memo.contains_key(&t) || (t != root && names.contains_key(&t)) {
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
                if ready {
                    let mut text = format!("({}", op_str(*op));
                    for a in args {
                        text.push(' ');
                        match names.get(a) {
                            Some(n) if *a != root => text.push_str(n),
                            _ => text.push_str(&memo[a]),
                        }
                    }
                    text.push(')');
                    memo.insert(t, text);
                } else {
                    stack.push((t, true));
                    for &a in &**args {
                        if !names.contains_key(&a) {
                            stack.push((a, false));
                        }
                    }
                }
            }
        }
    }
    memo.remove(&root).expect("root rendered")
}

fn op_str(op: Op) -> String {
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
