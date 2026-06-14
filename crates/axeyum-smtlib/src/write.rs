//! Sharing-preserving SMT-LIB 2 script export.
//!
//! Shared interior nodes (fan-in > 1) are emitted as 0-ary `define-fun`s,
//! so output size is linear in the DAG — never the unfolded tree
//! (query-cost-control hard rule). Children always intern before parents,
//! so ascending `TermId` order is a valid emission order.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use axeyum_ir::{FuncId, Op, Sort, TermArena, TermId, TermNode};

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
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut symbols: Vec<(String, Sort)> = Vec::new();
    let mut functions: Vec<FuncId> = Vec::new();
    let mut seen_functions: HashSet<FuncId> = HashSet::new();
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
            TermNode::App { op, args } => {
                if let Op::Apply(func) = op
                    && seen_functions.insert(*func)
                {
                    functions.push(*func);
                }
                for &a in &**args {
                    *uses.entry(a).or_insert(0) += 1;
                    stack.push(a);
                }
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {}
        }
    }
    symbols.sort_by(|a, b| a.0.cmp(&b.0));
    functions.sort_by_key(|f| arena.function(*f).0.to_owned());
    let mut used_names: HashSet<String> = symbols.iter().map(|(name, _)| name.clone()).collect();

    // Assemble the quantifier-free logic name from the features present:
    // `QF_` + `A` (arrays) + `UF` (functions) + arithmetic core (`LIA` for
    // integers, else `BV`). Yields e.g. QF_BV, QF_ABV, QF_UFBV, QF_LIA, QF_UFLIA.
    let has_arrays = symbols
        .iter()
        .any(|(_, sort)| matches!(sort, Sort::Array { .. }));
    let has_integers = symbols.iter().any(|(_, sort)| *sort == Sort::Int);
    let has_reals = symbols.iter().any(|(_, sort)| *sort == Sort::Real);
    let arithmetic = if has_reals {
        "LRA"
    } else if has_integers {
        "LIA"
    } else {
        "BV"
    };
    let logic = format!(
        "QF_{}{}{arithmetic}",
        if has_arrays { "A" } else { "" },
        if functions.is_empty() { "" } else { "UF" },
    );
    let mut out = format!("(set-logic {logic})\n");
    for (name, sort) in &symbols {
        let _ = writeln!(
            out,
            "(declare-const {} {})",
            symbol_syntax(name),
            sort_str(*sort)
        );
    }
    for &func in &functions {
        let (name, params, result) = arena.function(func);
        let params_str = params
            .iter()
            .map(|&s| sort_str(s))
            .collect::<Vec<_>>()
            .join(" ");
        let _ = writeln!(
            out,
            "(declare-fun {} ({params_str}) {})",
            symbol_syntax(name),
            sort_str(result)
        );
    }

    // Emit shared App nodes as defs in ascending id order (children first).
    let mut names: HashMap<TermId, String> = HashMap::new();
    let mut ordered: Vec<TermId> = seen.iter().copied().collect();
    ordered.sort();
    for t in ordered {
        let shared_app =
            uses.get(&t).copied().unwrap_or(0) > 1 && matches!(arena.node(t), TermNode::App { .. });
        if shared_app {
            let name = fresh_def_name(t, &mut used_names);
            let escaped_name = symbol_syntax(&name);
            let body = render_node(arena, t, &names);
            let _ = writeln!(
                out,
                "(define-fun {escaped_name} () {} {body})",
                sort_str(arena.sort_of(t))
            );
            names.insert(t, escaped_name);
        }
    }
    for &t in assertions {
        let _ = writeln!(out, "(assert {})", render_ref(arena, t, &names));
    }
    out.push_str("(check-sat)\n");
    out
}

fn fresh_def_name(t: TermId, used_names: &mut HashSet<String>) -> String {
    let base = format!("axy.t{}", t.index());
    if used_names.insert(base.clone()) {
        return base;
    }
    let mut i = 1u32;
    loop {
        let candidate = format!("{base}.{i}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
        i += 1;
    }
}

fn symbol_syntax(name: &str) -> String {
    if is_simple_symbol(name) {
        name.to_owned()
    } else {
        format!("|{}|", name.replace('|', "\\|"))
    }
}

fn is_simple_symbol(name: &str) -> bool {
    fn is_initial(c: char) -> bool {
        c.is_ascii_alphabetic() || "~!@$%^&*_-+=<>.?/".contains(c)
    }

    fn is_rest(c: char) -> bool {
        is_initial(c) || c.is_ascii_digit()
    }

    const RESERVED: &[&str] = &[
        "!", "_", "as", "Bool", "exists", "false", "forall", "let", "match", "par", "true",
    ];

    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    is_initial(first)
        && chars.all(is_rest)
        && !name.starts_with('#')
        && !name.starts_with(':')
        && !RESERVED.contains(&name)
}

fn sort_str(sort: Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_owned(),
        Sort::BitVec(w) => format!("(_ BitVec {w})"),
        Sort::Array { index, element } => {
            format!("(Array (_ BitVec {index}) (_ BitVec {element}))")
        }
        Sort::Int => "Int".to_owned(),
        Sort::Real => "Real".to_owned(),
        Sort::Datatype(id) => format!("(Datatype {})", id.index()),
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
#[allow(clippy::too_many_lines)]
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
            TermNode::IntConst(value) => {
                // SMT-LIB renders negative integers as `(- n)`.
                if *value < 0 {
                    memo.insert(t, format!("(- {})", value.unsigned_abs()));
                } else {
                    memo.insert(t, value.to_string());
                }
            }
            TermNode::RealConst(value) => {
                // Render so the literal re-parses as `Real` (never `Int`):
                // an integer value as `n.0`, otherwise `(/ n d)`; `(- ...)` for
                // negatives.
                let num = value.numerator();
                let den = value.denominator();
                let magnitude = if den == 1 {
                    format!("{}.0", num.unsigned_abs())
                } else {
                    format!("(/ {}.0 {den}.0)", num.unsigned_abs())
                };
                if num < 0 {
                    memo.insert(t, format!("(- {magnitude})"));
                } else {
                    memo.insert(t, magnitude);
                }
            }
            TermNode::Symbol(s) => {
                memo.insert(t, symbol_syntax(arena.symbol(*s).0));
            }
            TermNode::App { op, args } => {
                if ready {
                    // Quantifiers render in SMT-LIB binder form:
                    // `(forall ((x Sort)) body)`.
                    if let Op::Forall(var) | Op::Exists(var) = op {
                        let (name, sort) = arena.symbol(*var);
                        let keyword = if matches!(op, Op::Forall(_)) {
                            "forall"
                        } else {
                            "exists"
                        };
                        let body = match names.get(&args[0]) {
                            Some(n) if args[0] != root => n.clone(),
                            _ => memo[&args[0]].clone(),
                        };
                        memo.insert(
                            t,
                            format!(
                                "({keyword} (({} {})) {body})",
                                symbol_syntax(name),
                                sort_str(sort)
                            ),
                        );
                        continue;
                    }
                    // Constant arrays render with an `(as const (Array I E))` head.
                    if let Op::ConstArray { index } = op {
                        let element = match arena.sort_of(t) {
                            Sort::Array { element, .. } => element,
                            _ => *index, // unreachable: ConstArray is array-sorted
                        };
                        let value = match names.get(&args[0]) {
                            Some(n) if args[0] != root => n.clone(),
                            _ => memo[&args[0]].clone(),
                        };
                        memo.insert(
                            t,
                            format!(
                                "((as const (Array (_ BitVec {index}) (_ BitVec {element}))) {value})"
                            ),
                        );
                        continue;
                    }
                    let head = match op {
                        Op::Apply(func) => symbol_syntax(arena.function(*func).0),
                        _ => op_str(*op),
                    };
                    let mut text = format!("({head}");
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
        Op::Select => "select".into(),
        Op::Store => "store".into(),
        // Rendered via its `(as const (Array …))` head in `render_node`.
        Op::ConstArray { .. } => unreachable!("const arrays render via their `as const` head"),
        Op::Bv2Nat => "bv2nat".into(),
        Op::Int2Bv { width } => format!("(_ int2bv {width})"),
        // Applications are rendered via the function name in `render_node`.
        Op::Apply(_) => unreachable!("Op::Apply is rendered via its function name"),
        Op::IntNeg | Op::IntSub | Op::RealNeg | Op::RealSub => "-".into(),
        Op::IntAdd | Op::RealAdd => "+".into(),
        Op::IntMul | Op::RealMul => "*".into(),
        Op::RealDiv => "/".into(),
        Op::IntDiv => "div".into(),
        Op::IntMod => "mod".into(),
        Op::IntAbs => "abs".into(),
        Op::IntLt | Op::RealLt => "<".into(),
        Op::IntLe | Op::RealLe => "<=".into(),
        Op::IntGt | Op::RealGt => ">".into(),
        Op::IntGe | Op::RealGe => ">=".into(),
        // Quantifiers render via their binder form in `render_node`.
        Op::Forall(_) | Op::Exists(_) => {
            unreachable!("quantifiers are rendered via their binder form")
        }
        Op::DtConstruct { constructor, .. } => format!("construct/{}", constructor.index()),
        Op::DtSelect { constructor, index } => format!("select/{}/{index}", constructor.index()),
        Op::DtTest(constructor) => format!("is/{}", constructor.index()),
    }
}
