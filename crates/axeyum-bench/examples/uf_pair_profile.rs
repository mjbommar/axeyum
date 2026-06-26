//! Diagnostic probe for lazy UF application-pair shape.
//!
//! Run with one SMT-LIB file path and an optional sample limit:
//!
//! ```sh
//! cargo run -q -p axeyum-bench --example uf_pair_profile -- file.smt2 20
//! ```
//!
//! This is read-only instrumentation for deciding whether a lazy Ackermann
//! pre-seed can be made narrow enough to be useful. It reports deterministic
//! same-function application groups, pair categories, and a bounded sample of
//! concrete pairs.

use std::collections::BTreeMap;
use std::path::PathBuf;

use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode, render};
use axeyum_rewrite::eliminate_functions;
use axeyum_smtlib::parse_script;

type Application<'a> = (usize, &'a [TermId], SymbolId);
type FunctionGroup<'a> = (FuncId, Vec<Application<'a>>);

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let file = args.get(1).map_or_else(
        || {
            eprintln!("usage: uf_pair_profile <file.smt2> [sample_limit]");
            std::process::exit(2);
        },
        PathBuf::from,
    );
    let sample_limit = args
        .get(2)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(20);

    let text = std::fs::read_to_string(&file).expect("read SMT-LIB file");
    let mut script = parse_script(&text).expect("parse SMT-LIB file");
    let assertions = script.assertions.clone();
    let elim = eliminate_functions(&mut script.arena, &assertions).expect("eliminate functions");
    let applications = elim.applications();

    let mut groups: Vec<FunctionGroup<'_>> = Vec::new();
    for (idx, (func, args, fresh)) in applications.iter().enumerate() {
        if let Some((_func, members)) = groups.iter_mut().find(|(g, _)| g == func) {
            members.push((idx, *args, *fresh));
        } else {
            groups.push((*func, vec![(idx, *args, *fresh)]));
        }
    }

    let potential_pairs = groups
        .iter()
        .map(|(_func, members)| members.len() * members.len().saturating_sub(1) / 2)
        .sum::<usize>();
    println!("file: {}", file.display());
    println!("assertions: {}", assertions.len());
    println!("applications: {}", applications.len());
    println!("function_groups: {}", groups.len());
    println!("potential_pairs: {potential_pairs}");

    let mut total_categories = BTreeMap::<String, usize>::new();
    for (func, members) in &groups {
        let (name, domain, range) = script.arena.function(*func);
        let group_pairs = members.len() * members.len().saturating_sub(1) / 2;
        println!(
            "\nfunction {name}: arity={} range={range} applications={} pairs={group_pairs}",
            domain.len(),
            members.len()
        );
        for (idx, args, fresh) in members {
            let fresh_name = script.arena.symbol(*fresh).0;
            let rendered_args = args
                .iter()
                .map(|&arg| render(&script.arena, arg))
                .collect::<Vec<_>>()
                .join(", ");
            println!("  app#{idx} -> {fresh_name}({rendered_args})");
        }

        let mut categories = BTreeMap::<String, usize>::new();
        let mut samples = Vec::new();
        for a in 0..members.len() {
            for b in (a + 1)..members.len() {
                let (i, args_i, _fresh_i) = members[a];
                let (j, args_j, _fresh_j) = members[b];
                let category = pair_category(&script.arena, args_i, args_j);
                *categories.entry(category.clone()).or_default() += 1;
                *total_categories.entry(category.clone()).or_default() += 1;
                if samples.len() < sample_limit {
                    samples.push((
                        i,
                        j,
                        category,
                        render_args(&script.arena, args_i),
                        render_args(&script.arena, args_j),
                    ));
                }
            }
        }
        println!("  pair_categories:");
        for (category, count) in &categories {
            println!("    {category}: {count}");
        }
        if !samples.is_empty() {
            println!("  pair_samples:");
            for (i, j, category, args_i, args_j) in samples {
                println!("    app#{i} vs app#{j}: {category}: ({args_i}) == ({args_j})");
            }
        }
    }

    println!("\ntotal_pair_categories:");
    for (category, count) in total_categories {
        println!("  {category}: {count}");
    }
}

fn render_args(arena: &TermArena, args: &[TermId]) -> String {
    args.iter()
        .map(|&arg| render(arena, arg))
        .collect::<Vec<_>>()
        .join(", ")
}

fn pair_category(arena: &TermArena, args_i: &[TermId], args_j: &[TermId]) -> String {
    if args_i.len() != args_j.len() {
        return "arity-mismatch".to_owned();
    }
    if args_i == args_j {
        return "syntactic-equal".to_owned();
    }
    if args_i.len() == 1 {
        return unary_pair_category(arena, args_i[0], args_j[0]);
    }
    if args_i
        .iter()
        .zip(args_j)
        .all(|(&a, &b)| same_sort_int_like(arena, a, b))
    {
        "multi-int-like".to_owned()
    } else {
        "multi-other".to_owned()
    }
}

fn unary_pair_category(arena: &TermArena, a: TermId, b: TermId) -> String {
    let ka = arg_kind(arena, a);
    let kb = arg_kind(arena, b);
    if ka <= kb {
        format!("{ka}-{kb}")
    } else {
        format!("{kb}-{ka}")
    }
}

fn same_sort_int_like(arena: &TermArena, a: TermId, b: TermId) -> bool {
    arena.sort_of(a) == Sort::Int && arena.sort_of(b) == Sort::Int
}

fn arg_kind(arena: &TermArena, term: TermId) -> &'static str {
    match arena.node(term) {
        TermNode::IntConst(_) => "int-const",
        TermNode::BoolConst(_) => "bool-const",
        TermNode::BvConst { .. } | TermNode::WideBvConst(_) => "bv-const",
        TermNode::Symbol(_) if arena.sort_of(term) == Sort::Int => "int-symbol",
        TermNode::Symbol(_) => "symbol",
        TermNode::App { op, args } if affine_unit_int_term(arena, *op, args) => "int-affine-unit",
        TermNode::App {
            op: Op::IntAdd | Op::IntSub | Op::IntMul,
            ..
        } => "int-arith",
        TermNode::App { .. } => "app",
        TermNode::RealConst(_) => "real-const",
    }
}

fn affine_unit_int_term(arena: &TermArena, op: Op, args: &[TermId]) -> bool {
    if !matches!(op, Op::IntAdd | Op::IntSub) {
        return false;
    }
    let mut symbols = 0usize;
    let mut constants = 0usize;
    let mut stack = args.to_vec();
    while let Some(term) = stack.pop() {
        match arena.node(term) {
            TermNode::IntConst(_) => constants += 1,
            TermNode::Symbol(_) if arena.sort_of(term) == Sort::Int => symbols += 1,
            TermNode::App {
                op: Op::IntAdd | Op::IntSub,
                args,
            } => stack.extend(args.iter().copied()),
            TermNode::App {
                op: Op::IntMul,
                args,
            } if args.len() == 2 && has_one_int_const(arena, args) => symbols += 1,
            _ => return false,
        }
    }
    symbols > 0 && constants <= 2
}

fn has_one_int_const(arena: &TermArena, args: &[TermId]) -> bool {
    matches!(arena.node(args[0]), TermNode::IntConst(_))
        ^ matches!(arena.node(args[1]), TermNode::IntConst(_))
}
