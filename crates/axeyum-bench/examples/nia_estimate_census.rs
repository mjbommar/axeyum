//! Per-file `QF_NIA` shape and clause-estimate census (lane `NIA-TRACE`, ADR-2112).
//!
//! Analysis-only. For each `.smt2` target it reports, as one TSV row per
//! (file, width):
//!
//! - the ORIGINAL integer shape, read before any blast: integer symbols, the
//!   maximum multiplicative degree, how many `*` nodes are genuinely nonlinear
//!   (at least two non-constant operands), and whether `div`/`mod`/`abs` occur;
//! - the production pre-lowering clause ESTIMATE at that width, recomputed by
//!   the same walk `sat_bv_backend::estimate_blast_clauses` performs (that
//!   function is `pub(crate)`, so an example cannot call it; the estimate here
//!   is held to the production one by reproducing its per-operator table
//!   verbatim, and by this example's own agreement with the frozen values
//!   `clause_estimate_attribution` pins);
//! - with `--actual`, the ACTUAL clause count the shipped lowering emits at
//!   that width, obtained by running the real backend with the pre-lowering
//!   gate lifted (`cnf_clause_budget = u64::MAX`) and the SAT search stopped
//!   the moment it starts (`resource_limit = 0`), so the number measured is
//!   the encoding and nothing else.
//!
//! The estimate/actual pair is the point: the shipped gate refuses on the
//! ESTIMATE, and `check_cnf_budgets`'s own comment says a query is "(more
//! often) refused there and fit here".

use std::collections::{HashMap, HashSet};
use std::path::Path;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::blast_integers;
use axeyum_smtlib::parse_script;
use axeyum_solver::{SatBvBackend, SolverBackend, SolverConfig};

/// The per-operator gate cost of `sat_bv_backend::estimate_blast_clauses`,
/// reproduced verbatim.
fn gate_cost(op: Op, width: u64) -> u64 {
    match op {
        Op::BvMul => width.saturating_mul(width).saturating_mul(8),
        Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
            width.saturating_mul(width).saturating_mul(10)
        }
        Op::BvShl | Op::BvLshr | Op::BvAshr => {
            let log_width = 64_u64 - u64::from(width.leading_zeros());
            width.saturating_mul(log_width.max(1))
        }
        _ => width.max(1),
    }
}

fn sort_width(arena: &TermArena, term: TermId) -> u64 {
    match arena.sort_of(term) {
        Sort::Bool => 1,
        Sort::BitVec(bits) => u64::from(bits),
        _ => 0,
    }
}

/// `estimate_blast_clauses`, reproduced: one DAG walk, per-node gate cost in
/// the node's own result width, then `3x` for Tseitin.
fn estimate_clauses(arena: &TermArena, roots: &[TermId]) -> u64 {
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut gates: u64 = 0;
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            gates = gates.saturating_add(gate_cost(*op, sort_width(arena, term)));
            for &arg in &**args {
                stack.push(arg);
            }
        } else {
            gates = gates.saturating_add(sort_width(arena, term).max(1));
        }
    }
    gates.saturating_mul(3)
}

/// How many gates the multiplies alone contribute — the number that says
/// whether the estimate is a multiplier estimate or a term-count estimate.
struct BlastShape {
    nodes: u64,
    mul_nodes: u64,
    mul_gates: u64,
    divrem_nodes: u64,
    divrem_gates: u64,
}

fn blast_shape(arena: &TermArena, roots: &[TermId]) -> BlastShape {
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut shape = BlastShape {
        nodes: 0,
        mul_nodes: 0,
        mul_gates: 0,
        divrem_nodes: 0,
        divrem_gates: 0,
    };
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        shape.nodes += 1;
        if let TermNode::App { op, args } = arena.node(term) {
            let width = sort_width(arena, term);
            match op {
                Op::BvMul => {
                    shape.mul_nodes += 1;
                    shape.mul_gates = shape.mul_gates.saturating_add(gate_cost(*op, width));
                }
                Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
                    shape.divrem_nodes += 1;
                    shape.divrem_gates = shape.divrem_gates.saturating_add(gate_cost(*op, width));
                }
                _ => {}
            }
            for &arg in &**args {
                stack.push(arg);
            }
        }
    }
    shape
}

/// The ORIGINAL integer shape, read before any blast.
struct IntShape {
    int_symbols: usize,
    nodes: usize,
    mul_nodes: usize,
    nonlinear_mul_nodes: usize,
    max_degree: u32,
    has_div: bool,
    has_mod: bool,
    has_abs: bool,
}

fn is_int_const(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::IntConst(_))
}

/// Multiplicative degree of a term: a constant is 0, an `Int` symbol 1, a
/// product the sum of its factors' degrees, and everything else the max over
/// its arguments. Memoised over the shared DAG, so this is linear in nodes.
fn degrees(arena: &TermArena, roots: &[TermId]) -> HashMap<TermId, u32> {
    let mut order: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&root| (root, false)).collect();
    while let Some((term, expanded)) = stack.pop() {
        if expanded {
            order.push(term);
            continue;
        }
        if !seen.insert(term) {
            continue;
        }
        stack.push((term, true));
        if let TermNode::App { args, .. } = arena.node(term) {
            for &arg in &**args {
                stack.push((arg, false));
            }
        }
    }
    let mut degree: HashMap<TermId, u32> = HashMap::new();
    for term in order {
        let value = match arena.node(term) {
            TermNode::Symbol { .. } => u32::from(arena.sort_of(term) == Sort::Int),
            TermNode::App { op, args } => {
                let child = |arg: &TermId| degree.get(arg).copied().unwrap_or(0);
                if *op == Op::IntMul {
                    args.iter().map(child).sum()
                } else {
                    args.iter().map(child).max().unwrap_or(0)
                }
            }
            _ => 0,
        };
        degree.insert(term, value);
    }
    degree
}

fn int_shape(arena: &TermArena, roots: &[TermId]) -> IntShape {
    let degree = degrees(arena, roots);
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut shape = IntShape {
        int_symbols: 0,
        nodes: 0,
        mul_nodes: 0,
        nonlinear_mul_nodes: 0,
        max_degree: 0,
        has_div: false,
        has_mod: false,
        has_abs: false,
    };
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        shape.nodes += 1;
        shape.max_degree = shape
            .max_degree
            .max(degree.get(&term).copied().unwrap_or(0));
        match arena.node(term) {
            TermNode::Symbol { .. } if arena.sort_of(term) == Sort::Int => shape.int_symbols += 1,
            TermNode::App { op, args } => {
                match op {
                    Op::IntMul => {
                        shape.mul_nodes += 1;
                        if args.iter().filter(|&&a| !is_int_const(arena, a)).count() >= 2 {
                            shape.nonlinear_mul_nodes += 1;
                        }
                    }
                    Op::IntDiv => shape.has_div = true,
                    Op::IntMod => shape.has_mod = true,
                    Op::IntAbs => shape.has_abs = true,
                    _ => {}
                }
                for &arg in &**args {
                    stack.push(arg);
                }
            }
            _ => {}
        }
    }
    shape
}

/// The minimum signed bit-width that holds `value`.
fn signed_width_for(value: i128) -> u32 {
    let mut width = 2_u32;
    while width < 128 {
        let min = -(1_i128 << (width - 1));
        let max = (1_i128 << (width - 1)) - 1;
        if value >= min && value <= max {
            return width;
        }
        width += 1;
    }
    128
}

/// What the two halves of the query demand of a single global width.
///
/// `constant_width` is the smallest width at which `blast_integers` admits the
/// query at all — one integer literal too large for `w` makes `encode_constant`
/// return `ConstantOutOfRange` and kills the whole rung
/// (`axeyum-rewrite/src/int_blast.rs:603`).
///
/// `bound_width` is the smallest width that holds every VARIABLE's own declared
/// range, read from the top-level `lo <= x` / `x <= hi` atoms the query states
/// about its own symbols. A symbol with no such atom is counted in
/// `unbounded_symbols` and contributes nothing, so `bound_width` is a LOWER
/// bound on what a per-variable policy would need — never an over-claim.
struct WidthDemand {
    constant_width: u32,
    max_constant: i128,
    bound_width: u32,
    bounded_symbols: usize,
    unbounded_symbols: usize,
}

fn width_demand(arena: &TermArena, roots: &[TermId]) -> WidthDemand {
    let mut constant_width = 2_u32;
    let mut max_constant: i128 = 0;
    let mut symbols: HashSet<TermId> = HashSet::new();
    let mut lower: HashMap<TermId, i128> = HashMap::new();
    let mut upper: HashMap<TermId, i128> = HashMap::new();

    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::IntConst(value) => {
                constant_width = constant_width.max(signed_width_for(*value));
                if value.unsigned_abs() > max_constant.unsigned_abs() {
                    max_constant = *value;
                }
            }
            // Outside `i128` entirely: no width this route accepts can hold it.
            TermNode::WideIntConst(_) => constant_width = 128,
            TermNode::Symbol { .. } if arena.sort_of(term) == Sort::Int => {
                symbols.insert(term);
            }
            TermNode::App { op, args } => {
                // `lo <= x`, `x <= hi`, and the strict/reversed forms. Only the
                // literal-vs-symbol shape is read; anything else is ignored,
                // which can only make `bound_width` larger, never smaller.
                if matches!(op, Op::IntLe | Op::IntLt | Op::IntGe | Op::IntGt) && args.len() == 2 {
                    let (left, right) = (args[0], args[1]);
                    let strict = matches!(op, Op::IntLt | Op::IntGt);
                    let flip = matches!(op, Op::IntGe | Op::IntGt);
                    if let (TermNode::IntConst(value), TermNode::Symbol { .. }) =
                        (arena.node(left), arena.node(right))
                        && arena.sort_of(right) == Sort::Int
                    {
                        let bound = if strict { value + 1 } else { *value };
                        let slot = if flip { &mut upper } else { &mut lower };
                        let entry = slot.entry(right).or_insert(bound);
                        *entry = if flip {
                            (*entry).max(bound)
                        } else {
                            (*entry).min(bound)
                        };
                    }
                    if let (TermNode::Symbol { .. }, TermNode::IntConst(value)) =
                        (arena.node(left), arena.node(right))
                        && arena.sort_of(left) == Sort::Int
                    {
                        let bound = if strict { value - 1 } else { *value };
                        let slot = if flip { &mut lower } else { &mut upper };
                        let entry = slot.entry(left).or_insert(bound);
                        *entry = if flip {
                            (*entry).min(bound)
                        } else {
                            (*entry).max(bound)
                        };
                    }
                }
                for &arg in &**args {
                    stack.push(arg);
                }
            }
            _ => {}
        }
    }

    let mut bound_width = 2_u32;
    let mut bounded = 0_usize;
    for symbol in &symbols {
        if let (Some(&low), Some(&high)) = (lower.get(symbol), upper.get(symbol)) {
            bounded += 1;
            bound_width = bound_width
                .max(signed_width_for(low))
                .max(signed_width_for(high));
        }
    }
    WidthDemand {
        constant_width,
        max_constant,
        bound_width,
        bounded_symbols: bounded,
        unbounded_symbols: symbols.len() - bounded,
    }
}

fn status_of(source: &str) -> &'static str {
    if source.contains(":status unsat") {
        "unsat"
    } else if source.contains(":status sat") {
        "sat"
    } else if source.contains(":status unknown") {
        "unknown"
    } else {
        "none"
    }
}

/// The actual encoded clause count at this width: the shipped backend with the
/// pre-lowering gate lifted and the search stopped at zero conflicts.
fn actual_clauses(arena: &TermArena, assertions: &[TermId]) -> Result<u64, String> {
    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default()
        .with_cnf_clause_budget(u64::MAX)
        .with_resource_limit(0);
    backend
        .check(arena, assertions, &config)
        .map_err(|error| error.to_string())?;
    let stats = backend.last_stats().ok_or("no stats")?;
    let clauses = stats
        .backend
        .iter()
        .find(|(name, _)| name == "cnf_clauses")
        .map(|(_, value)| *value)
        .ok_or("no cnf_clauses stat")?;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // a clause count
    Ok(clauses.max(0.0) as u64)
}

fn main() {
    let mut widths: Vec<u32> = vec![4, 8, 12, 16, 24, 32];
    let mut want_actual = false;
    let mut paths: Vec<String> = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--actual" => want_actual = true,
            "--widths" => {
                let raw = args.next().unwrap_or_default();
                widths = raw
                    .split(',')
                    .filter_map(|width| width.trim().parse::<u32>().ok())
                    .collect();
            }
            other => paths.push(other.to_owned()),
        }
    }
    if paths.is_empty() {
        eprintln!("usage: nia_estimate_census [--actual] [--widths 4,8,32] <file.smt2>...");
        std::process::exit(2);
    }
    println!(
        "path\tstatus\tint_symbols\tsrc_nodes\tmul_nodes\tnonlinear_mul_nodes\tmax_degree\t\
         has_div\thas_mod\thas_abs\tconstant_width\tmax_constant\tbound_width\t\
         bounded_symbols\tunbounded_symbols\twidth\tblast_nodes\tblast_mul_nodes\tmul_gates\t\
         divrem_nodes\tdivrem_gates\testimate\tactual\tnote"
    );
    for path in paths {
        let path = Path::new(&path);
        let Ok(source) = std::fs::read_to_string(path) else {
            println!("{}\tREAD-ERROR", path.display());
            continue;
        };
        let status = status_of(&source);
        let script = match parse_script(&source) {
            Ok(script) => script,
            Err(error) => {
                println!("{}\t{status}\tPARSE-ERROR: {error}", path.display());
                continue;
            }
        };
        let Some(original) = script.solvable_flat_view().map(<[TermId]>::to_vec) else {
            println!("{}\t{status}\tNO-FLAT-VIEW", path.display());
            continue;
        };
        let src = int_shape(&script.arena, &original);
        let demand = width_demand(&script.arena, &original);
        let prefix = format!(
            "{}\t{status}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            path.display(),
            src.int_symbols,
            src.nodes,
            src.mul_nodes,
            src.nonlinear_mul_nodes,
            src.max_degree,
            src.has_div,
            src.has_mod,
            src.has_abs,
            demand.constant_width,
            demand.max_constant,
            demand.bound_width,
            demand.bounded_symbols,
            demand.unbounded_symbols,
        );
        for &width in &widths {
            let mut arena = script.arena.clone();
            let blast = match blast_integers(&mut arena, &original, width) {
                Ok(blast) => blast,
                Err(error) => {
                    println!("{prefix}\t{width}\t\t\t\t\t\t\t\tBLAST-ERROR: {error}");
                    continue;
                }
            };
            let blasted = blast.assertions().to_vec();
            let shape = blast_shape(&arena, &blasted);
            let estimate = estimate_clauses(&arena, &blasted);
            let (actual, note) = if want_actual {
                match actual_clauses(&arena, &blasted) {
                    Ok(count) => (count.to_string(), String::new()),
                    Err(error) => (String::new(), format!("ACTUAL-ERROR: {error}")),
                }
            } else {
                (String::new(), String::new())
            };
            println!(
                "{prefix}\t{width}\t{}\t{}\t{}\t{}\t{}\t{estimate}\t{actual}\t{note}",
                shape.nodes,
                shape.mul_nodes,
                shape.mul_gates,
                shape.divrem_nodes,
                shape.divrem_gates,
            );
        }
    }
}
