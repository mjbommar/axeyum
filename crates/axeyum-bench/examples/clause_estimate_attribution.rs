//! Analysis-only attribution for the frozen `QF_NIA` A3 pre-lowering refusals.
//!
//! This example parses and integer-blasts the two preregistered targets, then
//! reproduces the production clause estimate and the existing structural bit-
//! demand transfer rules. It deliberately never calls an AIG/CNF lowerer or a
//! solver.

use std::collections::{BTreeMap, HashSet};
use std::fmt::Write as _;
use std::path::Path;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::blast_integers;
use axeyum_smtlib::parse_script;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const BLAST_WIDTH: u32 = 32;
const MAX_REACHABLE_NODES: usize = 2_000_000;
const MAX_DEMAND_REQUESTS: u64 = 8_000_000;

struct FrozenTarget {
    suffix: &'static str,
    sha256: &'static str,
    estimate: u64,
}

const TARGETS: [FrozenTarget; 2] = [
    FrozenTarget {
        suffix: "From_AProVE_2014__juHashMapCreateContainsKey.jar-obl-11__p31818_safety_0.smt2",
        sha256: "a746f09965b418b961a77ec34a869381e4453719b936d5aaee0975050fed3d34",
        estimate: 81_482_280,
    },
    FrozenTarget {
        suffix: "From_AProVE_2014__juHashMapCreateRemove.jar-obl-11__p6984_safety_0.smt2",
        sha256: "730a2c10adde08316d7e3de2a2ad190d1c343623dc7b37145d7ab246d07d4828",
        estimate: 82_590_729,
    },
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConstantKind {
    Zero,
    One,
    AllOnes,
    Other { population: u32 },
}

impl ConstantKind {
    fn label(self) -> &'static str {
        match self {
            Self::Zero => "zero",
            Self::One => "one",
            Self::AllOnes => "all-ones",
            Self::Other { .. } => "other",
        }
    }

    fn population(self) -> u32 {
        match self {
            Self::Zero => 0,
            Self::One => 1,
            Self::AllOnes => u32::MAX,
            Self::Other { population } => population,
        }
    }
}

#[derive(Default)]
struct Analysis {
    reachable_nodes: usize,
    estimated_gates: u64,
    estimated_clauses: u64,
    operator_width: BTreeMap<String, Aggregate>,
    multiplier_class: BTreeMap<String, Aggregate>,
    multiplier_constants: BTreeMap<String, Aggregate>,
    multiplier_terms: Vec<MultiplierTerm>,
    demand_requests: u64,
    multiplier_bits_total: u64,
    multiplier_bits_demanded: u64,
    multiplier_bits_narrower: u64,
    narrower_multiplier_clauses: u64,
}

#[derive(Clone, Copy, Default)]
struct Aggregate {
    nodes: u64,
    gates: u64,
    clauses: u64,
}

struct MultiplierTerm {
    term: TermId,
    width: u32,
    clauses: u64,
}

fn width(arena: &TermArena, term: TermId) -> Result<u32, String> {
    match arena.sort_of(term) {
        Sort::Bool => Ok(1),
        Sort::BitVec(width) => Ok(width),
        other => Err(format!(
            "term #{} retained non-lowerable sort {other}",
            term.index()
        )),
    }
}

fn node_gate_cost(op: Option<Op>, width: u64) -> u64 {
    match op {
        Some(Op::BvMul) => width.saturating_mul(width).saturating_mul(8),
        Some(Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod) => {
            width.saturating_mul(width).saturating_mul(10)
        }
        Some(Op::BvShl | Op::BvLshr | Op::BvAshr) => {
            let log_width = 64_u64 - u64::from(width.leading_zeros());
            width.saturating_mul(log_width.max(1))
        }
        _ => width.max(1),
    }
}

fn constant_kind(arena: &TermArena, term: TermId) -> Option<ConstantKind> {
    let term_width = width(arena, term).ok()?;
    let (is_zero, is_one, is_all_ones, population) = match arena.node(term) {
        TermNode::BvConst { value, .. } => {
            let mask = if term_width == 128 {
                u128::MAX
            } else {
                (1_u128 << term_width) - 1
            };
            (*value == 0, *value == 1, *value == mask, value.count_ones())
        }
        TermNode::WideBvConst(value) => {
            let population = u32::try_from((0..term_width).filter(|&bit| value.bit(bit)).count())
                .expect("constant population is bounded by its u32 width");
            (
                population == 0,
                population == 1 && value.bit(0),
                population == term_width,
                population,
            )
        }
        _ => return None,
    };
    Some(if is_zero {
        ConstantKind::Zero
    } else if is_one {
        ConstantKind::One
    } else if is_all_ones {
        ConstantKind::AllOnes
    } else {
        ConstantKind::Other { population }
    })
}

fn add_aggregate(map: &mut BTreeMap<String, Aggregate>, key: String, gates: u64) {
    let entry = map.entry(key).or_default();
    entry.nodes = entry.nodes.saturating_add(1);
    entry.gates = entry.gates.saturating_add(gates);
    entry.clauses = entry.clauses.saturating_add(gates.saturating_mul(3));
}

fn classify_multiplier(
    arena: &TermArena,
    term: TermId,
    args: &[TermId],
    width: u32,
    gates: u64,
    analysis: &mut Analysis,
) -> Result<(), String> {
    let [lhs, rhs] = args else {
        return Err(format!("bvmul term #{} is not binary", term.index()));
    };
    let lhs_constant = constant_kind(arena, *lhs);
    let rhs_constant = constant_kind(arena, *rhs);
    let (class, side) = match (lhs_constant, rhs_constant) {
        (Some(_), Some(_)) => ("constant-constant", "both"),
        (Some(_), None) => ("constant-nonconstant", "left"),
        (None, Some(_)) => ("constant-nonconstant", "right"),
        (None, None) => ("nonconstant-nonconstant", "neither"),
    };
    add_aggregate(
        &mut analysis.multiplier_class,
        format!("{class}|width={width}|side={side}"),
        gates,
    );
    for (operand_side, kind) in [("left", lhs_constant), ("right", rhs_constant)] {
        if let Some(kind) = kind {
            let population = if kind == ConstantKind::AllOnes {
                width
            } else {
                kind.population()
            };
            add_aggregate(
                &mut analysis.multiplier_constants,
                format!(
                    "width={width}|side={operand_side}|kind={}|population={population}",
                    kind.label()
                ),
                gates,
            );
        }
    }
    analysis.multiplier_terms.push(MultiplierTerm {
        term,
        width,
        clauses: gates.saturating_mul(3),
    });
    Ok(())
}

fn analyze_estimate(arena: &TermArena, roots: &[TermId]) -> Result<Analysis, String> {
    let mut analysis = Analysis::default();
    let mut visited = HashSet::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if visited.len() > MAX_REACHABLE_NODES {
            return Err(format!(
                "reachable-node limit exceeded: {} > {MAX_REACHABLE_NODES}",
                visited.len()
            ));
        }
        let term_width = width(arena, term)?;
        let (op, args): (Option<Op>, &[TermId]) = match arena.node(term) {
            TermNode::App { op, args } => (Some(*op), args),
            _ => (None, &[]),
        };
        let gates = node_gate_cost(op, u64::from(term_width));
        let op_label = op.map_or_else(|| leaf_label(arena.node(term)), |op| format!("{op:?}"));
        add_aggregate(
            &mut analysis.operator_width,
            format!("{op_label}|width={term_width}"),
            gates,
        );
        if op == Some(Op::BvMul) {
            classify_multiplier(arena, term, args, term_width, gates, &mut analysis)?;
        }
        analysis.estimated_gates = analysis.estimated_gates.saturating_add(gates);
        stack.extend(args.iter().copied());
    }
    analysis.reachable_nodes = visited.len();
    analysis.estimated_clauses = analysis.estimated_gates.saturating_mul(3);
    let grouped_clauses = analysis
        .operator_width
        .values()
        .fold(0_u64, |sum, item| sum.saturating_add(item.clauses));
    if grouped_clauses != analysis.estimated_clauses {
        return Err(format!(
            "operator accounting mismatch: grouped {grouped_clauses}, total {}",
            analysis.estimated_clauses
        ));
    }
    analyze_demand(arena, roots, &mut analysis)?;
    Ok(analysis)
}

fn leaf_label(node: &TermNode) -> String {
    match node {
        TermNode::BoolConst(_) => "BoolConst".to_string(),
        TermNode::BvConst { .. } => "BvConst".to_string(),
        TermNode::WideBvConst(_) => "WideBvConst".to_string(),
        TermNode::Symbol(_) => "Symbol".to_string(),
        TermNode::IntConst(_) => "IntConst".to_string(),
        TermNode::RealConst(_) => "RealConst".to_string(),
        TermNode::App { .. } => unreachable!(),
    }
}

fn sort_width(sort: Sort) -> Result<u32, String> {
    match sort {
        Sort::Bool => Ok(1),
        Sort::BitVec(width) => Ok(width),
        Sort::RoundingMode => Ok(3),
        Sort::Float { exp, sig } => Ok(exp + sig),
        other => Err(format!("non-lowerable demand sort {other}")),
    }
}

fn push_all_bits(
    arena: &TermArena,
    term: TermId,
    stack: &mut Vec<(TermId, u32)>,
) -> Result<(), String> {
    let width = sort_width(arena.sort_of(term))?;
    if width > 128 {
        return Err(format!(
            "term #{} width {width} exceeds diagnostic mask width 128",
            term.index()
        ));
    }
    stack.extend((0..width).map(|bit| (term, bit)));
    Ok(())
}

fn propagate_demand(
    arena: &TermArena,
    term: TermId,
    bit: u32,
    stack: &mut Vec<(TermId, u32)>,
) -> Result<(), String> {
    let TermNode::App { op, args } = arena.node(term) else {
        return Ok(());
    };
    match *op {
        Op::Extract { lo, .. } => stack.push((args[0], bit + lo)),
        Op::Concat => {
            let low_width = sort_width(arena.sort_of(args[1]))?;
            if bit < low_width {
                stack.push((args[1], bit));
            } else {
                stack.push((args[0], bit - low_width));
            }
        }
        Op::ZeroExt { .. } => {
            let source_width = sort_width(arena.sort_of(args[0]))?;
            if bit < source_width {
                stack.push((args[0], bit));
            }
        }
        Op::SignExt { .. } => {
            let source_width = sort_width(arena.sort_of(args[0]))?;
            stack.push((args[0], bit.min(source_width - 1)));
        }
        Op::BoolNot
        | Op::BoolAnd
        | Op::BoolOr
        | Op::BoolXor
        | Op::BoolImplies
        | Op::BvNot
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvNand
        | Op::BvNor
        | Op::BvXnor
        | Op::FpFromBits { .. }
        | Op::RoundingModeFromBits => stack.extend(args.iter().map(|arg| (*arg, bit))),
        Op::Ite => {
            stack.push((args[0], 0));
            stack.push((args[1], bit));
            stack.push((args[2], bit));
        }
        Op::RotateLeft { by } => {
            let width = sort_width(arena.sort_of(args[0]))?;
            let shift = by % width;
            stack.push((args[0], (bit + width - shift) % width));
        }
        Op::RotateRight { by } => {
            let width = sort_width(arena.sort_of(args[0]))?;
            let shift = by % width;
            stack.push((args[0], (bit + shift) % width));
        }
        _ => {
            for &arg in args {
                push_all_bits(arena, arg, stack)?;
            }
        }
    }
    Ok(())
}

fn analyze_demand(
    arena: &TermArena,
    roots: &[TermId],
    analysis: &mut Analysis,
) -> Result<(), String> {
    let mut masks = vec![0_u128; arena.len()];
    let mut stack = Vec::new();
    for &root in roots {
        push_all_bits(arena, root, &mut stack)?;
    }
    while let Some((term, bit)) = stack.pop() {
        analysis.demand_requests = analysis.demand_requests.saturating_add(1);
        if analysis.demand_requests > MAX_DEMAND_REQUESTS {
            return Err(format!(
                "structural-demand request limit exceeded: {} > {MAX_DEMAND_REQUESTS}",
                analysis.demand_requests
            ));
        }
        let bit_mask = 1_u128
            .checked_shl(bit)
            .ok_or_else(|| format!("term #{} demand bit {bit} exceeds 127", term.index()))?;
        if masks[term.index()] & bit_mask != 0 {
            continue;
        }
        masks[term.index()] |= bit_mask;
        propagate_demand(arena, term, bit, &mut stack)?;
    }
    for multiplier in &analysis.multiplier_terms {
        let demanded = u64::from(masks[multiplier.term.index()].count_ones());
        let width = u64::from(multiplier.width);
        analysis.multiplier_bits_total = analysis.multiplier_bits_total.saturating_add(width);
        analysis.multiplier_bits_demanded =
            analysis.multiplier_bits_demanded.saturating_add(demanded);
        if demanded < width {
            analysis.multiplier_bits_narrower = analysis
                .multiplier_bits_narrower
                .saturating_add(width - demanded);
            analysis.narrower_multiplier_clauses = analysis
                .narrower_multiplier_clauses
                .saturating_add(multiplier.clauses);
        }
    }
    Ok(())
}

fn aggregate_json(map: &BTreeMap<String, Aggregate>) -> Value {
    Value::Array(
        map.iter()
            .map(|(key, item)| {
                json!({
                    "key": key,
                    "nodes": item.nodes,
                    "estimated_gates": item.gates,
                    "estimated_clauses": item.clauses,
                })
            })
            .collect(),
    )
}

fn class_clauses(analysis: &Analysis, class: &str) -> u64 {
    analysis
        .multiplier_class
        .iter()
        .filter(|(key, _)| key.starts_with(class))
        .fold(0_u64, |sum, (_, item)| sum.saturating_add(item.clauses))
}

fn basis_points(numerator: u64, denominator: u64) -> u64 {
    numerator
        .saturating_mul(10_000)
        .checked_div(denominator)
        .unwrap_or(0)
}

fn render(
    path: &Path,
    digest: &str,
    original_assertions: usize,
    blasted_assertions: usize,
    restricting_constraints: usize,
    analysis: &Analysis,
) -> Value {
    let constant_clauses = class_clauses(analysis, "constant-constant")
        .saturating_add(class_clauses(analysis, "constant-nonconstant"));
    let demand_basis_points = basis_points(
        analysis.narrower_multiplier_clauses,
        analysis.estimated_clauses,
    );
    let constant_basis_points = basis_points(constant_clauses, analysis.estimated_clauses);
    let disposition = if demand_basis_points >= 2_000 {
        "demand-candidate"
    } else if constant_basis_points >= 2_000 {
        "constant-aware-candidate"
    } else {
        "no-bounded-candidate"
    };
    json!({
        "schema": "axeyum-qf-nia-a3-clause-estimate-attribution-v1",
        "source": path.display().to_string(),
        "source_sha256": digest,
        "blast_width": BLAST_WIDTH,
        "original_assertions": original_assertions,
        "blasted_assertions": blasted_assertions,
        "restricting_constraints": restricting_constraints,
        "reachable_shared_nodes": analysis.reachable_nodes,
        "estimated_gates": analysis.estimated_gates,
        "estimated_clauses": analysis.estimated_clauses,
        "operator_width_attribution": aggregate_json(&analysis.operator_width),
        "multiplier_class_attribution": aggregate_json(&analysis.multiplier_class),
        "multiplier_constant_attribution": aggregate_json(&analysis.multiplier_constants),
        "structural_demand": {
            "complete": true,
            "request_limit": MAX_DEMAND_REQUESTS,
            "requests": analysis.demand_requests,
            "multiplier_bits_total": analysis.multiplier_bits_total,
            "multiplier_bits_demanded": analysis.multiplier_bits_demanded,
            "multiplier_bits_narrower_than_full": analysis.multiplier_bits_narrower,
            "estimated_clauses_with_narrower_multiplier_output": analysis.narrower_multiplier_clauses,
            "attribution_basis_points": demand_basis_points,
        },
        "immediate_constant_multiplier_clauses": constant_clauses,
        "immediate_constant_attribution_basis_points": constant_basis_points,
        "disposition": disposition,
        "invariants": {
            "operator_sum_matches_total": true,
            "no_aig_or_cnf_lowering": true,
        },
    })
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a string cannot fail");
            output
        })
}

fn run(path: &Path) -> Result<Value, String> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("non-UTF-8 target path: {}", path.display()))?;
    let target = TARGETS
        .iter()
        .find(|target| target.suffix == name)
        .ok_or_else(|| format!("target is not in the frozen population: {name}"))?;
    let bytes =
        std::fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let digest = sha256(&bytes);
    if digest != target.sha256 {
        return Err(format!(
            "source digest mismatch for {name}: expected {}, found {digest}",
            target.sha256
        ));
    }
    let source = std::str::from_utf8(&bytes)
        .map_err(|error| format!("{} is not UTF-8: {error}", path.display()))?;
    let mut script = parse_script(source).map_err(|error| error.to_string())?;
    let original = script
        .solvable_flat_view()
        .ok_or_else(|| format!("{name} unexpectedly used the word-only fallback"))?
        .to_vec();
    let original_assertions = original.len();
    let blast = blast_integers(&mut script.arena, &original, BLAST_WIDTH)
        .map_err(|error| error.to_string())?;
    let restricting_constraints = blast.restricting_constraints();
    let blasted = blast.assertions();
    let analysis = analyze_estimate(&script.arena, blasted)?;
    if analysis.estimated_clauses != target.estimate {
        return Err(format!(
            "retained estimate mismatch for {name}: expected {}, found {}",
            target.estimate, analysis.estimated_clauses
        ));
    }
    Ok(render(
        path,
        &digest,
        original_assertions,
        blasted.len(),
        restricting_constraints,
        &analysis,
    ))
}

fn main() {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: clause_estimate_attribution <frozen-target.smt2> [...]");
        std::process::exit(2);
    }
    for path in paths {
        let path = Path::new(&path);
        match run(path) {
            Ok(report) => println!(
                "{}",
                serde_json::to_string(&report).expect("serialize JSON")
            ),
            Err(error) => {
                eprintln!("clause_estimate_attribution: {error}");
                std::process::exit(1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use super::{aggregate_json, analyze_estimate, class_clauses};

    #[test]
    fn shared_nodes_are_charged_once_and_classes_reconcile() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y_symbol = arena.declare("y", Sort::BitVec(8)).unwrap();
        let x = arena.var(x_symbol);
        let y = arena.var(y_symbol);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let cc = arena.bv_mul(one, three).unwrap();
        let cn_left = arena.bv_mul(three, x).unwrap();
        let cn_right = arena.bv_mul(y, zero).unwrap();
        let nn = arena.bv_mul(x, y).unwrap();
        let shared = arena.bv_add(nn, nn).unwrap();
        let roots = [cc, cn_left, cn_right, shared];
        let analysis = analyze_estimate(&arena, &roots).unwrap();

        assert_eq!(analysis.multiplier_terms.len(), 4);
        assert_eq!(class_clauses(&analysis, "constant-constant"), 1_536);
        assert_eq!(class_clauses(&analysis, "constant-nonconstant"), 3_072);
        assert_eq!(class_clauses(&analysis, "nonconstant-nonconstant"), 1_536);
        assert_eq!(
            analysis
                .operator_width
                .values()
                .map(|item| item.clauses)
                .sum::<u64>(),
            analysis.estimated_clauses
        );
    }

    #[test]
    fn width_groups_and_serialization_are_deterministic() {
        let mut arena = TermArena::new();
        let x8_symbol = arena.declare("x8", Sort::BitVec(8)).unwrap();
        let x16_symbol = arena.declare("x16", Sort::BitVec(16)).unwrap();
        let x8 = arena.var(x8_symbol);
        let x16 = arena.var(x16_symbol);
        let one8 = arena.bv_const(8, 1).unwrap();
        let ones16 = arena.bv_const(16, u128::from(u16::MAX)).unwrap();
        let m8 = arena.bv_mul(x8, one8).unwrap();
        let m16 = arena.bv_mul(ones16, x16).unwrap();
        let first = analyze_estimate(&arena, &[m16, m8]).unwrap();
        let second = analyze_estimate(&arena, &[m16, m8]).unwrap();

        assert!(
            first
                .multiplier_class
                .keys()
                .any(|key| key.contains("width=8"))
        );
        assert!(
            first
                .multiplier_class
                .keys()
                .any(|key| key.contains("width=16"))
        );
        assert_eq!(
            aggregate_json(&first.multiplier_class),
            aggregate_json(&second.multiplier_class)
        );
    }
}
