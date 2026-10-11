//! Source-preserving bounded propositional adapter for the existing Alethe tail.
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use axeyum_cnf::{AletheCommand, AletheTerm, check_alethe};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::backend::SolverConfig;

pub(crate) fn prove(
    input: &str,
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Option<Vec<AletheCommand>> {
    let timeout = config.timeout.unwrap_or(Duration::from_secs(10));
    if timeout.is_zero() || assertions.len() > 128 {
        return None;
    }
    let deadline = Instant::now().checked_add(timeout)?;
    let mut remaining = 512;
    let _typed_formulas = assertions
        .iter()
        .map(|&term| convert(arena, term, 0, &mut remaining))
        .collect::<Option<Vec<_>>>()?;
    let formulas = source_formulas(input, assertions.len())?;
    if Instant::now() >= deadline {
        return None;
    }
    let (proof, _) = crate::qfbv_alethe::prove_bit_gate_unsat_alethe_within(
        &formulas,
        BTreeMap::new(),
        Some(deadline),
    )?;
    if Instant::now() >= deadline || proof.len() > 20_000 {
        return None;
    }
    matches!(check_alethe(&proof), Ok(true)).then_some(proof)
}

fn convert(
    arena: &TermArena,
    term: TermId,
    depth: usize,
    remaining: &mut usize,
) -> Option<AletheTerm> {
    if depth > 32 || arena.sort_of(term) != Sort::Bool {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            let (name, _) = arena.symbol(*symbol);
            if name.len() > 128 {
                return None;
            }
            // Quoted names must remain atoms, including names resembling constants.
            let name = if (name.starts_with('|') && name.ends_with('|'))
                || (name != "true"
                    && name != "false"
                    && name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || "_~!@$%^&*+-=<>.?/".contains(c))
                    && !name.chars().next()?.is_ascii_digit())
            {
                name.to_owned()
            } else if !name.contains(['|', '\\']) {
                format!("|{name}|")
            } else {
                return None;
            };
            Some(AletheTerm::Const(name))
        }
        TermNode::BoolConst(value) => Some(AletheTerm::Const(value.to_string())),
        TermNode::App { op, args } => {
            let head = match (op, args.len()) {
                (Op::BoolNot, 1) => "not",
                (Op::BoolAnd, 2) => "and",
                (Op::BoolOr, 2) => "or",
                (Op::BoolXor, 2) => "xor",
                (Op::BoolImplies, 2) => "=>",
                (Op::Ite, 3) => "ite",
                (Op::Eq, 2) => "=",
                _ => return None,
            };
            let children = args
                .iter()
                .map(|&child| convert(arena, child, depth + 1, remaining))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(head.to_owned(), children))
        }
        _ => None,
    }
}

// Keep source assertions before IR constant folding. Restrict command shapes
// until incremental/macro source reconstruction has an explicit contract.
fn source_formulas(input: &str, count: usize) -> Option<Vec<AletheTerm>> {
    if input.len() > 65_536 {
        return None;
    }
    let commands = axeyum_smtlib::read_all(input).ok()?;
    let mut formulas = Vec::new();
    let mut remaining = 512;
    for command in &commands {
        let parts = command.list()?;
        let head = parts.first()?.atom()?;
        match head {
            "assert" if parts.len() == 2 => {
                formulas.push(source_term(&parts[1], 0, &mut remaining)?);
            }
            "declare-const" | "declare-fun" => {
                if matches!(parts.get(1)?.atom()?, "true" | "false") {
                    return None;
                }
            }
            "set-logic" | "set-option" | "set-info" | "check-sat" | "get-proof" | "exit" => {}
            _ => return None,
        }
    }
    (formulas.len() == count).then_some(formulas)
}

fn source_term(
    term: &axeyum_smtlib::SExpr,
    depth: usize,
    remaining: &mut usize,
) -> Option<AletheTerm> {
    if depth > 32 {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    match term {
        axeyum_smtlib::SExpr::Atom(name) if name.len() <= 128 => {
            let atom = if name == "true"
                || name == "false"
                || (name.starts_with('|') && name.ends_with('|'))
                || name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || "_~!@$%^&*+-=<>.?/".contains(c))
            {
                name.clone()
            } else if !name.contains(['|', '\\']) {
                format!("|{name}|")
            } else {
                return None;
            };
            Some(AletheTerm::Const(atom))
        }
        axeyum_smtlib::SExpr::List(parts) => {
            let (head, args) = parts.split_first()?;
            let head = head.atom()?;
            match (head, args.len()) {
                ("not", 1) | ("and" | "or", _) | ("=" | "xor" | "=>", 2) | ("ite", 3) => {}
                _ => return None,
            }
            let children = args
                .iter()
                .map(|arg| source_term(arg, depth + 1, remaining))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(head.to_owned(), children))
        }
        axeyum_smtlib::SExpr::Atom(_) => None,
    }
}
