//! Bounded source-preserving Boolean/LIA composition. Integer lemmas are internal.
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_smtlib::SExpr;

use crate::backend::SolverConfig;

pub(crate) fn prove(input: &str, config: &SolverConfig) -> Option<Vec<AletheCommand>> {
    if input.len() > 65_536 {
        return None;
    }
    let timeout = config.timeout.unwrap_or(Duration::from_secs(10));
    if timeout.is_zero() {
        return None;
    }
    let deadline = Instant::now().checked_add(timeout)?;
    let commands = axeyum_smtlib::read_all(input).ok()?;
    let (mut state, source) = collect_source(&commands)?;
    let formulas = source
        .iter()
        .map(|term| state.boolean(term, 0))
        .collect::<Option<Vec<_>>>()?;
    if state.atoms.is_empty() {
        return None;
    }
    let mut theory = Vec::new();
    for assignment in 0..(1_usize << state.atoms.len()) {
        if Instant::now() >= deadline {
            return None;
        }
        let clause: Vec<_> = state
            .atoms
            .iter()
            .enumerate()
            .map(|(i, (_, atom))| AletheLit {
                atom: atom.clone(),
                negated: assignment & (1 << i) != 0,
            })
            .collect();
        if crate::alethe_lra::la_generic_check_pub("lia_generic", &clause) == Some(true) {
            theory.push(
                state
                    .atoms
                    .iter()
                    .enumerate()
                    .map(|(i, (name, _))| AletheLit {
                        atom: AletheTerm::Const(name.clone()),
                        negated: assignment & (1 << i) != 0,
                    })
                    .collect(),
            );
        }
    }
    let (mut proof, _) = crate::qfbv_alethe::prove_bit_gate_unsat_alethe_with_theory(
        &formulas,
        BTreeMap::new(),
        &theory,
        Some(deadline),
    )?;
    if proof.len() > 20_000 || Instant::now() >= deadline {
        return None;
    }
    let replacements: BTreeMap<_, _> = state.atoms.into_iter().collect();
    for command in &mut proof {
        match command {
            AletheCommand::Assume { clause, .. } => {
                for literal in clause {
                    substitute(&mut literal.atom, &replacements);
                }
            }
            AletheCommand::Step { clause, args, .. } => {
                for literal in clause {
                    substitute(&mut literal.atom, &replacements);
                }
                for arg in args {
                    substitute(arg, &replacements);
                }
            }
        }
    }
    let serialized = axeyum_cnf::write_alethe(&proof);
    let replay = axeyum_cnf::parse_alethe(&serialized).ok()?;
    if !matches!(crate::check_alethe_lra(&replay), Ok(true)) || Instant::now() >= deadline {
        return None;
    }
    Some(replay)
}

fn collect_source(commands: &[SExpr]) -> Option<(Converter, Vec<&SExpr>)> {
    let mut sorts = BTreeMap::new();
    let mut source = Vec::new();
    for command in commands {
        let row = command.list()?;
        match row.first()?.atom()? {
            "declare-const" if row.len() == 3 => {
                let name = row[1].atom()?;
                let sort = row[2].atom()?;
                if name.len() > 128
                    || matches!(name, "true" | "false")
                    || name.parse::<i128>().is_ok()
                    || !matches!(sort, "Bool" | "Int")
                {
                    return None;
                }
                sorts.insert(name.to_owned(), sort.to_owned());
            }
            "declare-fun" if row.len() == 4 && row[2].list()?.is_empty() => {
                let name = row[1].atom()?;
                let sort = row[3].atom()?;
                if name.len() > 128
                    || matches!(name, "true" | "false")
                    || name.parse::<i128>().is_ok()
                    || !matches!(sort, "Bool" | "Int")
                {
                    return None;
                }
                sorts.insert(name.to_owned(), sort.to_owned());
            }
            "assert" if row.len() == 2 => source.push(&row[1]),
            "set-logic" | "set-option" | "set-info" | "check-sat" | "get-proof" | "exit" => {}
            _ => return None,
        }
    }
    if source.len() > 128 {
        return None;
    }
    let state = Converter {
        sorts,
        atoms: Vec::new(),
        remaining: 512,
    };
    Some((state, source))
}

fn substitute(term: &mut AletheTerm, replacements: &BTreeMap<String, AletheTerm>) {
    match term {
        AletheTerm::Const(name) => {
            if let Some(original) = replacements.get(name) {
                *term = original.clone();
            }
        }
        AletheTerm::App(_, args) | AletheTerm::Indexed { args, .. } => {
            for arg in args {
                substitute(arg, replacements);
            }
        }
    }
}

struct Converter {
    sorts: BTreeMap<String, String>,
    atoms: Vec<(String, AletheTerm)>,
    remaining: usize,
}

impl Converter {
    fn visit(&mut self, depth: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(1)?;
        (depth <= 32).then_some(())
    }

    fn integer(&mut self, term: &SExpr, depth: usize) -> Option<AletheTerm> {
        self.visit(depth)?;
        match term {
            SExpr::Atom(name)
                if name.len() <= 128
                    && ((!name.is_empty() && name.bytes().all(|b| b.is_ascii_digit()))
                        || self.sorts.get(name).is_some_and(|s| s == "Int")) =>
            {
                Some(AletheTerm::Const(source_atom(name)?))
            }
            SExpr::List(row) => {
                let head = row.first()?.atom()?;
                if !matches!((head, row.len() - 1), ("-", 1 | 2) | ("+" | "*", 2)) {
                    return None;
                }
                let args = row[1..]
                    .iter()
                    .map(|arg| self.integer(arg, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                Some(AletheTerm::App(head.to_owned(), args))
            }
            SExpr::Atom(_) => None,
        }
    }

    fn boolean(&mut self, term: &SExpr, depth: usize) -> Option<AletheTerm> {
        self.visit(depth)?;
        match term {
            SExpr::Atom(name)
                if matches!(name.as_str(), "true" | "false")
                    || self.sorts.get(name).is_some_and(|s| s == "Bool") =>
            {
                Some(AletheTerm::Const(source_atom(name)?))
            }
            SExpr::List(row) => {
                let head = row.first()?.atom()?;
                if matches!(head, "=" | "<" | "<=" | ">" | ">=") && row.len() == 3 {
                    // Failed arithmetic probing must not consume the Boolean budget.
                    let saved = self.remaining;
                    let integer_args = row[1..]
                        .iter()
                        .map(|arg| self.integer(arg, depth + 1))
                        .collect::<Option<Vec<_>>>();
                    if let Some(args) = integer_args {
                        let atom = AletheTerm::App(head.to_owned(), args);
                        if let Some((name, _)) = self.atoms.iter().find(|(_, a)| a == &atom) {
                            return Some(AletheTerm::Const(source_atom(name)?));
                        }
                        if self.atoms.len() >= 8 {
                            return None;
                        }
                        let mut index = self.atoms.len();
                        let name = loop {
                            let candidate = format!("|@axeyum_lia_atom_{index}|");
                            if !self.sorts.contains_key(&candidate)
                                && !self.sorts.contains_key(candidate.trim_matches('|'))
                                && !self.atoms.iter().any(|(n, _)| n == &candidate)
                            {
                                break candidate;
                            }
                            index += 1;
                        };
                        self.atoms.push((name.clone(), atom));
                        return Some(AletheTerm::Const(name));
                    }
                    self.remaining = saved;
                }
                if !matches!(
                    (head, row.len() - 1),
                    ("not", 1) | ("and" | "or", _) | ("=" | "xor" | "=>", 2) | ("ite", 3)
                ) {
                    return None;
                }
                let args = row[1..]
                    .iter()
                    .map(|arg| self.boolean(arg, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                Some(AletheTerm::App(head.to_owned(), args))
            }
            SExpr::Atom(_) => None,
        }
    }
}

fn source_atom(name: &str) -> Option<String> {
    if (name.starts_with('|') && name.ends_with('|'))
        || name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "_~!@$%^&*+-=<>.?/".contains(c))
    {
        Some(name.to_owned())
    } else if !name.contains(['|', '\\']) {
        Some(format!("|{name}|"))
    } else {
        None
    }
}
