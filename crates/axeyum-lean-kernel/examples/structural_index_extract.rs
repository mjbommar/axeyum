//! `structural_index_extract` — L3 phase D2's raw feature extractor.
//!
//! `shape_search`/`shape_index` already answer "does a declaration of this
//! type-shape exist?" (conclusion head, hypothesis heads, type constants).
//! This tool does not reindex any of that from scratch; it drives the SAME
//! prelude builders `shape_search` does and reads the SAME `Kernel` accessors
//! (`theorem_dependencies`, `declaration_dependencies`,
//! `declaration_type_dependencies`, `display_name`) to add the fields
//! `shape_index::Entry` does not carry: which of a declaration's direct
//! dependencies are THEOREMS vs DEFINITIONS vs RECURSORS, a coarse binder-role
//! classification, a best-effort rewrite direction for `Eq`/`Iff`
//! conclusions, and two derived fingerprints (a full proof-skeleton digest and
//! an "external dependency" digest restricted to names outside the
//! declaration's own namespace — the signal
//! `docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md` D2 calls
//! out as the one that finds `Int.prodRange_permute` from a `Nat.countRange`
//! query, because both name `Nat.restrict_injective` and
//! `Nat.restrict_maps_into` directly and neither name is in either
//! declaration's own namespace).
//!
//! Every value emitted is a DECLARATION NAME (a `String`) or a derived digest
//! over a list of names — never a literal, a numeral, or a rendered proof
//! term. This is deliberate: the index answers "what did this proof use?",
//! never "what did this proof compute?", which is what ADR-0800's type/value
//! split protects for the same reason one namespace over.
//!
//! Output is one JSON array to stdout, entries sorted by rendered name so two
//! runs against the same tree are byte-identical.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example structural_index_extract \
//!   -- --include-constructed > artifacts/structural-index/theorems.json
//! ```

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write;

use axeyum_lean_kernel::shape_index::namespace_root;
use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, build_arith_prelude, build_characterization,
    build_complex_prelude, build_cpoint_prelude, build_creal_prelude, build_int_prelude,
    build_logic_prelude, build_nat_prelude, build_rat_prelude, build_string_prelude,
};

/// Declaration kinds, mirrored from `shape_index::DeclKind` (that enum is not
/// itself `pub` constructible from a bare `&Declaration` outside the crate's
/// own module, so this is a second, independent classification — not a
/// re-export — over the same public `Declaration` enum).
fn decl_kind_label(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        Declaration::Quotient { .. } => "quot",
    }
}

fn telescope(kernel: &Kernel, mut ty: ExprId) -> (Vec<ExprId>, ExprId) {
    let mut binders = Vec::new();
    loop {
        match kernel.expr_node(ty) {
            ExprNode::Pi(_, domain, body, _) => {
                binders.push(*domain);
                ty = *body;
            }
            _ => return (binders, ty),
        }
    }
}

fn head_const(kernel: &Kernel, mut expr: ExprId) -> Option<axeyum_lean_kernel::NameId> {
    loop {
        match kernel.expr_node(expr) {
            ExprNode::App(f, _) => expr = *f,
            ExprNode::Const(name, _) => return Some(*name),
            _ => return None,
        }
    }
}

/// The applied arguments of `expr`, outermost-last, i.e. `f a b c` yields
/// `(f, [a, b, c])`.
fn spine(kernel: &Kernel, mut expr: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    loop {
        if let ExprNode::App(f, a) = kernel.expr_node(expr) {
            args.push(*a);
            expr = *f;
        } else {
            args.reverse();
            return (expr, args);
        }
    }
}

/// A capped, memoized node count — this walks an already-elaborated small
/// TYPE expression (a conclusion's left/right side), never a checked proof
/// VALUE, so it does not run into the delta-unfolding blowups CLAUDE.md
/// documents for defeq checking. The memo table still guards against a
/// pathologically shared DAG.
fn node_count(
    kernel: &Kernel,
    expr: ExprId,
    cap: usize,
    memo: &mut HashMap<ExprId, usize>,
) -> usize {
    if let Some(&n) = memo.get(&expr) {
        return n;
    }
    if memo.len() > cap {
        return cap;
    }
    let n = match kernel.expr_node(expr) {
        ExprNode::BVar(_)
        | ExprNode::FVar(_)
        | ExprNode::Sort(_)
        | ExprNode::Const(_, _)
        | ExprNode::Lit(_) => 1,
        ExprNode::Proj(_, _, inner) => 1 + node_count(kernel, *inner, cap, memo),
        ExprNode::App(f, a) => {
            1 + node_count(kernel, *f, cap, memo) + node_count(kernel, *a, cap, memo)
        }
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            1 + node_count(kernel, *ty, cap, memo) + node_count(kernel, *body, cap, memo)
        }
        ExprNode::Let(_, ty, val, body) => {
            1 + node_count(kernel, *ty, cap, memo)
                + node_count(kernel, *val, cap, memo)
                + node_count(kernel, *body, cap, memo)
        }
    };
    memo.insert(expr, n);
    n
}

const CARRIER_HEADS: &[&str] = &[
    "Nat", "Int", "Rat", "AxReal", "CReal", "Complex", "Bool", "String", "Char", "Nat.Pair",
    "Nat.Fin",
];
const CONNECTIVE_HEADS: &[&str] = &[
    "Eq", "Iff", "Le", "Lt", "Ne", "Not", "And", "Or", "Dvd", "Exists", "Nat.le", "True", "False",
];

fn binder_role(head: Option<&str>) -> &'static str {
    match head {
        None => "unknown",
        Some(h) if CARRIER_HEADS.contains(&h) => "carrier",
        Some(h) if CONNECTIVE_HEADS.contains(&h) => "connective",
        Some(_) => "hypothesis",
    }
}

/// A stable content fingerprint over a sorted list of declaration NAMES --
/// never a proof value. Uses the same primitive Python's `hashlib.sha256`
/// does (`sha2`, already resolved in `Cargo.lock` via other workspace
/// crates), so a Python-side re-check of this digest is a one-line
/// `hashlib.sha256(...).hexdigest()` away if ever needed.
fn sha256_hex_of_lines(lines: &[String]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(lines.join("\n").as_bytes());
    hasher
        .finalize()
        .iter()
        .fold(String::with_capacity(64), |mut out, byte| {
            use std::fmt::Write as _;
            let _ = write!(out, "{byte:02x}");
            out
        })
}

fn json_escape(s: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

fn json_str(s: &str) -> String {
    format!("\"{}\"", json_escape(s))
}

fn json_opt_str(s: Option<&str>) -> String {
    match s {
        Some(s) => json_str(s),
        None => "null".to_owned(),
    }
}

fn json_str_array(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|s| json_str(s)).collect();
    format!("[{}]", parts.join(","))
}

struct Record {
    name: String,
    kind: &'static str,
    namespace: String,
    groups: BTreeSet<String>,
    arity: usize,
    binder_heads: Vec<Option<String>>,
    binder_roles: Vec<&'static str>,
    concl_head: Option<String>,
    type_constants: BTreeSet<String>,
    definitions_used: BTreeSet<String>,
    theorem_dependencies: BTreeSet<String>,
    recursors_used: BTreeSet<String>,
    rewrite_direction: &'static str,
    rewrite_note: String,
    proof_skeleton_digest: String,
    external_dependency_fingerprint: Vec<String>,
    external_dependency_digest: String,
}

// One record per declaration, gathering nine independent, already-tested
// `Kernel` accessors plus two small local heuristics (binder role, rewrite
// direction) -- splitting it would scatter one declaration's derivation
// across several functions each taking most of the same arguments back.
#[allow(clippy::too_many_lines)]
fn build_record(kernel: &Kernel, declaration: &Declaration, group: &str) -> Record {
    let name_id = declaration.name();
    let name = kernel.display_name(name_id).to_string();
    let ty = declaration.ty();
    let (binders, conclusion) = telescope(kernel, ty);
    let binder_heads: Vec<Option<String>> = binders
        .iter()
        .map(|&domain| {
            let (_, inner) = telescope(kernel, domain);
            head_const(kernel, inner).map(|h| kernel.display_name(h).to_string())
        })
        .collect();
    let binder_roles: Vec<&'static str> = binder_heads
        .iter()
        .map(|h| binder_role(h.as_deref()))
        .collect();
    let concl_head = head_const(kernel, conclusion).map(|h| kernel.display_name(h).to_string());

    let type_constants: BTreeSet<String> = kernel
        .declaration_type_dependencies(name_id)
        .into_iter()
        .map(|d| kernel.display_name(d).to_string())
        .collect();

    let theorem_dependencies: BTreeSet<String> = kernel
        .theorem_dependencies(name_id)
        .into_iter()
        .map(|d| kernel.display_name(d).to_string())
        .collect();

    let mut definitions_used = BTreeSet::new();
    let mut recursors_used = BTreeSet::new();
    for dep in kernel.declaration_dependencies(name_id) {
        let Some(dep_decl) = kernel.environment().get(dep) else {
            continue;
        };
        let rendered = kernel.display_name(dep).to_string();
        match dep_decl {
            Declaration::Definition { .. } => {
                definitions_used.insert(rendered);
            }
            Declaration::Recursor { .. } => {
                recursors_used.insert(rendered);
            }
            _ => {}
        }
    }

    // Rewrite direction: only meaningful for an Eq/Iff conclusion, and only a
    // heuristic — it compares the elaborated NODE COUNT of the conclusion's
    // last two applied arguments (the presumed lhs/rhs), never their values.
    let (rewrite_direction, rewrite_note) = match concl_head.as_deref() {
        Some("Eq" | "Iff") => {
            let (_, args) = spine(kernel, conclusion);
            if args.len() >= 2 {
                let rhs = args[args.len() - 1];
                let lhs = args[args.len() - 2];
                let mut memo = HashMap::new();
                let lhs_n = node_count(kernel, lhs, 5000, &mut memo);
                let rhs_n = node_count(kernel, rhs, 5000, &mut memo);
                let note = format!("lhs_nodes={lhs_n} rhs_nodes={rhs_n}");
                let direction = match lhs_n.cmp(&rhs_n) {
                    std::cmp::Ordering::Greater => "lhs_to_rhs",
                    std::cmp::Ordering::Less => "rhs_to_lhs",
                    std::cmp::Ordering::Equal => "symmetric",
                };
                (direction, note)
            } else {
                ("n/a", String::from("fewer than 2 trailing args"))
            }
        }
        _ => ("n/a", String::from("conclusion is not Eq/Iff")),
    };

    let namespace = namespace_root(&name).to_owned();

    let mut skeleton_tokens: Vec<String> = Vec::new();
    skeleton_tokens.extend(type_constants.iter().map(|c| format!("type:{c}")));
    skeleton_tokens.extend(definitions_used.iter().map(|c| format!("def:{c}")));
    skeleton_tokens.extend(theorem_dependencies.iter().map(|c| format!("thm:{c}")));
    skeleton_tokens.extend(recursors_used.iter().map(|c| format!("rec:{c}")));
    skeleton_tokens.sort();
    let proof_skeleton_digest = sha256_hex_of_lines(&skeleton_tokens);

    let mut external_dependency_fingerprint: Vec<String> = theorem_dependencies
        .iter()
        .chain(recursors_used.iter())
        .chain(definitions_used.iter())
        .filter(|c| namespace_root(c) != namespace)
        .cloned()
        .collect();
    external_dependency_fingerprint.sort();
    external_dependency_fingerprint.dedup();
    let external_dependency_digest = sha256_hex_of_lines(&external_dependency_fingerprint);

    Record {
        name,
        kind: decl_kind_label(declaration),
        namespace,
        groups: [group.to_owned()].into_iter().collect(),
        arity: binders.len(),
        binder_heads,
        binder_roles,
        concl_head,
        type_constants,
        definitions_used,
        theorem_dependencies,
        recursors_used,
        rewrite_direction,
        rewrite_note,
        proof_skeleton_digest,
        external_dependency_fingerprint,
        external_dependency_digest,
    }
}

fn record_to_json(r: &Record) -> String {
    let binders_json: Vec<String> = r
        .binder_heads
        .iter()
        .zip(r.binder_roles.iter())
        .enumerate()
        .map(|(i, (head, role))| {
            format!(
                "{{\"index\":{i},\"head\":{},\"role\":{}}}",
                json_opt_str(head.as_deref()),
                json_str(role)
            )
        })
        .collect();
    let type_constants: Vec<String> = r.type_constants.iter().cloned().collect();
    let definitions_used: Vec<String> = r.definitions_used.iter().cloned().collect();
    let theorem_dependencies: Vec<String> = r.theorem_dependencies.iter().cloned().collect();
    let recursors_used: Vec<String> = r.recursors_used.iter().cloned().collect();
    let groups: Vec<String> = r.groups.iter().cloned().collect();
    format!(
        "{{\"name\":{},\"kind\":{},\"namespace\":{},\"groups\":{},\"arity\":{},\"binders\":[{}],\"concl_head\":{},\"type_constants\":{},\"definitions_used\":{},\"theorem_dependencies\":{},\"recursors_used\":{},\"rewrite_direction\":{},\"rewrite_direction_note\":{},\"proof_skeleton_digest\":{},\"external_dependency_fingerprint\":{},\"external_dependency_digest\":{}}}",
        json_str(&r.name),
        json_str(r.kind),
        json_str(&r.namespace),
        json_str_array(&groups),
        r.arity,
        binders_json.join(","),
        json_opt_str(r.concl_head.as_deref()),
        json_str_array(&type_constants),
        json_str_array(&definitions_used),
        json_str_array(&theorem_dependencies),
        json_str_array(&recursors_used),
        json_str(r.rewrite_direction),
        json_str(&r.rewrite_note),
        json_str(&r.proof_skeleton_digest),
        json_str_array(&r.external_dependency_fingerprint),
        json_str(&r.external_dependency_digest),
    )
}

fn main() {
    let include_constructed = std::env::args().any(|a| a == "--include-constructed");

    let mut merged: BTreeMap<String, Record> = BTreeMap::new();
    let insert_all = |kernel: &Kernel, group: &str, merged: &mut BTreeMap<String, Record>| {
        for (_, declaration) in kernel.environment().iter() {
            let record = build_record(kernel, declaration, group);
            merged
                .entry(record.name.clone())
                .and_modify(|existing| {
                    existing.groups.insert(group.to_owned());
                })
                .or_insert(record);
        }
    };

    let mut logic = Kernel::new();
    build_logic_prelude(&mut logic).expect("logic prelude must build");
    insert_all(&logic, "logic", &mut merged);

    let mut nat = Kernel::new();
    build_nat_prelude(&mut nat).expect("Nat prelude must build");
    insert_all(&nat, "nat", &mut merged);

    let mut axreal = Kernel::new();
    build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    insert_all(&axreal, "axreal", &mut merged);

    let mut integer = Kernel::new();
    build_int_prelude(&mut integer).expect("Int prelude must build");
    insert_all(&integer, "integer", &mut merged);

    let mut rational = Kernel::new();
    build_rat_prelude(&mut rational).expect("Rat prelude must build");
    insert_all(&rational, "rat", &mut merged);

    let mut characterization = Kernel::new();
    build_characterization(&mut characterization).expect("characterization must build");
    insert_all(&characterization, "characterization", &mut merged);

    let mut string = Kernel::new();
    let string_handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    build_string_prelude(&mut string, string_handle, 2).expect("string prelude must build");
    insert_all(&string, "string", &mut merged);

    if include_constructed {
        let mut creal = Kernel::new();
        build_creal_prelude(&mut creal).expect("CReal prelude must build");
        insert_all(&creal, "creal", &mut merged);

        let mut complex = Kernel::new();
        build_complex_prelude(&mut complex).expect("Complex prelude must build");
        insert_all(&complex, "complex", &mut merged);

        let mut cpoint = Kernel::new();
        build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
        insert_all(&cpoint, "cpoint", &mut merged);
    }

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    write!(out, "[").expect("write");
    for (i, (_, record)) in merged.iter().enumerate() {
        if i > 0 {
            write!(out, ",").expect("write");
        }
        write!(out, "{}", record_to_json(record)).expect("write");
    }
    writeln!(out, "]").expect("write");
    eprintln!(
        "structural_index_extract: {} declarations, include_constructed={}",
        merged.len(),
        include_constructed
    );
}
