//! `structural_index_extract` — L3 phase D2's raw feature extractor.
//!
//! `shape_search`/`shape_index` already answer "does a declaration of this
//! type-shape exist?" (conclusion head, hypothesis heads, type constants).
//! This tool does not reindex any of that from scratch; it drives the SAME
//! prelude builders shape_search does and reads the SAME `Kernel` accessors
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
        match kernel.expr_node(expr) {
            ExprNode::App(f, a) => {
                args.push(*a);
                expr = *f;
            }
            _ => {
                args.reverse();
                return (expr, args);
            }
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
        ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Const(_, _) => 1,
        ExprNode::Lit(_) => 1,
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

fn sha256_hex_of_lines(lines: &[String]) -> String {
    // A small dependency-free FNV-1a-based digest is deliberately NOT used
    // here: this repository already has `sha2` on the workspace dependency
    // graph via other checkers reading its output in Python, so the Rust
    // side hashes with the same primitive Python's `hashlib.sha256` uses,
    // computed by hand over bytes (no external crate needed: this is the
    // textbook SHA-256 fixed-point implementation, kept local and untested-
    // library-free on purpose so this extractor adds no new dependency).
    sha256_hex(lines.join("\n").as_bytes())
}

// A minimal, self-contained SHA-256 (FIPS 180-4). Kept here rather than
// pulled from a crate so this extractor adds zero new dependencies to
// axeyum-lean-kernel's example set. Not used anywhere security-sensitive —
// only as a stable content fingerprint for a retrieval index.
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64) * 8;
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
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
        Some("Eq") | Some("Iff") => {
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
