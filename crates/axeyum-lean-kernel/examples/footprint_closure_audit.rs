//! Does `Kernel::axiom_footprint`'s dependency DAG cover the ENTIRETY of what
//! a theorem rests on — or can an assumption be absorbed at a node the
//! closure never reaches?
//!
//! `Kernel::decl_deps` (private, `lean_pp.rs`) collects, for an `Inductive`,
//! only the constants in the inductive's OWN type — deliberately: a
//! constructor's type is not what a proof rests on when the proof never
//! mentions the constructor. But the module RENDERER (`Kernel::render_deps`)
//! widens exactly this case, adding the constructors' types, because a
//! rendered module has to declare them before the family. If a proof uses an
//! inductive FAMILY as a type without ever mentioning a constructor, and a
//! constructor's type (or the family's recursor's type) reaches a trusted
//! declaration, `axiom_footprint` never sees the edge — even though the
//! family's well-formedness depends on it.
//!
//! This is a diagnostic, not a fix. It does **not** modify `axiom_footprint`,
//! `decl_deps`, or any prelude. It reimplements the narrow walk and a WIDENED
//! walk (constructors' types **and** the recursor's type — one step further
//! than `render_deps`, which only widens for constructors) entirely over the
//! kernel's **public** surface (`environment()`, `expr_node`,
//! `Declaration::ty`/`value`, `anon`/`name_str`), specifically so this file
//! never has to touch `lean_pp.rs`. Fidelity of the reimplementation is
//! checked, not assumed: for every theorem in every prelude this asserts the
//! narrow closure's trusted subset equals `Kernel::axiom_footprint`'s own
//! answer, and the narrow closure's full membership equals
//! `Kernel::declaration_dependency_closure`'s own answer. A mismatch aborts
//! the run rather than silently reporting a wrong number.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example footprint_closure_audit \
//!   -- --include-constructed
//! ```
//!
//! # What this does NOT establish
//!
//! The kernel's own reduction and typing rules (β/η/δ/ι/ζ, proof
//! irrelevance, strict positivity, universe constraints, elimination
//! restrictions) justify every non-leaf node in this graph and are entirely
//! outside it — they are checked by differential replay against official
//! Lean 4.30.0, not by this audit. A declaration name that resolves to
//! nothing in the environment yields a vacuously empty footprint from that
//! edge; this audit counts those ("dangling" references) separately rather
//! than silently treating them as "no dependency".

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, Lit, NameId, build_arith_prelude, build_complex_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_logic_prelude,
    build_nat_prelude, build_rat_prelude, build_string_prelude,
};

/// Declaration-kind label used in closure-composition histograms.
fn kind_label(decl: &Declaration) -> &'static str {
    match decl {
        Declaration::Axiom { .. } => "Axiom",
        Declaration::Definition { .. } => "Definition",
        Declaration::Theorem { .. } => "Theorem",
        Declaration::Opaque { .. } => "Opaque",
        Declaration::Inductive { .. } => "Inductive",
        Declaration::Constructor { .. } => "Constructor",
        Declaration::Recursor { .. } => "Recursor",
        Declaration::Quotient { .. } => "Quotient",
    }
}

fn is_trusted(decl: &Declaration) -> bool {
    matches!(
        decl,
        Declaration::Axiom { .. } | Declaration::Opaque { .. } | Declaration::Quotient { .. }
    )
}

/// `Kernel::collect_const_deps` (private to `lean_pp.rs`), reimplemented over
/// the crate's PUBLIC surface only: `expr_node`, and the `ExprNode` variants
/// themselves are public. This is the audit's edge-collection primitive and
/// must match the kernel's private walk exactly; fidelity is checked in
/// `main` rather than assumed.
///
/// `string_lit_hits` counts how many times the `Lit::Str` arm actually fires,
/// across the whole run — a real counter, not an assumption, so if a FUTURE
/// prelude starts embedding string literals in a theorem's type/value, that
/// shows up as a nonzero count in the summary rather than silently changing
/// this audit's edge set.
fn collect_const_deps(
    kernel: &Kernel,
    root: ExprId,
    out: &mut Vec<NameId>,
    string_deps: &[NameId],
    string_lit_hits: &mut usize,
) {
    let mut visited: HashSet<ExprId> = HashSet::new();
    let mut stack = vec![root];
    while let Some(e) = stack.pop() {
        if !visited.insert(e) {
            continue;
        }
        match kernel.expr_node(e) {
            ExprNode::Const(n, _) => out.push(*n),
            ExprNode::Proj(type_name, _, structure) => {
                out.push(*type_name);
                stack.push(*structure);
            }
            ExprNode::App(f, a) => {
                stack.push(*f);
                stack.push(*a);
            }
            ExprNode::Lam(_, t, b, _) | ExprNode::Pi(_, t, b, _) => {
                stack.push(*t);
                stack.push(*b);
            }
            ExprNode::Let(_, t, v, b) => {
                stack.push(*t);
                stack.push(*v);
                stack.push(*b);
            }
            ExprNode::Lit(Lit::Str(_)) => {
                *string_lit_hits += 1;
                out.extend(string_deps.iter().copied());
            }
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Lit(Lit::Nat(_)) => {}
        }
    }
}

/// `Kernel::decl_deps`, reimplemented: the constants in a declaration's type,
/// plus (for `Definition`/`Theorem`/`Opaque`, i.e. wherever `Declaration::value`
/// returns `Some`) the constants in its value. This is the NARROW edge set —
/// exactly what `axiom_footprint` uses.
fn decl_deps_of(
    kernel: &Kernel,
    name: NameId,
    string_deps: &[NameId],
    string_lit_hits: &mut usize,
) -> Vec<NameId> {
    let mut deps = Vec::new();
    if let Some(decl) = kernel.environment().get(name) {
        collect_const_deps(kernel, decl.ty(), &mut deps, string_deps, string_lit_hits);
        if let Some(value) = decl.value() {
            collect_const_deps(kernel, value, &mut deps, string_deps, string_lit_hits);
        }
    }
    deps
}

/// The constants an `Inductive`'s CONSTRUCTORS' types mention (empty for any
/// other declaration kind). Split out from [`recursor_deps_of`] so the
/// audit can attribute an edge-set difference to one source or the other
/// rather than reporting only that widening changed something.
fn ctor_deps_of(
    kernel: &Kernel,
    name: NameId,
    string_deps: &[NameId],
    string_lit_hits: &mut usize,
) -> Vec<NameId> {
    let mut deps = Vec::new();
    if let Some(Declaration::Inductive { ctor_names, .. }) = kernel.environment().get(name) {
        for &ctor in ctor_names {
            deps.extend(decl_deps_of(kernel, ctor, string_deps, string_lit_hits));
        }
    }
    deps
}

/// The constants an `Inductive`'s RECURSOR's type mentions (empty if `name`
/// is not an inductive with a recursor this audit could resolve).
fn recursor_deps_of(
    kernel: &Kernel,
    name: NameId,
    string_deps: &[NameId],
    rec_of: &HashMap<NameId, NameId>,
    string_lit_hits: &mut usize,
) -> Vec<NameId> {
    match rec_of.get(&name) {
        Some(&rec_name) => decl_deps_of(kernel, rec_name, string_deps, string_lit_hits),
        None => Vec::new(),
    }
}

/// `decl_deps_of`, WIDENED for an `Inductive`: also the constants its
/// constructors' types mention, and the constants its RECURSOR's type
/// mentions. `Kernel::render_deps` (the module renderer's edge set) widens
/// only with constructor types; this goes one step further per the task,
/// because a recursor's type can itself mention a trusted declaration the
/// narrow walk never reaches.
fn widened_deps_of(
    kernel: &Kernel,
    name: NameId,
    string_deps: &[NameId],
    rec_of: &HashMap<NameId, NameId>,
    string_lit_hits: &mut usize,
) -> Vec<NameId> {
    let mut deps = decl_deps_of(kernel, name, string_deps, string_lit_hits);
    deps.extend(ctor_deps_of(kernel, name, string_deps, string_lit_hits));
    deps.extend(recursor_deps_of(
        kernel,
        name,
        string_deps,
        rec_of,
        string_lit_hits,
    ));
    deps
}

/// `Kernel::string_literal_dependency_names` (`pub(crate)`, `lean_export.rs`),
/// re-derived from the PUBLIC, idempotent `anon`/`name_str` interning
/// surface. Interning is a lookup-or-create, so calling this can only ever
/// return an EXISTING name if one was already built by some prelude, or mint
/// an unused, harmless name otherwise — it can never fabricate a declaration.
/// In every prelude this audit covers, no term contains an
/// `ExprNode::Lit(Lit::Str(_))` node at all (`Lit::Str` is constructed only in
/// `tc.rs` string-literal type inference and in unit tests; the free-monoid
/// `string_prelude` represents strings via `Str.cons`/`Char.cN` applications,
/// never via the literal node) — confirmed below by a runtime counter that
/// this path fires zero times.
fn string_literal_dependency_names(kernel: &mut Kernel) -> Vec<NameId> {
    let anon = kernel.anon();
    let string = kernel.name_str(anon, "String");
    let char_ = kernel.name_str(anon, "Char");
    let list = kernel.name_str(anon, "List");
    let nat = kernel.name_str(anon, "Nat");
    let of_list = kernel.name_str(string, "ofList");
    let char_of_nat = kernel.name_str(char_, "ofNat");
    vec![string, char_, list, nat, of_list, char_of_nat]
}

/// `name.rec` for every declared `Inductive`, via the public, idempotent
/// `name_str` interner (a lookup-or-create against the SAME chain
/// `Kernel::add_inductive` always uses to mint a family's recursor name —
/// confirmed by grep: every prelude names its recursor
/// `kernel.name_str(family.name, "rec")`). This can only resolve to the
/// recursor the environment actually contains, or (if inductive admission
/// changes shape in the future) a dangling name the audit already handles.
fn recursor_names(kernel: &mut Kernel) -> HashMap<NameId, NameId> {
    let inductive_names: Vec<NameId> = kernel
        .environment()
        .iter()
        .filter(|&(_, d)| matches!(d, Declaration::Inductive { .. }))
        .map(|(_, d)| d.name())
        .collect();
    inductive_names
        .into_iter()
        .map(|name| {
            let rec = kernel.name_str(name, "rec");
            (name, rec)
        })
        .collect()
}

/// The transitive closure from `root`, mirroring `Kernel::axiom_footprint`'s
/// BFS shape exactly (`seen` seeded with `root`, popped worklist, insert only
/// if new). `widen` selects `decl_deps_of` (narrow) or `widened_deps_of`
/// (widened) as the edge function at EVERY node, so a widened edge discovered
/// partway through the walk is itself widened when it is an inductive.
struct Closure {
    /// Reachable declarations, excluding `root` itself.
    reached: BTreeSet<NameId>,
    /// Names some reached declaration (or `root`) mentions that resolve to
    /// nothing in the environment at all.
    dangling: BTreeSet<NameId>,
}

fn closure_from(
    kernel: &Kernel,
    root: NameId,
    widen: bool,
    string_deps: &[NameId],
    rec_of: &HashMap<NameId, NameId>,
    string_lit_hits: &mut usize,
) -> Closure {
    let mut seen: BTreeSet<NameId> = BTreeSet::new();
    let mut dangling: BTreeSet<NameId> = BTreeSet::new();
    let mut work = vec![root];
    seen.insert(root);
    while let Some(n) = work.pop() {
        let deps = if widen {
            widened_deps_of(kernel, n, string_deps, rec_of, string_lit_hits)
        } else {
            decl_deps_of(kernel, n, string_deps, string_lit_hits)
        };
        for d in deps {
            if kernel.environment().get(d).is_none() {
                dangling.insert(d);
                continue;
            }
            if seen.insert(d) {
                work.push(d);
            }
        }
    }
    seen.remove(&root);
    Closure {
        reached: seen,
        dangling,
    }
}

fn kind_counts(kernel: &Kernel, names: &BTreeSet<NameId>) -> BTreeMap<&'static str, usize> {
    let mut counts = BTreeMap::new();
    for &n in names {
        if let Some(decl) = kernel.environment().get(n) {
            *counts.entry(kind_label(decl)).or_insert(0) += 1;
        }
    }
    counts
}

fn trusted_name_strings(kernel: &Kernel, names: &BTreeSet<NameId>) -> BTreeSet<String> {
    names
        .iter()
        .filter(|&&n| kernel.environment().get(n).is_some_and(is_trusted))
        .map(|&n| kernel.display_name(n).to_string())
        .collect()
}

fn format_counts(counts: &BTreeMap<&'static str, usize>) -> String {
    counts
        .iter()
        .map(|(k, v)| format!("{k}={v}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// Build every prelude group the theorem inventories build, in dependency
/// order (mirrors `prelude_theorem_inventory.rs`).
fn build_groups(include_constructed: bool) -> Vec<(&'static str, Kernel)> {
    let mut groups: Vec<(&str, Kernel)> = Vec::new();

    let mut logic = Kernel::new();
    let _ = build_logic_prelude(&mut logic).expect("logic prelude must build");
    groups.push(("logic", logic));

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    groups.push(("nat", nat));

    let mut axreal = Kernel::new();
    let _ = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    groups.push(("axreal", axreal));

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    groups.push(("integer", integer));

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    groups.push(("rat", rational));

    let mut string = Kernel::new();
    let handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, handle, 2).expect("string prelude must build");
    groups.push(("string", string));

    if include_constructed {
        let mut creal = Kernel::new();
        let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
        groups.push(("creal", creal));

        let mut complex = Kernel::new();
        let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
        groups.push(("complex", complex));

        let mut cpoint = Kernel::new();
        let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
        groups.push(("cpoint", cpoint));
    }
    groups
}

/// Everything computed and cross-checked for ONE theorem: the narrow/widened
/// trusted footprints, the closure-composition histogram, the reachable-set
/// (for the caller's per-prelude union), and any inductive whose widened
/// edges reach outside the narrow closure (secondary finding #1). Pulled out
/// of `main` so the per-prelude loop stays under clippy's line budget.
struct TheoremAudit {
    name: String,
    kind_counts_str: String,
    narrow_dangling: usize,
    narrow_trusted: BTreeSet<String>,
    widened_trusted: BTreeSet<String>,
    widened_dangling: usize,
    edge_diff_str: String,
    has_edge_diff: bool,
    reached: BTreeSet<NameId>,
    dangling: BTreeSet<NameId>,
}

fn audit_theorem(
    kernel: &Kernel,
    label: &str,
    name: NameId,
    string_deps: &[NameId],
    rec_of: &HashMap<NameId, NameId>,
    string_lit_hits: &mut usize,
) -> TheoremAudit {
    let theorem_name_str = kernel.display_name(name).to_string();

    let narrow = closure_from(kernel, name, false, string_deps, rec_of, string_lit_hits);
    let widened = closure_from(kernel, name, true, string_deps, rec_of, string_lit_hits);

    // --- fidelity cross-checks: this reimplementation must agree with the
    // kernel's own private-walk-backed public methods. ---
    let narrow_trusted = trusted_name_strings(kernel, &narrow.reached);
    let axiom_footprint_names: BTreeSet<String> = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|id| kernel.display_name(id).to_string())
        .collect();
    assert_eq!(
        narrow_trusted, axiom_footprint_names,
        "reimplementation diverges from axiom_footprint for {label}::{theorem_name_str}"
    );

    let full_closure_names: BTreeSet<String> = kernel
        .declaration_dependency_closure(name)
        .into_iter()
        .map(|id| kernel.display_name(id).to_string())
        .collect();
    let narrow_all_names: BTreeSet<String> = narrow
        .reached
        .iter()
        .map(|&id| kernel.display_name(id).to_string())
        .collect();
    assert_eq!(
        narrow_all_names, full_closure_names,
        "reimplementation diverges from declaration_dependency_closure for \
         {label}::{theorem_name_str}"
    );

    let widened_trusted = trusted_name_strings(kernel, &widened.reached);

    // Secondary finding #1: an inductive in the NARROW closure whose widened
    // edges (ctor types, recursor type) reach outside the narrow closure at
    // all, trusted or not -- the precondition for the headline gap. Ctor and
    // recursor contributions are attributed separately so the write-up can
    // say WHICH source introduces the extra edge, not just that widening
    // changed something.
    let mut edge_diffs: Vec<(String, Vec<String>)> = Vec::new();
    for &n in &narrow.reached {
        if matches!(
            kernel.environment().get(n),
            Some(Declaration::Inductive { .. })
        ) {
            let narrow_of_n: BTreeSet<NameId> =
                decl_deps_of(kernel, n, string_deps, string_lit_hits)
                    .into_iter()
                    .collect();
            let outside = |d: &NameId| *d != n && *d != name && !narrow.reached.contains(d);

            let ctor_extra: Vec<NameId> = ctor_deps_of(kernel, n, string_deps, string_lit_hits)
                .into_iter()
                .filter(|d| !narrow_of_n.contains(d))
                .filter(outside)
                .collect();
            let rec_extra: Vec<NameId> =
                recursor_deps_of(kernel, n, string_deps, rec_of, string_lit_hits)
                    .into_iter()
                    .filter(|d| !narrow_of_n.contains(d))
                    .filter(outside)
                    .collect();

            if !ctor_extra.is_empty() || !rec_extra.is_empty() {
                let render = |ids: &[NameId]| -> String {
                    let names: BTreeSet<String> = ids
                        .iter()
                        .map(|&id| kernel.display_name(id).to_string())
                        .collect();
                    names.into_iter().collect::<Vec<_>>().join(";")
                };
                edge_diffs.push((
                    kernel.display_name(n).to_string(),
                    vec![format!(
                        "ctor=[{}];rec=[{}]",
                        render(&ctor_extra),
                        render(&rec_extra)
                    )],
                ));
            }
        }
    }

    TheoremAudit {
        name: theorem_name_str,
        kind_counts_str: format_counts(&kind_counts(kernel, &narrow.reached)),
        narrow_dangling: narrow.dangling.len(),
        has_edge_diff: !edge_diffs.is_empty(),
        edge_diff_str: edge_diffs
            .iter()
            .map(|(ind, extra)| format!("{ind}:[{}]", extra.join(";")))
            .collect::<Vec<_>>()
            .join("|"),
        widened_dangling: widened.dangling.len(),
        reached: narrow.reached,
        dangling: narrow.dangling,
        narrow_trusted,
        widened_trusted,
    }
}

fn main() -> ExitCode {
    let include_constructed = std::env::args()
        .skip(1)
        .any(|a| a == "--include-constructed");
    let groups = build_groups(include_constructed);

    // theorem name -> (narrow trusted names, widened trusted names), first
    // occurrence across preludes (preludes nest, so a theorem present in
    // several groups is recorded once).
    let mut headline: BTreeMap<String, (BTreeSet<String>, BTreeSet<String>)> = BTreeMap::new();
    let mut string_lit_hits = 0usize;

    println!(
        "prelude\ttheorem\tnarrow_kinds\tnarrow_dangling\tnarrow_trusted\twidened_trusted\twidened_dangling\tinductive_edge_diffs"
    );

    for (label, mut kernel) in groups {
        let opaque_count = kernel
            .environment()
            .iter()
            .filter(|(_, d)| matches!(d, Declaration::Opaque { .. }))
            .count();
        let quotient_count = kernel
            .environment()
            .iter()
            .filter(|(_, d)| matches!(d, Declaration::Quotient { .. }))
            .count();

        let string_deps = string_literal_dependency_names(&mut kernel);
        let rec_of = recursor_names(&mut kernel);

        let theorem_names: Vec<NameId> = kernel
            .environment()
            .iter()
            .filter(|&(_, d)| matches!(d, Declaration::Theorem { .. }))
            .map(|(_, d)| d.name())
            .collect();

        let mut prelude_headline = 0usize;
        let mut prelude_edge_diff_theorems = 0usize;
        let mut union_reached: BTreeSet<NameId> = BTreeSet::new();
        let mut union_dangling: BTreeSet<NameId> = BTreeSet::new();

        for &name in &theorem_names {
            let audit = audit_theorem(
                &kernel,
                label,
                name,
                &string_deps,
                &rec_of,
                &mut string_lit_hits,
            );

            union_reached.extend(audit.reached.iter().copied());
            union_dangling.extend(audit.dangling.iter().copied());

            if audit.narrow_trusted.is_empty() && !audit.widened_trusted.is_empty() {
                prelude_headline += 1;
                headline.entry(audit.name.clone()).or_insert_with(|| {
                    (audit.narrow_trusted.clone(), audit.widened_trusted.clone())
                });
            }
            if audit.has_edge_diff {
                prelude_edge_diff_theorems += 1;
            }

            println!(
                "{label}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                audit.name,
                audit.kind_counts_str,
                audit.narrow_dangling,
                audit
                    .narrow_trusted
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(","),
                audit
                    .widened_trusted
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(","),
                audit.widened_dangling,
                audit.edge_diff_str,
            );
        }

        let union_kinds = format_counts(&kind_counts(&kernel, &union_reached));
        eprintln!(
            "{label}: theorems={} headline_gap={prelude_headline} \
             inductive_edge_diff_theorems={prelude_edge_diff_theorems} \
             opaque_decls={opaque_count} quotient_decls={quotient_count} \
             union_closure_kinds=[{union_kinds}] union_dangling={}",
            theorem_names.len(),
            union_dangling.len(),
        );
    }

    eprintln!(
        "string_literal_node_hits: {string_lit_hits} (expected 0 -- no prelude term contains \
         ExprNode::Lit(Lit::Str(_)))"
    );

    eprintln!(
        "HEADLINE: theorems_with_empty_narrow_and_nonempty_widened_trusted_footprint = {}",
        headline.len()
    );
    for (name, (narrow, widened)) in &headline {
        eprintln!("  {name}: narrow_trusted={narrow:?} widened_trusted={widened:?}");
    }

    ExitCode::SUCCESS
}
