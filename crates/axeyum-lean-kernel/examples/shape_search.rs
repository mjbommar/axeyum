//! `shape_search` — *"does a declaration of this SHAPE exist, anywhere, under
//! any name?"*
//!
//! Not a replacement for `kernel_declaration_projection --require-declaration`,
//! which already answers *"does a declaration with EXACTLY this name exist?"*
//! with a non-zero exit on absence, across every kind. Use that when you know
//! the name. Use this when you do not — which, per the retrospective, is the
//! case that has cost this repository real work.
//!
//! Every other instrument in this crate answers *"is this name taken?"*. That
//! question cannot find a lemma whose name you do not know, and lanes here have
//! repeatedly declared themselves blocked on a lemma that already exists,
//! proved, in the tree — the search was competent and its answer was correct.
//!
//! ```sh
//! # Is there already a congruence lemma for uniformly continuous functions?
//! cargo run --release -p axeyum-lean-kernel --example shape_search -- \
//!   --concl CReal.Equiv --hyp CReal.UniformlyContinuousOn
//!
//! # Does the DEFINITION Rat.polyEval exist (not its sixteen lemmas)?
//! cargo run --release -p axeyum-lean-kernel --example shape_search -- \
//!   --name Rat.polyEval --kind definition
//!
//! # Which declarations' PROOFS use this step? (the partial route to an
//! # inline, unnamed step — see "Blind spots" below)
//! cargo run --release -p axeyum-lean-kernel --example shape_search -- \
//!   --index-values --value-const CReal.speedup_close
//!
//! # Are two declarations stating the same proposition?
//! cargo run --release -p axeyum-lean-kernel --example shape_search -- --duplicates
//! ```
//!
//! # Exit status depends on what the run FOUND
//!
//! * **0** — at least one match (or exactly `--expect N`, or `--expect-absent`
//!   with nothing found).
//! * **1** — the query was answerable and the assertion failed: nothing
//!   matched, or the count differed, or `--expect-absent` found something.
//! * **2** — usage error.
//! * **3** — **unanswerable**. The query named a constant, kind or namespace
//!   the built index does not carry, so a zero would be meaningless. This is
//!   the same-kind positive control made structural rather than advisory: you
//!   cannot receive "0 rows" from a subject the tool was never pointed at.
//!
//! A fact-ledger `checker_command` can therefore depend on this tool, in either
//! direction — `--expect 1` for a construction that must exist, `--expect-absent`
//! for a shape the library must not yet duplicate — and neither can pass by the
//! run merely completing.
//!
//! # Coverage is declared, and unbuilt is not absent
//!
//! The default index covers `logic`, `nat`, `axreal`, `integer`, `rat`,
//! `characterization` and `string`. `--include-constructed` adds `creal`, `complex`, `cpoint`, `metric` and `intspace`,
//! `characterization` and `string`. `--include-constructed` adds `creal`, `complex`, `cpoint`, `metric` and `rn`,
//! which cost real kernel type-checking. Querying a `CReal` name without it is
//! **unanswerable**, not absent. Every run prints the groups it covered and a
//! per-kind census before any verdict.
//!
//! # There is no single naming convention, so `--name-like` ignores spelling
//!
//! Measured over the 464 `CReal` declarations: 315 contain an underscore, 200
//! contain an internal capital, **114 contain both**.
//! `CReal.congrOfUniformlyContinuous` and `CReal.equiv_of_le_le` are in one
//! namespace, and the Rust FIELD for the first is
//! `congr_of_uniformly_continuous` — the spelling every design document uses.
//! `--name-like congr_of_uniformly_continuous` retrieves it anyway; a grep for
//! that string against the kernel inventory returns nothing.
//!
//! # Names are KERNEL names
//!
//! Rows render through `Kernel::display_name`: the naturals are `Nat`, not
//! `AxNat`. `AxNat` is `lean_pp`'s non-shadowing EXPORT root — the `Ax` is
//! *axeyum*, and `nat` has zero axioms. `AxReal` (the axiomatized ordered
//! field, 30 axioms) and `CReal` (the constructed reals, 0) are separate roots
//! and are never matched against each other by prefix: `--concl`, `--hyp` and
//! `--const` compare whole rendered names.
//!
//! # Blind spots, stated rather than implied
//!
//! 1. **A reusable step built INLINE inside a larger declaration has no
//!    declaration.** `nat_prelude/powsq.rs`'s `declare_pow_half_split` performs
//!    a full `Nat` even/odd split purely as scaffolding toward a `pow`
//!    equation; nothing names it, so no index over declared names can list it.
//!    `--value-const` is a *partial* route and not a fix: it finds the
//!    ENCLOSING declaration when you can already guess a lemma the inline step
//!    uses. It cannot tell you the step is there if you cannot name one of its
//!    ingredients.
//! 2. **A lemma more general than its reputation** is found only if you query
//!    the general shape. The index stores the stated hypothesis heads, so
//!    `CReal.sumRange_cauchy_of_dominated` is retrieved by its real signature
//!    and not by the stronger one people assume it has — which helps, but only
//!    for a lane that thinks to query the weaker form.
//! 3. **Definitional unfolding is not searched.** Two statements that are
//!    defeq but structurally unrelated index differently, by design: the index
//!    is syntactic and cheap.

use std::collections::BTreeSet;
use std::process::ExitCode;

use axeyum_lean_kernel::shape_index::{
    DeclKind, Outcome, Query, ShapeIndex, index_kernel, namespace_root, run,
};
use axeyum_lean_kernel::{
    Kernel, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_intspace_prelude,
    build_ipc_soundness_prelude, build_logic_prelude, build_metric_prelude, build_nat_prelude,
    build_rat_prelude, build_rn_prelude, build_string_prelude, on_a_deep_stack,
};

const USAGE: &str = "\
shape_search — retrieve a declaration by the SHAPE of its type, not its name.

  --concl <Const>          conclusion is headed by <Const>
  --hyp <Const>            some hypothesis is headed by <Const> (repeatable;
                           repeats demand that many DISTINCT binders)
  --const <Const>          <Const> occurs anywhere in the type (repeatable)
  --value-const <Const>    <Const> occurs in the checked VALUE (repeatable;
                           requires --index-values)
  --name <Name>            exact rendered name
  --name-contains <S>      substring of the rendered name
  --name-like <S>          substring ignoring case, `_` and `.` — a snake_case
                           guess retrieves a camelCase declaration
  --kind <k>               axiom|definition|theorem|opaque|inductive|
                           constructor|recursor|quot (repeatable, OR)
  --ns <Root>              restrict to a namespace root
  --arity <n>              exact number of Pi binders
  --like <Name>            same hypothesis-head multiset and conclusion head
                           as this existing declaration

  --include-constructed    also build creal, complex, cpoint, metric and intspace
  --include-constructed    also build creal, complex, cpoint, metric and rn
  --index-values           also read every declaration's checked value
  --duplicates             report declarations stating the same proposition
  --list-namespaces        print the namespace census and stop
  --show-consts            print each match's type constants

  --expect <n>             assert exactly n matches
  --min <n>                assert at least n matches
  --expect-absent          assert nothing matches (still fails if unanswerable)
  --limit <n>              print at most n matches (default 40)

Exit: 0 assertion held, 1 assertion failed, 2 usage, 3 UNANSWERABLE.";

// Ten independent CLI toggles; a state machine would be less legible than the
// flags they mirror one-for-one.
#[allow(clippy::struct_excessive_bools)]
struct Args {
    query: Query,
    include_constructed: bool,
    index_values: bool,
    duplicates: bool,
    list_namespaces: bool,
    show_consts: bool,
    expect: Option<usize>,
    min: Option<usize>,
    expect_absent: bool,
    limit: usize,
}

fn parse_args() -> Result<Args, String> {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let mut args = Args {
        query: Query::default(),
        include_constructed: false,
        index_values: false,
        duplicates: false,
        list_namespaces: false,
        show_consts: false,
        expect: None,
        min: None,
        expect_absent: false,
        limit: 40,
    };
    let mut iter = raw.iter();
    let value = |slot: Option<&String>, flag: &str| -> Result<String, String> {
        slot.cloned().ok_or_else(|| format!("{flag} needs a value"))
    };
    let number = |slot: Option<&String>, flag: &str| -> Result<usize, String> {
        slot.ok_or_else(|| format!("{flag} needs a number"))?
            .parse()
            .map_err(|_| format!("{flag} expects a number"))
    };
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--help" | "-h" => return Err(String::from("--help")),
            "--concl" => args.query.concl = Some(value(iter.next(), "--concl")?),
            "--hyp" => args.query.hyps.push(value(iter.next(), "--hyp")?),
            "--const" => args.query.consts.push(value(iter.next(), "--const")?),
            "--value-const" => args
                .query
                .value_consts
                .push(value(iter.next(), "--value-const")?),
            "--name" => args.query.name = Some(value(iter.next(), "--name")?),
            "--name-contains" => {
                args.query.name_contains = Some(value(iter.next(), "--name-contains")?);
            }
            "--name-like" => args.query.name_like = Some(value(iter.next(), "--name-like")?),
            "--kind" => {
                let spelling = value(iter.next(), "--kind")?;
                let kind = DeclKind::parse(&spelling)
                    .ok_or_else(|| format!("unknown --kind {spelling:?}"))?;
                args.query.kinds.push(kind);
            }
            "--ns" => args.query.namespace = Some(value(iter.next(), "--ns")?),
            "--arity" => args.query.arity = Some(number(iter.next(), "--arity")?),
            "--like" => args.query.like = Some(value(iter.next(), "--like")?),
            "--include-constructed" => args.include_constructed = true,
            "--index-values" => args.index_values = true,
            "--duplicates" => args.duplicates = true,
            "--list-namespaces" => args.list_namespaces = true,
            "--show-consts" => args.show_consts = true,
            "--expect" => args.expect = Some(number(iter.next(), "--expect")?),
            "--min" => args.min = Some(number(iter.next(), "--min")?),
            "--expect-absent" => args.expect_absent = true,
            "--limit" => args.limit = number(iter.next(), "--limit")?,
            other => return Err(format!("unknown argument {other:?}")),
        }
    }
    if args.expect_absent && (args.expect.is_some() || args.min.is_some()) {
        return Err(String::from(
            "--expect-absent cannot be combined with --expect/--min",
        ));
    }
    Ok(args)
}

/// Build every prelude group and fold it into one index.
///
/// Preludes nest, so a declaration proved in `nat` is visible in `rat`, `creal`
/// and `cpoint` too; [`ShapeIndex::insert`] merges the group sets rather than
/// duplicating the row. The process-wide prelude cache (ADR-0464) makes the
/// repeated `CReal` builds a clone rather than a re-check.
fn build_index(include_constructed: bool, index_values: bool) -> ShapeIndex {
    let mut groups = vec![
        "logic".to_owned(),
        "nat".to_owned(),
        "axreal".to_owned(),
        "integer".to_owned(),
        "ipc".to_owned(),
        "rat".to_owned(),
        "characterization".to_owned(),
        "string".to_owned(),
    ];
    if include_constructed {
        groups.extend([
            "creal".to_owned(),
            "complex".to_owned(),
            "cpoint".to_owned(),
            "metric".to_owned(),
            "intspace".to_owned(),
            "rn".to_owned(),
        ]);
    }
    let mut index = ShapeIndex::new(groups, index_values);

    let mut logic = Kernel::new();
    let _handle = build_logic_prelude(&mut logic).expect("logic prelude must build");
    index_kernel(&logic, "logic", &mut index, index_values);

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    index_kernel(&nat, "nat", &mut index, index_values);

    let mut axreal = Kernel::new();
    let _ = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    index_kernel(&axreal, "axreal", &mut index, index_values);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    index_kernel(&integer, "integer", &mut index, index_values);

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    index_kernel(&rational, "rat", &mut index, index_values);

    // The IPC package. Same reason as `characterization` below, and the same
    // stakes: an ABSENT verdict from this tool is what a lane acts on, so a
    // prelude group it never builds produces a confident, wrong "no such
    // declaration". `build_ipc_soundness_prelude` transitively builds
    // provable -> heyting -> nat, so one call covers the whole
    // intuitionistic-logic surface. Added 2026-08-31, alongside the same gap in
    // `kernel_declaration_projection`, `prelude_theorem_inventory` and
    // `cross_prelude_collision_tests.rs` -- all four were blind to it.
    let mut ipc = Kernel::new();
    let _ = build_ipc_soundness_prelude(&mut ipc).expect("IPC soundness prelude must build");
    index_kernel(&ipc, "ipc", &mut index, index_values);

    // The Nat/Int characterization package: `kernel_declaration_projection`
    // builds it and this index would otherwise report its declarations absent.
    let mut characterization = Kernel::new();
    let _ =
        build_characterization(&mut characterization).expect("Nat/Int characterization must build");
    index_kernel(
        &characterization,
        "characterization",
        &mut index,
        index_values,
    );

    let mut string = Kernel::new();
    let string_handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, string_handle, 2).expect("string prelude must build");
    index_kernel(&string, "string", &mut index, index_values);

    if include_constructed {
        let mut creal = Kernel::new();
        let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
        index_kernel(&creal, "creal", &mut index, index_values);

        let mut complex = Kernel::new();
        let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
        index_kernel(&complex, "complex", &mut index, index_values);

        let mut cpoint = Kernel::new();
        let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
        index_kernel(&cpoint, "cpoint", &mut index, index_values);

        // `Metric.*` (ADR-1602) sits ON TOP of `cpoint`, so it is indexed as
        // its own group: without this call `--include-constructed` reports a
        // confident ABSENT for every metric/topology declaration, which is the
        // exact "tool never pointed at your subject" failure the `coverage:`
        // line below exists to prevent.
        let mut metric = Kernel::new();
        let _ = build_metric_prelude(&mut metric).expect("Metric prelude must build");
        index_kernel(&metric, "metric", &mut index, index_values);

        // `IntSpace.*` (ADR-1612) sits on top of `creal` and is a SIBLING of
        // `metric`, not a consumer of it, so neither group indexes the other.
        // Without this call `--include-constructed` reports a confident ABSENT
        // for every integration-space, measure and detachable-subset
        // declaration -- the same trap the `metric` call above was added to
        // close, one shelf later.
        let mut intspace = Kernel::new();
        let _ = build_intspace_prelude(&mut intspace).expect("IntSpace prelude must build");
        index_kernel(&intspace, "intspace", &mut index, index_values);
        // `RN.*` (ADR-1606, the euclidean-n carrier) sits ON TOP of `metric`,
        // for the same reason and with the same hazard: without this call
        // `--include-constructed` reports a confident ABSENT for every
        // declaration of the n-dimensional inner-product space.
        let mut rn = Kernel::new();
        let _ = build_rn_prelude(&mut rn).expect("RN prelude must build");
        index_kernel(&rn, "rn", &mut index, index_values);
    }

    index.finish();
    // The `groups` vector above is hand-written and the `index_kernel` calls
    // below it are hand-written, and NOTHING made them agree -- so the
    // `coverage:` line, whose entire job is to stop an empty answer from a tool
    // that was never pointed at your subject reading as a strong negative
    // result, could name a group nothing indexed, or omit one that was. Both
    // directions occurred: `ipc` was indexed by no call at all until
    // 2026-08-31, and when it was added the coverage line still listed ten
    // groups. Derived comparison, so the list cannot drift again.
    let declared: std::collections::BTreeSet<&str> =
        index.groups().iter().map(String::as_str).collect();
    let indexed: std::collections::BTreeSet<&str> = index
        .entries()
        .iter()
        .flat_map(|entry| entry.groups.iter().map(String::as_str))
        .collect();
    assert!(
        declared == indexed,
        "shape_search coverage disagrees with what was indexed: declared-only \
         {:?}, indexed-only {:?}. The `coverage:` line would then be a claim \
         about groups nobody built (or silently omit ones that were), which is \
         the exact defect that line exists to prevent",
        declared.difference(&indexed).collect::<Vec<_>>(),
        indexed.difference(&declared).collect::<Vec<_>>(),
    );

    index
}

// The reporting arms are deliberately inline: each verdict prints its own
// positive control, and splitting them apart is how a control gets dropped.
fn main() -> ExitCode {
    // Build every prelude on a DEEP stack, not the process's main thread.
    // `Kernel::add_declaration` recurses deeply enough through the constructed
    // preludes to overflow the default main-thread stack in a debug build, and
    // that failure (`SIGABRT`, exit 134) is indistinguishable from a broken
    // tool or an absent declaration — which is exactly the confusion this
    // whole example exists to prevent. A doc note saying "use --release"
    // cannot reach a caller that does not read it; carrying the documented
    // envelope makes every caller work unchanged.
    on_a_deep_stack(execute)
}

#[allow(clippy::too_many_lines)]
fn execute() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            if message == "--help" {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            eprintln!("error: {message}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };

    let started = std::time::Instant::now();
    let index = build_index(args.include_constructed, args.index_values);
    let elapsed = started.elapsed();

    // Coverage FIRST, before any verdict: an empty answer from a tool that was
    // never pointed at your subject is indistinguishable from a strong negative
    // result, so the reader always sees what was covered.
    println!(
        "coverage: groups=[{}] declarations={} values_indexed={} build={:.1}s",
        index.groups().join(","),
        index.entries().len(),
        index.values_indexed(),
        elapsed.as_secs_f64()
    );
    let census = index.kind_census();
    let census_line: Vec<String> = DeclKind::all()
        .iter()
        .map(|kind| {
            format!(
                "{}={}",
                kind.label(),
                census.get(kind).copied().unwrap_or(0)
            )
        })
        .collect();
    println!("control: {}", census_line.join(" "));

    if args.list_namespaces {
        for (root, count) in index.namespace_census() {
            println!("NAMESPACE  {root}  {count}");
        }
        return ExitCode::SUCCESS;
    }

    if args.duplicates {
        // A DEFINITION's type is not its statement, so an unrestricted scan is
        // dominated by rows sharing only an arity. Theorems unless told
        // otherwise; `--kind definition` opts back in deliberately.
        let kinds = args.query.kinds.clone();
        let groups = if kinds.is_empty() {
            index.duplicate_shapes()
        } else {
            index.duplicate_shapes_where(|entry| kinds.contains(&entry.kind))
        };
        let mut reported = 0usize;
        for group in &groups {
            let names: Vec<&str> = group.iter().map(|entry| entry.name.as_str()).collect();
            println!("DUPLICATE  {}  {}", group[0].signature(), names.join(" "));
            reported += 1;
            if reported >= args.limit {
                println!(
                    "… {} further duplicate groups not printed",
                    groups.len() - reported
                );
                break;
            }
        }
        println!("verdict: DUPLICATE-GROUPS {}", groups.len());
        if let Some(expected) = args.expect
            && groups.len() != expected
        {
            eprintln!(
                "FAIL: expected {expected} duplicate groups, found {}",
                groups.len()
            );
            return ExitCode::from(1);
        }
        return ExitCode::SUCCESS;
    }

    let outcome = run(&index, &args.query);

    match &outcome {
        Outcome::Unanswerable(reasons) => {
            for reason in reasons {
                eprintln!("UNANSWERABLE  {reason}");
            }
            eprintln!(
                "verdict: UNANSWERABLE — this is NOT a report that the declaration is \
                 absent. Fix the query or widen the index and ask again."
            );
            return ExitCode::from(3);
        }
        Outcome::Absent => {
            // The negative is paired with its same-kind positive control, in
            // the same output, without the caller having to ask for it.
            let kinds: Vec<String> = if args.query.kinds.is_empty() {
                vec![format!("any-kind={}", index.entries().len())]
            } else {
                args.query
                    .kinds
                    .iter()
                    .map(|kind| {
                        format!(
                            "{}={}",
                            kind.label(),
                            census.get(kind).copied().unwrap_or(0)
                        )
                    })
                    .collect()
            };
            let roots: BTreeSet<String> = args
                .query
                .vocabulary()
                .iter()
                .map(|name| namespace_root(name).to_owned())
                .chain(args.query.namespace.clone())
                .collect();
            let namespaces = index.namespace_census();
            let root_line: Vec<String> = roots
                .iter()
                .map(|root| format!("{root}={}", namespaces.get(root).copied().unwrap_or(0)))
                .collect();
            println!(
                "verdict: ABSENT  (positive control: {}{}{})",
                kinds.join(" "),
                if root_line.is_empty() { "" } else { " ns " },
                root_line.join(" ")
            );
            // A name-shaped query that found nothing gets the nearest declared
            // names, because "absent" is most often a spelling, and this is the
            // moment a lane would otherwise conclude the work is new.
            for probe in args
                .query
                .name
                .iter()
                .chain(args.query.name_contains.iter())
                .chain(args.query.name_like.iter())
            {
                let nearest = index.nearest(probe, 8);
                if !nearest.is_empty() {
                    println!(
                        "hint: names containing that component: {}",
                        nearest.join(", ")
                    );
                }
            }
        }
        Outcome::Found(matched) => {
            for name in matched.iter().take(args.limit) {
                let entry = index
                    .entries()
                    .iter()
                    .find(|entry| &entry.name == name)
                    .expect("a matched name is in the index");
                let consts = if args.show_consts {
                    format!(
                        "  consts=[{}]",
                        entry
                            .type_consts
                            .iter()
                            .cloned()
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                } else {
                    String::new()
                };
                println!(
                    "MATCH  {}  {}  arity={}  {}  groups=[{}]{consts}",
                    entry.name,
                    entry.kind.label(),
                    entry.arity,
                    entry.signature(),
                    entry.groups.iter().cloned().collect::<Vec<_>>().join(","),
                );
            }
            if matched.len() > args.limit {
                println!(
                    "… {} further matches not printed",
                    matched.len() - args.limit
                );
            }
            println!("verdict: FOUND {}", matched.len());
        }
    }

    let found = match &outcome {
        Outcome::Found(matched) => matched.len(),
        _ => 0,
    };
    if args.expect_absent {
        if found > 0 {
            eprintln!("FAIL: --expect-absent, but {found} declarations match");
            return ExitCode::from(1);
        }
        return ExitCode::SUCCESS;
    }
    if let Some(expected) = args.expect {
        if found != expected {
            eprintln!("FAIL: --expect {expected}, found {found}");
            return ExitCode::from(1);
        }
        return ExitCode::SUCCESS;
    }
    if let Some(minimum) = args.min {
        if found < minimum {
            eprintln!("FAIL: --min {minimum}, found {found}");
            return ExitCode::from(1);
        }
        return ExitCode::SUCCESS;
    }
    ExitCode::from(outcome.status())
}
