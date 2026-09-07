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
//! The default index covers `logic`, `nat`, `axreal`, `integer`, `rat`, `ipc`,
//! `ipc_eval`, `fo_order`, `fo_soundness`, `fo_substitution`,
//! `characterization`, `list` and `string`. `--include-constructed` adds
//! `creal`, `complex`, `cpoint`, `metric`, `metric_prod`,
//! `intspace`, `rn`, `geo` and `top`, which cost real kernel type-checking. Querying a `CReal`
//! name without it is **unanswerable**, not absent. Every run prints the groups
//! it covered and a per-kind census before any verdict; `--list-groups` prints
//! the table with the reason each group is its own row.
//!
//! Those groups are the crate's **whole** prelude inventory. That is
//! checked from outside, by `tests/shape_search_index_coverage.rs`, which reads
//! every `pub fn build_*_prelude` out of `src/` and every builder call site out
//! of this file and fails when the second does not reach the first. Before that
//! test existed (2026-09-06) this tool built 17 of 31 builders and was blind to
//! all eleven `fo_*` modules, to `metric_prod`, to the list prelude and to
//! `ipc_eval` — while its own internal cross-check passed, because both halves
//! of that check were hand-written and omitted the same builders.
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
    build_cpoint_prelude, build_creal_prelude, build_fo_order_prelude, build_fo_soundness_prelude,
    build_fo_substitution_prelude, build_geo_prelude, build_int_prelude, build_intspace_prelude,
    build_ipc_eval_prelude, build_ipc_soundness_prelude, build_list_nat_bridge, build_list_perm,
    build_logic_prelude, build_metric_completion_prelude, build_metric_prelude,
    build_metric_prod_prelude, build_nat_prelude, build_rat_prelude, build_rn_prelude,
    build_string_length_append, build_string_prelude, build_string_substr_arithmetic,
    build_top_frame_prelude, on_a_deep_stack,
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

  --include-constructed    also build creal, complex, cpoint, metric,
                           metric_prod, intspace, rn, geo and top
  --index-values           also read every declaration's checked value
  --duplicates             report declarations stating the same proposition
  --list-groups            print the group table (name, flag, reason) and stop
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
    list_groups: bool,
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
        list_groups: false,
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
            "--list-groups" => args.list_groups = true,
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

/// One indexed kernel.
///
/// This table is the SINGLE source of both halves of the coverage claim: the
/// `coverage:` line is `GROUPS.name`, and the kernels actually indexed are
/// `GROUPS.build`. They were two hand-written lists until 2026-09-06, and the
/// runtime cross-check between them passed the whole time because both halves
/// omitted the same fourteen builders — a check whose two sides are written by
/// one hand at one moment cannot fail. `tests/shape_search_index_coverage.rs`
/// is the outside check: it derives the crate's builder inventory from the
/// source and fails when this table does not reach all of it.
struct Group {
    /// The name on the `coverage:` line.
    name: &'static str,
    /// Only built under `--include-constructed`: these cost real kernel
    /// type-checking, and the flag is what makes that cost opt-in.
    constructed: bool,
    /// Fill a fresh kernel with this group's declarations.
    build: fn(&mut Kernel),
    /// Why this group is its own row. Printed by `--list-groups`; an
    /// unexplained row is how a group gets quietly dropped again.
    why: &'static str,
}

fn build_logic(kernel: &mut Kernel) {
    let _ = build_logic_prelude(kernel).expect("logic prelude must build");
}

fn build_nat(kernel: &mut Kernel) {
    let _ = build_nat_prelude(kernel).expect("Nat prelude must build");
}

fn build_axreal(kernel: &mut Kernel) {
    let _ = build_arith_prelude(kernel).expect("AxReal prelude must build");
}

fn build_integer(kernel: &mut Kernel) {
    let _ = build_int_prelude(kernel).expect("Int prelude must build");
}

fn build_rational(kernel: &mut Kernel) {
    let _ = build_rat_prelude(kernel).expect("Rat prelude must build");
}

// ---------------------------------------------------------------------------
// One kernel per row, and why a row cannot bundle two builders.
//
// Only `Logic`, `List`, `Nat`, `Int`, `Real`, `CReal` and `String` register a
// `PreludeKey`, so only those seven are idempotent inside one kernel. Every
// other builder re-declares its own names and the trusted gate rejects the
// second call outright, measured here as
// `DeclarationExists { name: NameId(2195) }` from `build_ipc_eval_prelude`
// called after `build_ipc_soundness_prelude` in the same kernel. So a package
// with two incomparable leaves (IPC: soundness and eval; FO: order, soundness
// and substitution) needs one row, and one fresh kernel, per leaf.
// ---------------------------------------------------------------------------

fn build_ipc(kernel: &mut Kernel) {
    // `build_ipc_soundness_prelude` transitively builds provable -> heyting ->
    // nat, but NOT `ipc_eval`, which sits BESIDE `provable` on top of
    // `heyting`, so one call left `IPC.eval` and its kin unindexed.
    let _ = build_ipc_soundness_prelude(kernel).expect("IPC soundness prelude must build");
}

fn build_ipc_eval(kernel: &mut Kernel) {
    let _ = build_ipc_eval_prelude(kernel).expect("IPC eval prelude must build");
}

// The first-order-logic package: eleven builders in three chains that meet at
// `fo_syntax`,
//   order -> robinson -> roundtrip -> decode -> numbering -> code -> syntax
//   soundness -> provable -> semantics -> syntax
//   substitution -> semantics
// so these three leaves reach all eleven. Until 2026-09-06 the index built none
// of them and `--ns FO` returned nothing against a 4,839-row dump: the single
// largest blind spot this tool had.

fn build_fo_order(kernel: &mut Kernel) {
    let _ = build_fo_order_prelude(kernel).expect("FO order prelude must build");
}

fn build_fo_soundness(kernel: &mut Kernel) {
    let _ = build_fo_soundness_prelude(kernel).expect("FO soundness prelude must build");
}

fn build_fo_substitution(kernel: &mut Kernel) {
    let _ = build_fo_substitution_prelude(kernel).expect("FO substitution prelude must build");
}

fn build_characterization_group(kernel: &mut Kernel) {
    // The Nat/Int characterization package: `kernel_declaration_projection`
    // builds it and this index would otherwise report its declarations absent.
    let _ = build_characterization(kernel).expect("Nat/Int characterization must build");
}

fn build_list(kernel: &mut Kernel) {
    // `List.*` (ADR-1495) sits on `logic` only, so nothing else in this table
    // reaches it. And `build_list_prelude` ALONE is not the list library:
    // `List.Perm` and its lemmas are declared by `build_list_perm` over
    // `build_list_nat_bridge`, which is the three-step every other list-aware
    // instrument here performs (`kernel_declaration_projection`,
    // `prelude_theorem_inventory`, `theorem_dependency_inventory`,
    // `list_theorem_inventory`). Measured 2026-09-06: the prelude alone gives
    // 15 rows in `List` and `--name-contains List.Perm` returns nothing.
    let (list, nat, bridge) = build_list_nat_bridge(kernel).expect("List/Nat bridge must build");
    let _ = build_list_perm(kernel, &list, &nat, &bridge).expect("List.Perm must build");
}

fn build_string(kernel: &mut Kernel) {
    let handle = build_logic_prelude(kernel).expect("logic prelude must build");
    let string = build_string_prelude(kernel, handle, 2).expect("string prelude must build");
    // `Str.length_append` and `Str.substr_append_split` are declared by two
    // separate builders on top of the prelude, exactly like `List.Perm`.
    let nat = build_nat_prelude(kernel).expect("Nat prelude must build");
    let _ =
        build_string_length_append(kernel, &string, &nat).expect("Str.length_append must build");
    let _ = build_string_substr_arithmetic(kernel, &string, &nat)
        .expect("Str.substr_append_split must build");
}

fn build_creal(kernel: &mut Kernel) {
    let _ = build_creal_prelude(kernel).expect("CReal prelude must build");
}

fn build_complex(kernel: &mut Kernel) {
    let _ = build_complex_prelude(kernel).expect("Complex prelude must build");
}

fn build_cpoint(kernel: &mut Kernel) {
    let _ = build_cpoint_prelude(kernel).expect("CPoint prelude must build");
}

fn build_metric(kernel: &mut Kernel) {
    // `Metric.*` (ADR-1602) sits ON TOP of `cpoint`, so it is indexed as its
    // own group: without it `--include-constructed` reported a confident
    // ABSENT for every metric/topology declaration.
    let _ = build_metric_prelude(kernel).expect("Metric prelude must build");
}

fn build_metric_completion(kernel: &mut Kernel) {
    // `Metric.completion*` (ADR-1678) sits on `metric` and is reached by
    // nothing else in this table. It landed 2026-09-06, AFTER this table was
    // written, and the census test caught the divergence on the next push.
    let _ = build_metric_completion_prelude(kernel).expect("Metric.completion prelude must build");
}

fn build_metric_prod(kernel: &mut Kernel) {
    // `Metric.prod*` sits on top of `metric` and is reached by nothing else in
    // this table; before 2026-09-06 `build_metric_prod_prelude` was called only
    // by its own tests and its own inventory example.
    let _ = build_metric_prod_prelude(kernel).expect("Metric.prod prelude must build");
}

fn build_intspace(kernel: &mut Kernel) {
    // `IntSpace.*` (ADR-1612) sits on top of `creal` and is a SIBLING of
    // `metric`, not a consumer of it, so neither group indexes the other.
    let _ = build_intspace_prelude(kernel).expect("IntSpace prelude must build");
}

fn build_rn(kernel: &mut Kernel) {
    // `RN.*` (ADR-1606, the euclidean-n carrier) sits ON TOP of `metric`.
    let _ = build_rn_prelude(kernel).expect("RN prelude must build");
}

fn build_geo(kernel: &mut Kernel) {
    // `Geo.*` (ADR-1635, synthetic incidence geometry and its rational model)
    // sits ON TOP of `cpoint`.
    let _ = build_geo_prelude(kernel).expect("Geo prelude must build");
}

fn build_top(kernel: &mut Kernel) {
    // `Top.*` (ADR-1643, the pointfree topological carrier) sits on top of
    // `creal` and is a SIBLING of `metric`, not a consumer of it.
    let _ = build_top_frame_prelude(kernel).expect("Top.Frame prelude must build");
}

/// Every group this tool can index. See [`Group`].
const GROUPS: &[Group] = &[
    Group {
        name: "logic",
        constructed: false,
        build: build_logic,
        why: "the base prelude every other group sits on",
    },
    Group {
        name: "nat",
        constructed: false,
        build: build_nat,
        why: "Nat and its ~900 lemmas; the root of the arithmetic ladder",
    },
    Group {
        name: "axreal",
        constructed: false,
        build: build_axreal,
        why: "AxReal, the AXIOMATIZED ordered field (30 axioms); a separate \
              root from CReal and never matched against it by prefix",
    },
    Group {
        name: "integer",
        constructed: false,
        build: build_integer,
        why: "Int, built on nat",
    },
    Group {
        name: "rat",
        constructed: false,
        build: build_rational,
        why: "Rat, built on integer",
    },
    Group {
        name: "ipc",
        constructed: false,
        build: build_ipc,
        why: "the intuitionistic propositional calculus; soundness reaches \
              provable -> heyting -> nat",
    },
    Group {
        name: "ipc_eval",
        constructed: false,
        build: build_ipc_eval,
        why: "IPC.eval, the sibling branch of provable that ipc soundness does \
              NOT reach; its own kernel because ipc_heyting is not idempotent",
    },
    Group {
        name: "fo_order",
        constructed: false,
        build: build_fo_order,
        why: "first-order logic, coding chain: order -> robinson -> roundtrip \
              -> decode -> numbering -> code -> syntax (7 builders)",
    },
    Group {
        name: "fo_soundness",
        constructed: false,
        build: build_fo_soundness,
        why: "first-order logic, proof-calculus chain: soundness -> provable \
              -> semantics -> syntax (4 builders)",
    },
    Group {
        name: "fo_substitution",
        constructed: false,
        build: build_fo_substitution,
        why: "first-order logic, substitution over semantics; the third \
              incomparable FO leaf",
    },
    Group {
        name: "characterization",
        constructed: false,
        build: build_characterization_group,
        why: "the Nat/Int characterization package that \
              kernel_declaration_projection also builds",
    },
    Group {
        name: "list",
        constructed: false,
        build: build_list,
        why: "List, the List/Nat bridge and List.Perm; sits on logic alone, so \
              no other group reaches it",
    },
    Group {
        name: "string",
        constructed: false,
        build: build_string,
        why: "String over a two-symbol alphabet, plus Str.length_append and \
              Str.substr_append_split; needs the logic handle passed in",
    },
    Group {
        name: "creal",
        constructed: true,
        build: build_creal,
        why: "the CONSTRUCTED reals (0 axioms); the largest single prelude",
    },
    Group {
        name: "complex",
        constructed: true,
        build: build_complex,
        why: "Complex, on creal",
    },
    Group {
        name: "cpoint",
        constructed: true,
        build: build_cpoint,
        why: "CPoint and the conics, on creal",
    },
    Group {
        name: "metric",
        constructed: true,
        build: build_metric,
        why: "ADR-1602, on cpoint",
    },
    Group {
        name: "metric_prod",
        constructed: true,
        build: build_metric_prod,
        why: "Metric.prod*, on metric; reached by nothing else in this table",
    },
    Group {
        name: "metric_completion",
        constructed: true,
        build: build_metric_completion,
        why: "Metric.completion* (ADR-1678), on metric; reached by nothing else",
    },
    Group {
        name: "intspace",
        constructed: true,
        build: build_intspace,
        why: "ADR-1612, on creal; a SIBLING of metric",
    },
    Group {
        name: "rn",
        constructed: true,
        build: build_rn,
        why: "ADR-1606, the euclidean-n carrier, on metric",
    },
    Group {
        name: "geo",
        constructed: true,
        build: build_geo,
        why: "ADR-1635, synthetic incidence geometry, on cpoint",
    },
    Group {
        name: "top",
        constructed: true,
        build: build_top,
        why: "ADR-1643, the pointfree topological carrier, on creal",
    },
];

/// Build every selected prelude group and fold it into one index.
///
/// Preludes nest, so a declaration proved in `nat` is visible in `rat`, `creal`
/// and `cpoint` too; [`ShapeIndex::insert`] merges the group sets rather than
/// duplicating the row. The process-wide prelude cache (ADR-0464) makes the
/// repeated `CReal` builds a clone rather than a re-check.
fn build_index(include_constructed: bool, index_values: bool) -> (ShapeIndex, String) {
    let selected: Vec<&Group> = GROUPS
        .iter()
        .filter(|group| include_constructed || !group.constructed)
        .collect();
    let mut index = ShapeIndex::new(
        selected
            .iter()
            .map(|group| group.name.to_owned())
            .collect::<Vec<_>>(),
        index_values,
    );
    // Per-group wall time, printed with the coverage line. Adding a group is
    // never free -- the default index went from 8 groups to 15 on 2026-09-06
    // and its build time roughly tripled -- and a future lane deciding what to
    // put behind `--include-constructed` should be reading a measurement, not
    // guessing from the prelude's reputation.
    let mut timing: Vec<(&'static str, f64)> = Vec::with_capacity(selected.len());
    for group in &selected {
        let started = std::time::Instant::now();
        let mut kernel = Kernel::new();
        (group.build)(&mut kernel);
        index_kernel(&kernel, group.name, &mut index, index_values);
        timing.push((group.name, started.elapsed().as_secs_f64()));
    }

    index.finish();
    // The declared groups and the indexed groups now come from ONE table, so
    // they cannot drift the way they did while they were two hand-written
    // lists. This assert survives as the check that no group built ZERO rows —
    // a builder that succeeds but declares nothing into its own namespace
    // would otherwise put a name on the `coverage:` line that stands for
    // nothing indexed, which is the same wrong answer by another route.
    let declared: BTreeSet<&str> = index.groups().iter().map(String::as_str).collect();
    let indexed: BTreeSet<&str> = index
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

    let timing_line = timing
        .iter()
        .map(|(name, secs)| format!("{name}={secs:.1}s"))
        .collect::<Vec<_>>()
        .join(" ");
    (index, timing_line)
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

    // `--list-groups` answers "what could this tool ever have seen?" and must
    // therefore be answerable WITHOUT paying for the index, so a reader who is
    // deciding whether an ABSENT verdict is trustworthy is not charged 100s to
    // find out.
    if args.list_groups {
        for group in GROUPS {
            println!(
                "GROUP  {}  {}  {}",
                group.name,
                if group.constructed {
                    "--include-constructed"
                } else {
                    "default"
                },
                group.why
            );
        }
        println!(
            "control: {} groups ({} default, {} constructed)",
            GROUPS.len(),
            GROUPS.iter().filter(|g| !g.constructed).count(),
            GROUPS.iter().filter(|g| g.constructed).count(),
        );
        return ExitCode::SUCCESS;
    }

    let started = std::time::Instant::now();
    let (index, timing_line) = build_index(args.include_constructed, args.index_values);
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
    println!("timing: {timing_line}");
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
