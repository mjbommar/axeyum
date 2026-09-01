//! Count **theorems** across every prelude, which nothing did until now.
//!
//! `docs/formalized-math-2026-08/05-throughput.md` concluded on 2026-08-19 that
//! this project's theorem-production rate is "not falsifiable in either
//! direction," and the reason was an instrument gap, not a measurement dispute:
//! `nat_theorem_inventory` counts `nat`, `int_theorem_inventory` counts
//! `integer`, and `rat`, `creal`, `complex`, `logic` and `string` had no
//! theorem counter at all. So the headline counter could not rise when the work
//! moved to ℚ and the constructed ℝ — and a fall would not have meant a
//! regression either. Only the *axiom* ledger was cross-prelude.
//!
//! This is the theorem-side twin of `nat_axiom_inventory`: same prelude groups,
//! same `--include-constructed` opt-in, same by-value pinning.
//!
//! ## Distinct, not summed
//!
//! Preludes nest — `build_nat_prelude` builds `logic` first, `build_rat_prelude`
//! builds ℤ, `build_creal_prelude` builds ℚ — so a theorem is present in every
//! group downstream of where it was proved. **Adding the per-group counts
//! therefore multiply-counts most of the library**, and the sum is not a
//! production figure. The distinct count over canonical names is, and it is what
//! `--expect-distinct` pins.
//!
//! Both are printed, because the per-group numbers are what tell you where the
//! work happened and the distinct number is what tells you how much there is.
//!
//! ## Axiom-bearing vs axiom-free
//!
//! Each theorem carries its `Kernel::axiom_footprint` — this kernel's
//! `#print axioms`. A theorem with an empty footprint rests on nothing assumed.
//! The counts are reported separately because "we proved N theorems" and "we
//! proved N theorems that assume nothing" are different claims, and only the
//! second is this programme's metric.
//!
//! ## Coverage is declared, not implied
//!
//! `--expect` naming a prelude that was not built is an **error**, not a silent
//! zero. This repository has already published a conclusion drawn from grepping
//! an inventory for a prelude it never covered; an empty answer from a tool that
//! was never pointed at your subject is indistinguishable from a strong negative
//! result. Passing `--expect creal=…` without `--include-constructed` fails.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example prelude_theorem_inventory \
//!   -- --include-constructed
//! ```
//!
//! ## `characterization` — a group this tool omitted entirely until 2026-08-27
//!
//! `build_characterization` (the Peano/initiality package: `Nat.Peano.*`,
//! `Int.Characterization.*`) is a real, axiom-free `Declaration::Theorem`
//! producer — `crates/axeyum-lean-kernel/examples/kernel_declaration_projection.rs`
//! has always built it, under the label `characterization` — but this tool's
//! own `build_groups` never called it, so every one of its theorems was
//! **silently absent from the distinct total and from every `--expect`
//! bucket**, with no error and no zero to notice: `gen-ledger-coverage.py`'s
//! denominator undercounted `nat` by 9 and `integer` by 23 for as long as this
//! gap existed (`docs/research/11-design-review/
//! 2026-08-27-rat-reindexing-and-the-denominator-gap.md`). This was not one of
//! the exclusions in the "Coverage is declared" section above — those are
//! `Declaration` KINDS excluded on purpose; this was a whole prelude GROUP
//! never built, which is the same "empty answer from a tool that was never
//! pointed at your subject" trap CLAUDE.md documents, just short by 32 instead
//! of empty. Built here in the same dependency-order position
//! `kernel_declaration_projection` uses (after `integer`, before `rat`), and
//! unconditionally rather than gated on `--include-constructed`: it costs no
//! more than the already-unconditional `integer` group, since it is exactly
//! `build_int_prelude` plus 32 more theorems.
//!
//! `scripts/tests/test_gen_ledger_coverage.py::CharacterizationCoverageTests`
//! guards this from recurring: a synthetic theorem-inventory TSV missing the
//! `Int.Characterization.*`/`Nat.Peano.*` rows must make
//! `check-ledger-coverage-denominator-agreement.py` fail loudly rather than
//! silently under-bucket `nat`/`integer`.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_ipc_soundness_prelude,
    build_logic_prelude, build_nat_prelude, build_rat_prelude, build_string_prelude,
};

/// One row: theorem name and the axioms it rests on, both display-rendered.
type Row = (String, Vec<String>);

fn theorems(kernel: &Kernel) -> Vec<Row> {
    let mut rows: Vec<Row> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Theorem { name, .. } => {
                let footprint = kernel
                    .axiom_footprint(*name)
                    .into_iter()
                    .map(|axiom| kernel.display_name(axiom).to_string())
                    .collect();
                Some((kernel.display_name(*name).to_string(), footprint))
            }
            _ => None,
        })
        .collect();
    rows.sort();
    rows.dedup();
    rows
}

struct Args {
    include_constructed: bool,
    /// `--expect <prelude>=<n>`
    expected: Vec<(String, usize)>,
    /// `--expect-distinct <n>`
    expect_distinct: Option<usize>,
    /// `--expect-axiom-free <n>`: distinct theorems with an empty footprint.
    expect_axiom_free: Option<usize>,
}

fn parse_args() -> Result<Args, String> {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let mut args = Args {
        include_constructed: false,
        expected: Vec::new(),
        expect_distinct: None,
        expect_axiom_free: None,
    };
    let mut iter = raw.iter();
    let number = |value: Option<&String>, flag: &str| -> Result<usize, String> {
        value
            .ok_or_else(|| format!("{flag} needs a number"))?
            .parse()
            .map_err(|_| format!("{flag} expects a number"))
    };
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--include-constructed" => args.include_constructed = true,
            "--expect" => {
                let spec = iter.next().ok_or("--expect needs <prelude>=<n>")?;
                let (label, raw) = spec
                    .split_once('=')
                    .ok_or_else(|| format!("--expect expects <prelude>=<n>, got {spec:?}"))?;
                let count = raw
                    .parse()
                    .map_err(|_| format!("--expect expects a number, got {raw:?}"))?;
                args.expected.push((label.to_owned(), count));
            }
            "--expect-distinct" => {
                args.expect_distinct = Some(number(iter.next(), "--expect-distinct")?);
            }
            "--expect-axiom-free" => {
                args.expect_axiom_free = Some(number(iter.next(), "--expect-axiom-free")?);
            }
            other => return Err(format!("unknown argument {other:?}")),
        }
    }
    Ok(args)
}

/// Build every prelude group, in dependency order.
///
/// Order matters twice: it is the order the rows print in, and it is the
/// tie-break for origin attribution when two groups have identical theorem sets.
fn build_groups(include_constructed: bool) -> Vec<(&'static str, Vec<Row>)> {
    let mut groups: Vec<(&str, Vec<Row>)> = Vec::new();

    let mut logic = Kernel::new();
    let _ = build_logic_prelude(&mut logic).expect("logic prelude must build");
    groups.push(("logic", theorems(&logic)));

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    groups.push(("nat", theorems(&nat)));

    let mut axreal = Kernel::new();
    let _ = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    groups.push(("axreal", theorems(&axreal)));

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    groups.push(("integer", theorems(&integer)));

    // The Peano/initiality characterization package (`Nat.Peano.*`,
    // `Int.Characterization.*`): NOT gated on `--include-constructed`, unlike
    // `creal`/`complex`/`cpoint` below -- it costs no more than the
    // already-unconditional `integer` group above, since it is exactly
    // `build_int_prelude` plus 32 more theorems. See the module doc's
    // "`characterization` — a group this tool omitted entirely" section for
    // why this group's absence was a real, silent denominator gap rather
    // than one of this tool's deliberate declaration-kind exclusions.
    let mut characterization = Kernel::new();
    let _ =
        build_characterization(&mut characterization).expect("Nat/Int characterization must build");
    groups.push(("characterization", theorems(&characterization)));

    // The IPC package. `build_ipc_soundness_prelude` transitively builds
    // provable -> heyting -> nat, so one group covers the whole
    // intuitionistic-logic surface. Unconditional, for `characterization`'s
    // reason: it is `build_nat_prelude` plus the IPC declarations, so it costs
    // no more than the already-unconditional `nat` group.
    //
    // Absent from all three tools until 2026-08-31, and the omission had a
    // measured cost outside the kernel: `scripts/check-trust-closure.py` read
    // `F:excluded-middle-not-intuitionistic` and
    // `F:heyting-3-chain-refutes-excluded-middle` as having no identifiable
    // subject, and a census wrote them down as "umbrella facts" -- about
    // several theorems at once. Each is about exactly one theorem
    // (`ipc_excluded_middle_not_provable`, `ipc_heyting_join_not_ne_top`,
    // both verified byte-for-byte against the fact's `formal.statement`).
    // A prelude group no tool builds is indistinguishable from declarations
    // that do not exist.
    let mut ipc = Kernel::new();
    let _ = build_ipc_soundness_prelude(&mut ipc).expect("IPC soundness prelude must build");
    groups.push(("ipc", theorems(&ipc)));

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    groups.push(("rat", theorems(&rational)));

    let mut string = Kernel::new();
    let handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, handle, 2).expect("string prelude must build");
    groups.push(("string", theorems(&string)));

    // The CONSTRUCTED ℝ and ℂ, opt-in: both together cost real kernel
    // type-checking, and `axreal` above says nothing about them.
    if include_constructed {
        let mut creal = Kernel::new();
        let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
        groups.push(("creal", theorems(&creal)));

        let mut complex = Kernel::new();
        let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
        groups.push(("complex", theorems(&complex)));

        // The plane over the CONSTRUCTED reals. Without this row the headline
        // theorem count silently EXCLUDES the whole geometry development —
        // Varignon, the inner product, Pythagoras, Thales — and a total that
        // omits them is indistinguishable from one that includes them.
        let mut cpoint = Kernel::new();
        let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
        groups.push(("cpoint", theorems(&cpoint)));
    }
    groups
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(args) => args,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };

    let groups = build_groups(args.include_constructed);

    // `prelude<TAB>theorem<TAB>axiom-count<TAB>axioms`. Every (prelude, theorem)
    // pair, so the rows say where each theorem is visible; the DISTINCT count
    // below is the one that means "how much library exists".
    for (label, rows) in &groups {
        for (name, footprint) in rows {
            println!(
                "{label}\t{name}\t{}\t{}",
                footprint.len(),
                footprint.join(",")
            );
        }
    }

    // Distinct over canonical names. A theorem present in four nested preludes
    // is one theorem.
    let mut distinct: BTreeMap<&str, &Vec<String>> = BTreeMap::new();
    for (_, rows) in &groups {
        for (name, footprint) in rows {
            distinct.entry(name.as_str()).or_insert(footprint);
        }
    }
    let axiom_free = distinct.values().filter(|f| f.is_empty()).count();

    // ORIGIN attribution. The per-group counts above are cumulative, so `rat`'s
    // 320 includes every Nat and Int theorem underneath it and the difference
    // between groups is what the ℚ development actually contributed. For nested
    // preludes the group with the FEWEST theorems among those containing a given
    // theorem is the minimal element of the inclusion order -- i.e. where it was
    // proved. Ties (two groups with identical theorem sets, e.g. `axreal` builds
    // `logic` and adds no theorems of its own) go to whichever was CONSTRUCTED
    // FIRST above, which is dependency order; breaking ties alphabetically
    // instead credited `axreal` with `logic`'s two theorems and reported
    // `logic: originated=0`, which is backwards. Ties are counted and printed so
    // the ambiguity is visible rather than silently absorbed.
    let mut origin: BTreeMap<&str, usize> = groups.iter().map(|(l, _)| (*l, 0)).collect();
    let mut ties = 0usize;
    for name in distinct.keys() {
        let mut containing: Vec<(usize, usize, &str)> = groups
            .iter()
            .enumerate()
            .filter(|(_, (_, rows))| rows.iter().any(|(n, _)| n == name))
            .map(|(index, (label, rows))| (rows.len(), index, *label))
            .collect();
        containing.sort_unstable();
        if containing.len() > 1 && containing[0].0 == containing[1].0 {
            ties += 1;
        }
        if let Some((_, _, label)) = containing.first() {
            *origin.get_mut(label).expect("group label is known") += 1;
        }
    }

    let built: BTreeSet<&str> = groups.iter().map(|(label, _)| *label).collect();
    for (label, rows) in &groups {
        let free = rows.iter().filter(|(_, f)| f.is_empty()).count();
        eprintln!(
            "{label}: theorems={} axiom_free={} axiom_bearing={} originated={}",
            rows.len(),
            free,
            rows.len() - free,
            origin[label]
        );
    }
    eprintln!("origin_ties: {ties}");
    eprintln!(
        "distinct: theorems={} axiom_free={} axiom_bearing={} preludes={}",
        distinct.len(),
        axiom_free,
        distinct.len() - axiom_free,
        built.iter().copied().collect::<Vec<_>>().join(",")
    );

    let mut failures = Vec::new();
    for (label, want) in &args.expected {
        // Coverage is declared. Expecting a prelude that was never built is an
        // error rather than a zero -- the whole point of this file.
        let Some((_, rows)) = groups.iter().find(|(name, _)| name == label) else {
            failures.push(format!(
                "--expect names {label:?}, which was not built (missing --include-constructed?); \
                 built: {}",
                built.iter().copied().collect::<Vec<_>>().join(",")
            ));
            continue;
        };
        if rows.len() != *want {
            failures.push(format!(
                "{label}: expected {want} theorems, found {}",
                rows.len()
            ));
        }
    }
    if let Some(want) = args.expect_distinct
        && distinct.len() != want
    {
        failures.push(format!(
            "expected {want} distinct theorems, found {}",
            distinct.len()
        ));
    }
    if let Some(want) = args.expect_axiom_free
        && axiom_free != want
    {
        failures.push(format!(
            "expected {want} axiom-free distinct theorems, found {axiom_free}"
        ));
    }
    if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        for failure in &failures {
            eprintln!("error: {failure}");
        }
        ExitCode::FAILURE
    }
}
