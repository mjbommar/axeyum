//! Emit the complete constructed-prelude declaration surface for Autogenesis.
//!
//! Rows carry both all-kind direct declaration references and the theorem-only
//! subset. The latter remains the proof dependency relation; the former is
//! search vocabulary and must not be confused with a transitive closure.
//!
//! # `--require-declaration <name>` — a DIRECT, discriminating presence check
//!
//! Every in-tree inventory example (`theorem_dependency_inventory`,
//! `nat_theorem_inventory`, `prelude_theorem_inventory`) filters to
//! `Declaration::Theorem` and explicitly excludes `Definition`s: "Definitions,
//! inductives and axioms are excluded" is `theorem_dependency_inventory`'s own
//! stated contract. So before this flag existed, no in-tree tool could assert
//! "definition `X` exists" with a non-zero exit when it does not — a fact
//! whose evidence is a `Definition` (e.g. `CReal.integral`, `CReal.e`) could
//! only be checked INDIRECTLY, via some theorem that cites it.
//!
//! `--require-declaration <name>` searches every constructed prelude's
//! environment (this binary already builds all of them for the unfiltered
//! mode) for a declaration whose `Kernel::display_name` is EXACTLY `<name>`
//! (e.g. `CReal.integral`, not a substring match), of ANY kind — axiom,
//! definition, theorem, opaque, inductive, constructor, recursor, or
//! quotient. On a match it prints `found\t<prelude-label>\t<kind>\t<name>\t
//! <footprint-size>` to stdout and exits 0. On NO match across every prelude
//! it prints an error to stderr and exits 1 — the same discriminating shape
//! `theorem_dependency_inventory` uses for a named filter matching nothing:
//! a deleted or renamed declaration must not read as a present one.
//!
//! Optional `--require-kind <kind>` (matching [`kind`]'s own strings:
//! `axiom`, `definition`, `theorem`, `opaque`, `inductive`, `constructor`,
//! `recursor`, `quotient`) additionally requires the match be of that exact
//! kind — a `Theorem` named `Foo.bar` must not satisfy a check meant to
//! confirm a `Definition` named `Foo.bar` exists (they cannot collide in this
//! kernel's namespacing, but the flag makes the intent explicit and checked
//! rather than assumed).
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example kernel_declaration_projection \
//!   -- --require-declaration CReal.integral --require-kind definition
//! ```
//!
//! `--release` is MANDATORY: this binary builds `creal`/`complex`/`cpoint`/`metric`/`intspace`,
//! `--release` is MANDATORY: this binary builds `creal`/`complex`/`cpoint`/`metric`/`rn`,
//! which recurse deep enough to overflow the default debug thread stack (the
//! deep-stack worker in `main` below covers the MAIN thread's frame, not
//! debug-vs-release per-frame size).

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_characterization, build_complex_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_intspace_prelude,
    build_ipc_soundness_prelude, build_list_nat_bridge, build_list_perm, build_logic_prelude,
    build_metric_prelude, build_nat_prelude, build_rat_prelude, build_string_prelude,
    build_cpoint_prelude, build_creal_prelude, build_int_prelude, build_ipc_soundness_prelude,
    build_list_nat_bridge, build_list_perm, build_logic_prelude, build_metric_prelude,
    build_nat_prelude, build_rat_prelude, build_rn_prelude, build_string_prelude,
};

fn kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        Declaration::Quotient { .. } => "quotient",
    }
}

fn emit(label: &str, kernel: &Kernel) {
    let mut rows = kernel
        .environment()
        .iter()
        .map(|(name, declaration)| {
            let rendered = kernel.display_name(*name).to_string();
            let direct_theorems = if matches!(declaration, Declaration::Theorem { .. }) {
                kernel
                    .theorem_dependencies(*name)
                    .into_iter()
                    .map(|dependency| kernel.display_name(dependency).to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            } else {
                String::new()
            };
            let direct_declarations = kernel
                .declaration_dependencies(*name)
                .into_iter()
                .map(|dependency| kernel.display_name(dependency).to_string())
                .collect::<Vec<_>>()
                .join(",");
            let direct_type_declarations = kernel
                .declaration_type_dependencies(*name)
                .into_iter()
                .map(|dependency| kernel.display_name(dependency).to_string())
                .collect::<Vec<_>>()
                .join(",");
            let canonical_type = kernel.render_lean(declaration.ty());
            assert!(
                !canonical_type.contains(['\t', '\n', '\r']),
                "canonical declaration type must remain one TSV field"
            );
            let footprint_size = kernel.axiom_footprint(*name).len();
            (
                rendered,
                kind(declaration),
                footprint_size,
                direct_type_declarations,
                direct_declarations,
                direct_theorems,
                canonical_type,
            )
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    for (
        name,
        declaration_kind,
        footprint_size,
        direct_type_declarations,
        direct_declarations,
        direct_theorems,
        canonical_type,
    ) in rows
    {
        println!(
            "{label}\t{declaration_kind}\t{name}\t{footprint_size}\t{direct_type_declarations}\t{direct_declarations}\t{direct_theorems}\t{canonical_type}"
        );
    }
}

/// If `target` is present in `kernel`'s environment (by exact rendered
/// display name), print `found\t<label>\t<kind>\t<name>\t<footprint-size>`
/// and return its kind string. Returns `None` on no match in this prelude.
fn check_declaration(label: &str, kernel: &Kernel, target: &str) -> Option<&'static str> {
    kernel.environment().iter().find_map(|(name, declaration)| {
        let rendered = kernel.display_name(*name).to_string();
        if rendered == target {
            let declaration_kind = kind(declaration);
            let footprint_size = kernel.axiom_footprint(*name).len();
            println!("found\t{label}\t{declaration_kind}\t{rendered}\t{footprint_size}");
            Some(declaration_kind)
        } else {
            None
        }
    })
}

fn main() -> ExitCode {
    // RUN THE WHOLE PROJECTION ON A DEEP STACK, not the process's main thread.
    //
    // This example builds every constructed prelude, and `Kernel::add_declaration`
    // recurses deeply enough through them to overflow the default 8 MiB
    // main-thread stack: `gen-autogenesis-kernel-dependency-projection.py`
    // shells out to it and got `died with <Signals.SIGABRT: 6>`, so the
    // projection could not be regenerated at all and had gone stale -- a lane
    // measured it holding 195 `Rat.*` declarations and zero `det2`, `cramer`
    // or `fib`.
    //
    // Same fix, and the same reasoning, as `theorem_dependency_inventory`:
    // `--release` happens to survive, but a doc note saying so cannot reach a
    // caller that does not read it. Carry the one documented envelope
    // (`axeyum_lean_kernel::DEEP_STACK_BYTES`, see `src/stack.rs`) here and
    // every caller works unchanged, debug or release.
    axeyum_lean_kernel::on_a_deep_stack(run)
}

// One line over the default `too_many_lines` threshold after the
// `collapsible_if` allow above was added; the function is a linear sequence
// of independent argument-validation steps, not a candidate for splitting.
#[allow(clippy::too_many_lines)]
fn run() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let require_declaration = args
        .iter()
        .position(|a| a == "--require-declaration")
        .and_then(|i| args.get(i + 1))
        .cloned();
    let require_kind = args
        .iter()
        .position(|a| a == "--require-kind")
        .and_then(|i| args.get(i + 1))
        .cloned();

    let unfiltered = require_declaration.is_none();

    let mut logic = Kernel::new();
    let _ = build_logic_prelude(&mut logic).expect("logic prelude must build");
    if unfiltered {
        emit("logic", &logic);
    }

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    if unfiltered {
        emit("nat", &nat);
    }

    // `List` (`list-carrier-1`/`list-carrier-2`), and it is the reason this
    // example was NOT a complete search surface for `List.count_toMultiset`/
    // `List.Perm` until 2026-09-03: `shape_search`-style lookups over this
    // projection could not have found them, which reads exactly like the
    // declarations not existing (the "does it already exist?" trap this
    // tool exists to prevent for every OTHER prelude). Built via the full
    // bridge + `Perm` package, not just `build_list_prelude`, so every `List`
    // declaration (including the `List`/`Nat.Multiset` bridge and `Perm`'s
    // four theorems) is searchable here, matching `prelude_theorem_inventory`'s
    // own `list` group.
    let mut list = Kernel::new();
    let (list_prelude, list_nat, list_bridge) =
        build_list_nat_bridge(&mut list).expect("List/Nat bridge must build");
    let _ = build_list_perm(&mut list, &list_prelude, &list_nat, &list_bridge)
        .expect("List.Perm must build");
    if unfiltered {
        emit("list", &list);
    }

    let mut axreal = Kernel::new();
    let _ = build_arith_prelude(&mut axreal).expect("AxReal prelude must build");
    if unfiltered {
        emit("axreal", &axreal);
    }

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    if unfiltered {
        emit("integer", &integer);
    }

    let mut characterization = Kernel::new();
    let _ =
        build_characterization(&mut characterization).expect("Nat/Int characterization must build");
    if unfiltered {
        emit("characterization", &characterization);
    }

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    if unfiltered {
        emit("rat", &rational);
    }

    let mut string = Kernel::new();
    let logic_handle = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic_handle, 2).expect("String prelude must build");
    if unfiltered {
        emit("string", &string);
    }

    let mut creal = Kernel::new();
    let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
    if unfiltered {
        emit("creal", &creal);
    }

    let mut complex = Kernel::new();
    let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
    if unfiltered {
        emit("complex", &complex);
    }

    let mut cpoint = Kernel::new();
    let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
    if unfiltered {
        emit("cpoint", &cpoint);
    }

    // `Metric.*` (ADR-1602), the metric-space carrier and its two instances.
    // It sits ON TOP of `cpoint` (which transitively builds `creal`), so it
    // needs its own label for exactly the reason the `ipc` comment below
    // records: a prelude this tool is blind to is indistinguishable from the
    // declaration not existing, and `--require-declaration` would report a
    // confident "no declaration named ..." for all 49 of them.
    let mut metric = Kernel::new();
    let _ = build_metric_prelude(&mut metric).expect("Metric prelude must build");
    // `IntSpace.*` (ADR-1612), the pre-integration space, its three instances
    // and the measure layer derived from the integral.
    let mut intspace = Kernel::new();
    let _ = build_intspace_prelude(&mut intspace).expect("IntSpace prelude must build");
    if unfiltered {
        emit("metric", &metric);
        emit("intspace", &intspace);
    }

    // `RN.*` (ADR-1606), the n-dimensional real inner-product space. It sits ON
    // TOP of `metric` and carries its own namespace, so it needs its own label
    // for exactly the reason the `metric` comment above records.
    let mut rn = Kernel::new();
    let _ = build_rn_prelude(&mut rn).expect("RN prelude must build");
    if unfiltered {
        emit("rn", &rn);
    }

    // The IPC package, and it is the reason this example is not "every prelude"
    // by accident. `build_ipc_soundness_prelude` transitively builds
    // `provable` -> `heyting` -> `nat`, so one label covers the whole
    // intuitionistic-logic surface: `ipc_excluded_middle_not_provable`,
    // `ipc_soundness`, `ipc_eval`, `ipc_ctx_meet`, and the 3-element Heyting
    // chain's `meet3`/`join3`/`himp3`/`not3`.
    //
    // It was ABSENT until 2026-08-31, and the omission had a measured cost:
    // `scripts/check-trust-closure.py` read two settled `kernel-lean` facts
    // (`F:excluded-middle-not-intuitionistic`,
    // `F:heyting-3-chain-refutes-excluded-middle`) as having no identifiable
    // subject, and an earlier census wrote them down as "umbrella facts" --
    // about several theorems at once. They are about exactly one each. The
    // tool was blind to the prelude, which is indistinguishable from the
    // declaration not existing.
    let mut ipc = Kernel::new();
    let _ = build_ipc_soundness_prelude(&mut ipc).expect("IPC soundness prelude must build");
    if unfiltered {
        emit("ipc", &ipc);
    }

    let Some(target) = require_declaration else {
        return ExitCode::SUCCESS;
    };

    // Check every constructed prelude's environment for the exact rendered
    // name. A declaration cannot appear in more than one of these disjoint
    // `Kernel`s under the same fully-qualified name by construction, so the
    // first match found is the only one possible; we still scan all of them
    // rather than stopping early so a rename into the wrong prelude cannot
    // silently pass by matching whichever prelude happens to be checked
    // first.
    let matches: Vec<&'static str> = [
        ("logic", &logic),
        ("nat", &nat),
        ("list", &list),
        ("axreal", &axreal),
        ("integer", &integer),
        ("characterization", &characterization),
        ("rat", &rational),
        ("string", &string),
        ("creal", &creal),
        ("complex", &complex),
        ("cpoint", &cpoint),
        ("metric", &metric),
        ("intspace", &intspace),
        ("rn", &rn),
        ("ipc", &ipc),
    ]
    .into_iter()
    .filter_map(|(label, kernel)| check_declaration(label, kernel, &target))
    .collect();

    if matches.is_empty() {
        eprintln!(
            "error: no declaration named {target:?} exists in any constructed prelude's \
             environment. Asking for a declaration and finding none is a failure, not an \
             empty answer -- a deleted or renamed declaration must not read as a present one."
        );
        return ExitCode::FAILURE;
    }

    #[allow(clippy::collapsible_if)]
    if let Some(wanted_kind) = require_kind {
        if !matches.iter().any(|&k| k == wanted_kind) {
            eprintln!(
                "error: {target:?} exists but not with kind {wanted_kind:?} (found kind(s): {})",
                matches.join(",")
            );
            return ExitCode::FAILURE;
        }
    }

    ExitCode::SUCCESS
}
