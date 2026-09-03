//! Emit, per admitted theorem, the theorems its statement and proof directly use.
//!
//! This exists to make the fact ledger's `depends_on` **derivable** rather than
//! transcribed — the position ADR-0465 already settled for the axiom ledger.
//!
//! # Why it is needed
//!
//! CLAUDE.md's flywheel ends with *"the concept DAG and the fact ledger say what
//! to prove next"*, and that arrow is `depends_on`. Measured 2026-08-17 by
//! `scripts/check-fact-dag.py`: of 109 facts, **65 declare no dependency and have
//! no dependent**, so proving one usually unlocks nothing. Some of that isolation
//! is honest — an SMT-LIB propositional refutation genuinely does not rest on a
//! Nat lemma — but 13 of the isolated facts are `kernel-lean`, and a kernel-route
//! proposition whose proof cites prelude theorems while declaring none is simply
//! unrecorded. Nothing could tell the two cases apart, because the information
//! lived only in the proof term.
//!
//! It was already being computed and discarded. `Kernel::axiom_footprint` walks
//! the whole constant closure and then keeps only `Axiom` / `Opaque` / `Quotient`;
//! `Kernel::theorem_dependencies` keeps the other half.
//!
//! # What it prints
//!
//! `name<TAB>dep,dep,dep` — DIRECT theorem references only, sorted, one line per
//! theorem, with the dependency list empty for a base theorem. Direct rather than
//! transitive because `depends_on` means what a proposition immediately rests on;
//! the transitive set of a late theorem is most of the prelude.
//!
//! Definitions, inductives and axioms are excluded: a proof of `Nat.add_comm`
//! references `Nat` and `Nat.add`, and recording those would say nothing about
//! which *propositions* it needs.
//!
//! ```sh
//! cargo run -q --release -p axeyum-lean-kernel --example theorem_dependency_inventory
//! cargo run -q --release -p axeyum-lean-kernel --example theorem_dependency_inventory -- euclid
//! ```
//!
//! # `--release` WAS mandatory for two hours, and is no longer — read this
//! before copying the flag from an older `checker_command`
//!
//! Adding `creal`/`complex`/`cpoint` made `Kernel::add_declaration` recurse
//! deeply enough that a DEBUG build blew the default main-thread stack:
//! `cargo build --release` exited 0 with 1,092 theorems while `cargo build`
//! aborted with `SIGABRT` -- `thread 'main' has overflowed its stack`, exit
//! 134. Nothing
//! was wrong with any theorem — a resource limit wearing a crash's clothes.
//!
//! That doc note is what this paragraph replaces, and it is worth saying why
//! rather than deleting it. The note was TRUE and it still did harm: it could
//! not reach the two scripts that already invoked this example without the
//! flag, so `just check` failed with `died with <Signals.SIGABRT: 6>` until
//! the example itself was fixed. **A doc comment cannot fix a call site it
//! does not know about.**
//!
//! The fix is the `axeyum_lean_kernel::on_a_deep_stack` worker in `main` below, and
//! it makes `--release` UNNECESSARY here: a debug build now exits 0 and
//! reports the same theorem count as release, measured on this tree by two
//! independent lanes. Passing `--release` remains correct and is faster, so
//! existing `checker_command`s need no change — but do not propagate
//! "mandatory" to a new one, and do not cite this tool as evidence that some
//! OTHER example needs the flag. `prelude_theorem_inventory
//! --include-constructed` and `nat_axiom_inventory --include-constructed` are
//! still genuinely affected; they have no deep-stack worker.
//!
//! # A filter that matches nothing is a FAILURE
//!
//! The same trap `nat_theorem_inventory` had until 2026-08-15: if this is ever a
//! fact's `checker_command`, a name that no longer exists must not print an empty
//! list and exit 0. A named filter matching nothing exits non-zero; an unfiltered
//! run has no expectation to violate and exits 0.

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, build_characterization, build_complex_prelude, build_cpoint_prelude,
    build_creal_prelude, build_int_prelude, build_list_nat_bridge, build_list_perm,
    build_logic_prelude, build_nat_prelude, build_rat_prelude, build_string_prelude,
};

fn main() -> ExitCode {
    // RUN THE WHOLE BUILD ON A DEEP STACK, not on the process's main thread.
    //
    // Extending this example to `creal`/`complex`/`cpoint` made a DEBUG build
    // overflow the default 8 MiB main-thread stack and die with SIGABRT before
    // printing anything. `--release` happens to survive, so the extension was
    // landed with a doc note saying `--release` is now mandatory -- and that
    // note did not reach the two scripts that already invoked this example
    // without it. `just check` then failed in `check-fact-depends-derived.py`
    // with `died with <Signals.SIGABRT: 6>`.
    //
    // A doc comment cannot fix a call site it does not know about, so carry
    // the stack here and let every caller -- debug or release, present or
    // future -- work unchanged. The size is `axeyum_lean_kernel::
    // DEEP_STACK_BYTES`, the one documented envelope (see `src/stack.rs`).
    axeyum_lean_kernel::on_a_deep_stack(run)
}

fn run() -> ExitCode {
    let filter: Option<String> = std::env::args().nth(1);

    let mut kernel = Kernel::new();
    // EVERY constructed prelude, not just `Nat`. Measured 2026-08-18, this
    // example built `Nat` alone and reported 139 theorems — so
    // `check-fact-depends-derived.py`, which reads this graph to decide whether
    // the ledger's `depends_on` agrees with the proof terms, was reporting
    // `missing_edges=0` while never looking at `Int`, `Rat`, `Str`, `Nat.Peano`
    // or `Int.Characterization`. Eight kernel-route facts sat outside its
    // coverage, including every one added that day. A zero from a tool that was
    // never pointed at the subject is indistinguishable from a strong negative,
    // which is exactly the trap CLAUDE.md records.
    //
    // `creal`/`complex`/`cpoint` (the constructed ℝ, ℂ, and the plane over
    // constructed ℝ) are now included: 423 theorems combined were previously
    // outside this tool's coverage, so a fact over them could never get a
    // derived `depends_on`. Each `build_*_prelude` call here is idempotent and
    // builds its own prerequisites (e.g. `build_creal_prelude` calls
    // `build_rat_prelude` itself), so re-adding `rat` here is a harmless no-op
    // rather than a duplicate build.
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    // `List` (`list-carrier-1`/`list-carrier-2`, 2026-09-03): absent here
    // until now, so `check-fact-depends-derived.py --fix` could not derive
    // ANY edge among the List-family facts (e.g. `List.count_reverse`
    // directly uses `List.count_append` in its proof term, but with `List`
    // outside this tool's coverage that dependency was invisible) --
    // reported `missing_edges=0` for the same reason the `Int`/`Rat`/`Str`
    // gap above once did: a zero from a tool never pointed at the subject.
    let (list_prelude, list_nat, list_bridge) =
        build_list_nat_bridge(&mut kernel).expect("List/Nat bridge must build");
    let _ = build_list_perm(&mut kernel, &list_prelude, &list_nat, &list_bridge)
        .expect("List.Perm must build");
    let _ = build_int_prelude(&mut kernel).expect("Int prelude must build");
    let _ = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    // The string prelude needs the logic package and an alphabet size; the Nat
    // build above already installed logic, so reuse it rather than rebuilding.
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let _ = build_string_prelude(&mut kernel, logic, 2).expect("String prelude must build");
    let _ = build_characterization(&mut kernel).expect("characterization must build");
    let _ = build_creal_prelude(&mut kernel).expect("CReal prelude must build");
    let _ = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
    let _ = build_cpoint_prelude(&mut kernel).expect("CPoint prelude must build");

    // Collect first, then sort by rendered name: environment iteration order is
    // an interning artifact and this output is meant to be diffable.
    let mut theorems: Vec<(String, Vec<String>)> = kernel
        .environment()
        .iter()
        .filter(|(_, decl)| matches!(decl, Declaration::Theorem { .. }))
        .map(|(name, _)| {
            let rendered = kernel.display_name(*name).to_string();
            let deps = kernel
                .theorem_dependencies(*name)
                .into_iter()
                .map(|d| kernel.display_name(d).to_string())
                .collect();
            (rendered, deps)
        })
        .collect();
    theorems.sort();

    let shown: Vec<&(String, Vec<String>)> = theorems
        .iter()
        .filter(|(name, _)| filter.as_ref().is_none_or(|f| name.contains(f)))
        .collect();

    for (name, deps) in &shown {
        println!("{name}\t{}", deps.join(","));
    }

    let with_deps = shown.iter().filter(|(_, d)| !d.is_empty()).count();
    let edges: usize = shown.iter().map(|(_, d)| d.len()).sum();
    eprintln!(
        "{} theorems, {with_deps} with dependencies, {edges} edges",
        shown.len()
    );

    if shown.is_empty() {
        if let Some(f) = filter {
            eprintln!(
                "error: no theorem matches {f:?}. Asking for a theorem and finding \
                 none is a failure, not an empty answer -- a deleted theorem must \
                 not read as a re-derived one."
            );
            return ExitCode::FAILURE;
        }
        eprintln!("error: the Nat prelude admitted no theorems at all");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
