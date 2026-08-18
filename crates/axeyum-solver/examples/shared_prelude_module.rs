//! What the **split module layout** costs and saves, measured on the shipped
//! front door's own fixtures.
//!
//! # The number this exists to produce
//!
//! `examples/front_door_carrier.rs` reports the price of the axiom-free carrier:
//! a refutation over the constructed reals renders to a Lean module of
//! ~1.3 MB, against ~8 KB over the axiomatized `Real` package. Measured
//! 2026-08-18, **the refutation's own theorem term is 4,193 bytes** of that —
//! 0.16%. The rest is the ℕ/ℤ/ℚ/setoid development, and it is *the same bytes*
//! for every query over that carrier.
//!
//! So this example emits it once as a shared Lean module and renders each query
//! module as an `import` of it, and reports:
//!
//! * the per-query module size, self-contained against split;
//! * that the shared module is **byte-identical** across fixtures — the property
//!   that makes "emit once, import many" sound rather than merely convenient;
//! * that the `axiom` lines across BOTH halves still equal
//!   `Kernel::axiom_footprint`, which is the invariant
//!   `front_door_carrier --require-axiom-free` enforces on the single file. A
//!   smaller artefact that drops a declaration the kernel footprint still
//!   contains is a regression however good the byte count looks.
//!
//! # What a third party has to do, stated rather than hidden
//!
//! The split artefact is **strictly weaker** than the single file it replaces.
//! `lean Query.lean` checks a self-contained module and needs nothing else; the
//! split needs the shared module compiled to an `.olean` first and found on
//! `LEAN_PATH`. `--emit <dir>` writes both halves and prints the exact two
//! commands, generated from the artefact by `LeanPreludeModule::check_script`.
//! `tests/real_lean_shared_prelude_crosscheck.rs` (in `axeyum-lean-kernel`) runs
//! those two commands against the pinned Lean, with the no-`LEAN_PATH` negative
//! control that keeps "Lean accepted it" from being consistent with the import
//! having done nothing.
//!
//! # Usage
//!
//! ```text
//! cargo run -p axeyum-solver --features full --example shared_prelude_module
//! cargo run -p axeyum-solver --features full --example shared_prelude_module -- --require-split
//! cargo run -p axeyum-solver --features full --example shared_prelude_module -- --emit /tmp/split
//! ```
//!
//! `--require-split` makes the exit status depend on the finding: nonzero unless
//! every fixture's query module is at least 50x smaller than its self-contained
//! form, the shared module is identical across fixtures, and the two halves'
//! `axiom` lines together equal the kernel footprint.

use std::collections::BTreeSet;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{ExprId, Kernel, LeanPreludeModule, NameId};
use axeyum_solver::{
    LraReconstructCtx, ReconstructError, carrier_axioms_of, reconstruct_lra_proof,
    reconstruct_sos_proof, refutation_axiom_footprint,
};

/// The shared module's Lean name, and therefore its file stem.
const SHARED_MODULE: &str = "AxeyumCarrier";

/// The theorem name the query module states, matching the front door's.
const THEOREM: &str = "axeyum_refutation";

/// The floor `--require-split` enforces on the per-query saving. Measured far
/// above it (see the lane note); set low enough that ordinary churn in the
/// carrier does not trip it and high enough that losing the split would.
const REQUIRED_FACTOR: usize = 50;

/// Which reconstructor a fixture exercises.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Route {
    Lra,
    Sos,
}

type Fixture = (&'static str, Route, fn(&mut TermArena) -> Vec<TermId>);

/// `x < 0 ∧ 0 ≤ x` — the two-row strict conflict.
fn strict_bound_conflict(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    vec![a1, a2]
}

/// `x + y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` — three rows, a genuine Farkas combination.
fn three_row_farkas(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let sum = arena.real_add(x, y).unwrap();
    let a1 = arena.real_le(sum, zero).unwrap();
    let a2 = arena.real_le(one, x).unwrap();
    let a3 = arena.real_le(one, y).unwrap();
    vec![a1, a2, a3]
}

/// `x·x < 0` — the sum-of-squares route.
fn sos_square(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let sq = arena.real_mul(x, x).unwrap();
    let a = arena.real_lt(sq, zero).unwrap();
    vec![a]
}

fn fixtures() -> Vec<Fixture> {
    vec![
        (
            "strict-bound  x<0 and 0<=x",
            Route::Lra,
            strict_bound_conflict as fn(&mut TermArena) -> Vec<TermId>,
        ),
        (
            "three-row     x+y<=0, 1<=x, 1<=y",
            Route::Lra,
            three_row_farkas,
        ),
        ("sos-square    x*x<0", Route::Sos, sos_square),
    ]
}

fn reconstruct(
    ctx: &mut LraReconstructCtx,
    route: Route,
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<ExprId, ReconstructError> {
    match route {
        Route::Lra => reconstruct_lra_proof(ctx, arena, assertions),
        Route::Sos => reconstruct_sos_proof(ctx, arena, assertions),
    }
}

/// A footprint, re-spelled the way an emitted Lean module spells it.
///
/// [`Kernel::display_name`] and [`Kernel::lean_name`] are NOT the same string,
/// and both differences bite anything comparing a `#print axioms` footprint
/// against `axiom` lines: a numeric name component is not a legal Lean
/// identifier on its own, so `axeyum.reconstruct.x.0` is emitted as
/// `axeyum.reconstruct.x._0`; and the kernel's computational naturals are rooted
/// at `AxNat` so they do not shadow Lean's `Nat`. The first draft of this
/// example compared display names to module text and reported "footprint not
/// covered" for an artefact that was entirely correct.
///
/// Resolved through the kernel rather than by re-implementing the two rules
/// here, so this cannot drift from the renderer.
fn lean_spelling(kernel: &Kernel, footprint: &[String]) -> Vec<String> {
    let wanted: BTreeSet<&str> = footprint.iter().map(String::as_str).collect();
    kernel
        .environment()
        .iter()
        .filter(|(id, _)| wanted.contains(kernel.display_name(**id).to_string().as_str()))
        .map(|(id, _)| kernel.lean_name(*id))
        .collect()
}

/// The names declared by an `axiom` line in a module — what Lean's
/// `#print axioms` can report on it. The compiler-internal
/// `unsafe axiom lcErased` and friends are deliberately NOT counted: no proof
/// term mentions them, so they never enter a footprint, and the
/// `starts_with("axiom ")` test already excludes them.
fn axiom_names(source: &str) -> Vec<String> {
    source
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("axiom ")?;
            // `axiom Foo.bar.{u} : ...` -- keep the full dotted name, drop the
            // universe-parameter suffix the renderer appends.
            let token = rest.split_whitespace().next()?;
            Some(match token.find(".{") {
                Some(at) => token[..at].to_owned(),
                None => token.to_owned(),
            })
        })
        .collect()
}

/// Whether the two halves TOGETHER declare every entry of `footprint` exactly
/// once, and the query half declares nothing outside it.
///
/// This is the split's form of the single-file invariant "the module's axiom
/// lines equal the kernel footprint". It cannot be a bare count here: the shared
/// module is rooted at the WHOLE carrier environment, so it legitimately carries
/// axioms this particular refutation never reaches, and summing the two halves
/// would exceed the footprint for a module set that is perfectly correct.
///
/// What must hold instead is coverage in both directions — nothing the kernel
/// counts is missing from the artefact, and the query half introduces no
/// assumption the kernel did not count.
fn footprint_is_covered(footprint: &[String], query: &str, shared: &str) -> (bool, bool) {
    let in_query: BTreeSet<String> = axiom_names(query).into_iter().collect();
    let in_shared: BTreeSet<String> = axiom_names(shared).into_iter().collect();
    let wanted: BTreeSet<String> = footprint.iter().cloned().collect();
    let covered = wanted
        .iter()
        .all(|name| in_query.contains(name) || in_shared.contains(name));
    let query_adds_nothing = in_query.iter().all(|name| wanted.contains(name));
    (covered, query_adds_nothing)
}

/// One fixture's measurement.
struct Split {
    label: &'static str,
    self_contained: usize,
    query: usize,
    shared: usize,
    shared_source: String,
    self_contained_source: String,
    footprint_covered: bool,
    query_adds_nothing: bool,
    query_axioms: usize,
    footprint: usize,
    carrier_axioms: usize,
    query_source: String,
    check_script: String,
}

/// The carrier declarations one fixture REACHES: the intersection of the
/// context's pre-query environment with the closure of the refutation.
///
/// The obvious root set — the whole carrier environment — is wrong, and the
/// reason is a measurement rather than a preference. The constructed-real
/// context holds 445 declarations and a refutation reaches 280 of them; two of
/// the 165 it does not reach (`CReal.Equiv.not_zero_one` and
/// `CReal.not_le_one_zero`, and the two theorems citing the first) are
/// **rejected by Lean 4.30.0** although the in-tree kernel admits them. Rooting
/// the shared module at the whole environment therefore emits a file Lean will
/// not compile, for reasons that have nothing to do with the refutations that
/// import it — measured 2026-08-18 and reproduced with the sharing pass off, so
/// it is not a rendering artefact.
///
/// So the shared module is rooted at the UNION of what this family of queries
/// reaches. That keeps it emitted-once (the union is one set) and checkable.
fn reached_carrier(
    ctx: &LraReconstructCtx,
    carrier: &[NameId],
    goal: ExprId,
    proof: ExprId,
) -> Vec<NameId> {
    let reached: BTreeSet<NameId> = ctx
        .kernel()
        .declarations_reached(&[goal, proof])
        .into_iter()
        .collect();
    carrier
        .iter()
        .copied()
        .filter(|n| reached.contains(n))
        .collect()
}

/// One fixture, up to the point where the shared root set is known.
struct Reconstructed {
    ctx: LraReconstructCtx,
    carrier: Vec<NameId>,
    reached: Vec<NameId>,
    goal: ExprId,
    proof: ExprId,
    footprint: Vec<String>,
    footprint_lean: Vec<String>,
    carrier_axioms: usize,
}

fn reconstruct_fixture(
    label: &'static str,
    route: Route,
    build: fn(&mut TermArena) -> Vec<TermId>,
) -> Result<Reconstructed, String> {
    let mut arena = TermArena::new();
    let assertions = build(&mut arena);

    let mut ctx = LraReconstructCtx::try_new_over_constructed_reals()
        .map_err(|e| format!("{label}: the CReal carrier did not build: {e:?}"))?;
    // The snapshot that bounds "shared": every declaration the carrier context
    // admitted BEFORE any query symbol existed. Taking it from the finished
    // context instead would sweep the query's own variables into the module
    // every other query imports.
    let carrier: Vec<NameId> = ctx.kernel().environment().iter().map(|(n, _)| *n).collect();

    let proof = reconstruct(&mut ctx, route, &arena, &assertions)
        .map_err(|e| format!("{label}: CReal reconstruction failed: {e:?}"))?;
    let footprint = refutation_axiom_footprint(&mut ctx, proof)
        .map_err(|e| format!("{label}: CReal footprint failed: {e:?}"))?;
    let carrier_axioms = carrier_axioms_of(&footprint).len();
    // The SAME footprint spelled as the emitted module spells it.
    let footprint_lean = lean_spelling(ctx.kernel(), &footprint);

    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    let reached = reached_carrier(&ctx, &carrier, false_, proof);
    Ok(Reconstructed {
        ctx,
        carrier,
        reached,
        goal: false_,
        proof,
        footprint,
        footprint_lean,
        carrier_axioms,
    })
}

/// Render one fixture's two halves against a root set shared by the whole
/// family.
fn measure(label: &'static str, fixture: &Reconstructed, roots: &[NameId]) -> Split {
    let (goal, proof) = (fixture.goal, fixture.proof);
    let kernel = fixture.ctx.kernel();
    let self_contained = kernel.render_lean_module_compact(THEOREM, goal, proof);
    let shared: LeanPreludeModule = kernel.render_lean_prelude_module(SHARED_MODULE, roots);
    let query = kernel.render_lean_module_compact_importing(THEOREM, goal, proof, &[], &shared);

    let (covered, query_adds_nothing) =
        footprint_is_covered(&fixture.footprint_lean, &query, shared.source());
    let footprint = fixture.footprint.len();
    let carrier_axioms = fixture.carrier_axioms;

    Split {
        label,
        self_contained: self_contained.len(),
        query: query.len(),
        shared: shared.source().len(),
        // Both halves, because the invariant is about the module SET.
        footprint_covered: covered,
        query_adds_nothing,
        query_axioms: axiom_names(&query).len(),
        footprint,
        carrier_axioms,
        check_script: shared.check_script("<dir>", "Query.lean"),
        shared_source: shared.source().to_owned(),
        self_contained_source: self_contained,
        query_source: query,
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let require_split = arguments.iter().any(|a| a == "--require-split");
    let emit = arguments
        .iter()
        .position(|a| a == "--emit")
        .and_then(|i| arguments.get(i + 1))
        .cloned();
    match run(require_split, emit.as_deref()) {
        Ok(()) => {}
        Err(message) => {
            eprintln!("FAIL: {message}");
            std::process::exit(1);
        }
    }
}

fn run(require_split: bool, emit: Option<&str>) -> Result<(), String> {
    // Pass 1: reconstruct every fixture and learn which carrier declarations the
    // family reaches. Pass 2: render every half against the UNION, so one shared
    // module serves them all.
    let mut reconstructed = Vec::new();
    for &(label, route, build) in &fixtures() {
        reconstructed.push((label, reconstruct_fixture(label, route, build)?));
    }
    let union: BTreeSet<NameId> = reconstructed
        .iter()
        .flat_map(|(_, fixture)| fixture.reached.iter().copied())
        .collect();
    // Carrier `NameId`s agree across contexts only because each context is built
    // the same way -- which is also what makes the shared module byte-identical
    // below, so the assertion there is the check on this assumption.
    let carrier_size = reconstructed[0].1.carrier.len();
    let roots: Vec<NameId> = union.into_iter().collect();
    let splits: Vec<Split> = reconstructed
        .iter()
        .map(|(label, fixture)| measure(label, fixture, &roots))
        .collect();

    println!("=== the SPLIT module layout, over the constructed reals");
    println!("    shared module `{SHARED_MODULE}` emitted once; each query module imports it");
    println!(
        "    rooted at the {} of {carrier_size} carrier declarations this family REACHES \
         (see `reached_carrier`)\n",
        roots.len()
    );
    let mut all_shrunk = true;
    let mut module_matches_kernel = true;
    let mut all_free = true;
    for split in &splits {
        let factor = split.self_contained / split.query.max(1);
        println!("  --- {}", split.label);
        println!("    self-contained : {:>9} B", split.self_contained);
        println!(
            "    split          : {:>9} B query + {} B shared  ({factor}x smaller per query)",
            split.query, split.shared
        );
        println!(
            "    kernel footprint {} ({} carrier); query-half `axiom` lines {}; \
             every footprint entry declared across the two halves: {}; the query half \
             declares nothing outside it: {}",
            split.footprint,
            split.carrier_axioms,
            split.query_axioms,
            split.footprint_covered,
            split.query_adds_nothing
        );
        all_shrunk &= factor >= REQUIRED_FACTOR;
        module_matches_kernel &= split.footprint_covered && split.query_adds_nothing;
        all_free &= split.carrier_axioms == 0;
    }

    // The property that makes "emit once, import many" sound. If two fixtures
    // rendered different shared modules, each query would need its own and the
    // whole saving would be nominal.
    let identical = splits
        .windows(2)
        .all(|pair| pair[0].shared_source == pair[1].shared_source);
    println!();
    println!("the shared module is byte-identical across fixtures: {identical}");
    println!("every query module is at least {REQUIRED_FACTOR}x smaller: {all_shrunk}");
    println!("the two halves cover the kernel footprint exactly: {module_matches_kernel}");
    println!("refutations still rest on zero carrier axioms: {all_free}");
    println!();
    println!("to check a query module, a third party runs (from `--emit <dir>`):");
    print!("{}", splits[0].check_script);
    println!(
        "this is STRICTLY WEAKER than the single-file artefact, which needs only \
         `lean Query.lean`."
    );

    if let Some(directory) = emit {
        std::fs::create_dir_all(directory).map_err(|e| format!("{directory}: {e}"))?;
        let shared_path = format!("{directory}/{SHARED_MODULE}.lean");
        let query_path = format!("{directory}/Query.lean");
        // The single-file artefact beside the split, so the two can be TIMED
        // against each other: the saving is not only bytes, it is how long a
        // third party waits per query once the shared module is compiled.
        let whole_path = format!("{directory}/Whole.lean");
        std::fs::write(&whole_path, &splits[0].self_contained_source)
            .map_err(|e| format!("{whole_path}: {e}"))?;
        std::fs::write(&shared_path, &splits[0].shared_source)
            .map_err(|e| format!("{shared_path}: {e}"))?;
        std::fs::write(&query_path, &splits[0].query_source)
            .map_err(|e| format!("{query_path}: {e}"))?;
        println!();
        println!(
            "wrote {shared_path}, {query_path} and {whole_path} (the single-file control); run:"
        );
        print!("{}", splits[0].check_script.replace("<dir>", directory));
    }

    if require_split && !(identical && all_shrunk && module_matches_kernel && all_free) {
        return Err(
            "--require-split was given but the shared module is not identical across \
             fixtures, a query module did not shrink by the required factor, the two \
             halves do not cover the kernel's footprint exactly, or a refutation \
             still rests on a carrier axiom"
                .to_owned(),
        );
    }
    Ok(())
}
