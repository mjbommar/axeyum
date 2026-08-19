//! What the **shipped front door** rests on, measured through the front door.
//!
//! # The claim this exists to falsify
//!
//! `examples/ordered_ring_refutation.rs --constructed-reals` already shows that
//! a Farkas/SOS refutation *can* be built over the constructed reals with an
//! empty carrier footprint. It builds its own context to do it, so it says
//! nothing about what `prove_unsat_to_lean_module` — the function a user calls —
//! actually runs. Until 2026-08-18 the answer was "the `AxReal` package", whose 30
//! axioms are this repository's entire remaining trusted surface: the axiom-free
//! carrier existed and nothing shipped used it.
//!
//! This example measures the shipped path itself, two ways:
//!
//! 1. **through `prove_unsat_to_lean_module`** — the public front door, given a
//!    query as a `TermArena`. It reports which carrier the emitted module names
//!    and how large the module is.
//! 2. **through the kernel** — the same reconstruction on the same queries, with
//!    the proof admitted as `Theorem : False` and `Kernel::axiom_footprint` read
//!    off it (this kernel's `#print axioms`, transitive). Anything in that
//!    footprint outside the `axeyum.reconstruct.` namespace is an assumption of
//!    the **carrier**, and that count is the number that matters.
//!
//! Both carriers are measured every run, because "zero carrier axioms over
//! `CReal`" is worth nothing without "non-zero over `AxReal`" beside it. A run in
//! which the `AxReal` control came back empty would mean the measurement is broken,
//! not that `AxReal` became free — so the exit status checks for that too.
//!
//! # Usage
//!
//! ```text
//! cargo run -p axeyum-solver --features full --example front_door_carrier
//! cargo run -p axeyum-solver --features full --example front_door_carrier -- --require-axiom-free
//! ```
//!
//! `--require-axiom-free` makes the exit status depend on the finding: nonzero
//! unless every fixture reconstructs over `CReal` with an empty carrier
//! footprint, the `AxReal` control is non-empty on every fixture, and the shipped
//! module names the constructed carrier.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_solver::{
    LraReconstructCtx, carrier_axioms_of, prove_unsat_to_lean_module, reconstruct_lra_proof,
    reconstruct_sos_proof, refutation_axiom_footprint,
};

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
) -> Result<axeyum_lean_kernel::ExprId, axeyum_solver::ReconstructError> {
    match route {
        Route::Lra => reconstruct_lra_proof(ctx, arena, assertions),
        Route::Sos => reconstruct_sos_proof(ctx, arena, assertions),
    }
}

/// The self-contained Lean module this refutation renders to, in bytes.
///
/// Reported because it is the price of the axiom-free carrier and it is not
/// small: an `AxReal` module states the carrier laws it uses as axioms and stops,
/// whereas a `CReal` module must carry the whole constructed development — ℕ, ℤ,
/// ℚ and the setoid — with every proof body. A reader deciding whether to adopt
/// this default needs the number, not a reassurance.
fn render_bytes(ctx: &mut LraReconstructCtx, proof: axeyum_lean_kernel::ExprId) -> (usize, usize) {
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    // The COMPACT writer, because that is what the front door runs: measuring
    // the other one would report a module no caller receives.
    let source = ctx
        .kernel()
        .render_lean_module_compact("axeyum_refutation", false_, proof);
    // `axiom` LINES in the emitted module — what `#print axioms` reports on the
    // Lean side. This writer emits every reachable inductive as a real Lean
    // `inductive`, not as an opaque `axiom`, so the constructed development
    // contributes none of these: the count is the query's own variable and
    // hypothesis axioms, and it tracks the kernel footprint rather than
    // contradicting it.
    let axiom_lines = source
        .lines()
        .filter(|line| line.starts_with("axiom "))
        .count();
    (source.len(), axiom_lines)
}

fn main() {
    let require_axiom_free = std::env::args().any(|a| a == "--require-axiom-free");
    match run(require_axiom_free) {
        Ok(()) => {}
        Err(message) => {
            eprintln!("FAIL: {message}");
            std::process::exit(1);
        }
    }
}

fn run(require_axiom_free: bool) -> Result<(), String> {
    let fixtures = fixtures();
    let mut all_free = true;
    let mut control_is_live = true;
    let mut front_door_is_constructed = true;
    let mut module_matches_kernel = true;

    println!("=== the SHIPPED front door: `prove_unsat_to_lean_module`");
    for &(label, _, build) in &fixtures {
        let mut arena = TermArena::new();
        let assertions = build(&mut arena);
        let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &assertions)
            .map_err(|e| format!("{label}: the front door declined: {e}"))?;
        // The carrier is decided by the carrier DECLARATION, not by a substring
        // of the module text. That used to be a workaround: the axiomatized
        // package was named `Real`, and `CReal.` matches a `contains("Real.")`
        // test, so a name probe could not tell the constructed carrier from the
        // assumed one. ADR-0522 renamed the axiomatized package `AxReal`, which
        // `CReal` does not contain, so the substring hazard is gone — but
        // reading the declaration is still the right check, because it says
        // *what was admitted* rather than what a name happens to spell.
        let constructed = source.contains("inductive CReal") || source.contains("axiom CReal");
        let axiomatized = source.contains("axiom AxReal : Sort");
        println!(
            "  {label}\n    fragment {fragment:?}, module {} bytes, carrier {}",
            source.len(),
            if constructed && !axiomatized {
                "CReal (constructed)"
            } else if axiomatized {
                "AxReal (AXIOMATIZED)"
            } else {
                "UNRECOGNIZED"
            }
        );
        if source.contains("sorryAx") {
            return Err(format!("{label}: the shipped module contains `sorryAx`"));
        }
        front_door_is_constructed &= constructed && !axiomatized;
    }

    println!();
    println!("=== the same queries through the kernel: `Kernel::axiom_footprint` of `False`");
    println!(
        "    (carrier axioms = footprint entries outside the `axeyum.reconstruct.` namespace)"
    );
    for &(label, route, build) in &fixtures {
        let mut arena = TermArena::new();
        let assertions = build(&mut arena);

        // (a) the control: the axiomatized `AxReal` package.
        let mut real_ctx = LraReconstructCtx::try_new()
            .map_err(|e| format!("{label}: the AxReal package did not build: {e:?}"))?;
        let real_proof = reconstruct(&mut real_ctx, route, &arena, &assertions)
            .map_err(|e| format!("{label}: AxReal reconstruction failed: {e:?}"))?;
        let real_footprint = refutation_axiom_footprint(&mut real_ctx, real_proof)
            .map_err(|e| format!("{label}: AxReal footprint failed: {e:?}"))?;
        let real_carrier = carrier_axioms_of(&real_footprint);
        let (real_bytes, real_axiom_lines) = render_bytes(&mut real_ctx, real_proof);

        // (b) what the front door now runs: the constructed reals.
        let mut ctx = LraReconstructCtx::try_new_over_constructed_reals()
            .map_err(|e| format!("{label}: the CReal carrier did not build: {e:?}"))?;
        let proof = reconstruct(&mut ctx, route, &arena, &assertions)
            .map_err(|e| format!("{label}: CReal reconstruction failed: {e:?}"))?;
        let footprint = refutation_axiom_footprint(&mut ctx, proof)
            .map_err(|e| format!("{label}: CReal footprint failed: {e:?}"))?;
        let carrier = carrier_axioms_of(&footprint);
        let (creal_bytes, creal_axiom_lines) = render_bytes(&mut ctx, proof);

        println!("  --- {label}");
        println!(
            "    over AxReal: footprint {} of which {} are CARRIER axioms; module {real_bytes} \
             bytes, {real_axiom_lines} `axiom` lines",
            real_footprint.len(),
            real_carrier.len()
        );
        println!(
            "    over CReal : footprint {} of which {} are CARRIER axioms; module {creal_bytes} \
             bytes ({}x), {creal_axiom_lines} `axiom` lines{}",
            footprint.len(),
            carrier.len(),
            creal_bytes / real_bytes.max(1),
            if carrier.is_empty() { "  <== NONE" } else { "" }
        );
        if !carrier.is_empty() {
            println!("    still carrier-dependent: {}", carrier.join(" "));
        }
        // The negative controls. An empty `AxReal` carrier footprint, or an empty
        // CReal footprint outright, would make the comparison vacuous.
        control_is_live &= !real_carrier.is_empty() && !footprint.is_empty();
        all_free &= carrier.is_empty();
        // The two measurements must AGREE. `axiom` lines are what Lean's
        // `#print axioms` will report on the emitted module; the footprint is
        // what this kernel computes. Checking each alone would let one drift.
        module_matches_kernel &=
            creal_axiom_lines == footprint.len() && real_axiom_lines == real_footprint.len();
    }

    println!();
    println!("shipped front door emits the CONSTRUCTED carrier: {front_door_is_constructed}");
    println!("refutations over CReal rest on zero carrier axioms: {all_free}");
    println!("the AxReal control is non-vacuous: {control_is_live}");
    println!("the module's axiom lines equal the kernel footprint: {module_matches_kernel}");

    if require_axiom_free
        && !(all_free && control_is_live && front_door_is_constructed && module_matches_kernel)
    {
        return Err(
            "--require-axiom-free was given but the shipped front door does not \
                    reconstruct over an axiom-free carrier, the AxReal control came back \
                    empty (which would mean the measurement is broken, not that AxReal is \
                    free), the emitted module still names the axiomatized carrier, or \
                    the module's axiom lines disagree with the kernel's footprint"
                .to_owned(),
        );
    }
    Ok(())
}
