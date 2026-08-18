//! An LRA/Farkas refutation that assumes **nothing**: the same proof term,
//! parameterised over the ordered-ring interface, with a measured-empty axiom
//! footprint — and the original `Real`-specific statement recovered from it by
//! instantiation.
//!
//! ## What this measures, and why it is not the same claim as before
//!
//! `reconstruct_lra_proof` builds a term of type `False` over the `Real`
//! prelude. That prelude is 30 trusted declarations, and ADR-0456 measured what
//! they are: eight carrier/operation symbols and 22 laws of an **ordered
//! commutative ring with 1** — no inverse, no division, no completeness, no
//! Archimedean axiom, not even totality. So the refutation was a statement
//! *about `Real`* resting on 30 assumptions.
//!
//! `generalize_over_ordered_ring` λ-abstracts those constants out of the proof
//! term. What comes back is
//!
//! ```text
//! ∀ (R : Type) (add mul : R → R → R) (neg : R → R) (zero one : R)
//!   (le lt : R → R → Prop),
//!   <the 22 laws> → ∀ (x₀ … : R), <the asserted constraints> → False
//! ```
//!
//! whose footprint is **empty**: the laws became the theorem's own hypotheses.
//! Applying it back to the 30 `Real` constants recovers the original `False`,
//! which the kernel re-checks — so nothing was lost, and the axioms became
//! unnecessary rather than proved.
//!
//! Three numbers are printed per fixture and each is measured, never asserted
//! by the code that produced it:
//!
//! - `footprint(generalized)` — must be empty; the exit status depends on it.
//! - `footprint(original)` — must NOT be empty, or the first number would be
//!   worthless. This is the negative control, in the same output.
//! - `footprint(instantiated)` — must cover the original, name for name.
//!
//! ```sh
//! cargo run --release -q -p axeyum-solver --features full \
//!     --example ordered_ring_refutation -- --require-empty
//! cargo run --release -q -p axeyum-solver --features full \
//!     --example ordered_ring_refutation -- --dump-statement
//! cargo run --release -q -p axeyum-solver --features full \
//!     --example ordered_ring_refutation -- --require-empty --constructed-reals
//! ```
//!
//! ## `--constructed-reals`: the same refutations with nothing assumed at all
//!
//! The generalized theorem is axiom-free either way — that is what abstraction
//! buys. The *instantiated* one is not: applying it back at the `Real` package
//! re-imports all 30 of that package's declarations, which are this repository's
//! entire remaining trusted surface. `--constructed-reals` applies it at
//! `CReal` instead (ADR-0483): a Bishop setoid of regular ℚ-sequences that
//! **proves** all 22 ordered-ring laws and all nine equality-slot obligations,
//! with an empty axiom footprint for each. The closed `False` then rests on
//! **zero** carrier axioms — only on the query's own variable and hypothesis
//! axioms — and the `Real` column in the same output is the control.

use std::process::ExitCode;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{CRealPrelude, Kernel, build_creal_prelude};
use axeyum_solver::{
    EqualitySlot, LraReconstructCtx, RingEquality, RingSignature, RingTelescope,
    generalize_over_ordered_ring, reconstruct_lra_proof, reconstruct_sos_proof,
    specialize_setoid_to_eq,
};

/// Which reconstructor a fixture goes through. Both land in the same kernel
/// over the same `Real` package, and both generalize the same way — the point
/// of listing an SOS fixture here is that it is the only route that touches the
/// multiplicative laws and `sq_nonneg`.
#[derive(Clone, Copy)]
enum Route {
    Lra,
    Sos,
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("ordered_ring_refutation: {message}");
            ExitCode::FAILURE
        }
    }
}

/// `x ≤ 0 ∧ 1 ≤ x` — the baby-Farkas order chain.
fn baby_farkas() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let upper = arena.real_le(x, zero).expect("x <= 0");
    let lower = arena.real_le(one, x).expect("1 <= x");
    (arena, vec![upper, lower])
}

/// `x + y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` — a Farkas *sum*, so the proof uses the
/// additive laws and not only the order chain.
fn farkas_sum() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let y = arena.real_var("y").expect("real variable");
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let sum = arena.real_add(x, y).expect("x + y");
    let a1 = arena.real_le(sum, zero).expect("x + y <= 0");
    let a2 = arena.real_le(one, x).expect("1 <= x");
    let a3 = arena.real_le(one, y).expect("1 <= y");
    (arena, vec![a1, a2, a3])
}

/// `x + y + z ≤ 1 ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z` — three multipliers.
fn farkas_three() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let y = arena.real_var("y").expect("real variable");
    let z = arena.real_var("z").expect("real variable");
    let one = arena.real_const(Rational::integer(1));
    let xy = arena.real_add(x, y).expect("x + y");
    let xyz = arena.real_add(xy, z).expect("x + y + z");
    let a0 = arena.real_le(xyz, one).expect("x + y + z <= 1");
    let a1 = arena.real_le(one, x).expect("1 <= x");
    let a2 = arena.real_le(one, y).expect("1 <= y");
    let a3 = arena.real_le(one, z).expect("1 <= z");
    (arena, vec![a0, a1, a2, a3])
}

/// `x < y ∧ y < x` — a strict cycle, so the proof uses `lt_trans`.
fn strict_cycle() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let y = arena.real_var("y").expect("real variable");
    let a1 = arena.real_lt(x, y).expect("x < y");
    let a2 = arena.real_lt(y, x).expect("y < x");
    (arena, vec![a1, a2])
}

/// `x·x < 0` — the sum-of-squares route, the only one that reaches
/// `sq_nonneg` and the multiplicative laws.
fn single_square() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").expect("real variable");
    let zero = arena.real_const(Rational::integer(0));
    let square = arena.real_mul(x, x).expect("x * x");
    let negative = arena.real_lt(square, zero).expect("x * x < 0");
    (arena, vec![negative])
}

/// The 30 rendered `Real` declaration names, so the "never reached" line can be
/// a set difference rather than a guess.
fn ordered_ring_declarations() -> Vec<String> {
    let leaves = [
        "add",
        "mul",
        "neg",
        "zero",
        "one",
        "le",
        "lt",
        "le_refl",
        "le_trans",
        "lt_irrefl",
        "lt_trans",
        "lt_of_lt_of_le",
        "lt_of_le_of_lt",
        "le_of_lt",
        "add_le_add",
        "add_comm",
        "add_assoc",
        "add_zero",
        "add_neg",
        "mul_le_mul_of_nonneg_left",
        "zero_lt_one",
        "add_lt_add_of_le_of_lt",
        "mul_comm",
        "mul_assoc",
        "mul_one",
        "mul_zero",
        "left_distrib",
        "mul_nonneg",
        "sq_nonneg",
    ];
    std::iter::once("Real".to_owned())
        .chain(leaves.iter().map(|leaf| format!("Real.{leaf}")))
        .collect()
}

/// One fixture: a label, the reconstructor it goes through, and its builder.
type Fixture = (&'static str, Route, fn() -> (TermArena, Vec<TermId>));

// One measurement walked end to end, printed as it goes.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut require_empty = false;
    let mut dump_statement = false;
    let mut footprint_table = false;
    let mut constructed_reals = false;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--require-empty" => require_empty = true,
            "--dump-statement" => dump_statement = true,
            "--footprint-table" => footprint_table = true,
            "--constructed-reals" => constructed_reals = true,
            other => return Err(format!("unknown flag `{other}`")),
        }
    }

    let fixtures: [Fixture; 5] = [
        ("baby-farkas     x<=0, 1<=x", Route::Lra, baby_farkas),
        ("farkas-sum      x+y<=0, 1<=x, 1<=y", Route::Lra, farkas_sum),
        (
            "farkas-three    x+y+z<=1, 1<=x,y,z",
            Route::Lra,
            farkas_three,
        ),
        ("strict-cycle    x<y, y<x", Route::Lra, strict_cycle),
        ("sos-square      x*x<0", Route::Sos, single_square),
    ];

    let mut all_empty = true;
    let mut all_recovered = true;
    let mut all_reproduced = true;
    let mut ever_used: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (label, route, build) in fixtures {
        let (arena, assertions) = build();
        let mut ctx = LraReconstructCtx::new();
        let proof = match route {
            Route::Lra => reconstruct_lra_proof(&mut ctx, &arena, &assertions),
            Route::Sos => reconstruct_sos_proof(&mut ctx, &arena, &assertions),
        }
        .map_err(|error| format!("{label}: reconstruction failed: {error:?}"))?;

        // The full ordered-ring interface: the uniform statement, all 30 bound.
        let full = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::FullInterface)
            .map_err(|error| format!("{label}: generalization failed: {error:?}"))?;
        // And the tight one: only what the proof rests on, so the instantiation
        // reproduces the original footprint name for name.
        let tight = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::Used)
            .map_err(|error| format!("{label}: tight generalization failed: {error:?}"))?;

        // ADR-0483 phase R3: the same query again, but with equality routed
        // through the declared slot instead of the kernel's `Eq`, generalized
        // over 39 binders, and then specialized BACK at `Eq` in the same kernel.
        // The specialization's inferred type must be the very expression `full`
        // already has -- expressions are hash-consed, so this is identity, not a
        // defeq that a normalizer could paper over.
        ctx.enable_setoid_equality()
            .map_err(|error| format!("{label}: the equality slot did not declare: {error:?}"))?;
        let setoid_proof = match route {
            Route::Lra => reconstruct_lra_proof(&mut ctx, &arena, &assertions),
            Route::Sos => reconstruct_sos_proof(&mut ctx, &arena, &assertions),
        }
        .map_err(|error| format!("{label}: setoid reconstruction failed: {error:?}"))?;
        let setoid =
            generalize_over_ordered_ring(&mut ctx, setoid_proof, RingTelescope::SetoidInterface)
                .map_err(|error| format!("{label}: setoid generalization failed: {error:?}"))?;
        let specialized = specialize_setoid_to_eq(&mut ctx, &setoid, &full)
            .map_err(|error| format!("{label}: specialization at `Eq` failed: {error:?}"))?;

        if footprint_table {
            // `theorem_axiom_footprint`'s exact shape --
            // `scope<TAB>theorem<TAB>size<TAB>comma-separated-axioms` -- so a
            // checker command can require the EMPTY column with one regex and
            // see the non-empty control row in the same output.
            //
            // The kernel example itself cannot be pointed at these theorems: it
            // builds the `nat`/`integer`/`real` preludes and nothing else, so a
            // grep of its output for an ordered-ring refutation returns nothing,
            // which reads exactly like "axiom-free" and is not. The measurement
            // below is the same `Kernel::axiom_footprint` call, made where the
            // declaration actually lives.
            println!(
                "ordered-ring\t{}\t{}\t{}",
                ctx.kernel().display_name(full.theorem),
                full.footprint.len(),
                full.footprint.join(",")
            );
            println!(
                "real-specific\t{}\t{}\t{}",
                ctx.kernel().display_name(full.original),
                full.original_footprint.len(),
                full.original_footprint.join(",")
            );
        }

        if !footprint_table {
            println!("=== {label}");
            println!(
                "  original     : False over the Real package -- footprint {} \
             ({} Real, {} variable/hypothesis)",
                full.original_footprint.len(),
                full.ring_used.len(),
                full.original_footprint.len() - full.ring_used.len()
            );
            println!(
                "  generalized  : forall (R : Type) .. {} binders ({} ring + {} vars + {} hyps) \
             -- footprint {}{}",
                full.binder_count(),
                full.ring_binders,
                full.var_binders,
                full.hyp_binders,
                full.footprint.len(),
                if full.footprint.is_empty() {
                    "  <== EMPTY"
                } else {
                    ""
                }
            );
            println!(
                "  tight form   : {} ring binders (only the laws this proof uses) -- footprint {}",
                tight.ring_binders,
                tight.footprint.len()
            );
            println!(
                "  instantiated : False again, footprint {} -- covers the original: {}, \
             exact under the tight form: {}",
                full.instantiated_footprint.len(),
                full.instantiation_recovers_original(),
                tight.instantiation_footprint_is_exact()
            );
            println!(
                "  setoid form  : {} ring binders (equality is a PARAMETER, not `Eq`) -- \
             footprint {}{}",
                setoid.ring_binders,
                setoid.footprint.len(),
                if setoid.footprint.is_empty() {
                    "  <== EMPTY"
                } else {
                    ""
                }
            );
            println!(
                "  back at Eq   : reproduces the {}-binder statement: {} -- specialization \
             footprint {}",
                full.ring_binders,
                specialized.reproduces_reference,
                specialized.footprint.len()
            );
            println!(
                "  setoid proof : kernel-`Eq` constants still mentioned: {}{}",
                specialized.setoid_residual_eq.len(),
                if specialized.setoid_residual_eq.is_empty() {
                    "  <== NONE, so it is instantiable at a defined equality"
                } else {
                    ""
                }
            );
            println!(
                "  binder types : {} of {} non-slot binder types reproduced exactly{}",
                specialized.binder_types_reproduced,
                full.ring_binders,
                if specialized.binder_type_mismatches.is_empty() {
                    ""
                } else {
                    "  <== MISMATCH"
                }
            );
            for mismatch in &specialized.binder_type_mismatches {
                println!("    mismatch: {mismatch}");
            }
            if !specialized.reproduces_reference {
                println!("    at Eq   : {}", specialized.statement_rendered);
                println!("    today   : {}", specialized.reference_rendered);
            }
            println!("  Real laws used ({}): {}", full.ring_used.len(), {
                let mut used = full.ring_used.clone();
                used.sort();
                used.join(" ")
            });

            if dump_statement {
                let rendered = ctx.kernel().render_lean(full.statement);
                println!("  statement    : {rendered}");
            }
        }

        ever_used.extend(full.ring_used.iter().cloned());
        all_reproduced &= specialized.reproduces_reference
            && specialized.footprint.is_empty()
            // Without this the other numbers all still read as a success while
            // the theorem is uninstantiable at anything but `Eq`.
            && specialized.setoid_residual_eq.is_empty()
            // The negative control: the setoid telescope must actually be WIDER,
            // or "reproduces the statement" would be the trivial claim that 30
            // binders reproduce 30 binders.
            && setoid.ring_binders == full.ring_binders + 9;
        all_empty &=
            full.footprint.is_empty() && tight.footprint.is_empty() && setoid.footprint.is_empty();
        all_recovered &= full.instantiation_recovers_original()
            && tight.instantiation_footprint_is_exact()
            // The negative control: an empty original footprint would make the
            // whole measurement vacuous.
            && !full.original_footprint.is_empty();
    }

    if footprint_table {
        return Ok(());
    }

    // Which of the 30 anything still USES. Not the same question as which are
    // declared: after this change no reconstructed refutation *depends* on any
    // of them, but a consumer that wants a `Real`-specific conclusion still
    // instantiates at the ones its proof shape invokes.
    println!();
    println!(
        "Real declarations reached by at least one fixture: {} of 30",
        ever_used.len()
    );
    let never: Vec<String> = ordered_ring_declarations()
        .into_iter()
        .filter(|name| !ever_used.contains(name))
        .collect();
    println!(
        "  never reached by any fixture ({}): {}",
        never.len(),
        never.join(" ")
    );

    println!();
    println!(
        "generalized refutations axiom-free: {all_empty}; original recovered by instantiation: \
         {all_recovered}; 39-binder setoid form specializes back to today's statement: \
         {all_reproduced}"
    );
    if require_empty && !(all_empty && all_recovered && all_reproduced) {
        return Err(
            "--require-empty was given but a refutation was not axiom-free, an \
             instantiation did not recover the original statement, the setoid \
             generalization did not specialize back to it at `Eq`, or the setoid \
             proof still mentions the kernel's `Eq`"
                .to_owned(),
        );
    }

    if constructed_reals {
        let carrier_free = over_the_constructed_reals(&fixtures)?;
        if require_empty && !carrier_free {
            return Err(
                "--require-empty was given but a refutation over the CONSTRUCTED reals \
                 still rests on a carrier axiom, cost a declaration to adopt its equality \
                 slot, or did not reduce the carrier footprint against the `Real` route"
                    .to_owned(),
            );
        }
    }
    Ok(())
}

/// The constructed reals as an ordered-ring signature, plus the equality slot
/// `CRealPrelude` already proves (ADR-0483 phase R4).
fn creal_signature() -> Result<(Kernel, RingSignature, EqualitySlot), String> {
    // Built once and cloned, on the same argument as `prelude_cache` (ADR-0464):
    // a clone is a bit-exact copy of a state this caller could have reached
    // itself, and nothing enters an environment except through the trusted gate,
    // which ran on the template. Measured 2026-08-18, one `build_creal_prelude`
    // is ~40 s in a debug build and this mode wants six of them.
    static TEMPLATE: std::sync::OnceLock<Result<(Kernel, CRealPrelude), String>> =
        std::sync::OnceLock::new();
    let (template, c) = TEMPLATE
        .get_or_init(|| {
            let mut kernel = Kernel::new();
            let c = build_creal_prelude(&mut kernel)
                .map_err(|error| format!("the CReal development did not build: {error:?}"))?;
            Ok((kernel, c))
        })
        .as_ref()
        .map_err(Clone::clone)?;
    let kernel = template.clone();
    let c = *c;
    let sig = RingSignature {
        // `CRealPrelude` has no `logic` field; the propositional prelude is three
        // hops down its rational/integer tower.
        logic: c.rat.int.logic,
        // NOT the kernel's `Eq`: `Eq CReal` is not the equality of real numbers,
        // and that is precisely what keeps the construction's trusted surface at
        // zero.
        equality: RingEquality::Defined(c.equiv),
        r: c.creal,
        add: c.add,
        mul: c.mul,
        neg: c.neg,
        zero: c.zero,
        one: c.one,
        le: c.le,
        lt: c.lt,
        le_refl: c.le_refl,
        le_trans: c.le_trans,
        lt_irrefl: c.lt_irrefl,
        lt_trans: c.lt_trans,
        lt_of_lt_of_le: c.lt_of_lt_of_le,
        lt_of_le_of_lt: c.lt_of_le_of_lt,
        le_of_lt: c.le_of_lt,
        add_le_add: c.add_le_add,
        add_comm: c.add_comm,
        add_assoc: c.add_assoc,
        add_zero: c.add_zero,
        add_neg: c.add_neg,
        mul_le_mul_of_nonneg_left: c.mul_le_mul_of_nonneg_left,
        zero_lt_one: c.zero_lt_one,
        add_lt_add_of_le_of_lt: c.add_lt_add_of_le_of_lt,
        mul_comm: c.mul_comm,
        mul_assoc: c.mul_assoc,
        mul_one: c.mul_one,
        mul_zero: c.mul_zero,
        left_distrib: c.left_distrib,
        mul_nonneg: c.mul_nonneg,
        sq_nonneg: c.sq_nonneg,
    };
    let slot = EqualitySlot {
        eq: c.equiv,
        eq_refl: c.equiv_refl,
        eq_symm: c.equiv_symm,
        eq_trans: c.equiv_trans,
        add_congr: c.add_congr,
        mul_congr: c.mul_congr,
        neg_congr: c.neg_congr,
        le_congr: c.le_congr,
        lt_congr: c.lt_congr,
    };
    Ok((kernel, sig, slot))
}

/// Run every fixture a second time over the **constructed** reals and report the
/// carrier footprint of the closed `False` each way.
///
/// The number that matters is the last column: how many of the refutation's
/// remaining axioms are *the carrier's*. Over the `Real` package it is 15-17 —
/// this repository's entire remaining trusted surface. Over `CReal` it is zero,
/// because `CRealPrelude` proves all 22 ordered-ring laws and all nine
/// equality-slot obligations outright.
///
/// Every figure is read out of the kernel. "Carrier axioms" is the intersection
/// of the instantiated theorem's measured `axiom_footprint` with the telescope
/// the generalization actually abstracted, so it cannot drift with a naming
/// convention.
fn over_the_constructed_reals(fixtures: &[Fixture]) -> Result<bool, String> {
    let (kernel, sig, slot) = creal_signature()?;
    println!();
    println!("=== the CONSTRUCTED reals (ADR-0483 phase R4): the same fixtures over `CReal`");

    // The equality slot, adopted rather than axiomatized. The control is in the
    // same line: the `Real` route has to declare eighteen axioms for it.
    let mut probe = LraReconstructCtx::with_ring_signature(kernel, sig)
        .map_err(|error| format!("CReal is not an admissible signature: {error:?}"))?;
    let adoption = probe
        .adopt_setoid_equality(&slot)
        .map_err(|error| format!("the equality slot did not adopt: {error:?}"))?;
    let real_slot_cost = {
        let mut real = LraReconstructCtx::new();
        let before = real.kernel().environment().len();
        real.enable_setoid_equality()
            .map_err(|error| format!("the Real route did not declare its slot: {error:?}"))?;
        real.kernel().environment().len() - before
    };
    println!(
        "  equality slot: `{}` adopted from CRealPrelude -- {} declarations added \
         (the `Real` route declares {} AXIOMS for the same slot)",
        adoption.relation, adoption.declarations_added, real_slot_cost
    );
    let mut all_carrier_free = adoption.declarations_added == 0 && real_slot_cost > 0;
    drop(probe);

    for &(label, route, build) in fixtures {
        let (arena, assertions) = build();

        // (a) The `Real` route, as the control.
        let mut real_ctx = LraReconstructCtx::new();
        let real_proof = reconstruct(&mut real_ctx, route, &arena, &assertions)
            .map_err(|error| format!("{label}: Real reconstruction failed: {error:?}"))?;
        let real_general =
            generalize_over_ordered_ring(&mut real_ctx, real_proof, RingTelescope::FullInterface)
                .map_err(|error| format!("{label}: Real generalization failed: {error:?}"))?;
        let real_carrier = carrier_axioms(&real_ctx, &real_general);

        // (b) The same query over the constructed reals.
        let (kernel, sig, slot) = creal_signature()?;
        let mut ctx = LraReconstructCtx::with_ring_signature(kernel, sig)
            .map_err(|error| format!("{label}: CReal is not an admissible signature: {error:?}"))?;
        ctx.adopt_setoid_equality(&slot)
            .map_err(|error| format!("{label}: the equality slot did not adopt: {error:?}"))?;
        let proof = reconstruct(&mut ctx, route, &arena, &assertions)
            .map_err(|error| format!("{label}: CReal reconstruction failed: {error:?}"))?;
        let residual = axeyum_solver::residual_eq_constants(&ctx, proof);
        let general = generalize_over_ordered_ring(&mut ctx, proof, RingTelescope::SetoidInterface)
            .map_err(|error| format!("{label}: CReal generalization failed: {error:?}"))?;
        let creal_carrier = carrier_axioms(&ctx, &general);

        println!("  --- {label}");
        println!(
            "    over Real  : closed False -- footprint {} of which {} are CARRIER axioms",
            real_general.instantiated_footprint.len(),
            real_carrier.len()
        );
        println!(
            "    over CReal : closed False -- footprint {} of which {} are CARRIER axioms{}",
            general.instantiated_footprint.len(),
            creal_carrier.len(),
            if creal_carrier.is_empty() {
                "  <== NONE"
            } else {
                ""
            }
        );
        println!(
            "    setoid form: {} ring binders -- footprint {}; kernel-`Eq` constants in the \
             proof term: {}",
            general.ring_binders,
            general.footprint.len(),
            residual.len()
        );
        if !creal_carrier.is_empty() {
            println!("    still carrier-dependent: {}", creal_carrier.join(" "));
        }

        all_carrier_free &= creal_carrier.is_empty()
            && general.footprint.is_empty()
            && residual.is_empty()
            && general.ring_binders == 39
            // The negative controls: an empty REAL carrier footprint, or an empty
            // CReal footprint outright, would make the comparison vacuous.
            && !real_carrier.is_empty()
            && !general.instantiated_footprint.is_empty();
    }

    println!();
    println!(
        "closed refutations over the CONSTRUCTED reals rest on zero carrier axioms: \
         {all_carrier_free}"
    );
    Ok(all_carrier_free)
}

/// The refutation's remaining axioms that belong to the **carrier**: the
/// measured footprint of the closed `False`, intersected with the telescope the
/// generalization abstracted. Everything else is the query's own variable and
/// hypothesis axioms.
fn carrier_axioms(
    ctx: &LraReconstructCtx,
    refutation: &axeyum_solver::OrderedRingRefutation,
) -> Vec<String> {
    let telescope: std::collections::BTreeSet<String> = refutation
        .ring_names
        .iter()
        .map(|&n| ctx.kernel().display_name(n).to_string())
        .collect();
    refutation
        .instantiated_footprint
        .iter()
        .filter(|name| telescope.contains(*name))
        .cloned()
        .collect()
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
