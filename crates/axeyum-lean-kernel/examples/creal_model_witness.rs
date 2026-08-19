//! **The `Real` axiom package has a model that is actually ℝ** — ADR-0512
//! phase R4, with the exit status depending on it.
//!
//! `arith_model_witness` prints the same table for the `Int` model and ends
//! with the sentence that bounds what it establishes: *"This is relative
//! consistency of the Real axiom set, not a discharge of it: Int is not R."*
//! This example is that caveat being discharged. The carrier is
//! [`CReal`](axeyum_lean_kernel::CRealPrelude) — a Bishop setoid of regular
//! ℚ-sequences over the constructed ℚ, admitted at **zero** trusted
//! declarations — and it is the real numbers, not a ring that happens to
//! satisfy 22 hypotheses.
//!
//! ```sh
//! cargo run --release -q -p axeyum-lean-kernel --example creal_model_witness
//! ```
//!
//! Each `law` row is a `Real` axiom, the `CReal` theorem modelling it, and the
//! `Kernel::axiom_footprint` of the witness `Real.CRealModel.<law>` — a theorem
//! whose type is the axiom's own type with the eight carrier/operation
//! constants substituted **and** `Eq Real` read as `CReal.Equiv`, computed from
//! the environment rather than written by hand, and type-checked by the kernel
//! at admission. `restated` marks the nine laws that needed the equality
//! rewrite; `identical` marks those whose interpreted type is the `CReal`
//! theorem's own statement symbol for symbol, not merely definitionally equal
//! to it.
//!
//! # What the exit status depends on
//!
//! 1. all 22 witnesses are **present as checked `Theorem`s** and carry an empty
//!    footprint — presence asserted before the footprint is read, because
//!    `axiom_footprint` of an interned-but-undeclared name is the empty vector
//!    and a footprint-only check passes with the witness deleted;
//! 2. the 22 laws come from the environment: every `Real.*` trusted declaration
//!    is either one of the eight interpreted symbols or a modelled law, so a
//!    31st axiom is a shortfall here rather than a smaller-but-tidy count;
//! 3. exactly **nine** are restated over `CReal.Equiv` and thirteen are
//!    verbatim — ADR-0512 Measurement 2, read out of the kernel; and
//! 4. the seven **discrimination** witnesses are present and axiom-free. This
//!    is the one the footprints cannot do for themselves. An empty carrier
//!    satisfies every ∀-law; the total relation is an equivalence relation and
//!    satisfies `le_refl`/`le_trans`/`add_le_add`; the *empty* relation
//!    satisfies six of the seven strict-order laws; and `fun _ _ => zero`
//!    satisfies `mul_zero`, `mul_comm` and `sq_nonneg`. Twenty-two empty
//!    footprints over a degenerate structure look exactly like twenty-two empty
//!    footprints over ℝ.
//!
//! # What this does NOT claim
//!
//! `Eq CReal` is **not** the equality of real numbers — `CReal.Equiv` is — and
//! nine of the 22 obligations say so in their own statement. A consumer that
//! wants its `Eq`-rewriting back goes through the ordered-ring telescope's
//! equality slot (ADR-0512 phase R3), which is the interface this model
//! satisfies; it does not get Leibniz equality on reals, which is what would
//! cost `Quot.sound`.
//!
//! The step from "every axiom translates" to "every *derivation* translates" is
//! the standard homomorphism argument over the term language and is not
//! machine-checked here — the kernel cannot state it.
//!
//! And the `Real` package's 30 axioms are **unchanged** by this: ADR-0512
//! retires them by *deletion*, once no consumer references them, not by
//! exhibiting a model. Measured after phase R3 landed, 18 files still reference
//! `build_arith_prelude`/`ArithPrelude`, and `LraReconstructCtx`'s own doc says
//! "the trusted base is `build_arith_prelude`'s axioms".

#![allow(clippy::too_many_lines)]

use axeyum_lean_kernel::{Declaration, Kernel, build_creal_model_of_arith};

fn main() {
    let mut kernel = Kernel::new();
    let model = build_creal_model_of_arith(&mut kernel).expect("the CReal model must build");
    let mut failed = false;

    println!("kind\treal\tinterpretation\tfootprint\trestated\tidentical");
    for &(real, creal) in &model.symbols {
        println!(
            "symbol\t{}\t{}\t-\t-\t-",
            kernel.display_name(real),
            kernel.display_name(creal)
        );
    }
    println!(
        "equality\t{}\t{}\t-\t-\t-",
        kernel.display_name(model.equality.0),
        kernel.display_name(model.equality.1)
    );

    // (1): presence FIRST, then the footprint.
    let mut rows: Vec<(String, String, String, bool, bool)> = Vec::new();
    for law in &model.laws {
        let present = matches!(
            kernel.environment().get(law.witness),
            Some(Declaration::Theorem { .. })
        );
        if !present {
            eprintln!(
                "FAIL: {} is not a checked Theorem. Its axiom_footprint is empty \
                 because the name was never declared, not because the law holds.",
                kernel.display_name(law.witness)
            );
            failed = true;
        }
        let footprint = kernel
            .axiom_footprint(law.witness)
            .into_iter()
            .map(|a| kernel.display_name(a).to_string())
            .collect::<Vec<_>>()
            .join(",");
        if present && !footprint.is_empty() {
            failed = true;
        }
        rows.push((
            kernel.display_name(law.real).to_string(),
            kernel.display_name(law.creal).to_string(),
            footprint,
            law.restated_over_equiv,
            law.identical,
        ));
    }
    rows.sort();
    for (real, creal, footprint, restated, identical) in &rows {
        let footprint = if footprint.is_empty() {
            "[]"
        } else {
            footprint
        };
        println!("law\t{real}\t{creal}\t{footprint}\t{restated}\t{identical}");
    }

    let axiom_free = rows
        .iter()
        .filter(|(_, _, footprint, _, _)| footprint.is_empty())
        .count();
    let identical = rows.iter().filter(|(_, _, _, _, id)| *id).count();
    let restated = model.restated_count();

    // (2): the population is derived from the environment, not from the table.
    let declared = kernel
        .environment()
        .iter()
        .filter(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => {
                let rendered = kernel.display_name(*name).to_string();
                rendered == "Real" || rendered.starts_with("Real.")
            }
            _ => false,
        })
        .count();
    if declared != model.symbols.len() + model.laws.len() {
        eprintln!(
            "FAIL: the Real package has {declared} trusted declarations but this model \
             accounts for {} symbols + {} laws. A Real axiom with no interpretation is \
             not modelled, whatever the footprints below say.",
            model.symbols.len(),
            model.laws.len()
        );
        failed = true;
    }

    // (3): ADR-0512 Measurement 2, read out of the kernel.
    if restated != 9 {
        eprintln!(
            "FAIL: {restated} laws were restated over CReal.Equiv, not 9. The Real \
             package's Eq-fragment changed shape and ADR-0512's Measurement 2 no \
             longer describes it."
        );
        failed = true;
    }

    // (4): the seven witnesses that stop 22 empty footprints being vacuous.
    // Presence FIRST here too, and for the same reason.
    let p = model.creal;
    let guards = [
        ("carrier inhabited", p.of_rat),
        ("Equiv discriminates", p.not_zero_one),
        ("le discriminates", p.not_le_one_zero),
        ("lt inhabited", p.zero_lt_one),
        ("lt irreflexive", p.lt_irrefl),
        ("mul agrees with Rat.mul on Q", p.of_rat_mul),
        ("mul discriminates", p.not_equiv_mul_one_one_zero),
    ];
    let mut guards_held = 0usize;
    for (what, name) in guards {
        let present = matches!(
            kernel.environment().get(name),
            Some(Declaration::Theorem { .. } | Declaration::Definition { .. })
        );
        if !present {
            eprintln!(
                "FAIL: {what} — {} is not a checked declaration. Every law above still \
                 has an empty footprint; an empty carrier, a total relation, an empty \
                 relation and a constant-zero product all produce exactly that.",
                kernel.display_name(name)
            );
            failed = true;
            continue;
        }
        if kernel.axiom_footprint(name).is_empty() {
            guards_held += 1;
        } else {
            eprintln!(
                "FAIL: {what} — {} does not rest on nothing.",
                kernel.display_name(name)
            );
            failed = true;
        }
    }

    eprintln!(
        "Real: {declared} trusted declarations = {} interpreted symbols + {} modelled \
         laws; {axiom_free}/{} witnesses have an EMPTY axiom footprint, {identical}/{} \
         are syntactically the CReal law, {restated}/{} needed restating over \
         CReal.Equiv; {guards_held}/{} discrimination witnesses hold",
        model.symbols.len(),
        model.laws.len(),
        rows.len(),
        rows.len(),
        rows.len(),
        guards.len()
    );

    if failed {
        eprintln!(
            "FAIL: the constructed reals are NOT a model of the Real axiom package as \
             claimed — see above. ADR-0512 phase R4 does not hold as stated."
        );
        std::process::exit(1);
    }
    eprintln!(
        "The Real axiom package is modelled by the CONSTRUCTED reals, at zero trusted \
         declarations. ADR-0456's caveat is discharged: the carrier is no longer Int, \
         it is a Bishop setoid of regular rational sequences, and CReal.ofRat embeds Q \
         into it. What is NOT on offer is Eq CReal as real-number equality — it is \
         CReal.Equiv, and the nine restated laws say so in their own statement."
    );
}
