//! Print the machine-checked **model** of the `AxReal` axiom package in the
//! constructed, axiom-free `Int` development.
//!
//! `nat_axiom_inventory` answers "how many trusted declarations does the `AxReal`
//! prelude have" (30) and stops there. That number, on its own, does not say
//! whether the axioms are *satisfiable* — and an inconsistent axiom package
//! would make every reconstruction built on it vacuously valid while every gate
//! in the repository stayed green. This example answers the next question: is
//! there a carrier we have actually built that satisfies all of them?
//!
//! Each row is a `AxReal` declaration and its interpretation. For a law, the
//! `witness` column names a theorem whose type is the `AxReal` axiom's type with
//! the eight carrier/operation constants substituted — computed from the
//! environment, not written by hand — and whose proof is the corresponding
//! `Int` theorem, type-checked by the kernel at admission. `footprint` is
//! `Kernel::axiom_footprint` on that witness; empty is the claim.
//!
//! What this does and does not license is spelled out in the module docs of
//! `arith_model.rs`: it is a relative-consistency result, not a discharge of
//! the `AxReal` axioms. `ℤ` is not `ℝ`.
//!
//! ```sh
//! cargo run --release -q -p axeyum-lean-kernel --example arith_model_witness
//! ```

use axeyum_lean_kernel::{Declaration, Kernel, build_int_model_of_arith};

fn main() {
    let mut kernel = Kernel::new();
    let model = build_int_model_of_arith(&mut kernel).expect("the Int model must build");

    println!("kind\treal\tinterpretation\tfootprint\tidentical");
    for &(real, int) in &model.symbols {
        println!(
            "symbol\t{}\t{}\t-\t-",
            kernel.display_name(real),
            kernel.display_name(int)
        );
    }
    let mut rows: Vec<(String, String, String, bool)> = model
        .laws
        .iter()
        .map(|law| {
            let footprint = kernel
                .axiom_footprint(law.witness)
                .into_iter()
                .map(|a| kernel.display_name(a).to_string())
                .collect::<Vec<_>>()
                .join(",");
            (
                kernel.display_name(law.real).to_string(),
                kernel.display_name(law.int).to_string(),
                footprint,
                law.identical,
            )
        })
        .collect();
    rows.sort();
    for (real, int, footprint, identical) in &rows {
        let footprint = if footprint.is_empty() {
            "[]"
        } else {
            footprint
        };
        println!("law\t{real}\t{int}\t{footprint}\t{identical}");
    }

    let axiom_free = rows
        .iter()
        .filter(|(_, _, footprint, _)| footprint.is_empty())
        .count();
    let identical = rows.iter().filter(|(_, _, _, id)| *id).count();

    // The population is derived from the environment, not from the table above:
    // an AxReal declaration this model forgot must show up as a shortfall here
    // rather than as a smaller-but-still-tidy count.
    let declared = kernel
        .environment()
        .iter()
        .filter(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => {
                let rendered = kernel.display_name(*name).to_string();
                rendered == "AxReal" || rendered.starts_with("AxReal.")
            }
            _ => false,
        })
        .count();

    eprintln!(
        "AxReal: {declared} trusted declarations = {} interpreted symbols + {} modelled laws; \
         {axiom_free}/{} witnesses have an EMPTY axiom footprint, {identical}/{} are \
         syntactically the Int law",
        model.symbols.len(),
        model.laws.len(),
        rows.len(),
        rows.len()
    );
    eprintln!(
        "This is relative consistency of the AxReal axiom set, not a discharge of it: \
         Int is not R."
    );
}
