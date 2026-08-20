//! Per-theorem axiom footprints for every prelude — this kernel's `#print axioms`.
//!
//! Output: `prelude<TAB>theorem<TAB>footprint-size<TAB>comma-separated-axioms`,
//! sorted, with an empty final column for an axiom-free theorem.
//!
//! The summary on stderr is the part that matters when reading this by eye. It
//! reports, per prelude, how many theorems are axiom-free and how the footprint
//! sizes are spread against the environment-wide count. A spread that collapses
//! — every theorem resting on every axiom — would mean [`Kernel::axiom_footprint`]
//! bought nothing over enumerating the environment, which is the bound it exists
//! to improve on.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example theorem_axiom_footprint
//! cargo run -q -p axeyum-lean-kernel --example theorem_axiom_footprint -- Int.mul
//! ```

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_int_prelude, build_nat_prelude,
};

fn theorems(kernel: &Kernel) -> Vec<(String, Vec<String>)> {
    let mut rows: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            // Axioms are included, not just theorems. In the `Int` and `AxReal`
            // preludes they are the ONLY substantive declarations — those
            // preludes derive nothing, they assert 34 and 30 properties outright
            // — so restricting to theorems would report on two pieces of
            // well-founded-recursion scaffolding and nothing else.
            Declaration::Theorem { name, .. } | Declaration::Axiom { name, .. } => {
                let footprint = kernel
                    .axiom_footprint(*name)
                    .into_iter()
                    .map(|a| kernel.display_name(a).to_string())
                    .collect();
                Some((kernel.display_name(*name).to_string(), footprint))
            }
            _ => None,
        })
        .collect();
    rows.sort();
    rows
}

fn environment_axioms(kernel: &Kernel) -> usize {
    kernel
        .environment()
        .iter()
        .filter(|(_, d)| {
            matches!(
                d,
                Declaration::Axiom { .. }
                    | Declaration::Opaque { .. }
                    | Declaration::Quotient { .. }
            )
        })
        .count()
}

fn main() {
    let filter = std::env::args().nth(1).unwrap_or_default();

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    let mut real = Kernel::new();
    let _ = build_arith_prelude(&mut real).expect("AxReal prelude must build");

    for (label, kernel) in [("nat", &nat), ("integer", &integer), ("axreal", &real)] {
        let rows = theorems(kernel);
        let env_axioms = environment_axioms(kernel);

        for (name, footprint) in &rows {
            if !filter.is_empty() && !name.contains(&filter) {
                continue;
            }
            println!(
                "{label}\t{name}\t{}\t{}",
                footprint.len(),
                footprint.join(",")
            );
        }

        let free = rows.iter().filter(|(_, f)| f.is_empty()).count();
        let sizes: Vec<usize> = rows.iter().map(|(_, f)| f.len()).collect();
        let min = sizes.iter().copied().min().unwrap_or(0);
        let max = sizes.iter().copied().max().unwrap_or(0);
        let mean = if sizes.is_empty() {
            0.0
        } else {
            f64::from(u32::try_from(sizes.iter().sum::<usize>()).unwrap_or(u32::MAX))
                / f64::from(u32::try_from(sizes.len()).unwrap_or(u32::MAX))
        };
        eprintln!(
            "{label}: {} theorems, {free} axiom-free, footprint min={min} mean={mean:.1} \
             max={max}, environment has {env_axioms} trusted declarations",
            rows.len()
        );
    }
}
