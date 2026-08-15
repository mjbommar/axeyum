//! Time a full prelude build in a fresh kernel.
//!
//! The prelude build is the kernel's own critical-path workload: six call sites
//! rebuild one, and every reduction cache in the type checker is exercised by
//! it. Any change to the WHNF cache key has to be paid for here, so this
//! example exists to make that price a measurement rather than an estimate.
//!
//! Output is deterministic tab-separated data:
//! `prelude<TAB>iteration<TAB>elapsed-micros`. Aggregate downstream; the
//! example deliberately does no statistics of its own.

use std::time::Instant;

use axeyum_lean_kernel::{
    Kernel, build_arith_prelude, build_int_prelude, build_logic_prelude, build_nat_prelude,
    build_string_prelude,
};

fn iterations() -> u32 {
    std::env::args()
        .nth(1)
        .and_then(|raw| raw.parse().ok())
        .unwrap_or(5)
}

fn main() {
    let rounds = iterations();
    println!("prelude\titeration\telapsed_micros");
    for iteration in 0..rounds {
        for (label, build) in [
            (
                "nat",
                (|kernel: &mut Kernel| {
                    build_nat_prelude(kernel).expect("nat prelude must build");
                }) as fn(&mut Kernel),
            ),
            ("logic", |kernel: &mut Kernel| {
                build_logic_prelude(kernel).expect("logic prelude must build");
            }),
            ("integer", |kernel: &mut Kernel| {
                build_int_prelude(kernel).expect("integer prelude must build");
            }),
            ("real", |kernel: &mut Kernel| {
                build_arith_prelude(kernel).expect("real prelude must build");
            }),
            ("string", |kernel: &mut Kernel| {
                let logic = build_logic_prelude(kernel).expect("logic prelude must build");
                build_string_prelude(kernel, logic, 2).expect("string prelude must build");
            }),
        ] {
            let mut kernel = Kernel::new();
            let started = Instant::now();
            build(&mut kernel);
            let elapsed = started.elapsed().as_micros();
            println!("{label}\t{iteration}\t{elapsed}");
        }
    }
}
