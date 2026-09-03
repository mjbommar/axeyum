//! Print the per-term cost of the producers ADR-1591 adds: `simp::list`,
//! `decide` over ℤ and ℚ, and `tactic::int`'s `Then(Simp, Linarith)`.
//!
//! The measurements live in `crate::simp::cost::measure_list` and
//! `crate::decide::cost::measure`; this is the printer.
//!
//! `--release` is MANDATORY — see `simp_cost.rs`.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example list_int_rat_cost
//! ```

use axeyum_lean_kernel::on_a_deep_stack;
use axeyum_lean_kernel::{decide, simp};

const REPEATS: u32 = 200;

fn main() {
    on_a_deep_stack(|| {
        if cfg!(debug_assertions) {
            eprintln!(
                "list_int_rat_cost: NOT --release. Debug frames cost up to 32x here, so these \
                 numbers describe no shipped configuration. Re-run with --release."
            );
        }
        println!("ADR-1591 cost, {REPEATS} emissions per shape, prelude built once per shape");
        println!("{:-<80}", "");
        for r in simp::cost::measure_list(REPEATS)
            .into_iter()
            .chain(decide::cost::measure(REPEATS))
        {
            println!(
                "{:48}  search+emit {:7.3} ms   +kernel {:7.3} ms",
                r.label, r.search_ms, r.total_ms
            );
        }
    });
}
