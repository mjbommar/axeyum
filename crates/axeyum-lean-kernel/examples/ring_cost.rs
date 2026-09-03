//! Print the `ring` producer's wall-clock cost per emitted term.
//!
//! The measurement lives in `crate::ring::cost`; this is the printer.
//!
//! `--release` is MANDATORY. In debug the kernel's own recursion costs up to
//! 32x per frame, so a debug number describes no configuration anyone ships.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example ring_cost
//! ```

use axeyum_lean_kernel::on_a_deep_stack;
use axeyum_lean_kernel::ring::cost;

const REPEATS: u32 = 200;

fn main() {
    on_a_deep_stack(|| {
        if cfg!(debug_assertions) {
            eprintln!(
                "ring_cost: NOT --release. Debug frames cost up to 32x here, so these \
                 numbers describe no shipped configuration. Re-run with --release."
            );
        }
        println!("ring cost, {REPEATS} emissions per shape, prelude built once per shape");
        println!("{:-<80}", "");
        for r in cost::measure(REPEATS) {
            println!(
                "{:42}  search+emit {:7.3} ms   +kernel {:7.3} ms",
                r.label, r.search_ms, r.total_ms
            );
        }
    });
}
