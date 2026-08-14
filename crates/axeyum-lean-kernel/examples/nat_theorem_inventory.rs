//! Emit every theorem the Nat prelude admits, with its canonical type.
//!
//! There was no way to read this without building the environment.  The
//! declarations go through a `.theorem(name, ..)` helper taking an interned
//! `NameId` field (`p.add_comm`), not a string literal, so grepping the source
//! for `.theorem("...")` returns **zero matches** and grepping for
//! `Declaration::Theorem` returns 1 — the helper — against 119 real theorems.
//! Two separate lanes miscounted this repository's theorems from source text
//! before anyone built the environment to look.
//!
//! The cost of that gap was not just miscounting.  A fact ledger entry has to
//! carry the proposition *as the kernel admitted it*, and with no inventory the
//! only route was transcribing from doc comments — which produced three seed
//! facts with statements the kernel would reject, two of them unparseable, and
//! sent one extraction lane off to build an out-of-tree probe crate.  Dumping
//! `render_lean` of the admitted type removes the transcription step entirely.
//!
//! Output: `name<TAB>arity<TAB>canonical-type`, sorted by name, rendered as
//! Lean-ish text rather than hex — this one is meant to be read and pasted into
//! a `formal.statement`, not hashed.  For the hash-bound trusted-surface
//! inventory see `nat_axiom_inventory`.
//!
//! Filter with the first argument, which matches as a substring:
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory -- add_comm
//! ```

use axeyum_lean_kernel::{Declaration, Kernel, build_nat_prelude};

fn main() {
    let filter = std::env::args().nth(1).unwrap_or_default();

    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");

    let mut rows: Vec<(String, usize, String)> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Theorem { name, ty, .. } => {
                let name = kernel.display_name(*name).to_string();
                (filter.is_empty() || name.contains(&filter))
                    .then(|| (name, 0usize, kernel.render_lean(*ty)))
            }
            _ => None,
        })
        .collect();
    rows.sort();

    for (name, _, ty) in &rows {
        // The binder count is read off the rendered telescope rather than the
        // expression, so it describes exactly what a consumer pasting this
        // string will see.
        let binders = ty.matches("->").count();
        println!("{name}\t{binders}\t{ty}");
    }
    eprintln!("{} theorems", rows.len());
}
