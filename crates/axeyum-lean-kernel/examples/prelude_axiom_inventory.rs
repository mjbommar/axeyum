//! Emit the exact reconstruction-prelude axiom population for TL0.4.
//!
//! Output is deterministic tab-separated data:
//! `prelude<TAB>name<TAB>canonical-type-utf8-as-hex`.  Hex keeps the boundary
//! unambiguous without adding a serialization dependency to the zero-dependency
//! kernel crate.  The consumer hashes the decoded canonical type and binds it to
//! the reviewed ledger.

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_int_prelude, build_logic_prelude,
    build_string_prelude,
};

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

fn inventory(prelude: &str, kernel: &Kernel) -> Vec<(String, String, String)> {
    let mut rows: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, ty, .. } => Some((
                prelude.to_owned(),
                kernel.display_name(*name).to_string(),
                kernel.render_lean(*ty),
            )),
            _ => None,
        })
        .collect();
    rows.sort();
    rows
}

fn main() {
    // No hard-coded population sizes live here any more (ADR-0465).  They did:
    // `integer` was pinned at 34, the Int development was proved down to 1, and
    // this example -- which `scripts/gen-lean-axiom-ledger.py` shells out to --
    // spent two days exiting 101 because nothing checked its status.  An
    // `assert_eq!` in an emit path is not a gate; it is an outage that fires
    // when the number *improves*.  The expectation now lives in the ledger
    // manifest, is derived from this output rather than written down, and is
    // enforced by `gen-lean-axiom-ledger.py --check`.  Coverage is cross-checked
    // there against `nat_axiom_inventory`, which declares a per-prelude count
    // line even for the axiom-free preludes, so a prelude that silently stopped
    // being built here fails that gate instead of shrinking the published total.
    let mut real = Kernel::new();
    let _ = build_arith_prelude(&mut real).expect("AxReal prelude must build");
    let real_rows = inventory("real", &real);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    let integer_rows = inventory("integer", &integer);

    let mut string = Kernel::new();
    let logic = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic, 2).expect("string prelude must build");
    let string_rows = inventory("string", &string);

    let mut rows = real_rows;
    rows.extend(integer_rows);
    rows.extend(string_rows);
    rows.sort();
    for (prelude, name, canonical_type) in rows {
        println!("{prelude}\t{name}\t{}", hex(canonical_type.as_bytes()));
    }
}
