//! Emit the axiom population of the **Nat** reconstruction prelude.
//!
//! `prelude_axiom_inventory` covers `real`, `integer` and `string` only, and the
//! ledger it feeds (`scripts/gen-lean-axiom-ledger.py`) inherits exactly that
//! coverage.  So the layer this project makes its strongest claim about — a Nat
//! development with an empty axiom footprint — was the one layer no inventory
//! measured.  Reading zero Nat rows out of the existing inventory says only
//! "never enumerated", not "axiom-free"; the two are indistinguishable in that
//! output, and the difference is the whole claim.
//!
//! Output is `prelude<TAB>kind<TAB>name<TAB>canonical-type-utf8-as-hex`, sorted.
//! The extra `kind` column against `prelude_axiom_inventory` is deliberate: this
//! enumerates the whole trusted surface, not `Declaration::Axiom` alone (see
//! [`inventory`]).  For `nat` and `logic` an EMPTY body is the expected — and
//! meaningful — result, so the per-prelude counts go to stderr where they cannot
//! contaminate it, and an empty stdout is never ambiguous.
//!
//! `build_nat_prelude` builds the logic prelude first, so the `nat` group covers
//! the whole environment a Nat proof actually rests on; `logic` is enumerated
//! separately so its share is attributable rather than silently folded in.
//!
//! Measured 2026-08-14: `logic` and `nat` are 0 across all three trusted kinds,
//! and `real`/`integer`/`string` reproduce the ledger's committed 30/34/1 — so
//! the ledger's `Axiom`-only filter is not, in fact, under-binding today.

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_int_prelude, build_logic_prelude,
    build_nat_prelude, build_string_prelude,
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

/// Every declaration admitted **without** a checked proof body.
///
/// `prelude_axiom_inventory` filters on `Declaration::Axiom` alone, but that is
/// not the whole trusted surface: `Opaque` has no proof body to check, and
/// `Quotient` admits the quotient primitives — `Quot.sound` is literally one of
/// the three axioms Lean's own `#print axioms` reports. An `Axiom`-only count
/// can therefore read zero while trusted declarations are present, which is the
/// precise failure this example exists to rule out.
fn inventory(prelude: &str, kernel: &Kernel) -> Vec<(String, String, String, String)> {
    let mut rows: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| {
            let (kind, name, ty) = match declaration {
                Declaration::Axiom { name, ty, .. } => ("axiom", name, ty),
                Declaration::Opaque { name, ty, .. } => ("opaque", name, ty),
                Declaration::Quotient { name, ty, .. } => ("quotient", name, ty),
                _ => return None,
            };
            Some((
                prelude.to_owned(),
                kind.to_owned(),
                kernel.display_name(*name).to_string(),
                kernel.render_lean(*ty),
            ))
        })
        .collect();
    rows.sort();
    rows
}

fn main() {
    // The logic prelude alone, so its own share is attributable rather than
    // folded into Nat's (`build_nat_prelude` builds logic first).
    let mut logic_only = Kernel::new();
    let _ = build_logic_prelude(&mut logic_only).expect("logic prelude must build");
    let logic_rows = inventory("logic", &logic_only);

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    let nat_rows = inventory("nat", &nat);

    // The three preludes the existing ledger DOES cover, re-enumerated over the
    // full trusted surface rather than `Axiom` alone. A disagreement with the
    // ledger's committed counts (real=30, integer=34, string=1) is a finding:
    // it means the ledger binds less than it appears to.
    let mut real = Kernel::new();
    let _ = build_arith_prelude(&mut real).expect("Real prelude must build");
    let real_rows = inventory("real", &real);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    let integer_rows = inventory("integer", &integer);

    let mut string = Kernel::new();
    let logic = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic, 2).expect("string prelude must build");
    let string_rows = inventory("string", &string);

    let groups = [
        ("logic", &logic_rows),
        ("nat", &nat_rows),
        ("real", &real_rows),
        ("integer", &integer_rows),
        ("string", &string_rows),
    ];

    let mut rows: Vec<_> = groups.iter().flat_map(|(_, r)| (*r).clone()).collect();
    rows.sort();
    rows.dedup();
    for (prelude, kind, name, canonical_type) in &rows {
        println!(
            "{prelude}\t{kind}\t{name}\t{}",
            hex(canonical_type.as_bytes())
        );
    }

    for (label, group) in groups {
        let count = |k: &str| group.iter().filter(|(_, kind, _, _)| kind == k).count();
        eprintln!(
            "{label}: axiom={} opaque={} quotient={} total_trusted={}",
            count("axiom"),
            count("opaque"),
            count("quotient"),
            group.len()
        );
    }
}
