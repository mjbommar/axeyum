//! **ℂ, constructed, at trusted cost zero — and with no order, refuted rather
//! than omitted.**
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example complex_ring_witness
//! ```
//!
//! # What the exit status depends on
//!
//! Seven findings, and the last three are what stop this being a green light on
//! a vacuous or a degenerate claim:
//!
//! 1. every named declaration is a **checked** `Definition`/`Theorem`/
//!    inductive — never an `Axiom`, never an `Opaque`, never a `Quotient`;
//! 2. every one has an **empty** `Kernel::axiom_footprint`, and the whole
//!    environment's trusted surface (`Axiom` + `Opaque` + `Quotient`) is still
//!    empty afterwards — so ℚ, ℝ and ℂ together assume nothing;
//! 3. `ComplexPrelude::ring_laws` names **9 distinct** declarations and every
//!    one is a checked, footprint-empty `Theorem`. The headline count is read
//!    out of the kernel through that list and nowhere else, so a dropped or
//!    duplicated law flips the exit status rather than shrinking a sentence in
//!    a document;
//! 4. `Complex.ofReal` is present, so the carrier is **inhabited** — without
//!    it every law below could hold, footprint-free, of the empty type;
//! 5. `Complex.Equiv.not_zero_one` **and** `Complex.Equiv.not_zero_I` are both
//!    present. The first refuses the total relation; the second refuses one
//!    that ignores the imaginary component entirely, which the first cannot
//!    see. An equivalence relation that relates everything is still an
//!    equivalence relation;
//! 6. `Complex.ofReal_mul` **and** `Complex.I_sq` are both present, so
//!    `Complex.mul` is the product and not a degenerate binary operation.
//!    `mul_comm`, `mul_zero` and `left_distrib` all hold — footprint-free — of
//!    `fun _ _ => zero`. `ofReal_mul` pins the operation on the whole embedded
//!    ℝ; `I_sq` pins it at the one point `ofReal` cannot reach; and
//! 7. **`Complex.le` and `Complex.lt` do not exist, and
//!    `Complex.no_compatible_order` says why.**
//!    <!-- absent: Complex.le, Complex.lt -->
//!    Omitting an order proves
//!    nothing — a development that simply never got round to it looks
//!    identical. The theorem quantifies over both relations and derives
//!    `False` from seven of the `AxReal` package's 13 order laws, so this is a
//!    refutation and the absence is checked against it.
//!
//! # The nine, and the thirteen
//!
//! `ArithPrelude`'s axiomatized `AxReal` package is an **ordered** commutative
//! ring: 22 laws, 13 of which mention `le` or `lt`. The other nine —
//! `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`,
//! `mul_one`, `mul_zero`, `left_distrib` — are exactly what ℂ satisfies, and
//! all nine are stated over `Complex.Equiv` rather than `Eq`, because
//! `Eq Complex` is not the equality of complex numbers any more than
//! `Eq CReal` is the equality of real ones (ADR-0512).
//!
//! # What this does NOT claim
//!
//! No inverse, no division, no `√`, no completeness, no algebraic closure, and
//! no order. `Complex.normSq` lands in `CReal`'s **existing** nonneg cone,
//! which is available precisely because it is a statement about the components
//! rather than about ℂ.

#![allow(clippy::too_many_lines)]

use axeyum_lean_kernel::{Declaration, Kernel, build_complex_prelude};

fn main() {
    let mut kernel = Kernel::new();
    let p = build_complex_prelude(&mut kernel).expect("the Complex development must build");

    let admitted = [
        ("Complex", p.complex),
        ("Complex.mk", p.mk),
        ("Complex.rec", p.rec),
        ("Complex.re", p.re),
        ("Complex.im", p.im),
        ("Complex.Equiv", p.equiv),
        ("Complex.Equiv.refl", p.equiv_refl),
        ("Complex.Equiv.symm", p.equiv_symm),
        ("Complex.Equiv.trans", p.equiv_trans),
        ("Complex.ofReal", p.of_real),
        ("Complex.I", p.i),
        ("Complex.zero", p.zero),
        ("Complex.one", p.one),
        ("Complex.add", p.add),
        ("Complex.neg", p.neg),
        ("Complex.mul", p.mul),
        ("Complex.add_congr", p.add_congr),
        ("Complex.neg_congr", p.neg_congr),
        ("Complex.mul_congr", p.mul_congr),
        ("Complex.conj_congr", p.conj_congr),
        ("Complex.add_comm", p.add_comm),
        ("Complex.add_assoc", p.add_assoc),
        ("Complex.add_zero", p.add_zero),
        ("Complex.add_neg", p.add_neg),
        ("Complex.mul_comm", p.mul_comm),
        ("Complex.mul_assoc", p.mul_assoc),
        ("Complex.mul_one", p.mul_one),
        ("Complex.mul_zero", p.mul_zero),
        ("Complex.left_distrib", p.left_distrib),
        ("Complex.ofReal_add", p.of_real_add),
        ("Complex.ofReal_mul", p.of_real_mul),
        ("Complex.I_sq", p.i_sq),
        ("Complex.Equiv.not_zero_one", p.not_zero_one),
        ("Complex.Equiv.not_zero_I", p.not_zero_i),
        ("Complex.conj", p.conj),
        ("Complex.normSq", p.norm_sq),
        ("Complex.mul_conj", p.mul_conj),
        ("Complex.normSq_nonneg", p.norm_sq_nonneg),
        ("Complex.no_compatible_order", p.no_compatible_order),
    ];

    let mut failed = false;
    println!("declaration\tkind\tfootprint");
    for (label, name) in admitted {
        let Some(declaration) = kernel.environment().get(name) else {
            println!("{label}\tMISSING\t-");
            failed = true;
            continue;
        };
        let kind = match declaration {
            Declaration::Theorem { .. } => "theorem",
            Declaration::Definition { .. } => "definition",
            Declaration::Inductive { .. } => "inductive",
            Declaration::Constructor { .. } => "constructor",
            Declaration::Recursor { .. } => "recursor",
            Declaration::Axiom { .. } => "AXIOM",
            Declaration::Opaque { .. } => "OPAQUE",
            Declaration::Quotient { .. } => "QUOTIENT",
        };
        if matches!(
            declaration,
            Declaration::Axiom { .. } | Declaration::Opaque { .. } | Declaration::Quotient { .. }
        ) {
            failed = true;
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        if !footprint.is_empty() {
            failed = true;
        }
        println!(
            "{label}\t{kind}\t{}",
            if footprint.is_empty() {
                "-".to_owned()
            } else {
                footprint.join(",")
            }
        );
    }

    // (3): the headline count, read out of the kernel through `ring_laws`.
    let mut law_names: Vec<String> = p
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    law_names.sort();
    law_names.dedup();
    let laws_distinct = law_names.len() == 9;
    let laws_proved = p.ring_laws().into_iter().all(|law| {
        matches!(
            kernel.environment().get(law),
            Some(Declaration::Theorem { .. })
        ) && kernel.axiom_footprint(law).is_empty()
    });
    for law in p.ring_laws() {
        let footprint = kernel.axiom_footprint(law);
        println!(
            "law\t{}\t{}",
            kernel.display_name(law),
            if footprint.is_empty() {
                "[]".to_owned()
            } else {
                format!(
                    "[{}]",
                    footprint
                        .iter()
                        .map(|entry| kernel.display_name(*entry).to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                )
            }
        );
    }

    let theorem = |name| {
        matches!(
            kernel.environment().get(name),
            Some(Declaration::Theorem { .. })
        )
    };
    let inhabited = matches!(
        kernel.environment().get(p.of_real),
        Some(Declaration::Definition { .. })
    );
    let discriminating = theorem(p.not_zero_one);
    let imaginary_discriminating = theorem(p.not_zero_i);
    let multiplicative = theorem(p.of_real_mul);
    let imaginary_pinned = theorem(p.i_sq);
    let order_refuted = theorem(p.no_compatible_order);

    // (7): the absence of an order is CHECKED, not assumed from the fact that
    // this file does not mention one.
    let mut order_declared: Vec<String> = Vec::new();
    for forbidden in ["le", "lt"] {
        let name = kernel.name_str(p.complex, forbidden);
        if kernel.environment().get(name).is_some() {
            order_declared.push(format!("Complex.{forbidden}"));
        }
    }

    if !inhabited {
        eprintln!(
            "FAIL: Complex.ofReal is not a checked definition, so nothing exhibits an \
             inhabitant of the carrier. Every law above would hold — with empty \
             footprints — of the EMPTY type."
        );
        failed = true;
    }
    if !discriminating {
        eprintln!(
            "FAIL: Complex.Equiv.not_zero_one is not a checked theorem, so nothing says \
             Complex.Equiv separates any two complex numbers. The total relation is an \
             equivalence relation too."
        );
        failed = true;
    }
    if !imaginary_discriminating {
        eprintln!(
            "FAIL: Complex.Equiv.not_zero_I is not a checked theorem, so nothing says \
             Complex.Equiv looks at the IMAGINARY component at all. not_zero_one holds \
             of a relation that compares only real parts — under which ℂ is ℝ."
        );
        failed = true;
    }
    if !multiplicative {
        eprintln!(
            "FAIL: Complex.ofReal_mul is not a checked theorem, so nothing pins \
             Complex.mul to CReal.mul ANYWHERE. mul_comm, mul_zero and left_distrib all \
             hold — with empty footprints — of the product that returns zero on every \
             input."
        );
        failed = true;
    }
    if !imaginary_pinned {
        eprintln!(
            "FAIL: Complex.I_sq is not a checked theorem, so Complex.I is unconstrained: \
             ofReal_mul says nothing about it, because I is not in the image of ofReal. \
             I = 0 satisfies every other law here."
        );
        failed = true;
    }
    if !order_refuted {
        eprintln!(
            "FAIL: Complex.no_compatible_order is not a checked theorem, so the absence \
             of Complex.le/Complex.lt is an OMISSION and not a result. A development \
             that never got round to an order looks identical from here."
        );
        failed = true;
    }
    if !order_declared.is_empty() {
        eprintln!(
            "FAIL: {} is declared on Complex, and Complex.no_compatible_order refutes \
             any such relation satisfying seven of the AxReal package's order laws. The \
             two cannot both stand.",
            order_declared.join(", ")
        );
        failed = true;
    }
    if !laws_distinct {
        eprintln!(
            "FAIL: ComplexPrelude::ring_laws does not name 9 DISTINCT declarations, so \
             the count is inflated by a repeat."
        );
        failed = true;
    }
    if !laws_proved {
        eprintln!(
            "FAIL: not every entry of ComplexPrelude::ring_laws is a checked, \
             footprint-empty Theorem. The '9 of 9' claim is read from this list and \
             nowhere else."
        );
        failed = true;
    }

    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    if !trusted.is_empty() {
        failed = true;
    }

    let all_laws = laws_distinct && laws_proved;
    eprintln!(
        "ℂ as pairs of constructed reals: {} declarations named, trusted surface = {} \
         ({}); carrier inhabited = {inhabited}, Equiv discriminates on the real part = \
         {discriminating}, on the imaginary part = {imaginary_discriminating}, mul \
         agrees with CReal.mul on ℝ = {multiplicative}, I is pinned by I_sq = \
         {imaginary_pinned}, order refuted = {order_refuted}, order declared = {}; \
         all 9 commutative-ring laws proved = {all_laws}",
        admitted.len(),
        trusted.len(),
        if trusted.is_empty() {
            "empty".to_owned()
        } else {
            trusted.join(",")
        },
        if order_declared.is_empty() {
            "none".to_owned()
        } else {
            order_declared.join(",")
        }
    );
    if failed {
        eprintln!(
            "FAIL: the constructed complexes are NOT free, or not inhabited, or not \
             discriminating, or an order was declared — see above."
        );
        std::process::exit(1);
    }
    eprintln!(
        "9/9 ring laws have an EMPTY axiom footprint. ℂ over the constructed ℝ over \
         the constructed ℚ over the constructed ℤ costs ZERO trusted declarations: no \
         Quot.sound, no funext, no propext, no classical axiom. Complex.Equiv is a \
         DEFINED relation and every law that mentions equality is stated over it. The \
         13 ordered-ring laws are absent because Complex.no_compatible_order REFUTES \
         them: for any le, lt on Complex satisfying le_refl, lt_irrefl, lt_of_le_of_lt, \
         add_le_add, le_congr, sq_nonneg and zero_lt_one, False follows — the witness \
         is I, through Complex.I_sq"
    );
}
