//! Does prelude `Nat` arithmetic reach the kernel's binary literal fast path?
//!
//! The kernel carries Lean's `reduce_nat` acceleration
//! (`Kernel::reduce_nat_binop`), which evaluates `Nat.add`/`mul`/`div`/`gcd`/…
//! directly on `Lit::Nat` arguments. It fires only when **both** arguments whnf
//! to a literal. The prelude's own numeral constructor `NatOps::num` builds
//! `succ^n Nat.zero`, and `Nat.zero` is a constructor with no definition, so it
//! never whnfs to `Lit::Nat(0)`.
//!
//! This example measures that rather than asserting it: it builds the same
//! arithmetic term twice — once over unary numerals, once over `Lit::Nat` — and
//! times `Kernel::whnf` on each. Output is tab separated:
//! `shape<TAB>op<TAB>left<TAB>right<TAB>elapsed_micros<TAB>result`.
//!
//! `result` is `lit:<n>` when the term reduced to a literal, `succ-tower:<n>`
//! when it reduced to a unary numeral, and `stuck` otherwise — so a run that
//! reduced nothing cannot be mistaken for a fast one.

use std::time::Instant;

use axeyum_lean_kernel::{
    ExprId, ExprNode, Kernel, Lit, NameId, NatLit, NatPrelude, build_nat_prelude,
};

/// `succ^n Nat.zero`, exactly what `NatOps::num` builds today.
fn unary(kernel: &mut Kernel, prelude: &NatPrelude, n: u64) -> ExprId {
    let mut e = kernel.const_(prelude.zero, vec![]);
    for _ in 0..n {
        let s = kernel.const_(prelude.succ, vec![]);
        e = kernel.app(s, e);
    }
    e
}

/// The binary literal `n`.
fn literal(kernel: &mut Kernel, n: u64) -> ExprId {
    kernel.lit(Lit::Nat(NatLit::from(n)))
}

/// Peel one `Nat.succ` layer, reporting `Zero` at the bottom.
enum Layer {
    Succ(ExprId),
    Zero,
    Other,
}

fn peel(kernel: &Kernel, e: ExprId, succ: NameId, zero: NameId) -> Layer {
    match kernel.expr_node(e) {
        ExprNode::App(f, arg) => {
            let arg = *arg;
            match kernel.expr_node(*f) {
                ExprNode::Const(name, _) if *name == succ => Layer::Succ(arg),
                _ => Layer::Other,
            }
        }
        ExprNode::Const(name, _) if *name == zero => Layer::Zero,
        _ => Layer::Other,
    }
}

/// Classify a reduced head so a stuck term cannot look like a fast one.
///
/// Only the *head* is whnf'd, so the tower below it may still be unreduced;
/// the depth reported is therefore a lower bound and is printed as such.
fn classify(kernel: &mut Kernel, prelude: &NatPrelude, e: ExprId) -> String {
    if let ExprNode::Lit(Lit::Nat(value)) = kernel.expr_node(e) {
        return format!("lit:{value}");
    }
    let mut depth = 0u64;
    let mut cursor = e;
    loop {
        match peel(kernel, cursor, prelude.succ, prelude.zero) {
            Layer::Succ(inner) => {
                depth += 1;
                cursor = kernel.whnf(inner);
            }
            Layer::Zero => return format!("succ-tower:{depth}"),
            Layer::Other => {
                if let ExprNode::Lit(Lit::Nat(value)) = kernel.expr_node(cursor) {
                    return format!("succ-tower:{depth}+lit:{value}");
                }
                return format!("stuck(depth={depth})");
            }
        }
    }
}

fn main() {
    println!("shape\top\tleft\tright\telapsed_micros\tresult");

    // Sizes chosen to stay tolerable for the unary side. `Rat.normalize` on the
    // measured pi bound formed naturals up to 13,125; the `gcd`/`div` cases are
    // exactly the workload under suspicion.
    let cases: &[(&str, u64, u64)] = &[
        ("mul", 25, 21),
        ("mul", 75, 75),
        ("mul", 125, 105),
        ("gcd", 512, 1875),
        ("div", 13125, 25),
        ("mod", 13125, 25),
    ];

    for &(op, lhs_value, rhs_value) in cases {
        for shape in ["unary", "literal"] {
            let mut kernel = Kernel::new();
            let prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
            let (lhs, rhs) = if shape == "unary" {
                (
                    unary(&mut kernel, &prelude, lhs_value),
                    unary(&mut kernel, &prelude, rhs_value),
                )
            } else {
                (
                    literal(&mut kernel, lhs_value),
                    literal(&mut kernel, rhs_value),
                )
            };
            let operation = match op {
                "mul" => prelude.mul,
                "gcd" => prelude.gcd,
                "div" => prelude.div,
                _ => prelude.mod_,
            };
            let head = kernel.const_(operation, vec![]);
            let applied0 = kernel.app(head, lhs);
            let applied = kernel.app(applied0, rhs);

            let start = Instant::now();
            let reduced = kernel.whnf(applied);
            let micros = start.elapsed().as_micros();
            let result = classify(&mut kernel, &prelude, reduced);
            println!("{shape}\t{op}\t{lhs_value}\t{rhs_value}\t{micros}\t{result}");
        }
    }
}
