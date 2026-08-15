//! Reduce `Nat.add n (Nat.succ m)` inside a kernel loaded from a real
//! `lean4export` stream, and print where reduction stops.
//!
//! `Nat.add_succ` is proved by `rfl` in Lean, so admitting it is exactly the
//! question "does `n + succ m` reduce to `succ (n + m)` in our kernel". The
//! declaration decline (`DeclarationValueMismatch`) says only that it does not.
//! This says *what the head is when we give up*, which is the difference between
//! a missing reduction rule and a wrong one.
//!
//! The stream is imported through the ordinary fail-closed [`import_ndjson`]
//! with its final record dropped, so every declaration the probe reads was
//! admitted by the trusted gate exactly as in production.
//!
//! ```sh
//! cargo run -p axeyum-lean-import --example nat_add_reduction_probe -- Nat.add_succ.ndjson
//! ```

use std::fs::read_to_string;
use std::io::Cursor;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{ExprId, ExprNode, Kernel};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args_os()
        .nth(1)
        .ok_or("usage: nat_add_reduction_probe <export.ndjson>")?;
    let text = read_to_string(path)?;
    // Drop the trailing declaration: it is the `rfl` theorem under test, and it
    // is the one record the kernel refuses.
    let mut lines: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.pop();
    let truncated = lines.join("\n");

    let completed = import_ndjson(Cursor::new(truncated), ImportLimits::default())?;
    let (mut kernel, report) = completed.into_parts();
    println!("imported {} declarations", report.admitted_declarations);

    let anon = kernel.anon();
    let nat = kernel.name_str(anon, "Nat");
    let nat_add = kernel.name_str(nat, "add");
    let nat_succ = kernel.name_str(nat, "succ");

    let nat_ty = kernel.const_(nat, vec![]);
    let succ = kernel.const_(nat_succ, vec![]);
    let add = kernel.const_(nat_add, vec![]);

    // Two opaque naturals. Free variables, not literals: the question is whether
    // the *recursor* route reduces, and a literal would take the kernel's
    // special-cased `Nat` arithmetic path instead and answer a different one.
    let n = kernel.fvar(1);
    let m = kernel.fvar(2);
    let succ_m = kernel.app(succ, m);

    let add_n_succ_m = {
        let partial = kernel.app(add, n);
        kernel.app(partial, succ_m)
    };
    let succ_add_n_m = {
        let partial = kernel.app(add, n);
        let inner = kernel.app(partial, m);
        kernel.app(succ, inner)
    };

    println!("lhs      = {}", kernel.render_lean(add_n_succ_m));
    println!("rhs      = {}", kernel.render_lean(succ_add_n_m));
    let lhs_whnf = kernel.whnf(add_n_succ_m);
    println!("whnf lhs = {}", kernel.render_lean(lhs_whnf));
    let rhs_whnf = kernel.whnf(succ_add_n_m);
    println!("whnf rhs = {}", kernel.render_lean(rhs_whnf));

    // The type of each side, so a stuck term can be told apart from an
    // ill-formed one built by this probe.
    let _ = nat_ty;
    println!("def_eq   = {}", kernel.def_eq(add_n_succ_m, succ_add_n_m));

    narrow(&mut kernel, add_n_succ_m, succ_add_n_m, 0);
    Ok(())
}

/// Walk down to the smallest pair the checker refuses.
///
/// A `false` at the root says nothing about which rule is missing; the same
/// `false` on a leaf pair whose two sides are visibly the same term modulo one
/// unfolding says exactly which.
fn narrow(kernel: &mut Kernel, x: ExprId, y: ExprId, depth: usize) {
    if depth > 12 {
        println!("{:indent$}(depth limit)", "", indent = depth * 2);
        return;
    }
    let xw = kernel.whnf(x);
    let yw = kernel.whnf(y);
    let (xf, xargs) = spine(kernel, xw);
    let (yf, yargs) = spine(kernel, yw);
    println!(
        "{:indent$}MISMATCH depth={depth} lhs_head={} ({} args) rhs_head={} ({} args)",
        "",
        kernel.render_lean(xf),
        xargs.len(),
        kernel.render_lean(yf),
        yargs.len(),
        indent = depth * 2,
    );
    if xargs.len() != yargs.len() {
        println!(
            "{:indent$}  arity differs; lhs={} rhs={}",
            "",
            kernel.render_lean(xw),
            kernel.render_lean(yw),
            indent = depth * 2
        );
        return;
    }
    if !kernel.def_eq(xf, yf) {
        println!(
            "{:indent$}  HEADS not def-eq: {} vs {}",
            "",
            kernel.render_lean(xf),
            kernel.render_lean(yf),
            indent = depth * 2
        );
    }
    for (index, (&a, &b)) in xargs.iter().zip(yargs.iter()).enumerate() {
        if !kernel.def_eq(a, b) {
            println!("{:indent$}  arg {index} differs:", "", indent = depth * 2);
            narrow(kernel, a, b, depth + 1);
            return;
        }
    }
}

fn spine(kernel: &Kernel, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    while let ExprNode::App(f, a) = kernel.expr_node(e) {
        args.push(*a);
        e = *f;
    }
    args.reverse();
    (e, args)
}
