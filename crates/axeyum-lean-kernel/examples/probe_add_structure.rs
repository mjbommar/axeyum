// Single-character bindings are the kernel's own naming for de Bruijn-ish
// positions; this probe mirrors the terms it inspects.
#![allow(clippy::many_single_char_names)]

//! TEMPORARY probe: dump the structural `Declaration::Definition` value of
//! `Nat.add` alongside its rendered text, to separate a printer defect from a
//! kernel defeq divergence.

use axeyum_lean_kernel::{Declaration, ExprNode, Kernel, build_nat_prelude};

fn dump(k: &Kernel, e: axeyum_lean_kernel::ExprId, depth: usize) {
    let pad = "  ".repeat(depth);
    match k.expr_node(e) {
        ExprNode::BVar(i) => println!("{pad}BVar({i})"),
        ExprNode::FVar(i) => println!("{pad}FVar({i})"),
        ExprNode::Sort(_) => println!("{pad}Sort"),
        ExprNode::Const(n, _) => println!("{pad}Const({})", k.display_name(*n)),
        ExprNode::Proj(n, i, s) => {
            println!("{pad}Proj({}, {i})", k.display_name(*n));
            dump(k, *s, depth + 1);
        }
        ExprNode::App(f, a) => {
            println!("{pad}App");
            dump(k, *f, depth + 1);
            dump(k, *a, depth + 1);
        }
        ExprNode::Lam(n, t, b, _) => {
            println!("{pad}Lam({})", k.display_name(*n));
            dump(k, *t, depth + 1);
            dump(k, *b, depth + 1);
        }
        ExprNode::Pi(n, t, b, _) => {
            println!("{pad}Pi({})", k.display_name(*n));
            dump(k, *t, depth + 1);
            dump(k, *b, depth + 1);
        }
        ExprNode::Let(n, t, v, b) => {
            println!("{pad}Let({})", k.display_name(*n));
            dump(k, *t, depth + 1);
            dump(k, *v, depth + 1);
            dump(k, *b, depth + 1);
        }
        ExprNode::Lit(_) => println!("{pad}Lit"),
    }
}

fn main() {
    let target = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "Nat.add".to_owned());
    let mut kernel = Kernel::new();
    let _ = build_nat_prelude(&mut kernel).expect("Nat prelude must build");

    let mut found = None;
    for (&n, d) in kernel.environment().iter() {
        if kernel.display_name(n).to_string() == target {
            found = Some((n, d.clone()));
        }
    }
    let Some((_n, decl)) = found else {
        println!("not found: {target}");
        return;
    };
    match decl {
        Declaration::Definition {
            name, ty, value, ..
        } => {
            println!("== {} ==", kernel.display_name(name));
            println!("-- type (rendered): {}", kernel.render_lean(ty));
            println!("-- value (rendered): {}", kernel.render_lean(value));
            println!("-- value (structural):");
            dump(&kernel, value, 1);
        }
        other => println!("not a definition: {other:?}"),
    }
}
