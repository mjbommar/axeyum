//! Probe: which kernel constants do the `ring`/`linarith` producers actually
//! reference in the terms they emit, and what is each one's type?
//!
//! This is the measurement instrument behind the name-correspondence table in
//! ADR-1666 and behind `lean/axeyum-tactic/Axeyum/Shim.lean`: the shim has to
//! declare one Lean theorem per name in this list, with **exactly** the
//! argument order printed here, because the emitted term applies every
//! constant fully explicitly.
//!
//! It is a printer, not a gate. The gate is `scripts/check-lean-tactic.sh`,
//! where real Lean either accepts the emitted term or does not.

use std::collections::BTreeSet;

use axeyum_lean_kernel::{
    ExprId, ExprNode, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude, linarith,
    on_a_deep_stack, ring,
};

struct Fixture {
    k: Kernel,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }
    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

/// Every `Const` name reachable from `expr`, as the kernel spells it.
fn constants(kernel: &Kernel, expr: ExprId, out: &mut BTreeSet<NameId>) {
    let mut stack = vec![expr];
    let mut seen: BTreeSet<ExprId> = BTreeSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        match kernel.expr_node(id) {
            ExprNode::Const(name, _) => {
                out.insert(*name);
            }
            ExprNode::App(f, a) => {
                stack.push(*f);
                stack.push(*a);
            }
            ExprNode::Lam(_, t, b, _) | ExprNode::Pi(_, t, b, _) => {
                stack.push(*t);
                stack.push(*b);
            }
            ExprNode::Let(_, t, v, b) => {
                stack.push(*t);
                stack.push(*v);
                stack.push(*b);
            }
            ExprNode::Proj(_, _, e) => stack.push(*e),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
}

fn main() {
    on_a_deep_stack(|| {
        let mut k = Kernel::new();
        let p: NatPrelude = build_nat_prelude(&mut k).expect("nat prelude");
        let st = NatState::new(&mut k, p);
        let mut f = Fixture { k, st };

        let mut names: BTreeSet<NameId> = BTreeSet::new();

        let a_fv = f.fresh_fvar();
        let b_fv = f.fresh_fvar();
        let c_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let b = f.k.fvar(b_fv);
        let c = f.k.fvar(c_fv);

        // ring battery.
        let ring_goals: Vec<(&str, ExprId)> = {
            let mut v = Vec::new();
            let l = f.add(a, b);
            let r = f.add(b, a);
            v.push(("add_comm", f.eq(l, r)));
            let l = f.mul(a, b);
            let r = f.mul(b, a);
            v.push(("mul_comm", f.eq(l, r)));
            let ab = f.add(a, b);
            let l = f.add(ab, c);
            let bc = f.add(b, c);
            let r = f.add(a, bc);
            v.push(("add_assoc", f.eq(l, r)));
            let bc = f.add(b, c);
            let l = f.mul(a, bc);
            let ab = f.mul(a, b);
            let ac = f.mul(a, c);
            let r = f.add(ab, ac);
            v.push(("left_distrib", f.eq(l, r)));
            let two = f.num(2);
            let l = f.mul(a, two);
            let r = f.add(a, a);
            v.push(("mul_two", f.eq(l, r)));
            v
        };
        for (tag, goal) in ring_goals {
            match ring::nat::prove(&mut f, &p, goal) {
                Ok(term) => {
                    constants(&f.k, term, &mut names);
                    println!("ring {tag}: OK");
                }
                Err(d) => println!("ring {tag}: DECLINED {d:?}"),
            }
        }

        // linarith battery.
        let linarith_goals: Vec<(&str, ExprId)> = {
            let mut v = Vec::new();
            let s = f.add(a, b);
            v.push(("le_add_right", f.le(a, s)));
            let s = f.add(b, a);
            v.push(("le_add_left", f.le(a, s)));
            let z = f.zero();
            v.push(("zero_le", f.le(z, a)));
            v.push(("le_refl", f.le(a, a)));
            let sa = f.succ(a);
            v.push(("lt_succ", f.lt(a, sa)));
            v
        };
        for (tag, goal) in linarith_goals {
            match linarith::nat::prove(&mut f, &p, &[], goal) {
                Ok(term) => {
                    constants(&f.k, term, &mut names);
                    println!("linarith {tag}: OK");
                }
                Err(d) => println!("linarith {tag}: DECLINED {d:?}"),
            }
        }

        // linarith with a hypothesis (transitivity).
        {
            let hyp_ty = f.le(a, b);
            let h_fv = f.fresh_fvar();
            let h = f.k.fvar(h_fv);
            let sum = f.add(b, c);
            let goal = f.le(a, sum);
            match linarith::nat::prove(&mut f, &p, &[(hyp_ty, h)], goal) {
                Ok(term) => {
                    constants(&f.k, term, &mut names);
                    println!("linarith hyp_trans: OK");
                }
                Err(d) => println!("linarith hyp_trans: DECLINED {d:?}"),
            }
        }

        println!("\n=== constants referenced ({}) ===", names.len());
        let mut rows: Vec<(String, String)> = Vec::new();
        for &name in &names {
            let spelled = f.k.lean_name(name);
            let ty = f.k.environment().get(name).map_or_else(
                || "<not an environment declaration>".to_owned(),
                |d| f.k.render_lean(d.ty()),
            );
            rows.push((spelled, ty));
        }
        rows.sort();
        for (spelled, ty) in rows {
            println!("{spelled}\n    : {ty}");
        }
    });
}
