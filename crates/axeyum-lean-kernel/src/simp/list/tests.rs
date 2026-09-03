//! Tests for the `List` `simp` producer.
//!
//! Four batteries, mirroring `simp::nat`/`simp::int`'s own structure (see
//! their module docs):
//!
//! 1. **Eight goals, concrete and symbolic, proved and kernel-checked** —
//!    one covering each named default rule (`append_nil`, `nil_append`,
//!    `append_assoc`, `reverse_reverse`, `length_map`, `map_nil`+`map_cons`,
//!    `length_append`, `count_append`).
//! 2. **Three goals needing a lemma outside the default set decline
//!    `NoProgress`** — `List` has no commutativity/`reverse`-`length`/
//!    `reverse`-`count` law in the default set (each needs induction, which
//!    this producer does not attempt), so each gets a plain "did not move"
//!    refusal on both sides.
//! 3. **Two corrupted claims are rejected by the KERNEL**, with the
//!    procedure's own "did both sides converge to the same term" check
//!    switched off (`prove_eq_unverified`) — one at the `List` carrier, one
//!    at the `Nat` carrier a boundary rule (`length_map`) crosses into.
//! 4. **A looping extra rule set declines `BudgetExceeded`, not a hang** —
//!    `append_assoc`'s forward direction (already in the default set)
//!    together with its own backward copy oscillates forever, exactly the
//!    `add_comm_alone`/`mul_comm`-style control `simp::nat`/`simp::int`
//!    already carry (see the crate-root module docs' termination note and
//!    this module's own docs on why `append_assoc` alone is safe).

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use super::{
    Decline, ListDev, Rule, default_rules_with_perm, prove, prove_eq, prove_eq_unverified,
    rule_append_assoc_backward,
};
use crate::expr::ExprId;
use crate::{
    BinderInfo, Kernel, KernelError, ListNatBridge, ListPerm, ListPrelude, NameId, NatPrelude,
    build_list_nat_bridge, build_list_perm, on_a_deep_stack,
};

struct Fixture {
    k: Kernel,
    list: ListPrelude,
    nat: NatPrelude,
    bridge: ListNatBridge,
    perm: ListPerm,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let (list, nat, bridge) =
            build_list_nat_bridge(&mut k).expect("List/Nat bridge must build");
        let perm = build_list_perm(&mut k, &list, &nat, &bridge).expect("List.Perm must build");
        Self {
            k,
            list,
            nat,
            bridge,
            perm,
        }
    }

    fn dev(&mut self, alpha: ExprId) -> ListDev<'_> {
        let names = super::names_of(&self.list);
        ListDev::new_full(
            &mut self.k,
            &self.nat.logic,
            &names,
            &self.nat,
            &self.bridge,
            alpha,
        )
    }

    /// The full default rule set (`+ perm`) — read from `self` BEFORE
    /// `dev()` borrows it mutably, since `ListDev` no longer carries the
    /// four theorem `NameId`s (`list_prelude::theorems` builds a `ListDev`
    /// before those exist at all — see `names_of`'s doc).
    fn rules(&self) -> Vec<Rule> {
        default_rules_with_perm(
            self.list.append_nil,
            self.list.append_assoc,
            self.list.reverse_reverse,
            self.list.length_map,
            self.bridge.length_append,
            self.perm.count_append,
        )
    }

    fn nat_ty(&mut self) -> ExprId {
        self.k.const_(self.nat.nat, vec![])
    }

    fn list_nat_ty(&mut self) -> ExprId {
        let zero_lvl = self.k.level_zero();
        let nat = self.nat_ty();
        let c = self.k.const_(self.list.list, vec![zero_lvl]);
        self.k.app(c, nat)
    }
}

fn num(d: &mut ListDev<'_>, n: u32) -> ExprId {
    let mut e = d.nat_zero();
    for _ in 0..n {
        e = d.nat_succ(e);
    }
    e
}

fn arrow(d: &mut ListDev<'_>, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = d.kernel().anon();
    d.kernel().pi(anon, dom, cod, BinderInfo::Default)
}

/// Universally quantify `concl`/`proof` over `vars` (in the order given —
/// the FIRST entry becomes the OUTERMOST binder) and declare `name`.
fn quantify_and_declare(
    d: &mut ListDev<'_>,
    name: NameId,
    vars: &[(u64, ExprId)],
    concl: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = concl;
    let mut value = proof;
    for &(fv, vty) in vars.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }
    d.declare_theorem(name, ty, value)
}

/// Prove `Eq goal_ty lhs rhs` (with `lhs`/`rhs` built from `vars`) via
/// `rules`, quantify over `vars`, and require the kernel to admit it — the
/// same "declared AND `Kernel::infer` independently agrees" double-check
/// `simp::nat`/`simp::int`'s own `retire` uses.
fn prove_and_declare(
    label: &str,
    d: &mut ListDev<'_>,
    rules: &[Rule],
    vars: &[(u64, ExprId)],
    goal_ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) {
    let proof = prove_eq(d, rules, goal_ty, lhs, rhs)
        .unwrap_or_else(|e| panic!("{label}: producer declined: {e:?}"));
    let concl = d.eq(goal_ty, lhs, rhs);
    let name = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, label)
    };
    quantify_and_declare(d, name, vars, concl, proof)
        .unwrap_or_else(|e| panic!("{label}: kernel rejected: {e:?}"));
    assert!(
        d.kernel().environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
    let value = d
        .kernel()
        .environment()
        .get(name)
        .expect("declared")
        .value()
        .expect("a theorem carries a value");
    let inferred = d
        .kernel()
        .infer(value)
        .unwrap_or_else(|e| panic!("{label}: Kernel::infer rejected the emitted proof: {e:?}"));
    let ty = d.kernel().environment().get(name).expect("declared").ty();
    assert!(
        d.kernel().def_eq(inferred, ty),
        "{label}: Kernel::infer's type is not the declared statement",
    );
}

// ---------------------------------------------------------------------------
// 1. eight goals, concrete and symbolic
// ---------------------------------------------------------------------------

#[test]
fn append_nil_and_nil_append_together_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let nil = d.nil();
        let append_l_nil = d.append(l, nil);
        let lhs = d.append(nil, append_l_nil);
        prove_and_declare(
            "append_nil_and_nil_append_symbolic",
            &mut d,
            &rules,
            &[(l_fv, list_ty)],
            list_ty,
            lhs,
            l,
        );
    });
}

#[test]
fn append_nil_concrete() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let one = num(&mut d, 1);
        let two = num(&mut d, 2);
        let nil = d.nil();
        let l = {
            let inner = d.cons(two, nil);
            d.cons(one, inner)
        };
        let lhs = d.append(l, nil);
        prove_and_declare("append_nil_concrete", &mut d, &rules, &[], list_ty, lhs, l);
    });
}

#[test]
fn append_assoc_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let c_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let c = d.kernel().fvar(c_fv);
        let ab = d.append(a, b);
        let lhs = d.append(ab, c);
        let bc = d.append(b, c);
        let rhs = d.append(a, bc);
        prove_and_declare(
            "append_assoc_symbolic",
            &mut d,
            &rules,
            &[(a_fv, list_ty), (b_fv, list_ty), (c_fv, list_ty)],
            list_ty,
            lhs,
            rhs,
        );
    });
}

#[test]
fn reverse_reverse_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let rl = d.reverse(l);
        let lhs = d.reverse(rl);
        prove_and_declare(
            "reverse_reverse_symbolic",
            &mut d,
            &rules,
            &[(l_fv, list_ty)],
            list_ty,
            lhs,
            l,
        );
    });
}

#[test]
fn length_map_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let f_ty = arrow(&mut d, nat, nat);
        let f_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let func = d.kernel().fvar(f_fv);
        let l = d.kernel().fvar(l_fv);
        let mapped = d.map(func, l);
        let lhs = d.length(mapped);
        let rhs = d.length(l);
        prove_and_declare(
            "length_map_symbolic",
            &mut d,
            &rules,
            &[(f_fv, f_ty), (l_fv, list_ty)],
            nat,
            lhs,
            rhs,
        );
    });
}

#[test]
fn map_cons_and_map_nil_concrete_chain() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let succ_name = f.nat.succ; // captured before `d` borrows `f`.
        let mut d = f.dev(nat);
        let one = num(&mut d, 1);
        let two = num(&mut d, 2);
        let nil = d.nil();
        let l = {
            let inner = d.cons(two, nil);
            d.cons(one, inner)
        };
        // func := Nat.succ, a real Nat -> Nat function (not opaque), so the
        // RHS's `f 1`/`f 2` applications compare cleanly.
        let func = d.kernel().const_(succ_name, vec![]);
        let lhs = d.map(func, l);
        let f1 = d.apply(func, &[one]);
        let f2 = d.apply(func, &[two]);
        let rhs = {
            let nil2 = d.nil();
            let inner = d.cons(f2, nil2);
            d.cons(f1, inner)
        };
        prove_and_declare(
            "map_cons_and_map_nil_concrete_chain",
            &mut d,
            &rules,
            &[],
            list_ty,
            lhs,
            rhs,
        );
    });
}

#[test]
fn length_append_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let l1_fv = d.fresh_fvar();
        let l2_fv = d.fresh_fvar();
        let l1 = d.kernel().fvar(l1_fv);
        let l2 = d.kernel().fvar(l2_fv);
        let app = d.append(l1, l2);
        let lhs = d.length(app);
        let len1 = d.length(l1);
        let len2 = d.length(l2);
        let rhs = d.nat_add(len1, len2);
        prove_and_declare(
            "length_append_symbolic",
            &mut d,
            &rules,
            &[(l1_fv, list_ty), (l2_fv, list_ty)],
            nat,
            lhs,
            rhs,
        );
    });
}

#[test]
fn count_append_symbolic() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let a_fv = d.fresh_fvar();
        let l1_fv = d.fresh_fvar();
        let l2_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let l1 = d.kernel().fvar(l1_fv);
        let l2 = d.kernel().fvar(l2_fv);
        let app = d.append(l1, l2);
        let lhs = d.count(a, app);
        let c1 = d.count(a, l1);
        let c2 = d.count(a, l2);
        let rhs = d.nat_add(c1, c2);
        prove_and_declare(
            "count_append_symbolic",
            &mut d,
            &rules,
            &[(a_fv, nat), (l1_fv, list_ty), (l2_fv, list_ty)],
            nat,
            lhs,
            rhs,
        );
    });
}

// ---------------------------------------------------------------------------
// 2. three `NoProgress` goals
// ---------------------------------------------------------------------------

#[test]
fn append_comm_shaped_goal_declines_no_progress() {
    let mut f = Fixture::new();
    let rules = f.rules();
    let nat = f.nat_ty();
    let list_ty = f.list_nat_ty();
    let mut d = f.dev(nat);
    let l1_fv = d.fresh_fvar();
    let l2_fv = d.fresh_fvar();
    let l1 = d.kernel().fvar(l1_fv);
    let l2 = d.kernel().fvar(l2_fv);
    let lhs = d.append(l1, l2);
    let rhs = d.append(l2, l1);
    let result = prove_eq(&mut d, &rules, list_ty, lhs, rhs);
    assert_eq!(result, Err(Decline::NoProgress), "got {result:?}");
}

#[test]
fn length_reverse_shaped_goal_declines_no_progress() {
    let mut f = Fixture::new();
    let rules = f.rules();
    let nat = f.nat_ty();
    let mut d = f.dev(nat);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let rl = d.reverse(l);
    let lhs = d.length(rl);
    let rhs = d.length(l);
    let result = prove_eq(&mut d, &rules, nat, lhs, rhs);
    assert_eq!(result, Err(Decline::NoProgress), "got {result:?}");
}

#[test]
fn count_reverse_shaped_goal_declines_no_progress() {
    let mut f = Fixture::new();
    let rules = f.rules();
    let nat = f.nat_ty();
    let mut d = f.dev(nat);
    let a_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let l = d.kernel().fvar(l_fv);
    let rl = d.reverse(l);
    let lhs = d.count(a, rl);
    let rhs = d.count(a, l);
    let result = prove_eq(&mut d, &rules, nat, lhs, rhs);
    assert_eq!(result, Err(Decline::NoProgress), "got {result:?}");
}

// ---------------------------------------------------------------------------
// 3. two corrupted chains, rejected by the KERNEL
// ---------------------------------------------------------------------------

#[test]
fn a_corrupted_list_carrier_chain_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let l_fv = d.fresh_fvar();
        let l2_fv = d.fresh_fvar(); // unrelated, NOT equal to `l`.
        let l = d.kernel().fvar(l_fv);
        let l2 = d.kernel().fvar(l2_fv);
        let nil = d.nil();
        let lhs = d.append(l, nil);

        // `append l nil` rewrites (1 step, `append_nil`) to `l`; claiming
        // it equals the UNRELATED `l2` is false.
        let term = prove_eq_unverified(&mut d, &rules, list_ty, lhs, l2)
            .unwrap_or_else(|e| panic!("procedure declined instead of emitting: {e:?}"));
        let concl = d.eq(list_ty, lhs, l2);
        let name = {
            let anon = d.kernel().anon();
            d.kernel().name_str(anon, "corrupted_list")
        };
        let result = quantify_and_declare(
            &mut d,
            name,
            &[(l_fv, list_ty), (l2_fv, list_ty)],
            concl,
            term,
        );
        assert!(
            result.is_err(),
            "a corrupted List-carrier chain must be rejected, not admitted"
        );
    });
}

#[test]
fn a_corrupted_nat_carrier_chain_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let rules = f.rules();
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let f_ty = arrow(&mut d, nat, nat);
        let f_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar(); // unrelated Nat free variable.
        let func = d.kernel().fvar(f_fv);
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);

        let mapped = d.map(func, l);
        let lhs = d.length(mapped);
        // `length (map f l)` rewrites (1 step, `length_map`) to `length l`;
        // claiming it equals the UNRELATED `m` is false.
        let term = prove_eq_unverified(&mut d, &rules, nat, lhs, m)
            .unwrap_or_else(|e| panic!("procedure declined instead of emitting: {e:?}"));
        let concl = d.eq(nat, lhs, m);
        let name = {
            let anon = d.kernel().anon();
            d.kernel().name_str(anon, "corrupted_nat")
        };
        let result = quantify_and_declare(
            &mut d,
            name,
            &[(f_fv, f_ty), (l_fv, list_ty), (m_fv, nat)],
            concl,
            term,
        );
        assert!(
            result.is_err(),
            "a corrupted Nat-carrier chain must be rejected, not admitted"
        );
    });
}

// ---------------------------------------------------------------------------
// 4. a looping extra rule set declines `BudgetExceeded`, not a hang
// ---------------------------------------------------------------------------

#[test]
fn a_looping_extra_rule_set_declines_budget_exceeded_not_a_hang() {
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let mut rules = f.rules();
        let append_assoc_name = f.list.append_assoc;
        rules.push(rule_append_assoc_backward(append_assoc_name));
        let nat = f.nat_ty();
        let list_ty = f.list_nat_ty();
        let mut d = f.dev(nat);
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let z_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let z = d.kernel().fvar(z_fv);

        let yz = d.append(y, z);
        let lhs = d.append(x, yz); // append x (append y z) -- oscillates
        // under forward+backward `append_assoc` together.
        let rhs = lhs;
        let result = prove_eq(&mut d, &rules, list_ty, lhs, rhs);
        assert_eq!(
            result,
            Err(Decline::BudgetExceeded),
            "a forward+backward append_assoc rule set must decline BudgetExceeded, not hang or wrongly succeed; got {result:?}"
        );
    });
}

#[test]
fn prove_parses_a_literal_eq_goal_and_matches_prove_eq() {
    let mut f = Fixture::new();
    let rules = f.rules();
    let nat = f.nat_ty();
    let list_ty = f.list_nat_ty();
    let mut d = f.dev(nat);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let nil = d.nil();
    let lhs = d.append(l, nil);
    let goal = d.eq(list_ty, lhs, l);
    let via_prove = prove(&mut d, &rules, list_ty, goal);
    assert!(
        via_prove.is_ok(),
        "prove() must parse the literal `Eq` goal and close it: {via_prove:?}"
    );
}
