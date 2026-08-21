//! Regression: a lambda's binder domain must be a TYPE, even when the checker
//! took the bidirectional fast path.
//!
//! Found 2026-08-17 by the adversarial kernel-vs-kernel differential
//! (`axeyum-lean-import/tests/real_lean_wire_differential.rs`), which feeds the
//! same `lean4export` bytes to this kernel and to official Lean 4.30.0's
//! `addDeclCore`. One mutant of `Acc.inv`'s proof term was admitted here and
//! refused there — the only disagreement in 92 mutants, and in the direction
//! that matters: **we were more permissive than Lean.**
//!
//! Mechanism. `Kernel::check_core` has a bidirectional fast path: checking a
//! `Lam` against an expected `Pi` compared the two domains with `def_eq_core`
//! and recursed into the body, never going through `infer_lambda` — which is
//! where the domain's `infer_sort_of` lives. `def_eq_core` reduces, so a domain
//! that is ill typed but BETA-REDUCES to the expected one was erased before
//! anything checked it. In `Acc.inv` the domain sat inside a beta-redex, so any
//! of ten different expressions could be dropped into that argument position
//! and all ten were accepted.
//!
//! Lean's kernel cannot have this bug: it has no bidirectional path at all — it
//! infers a type and then `isDefEq`s, and `inferLambda` calls `ensureSortCore`
//! on the domain.
//!
//! This file is the minimal case, with the control that keeps it honest: the
//! well-typed twin must still be ACCEPTED, or the guard could be satisfied by a
//! checker that rejects everything.

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, build_logic_prelude};

/// `theorem t : True := h (fun (_ : domain) => trivial)` where
/// `h : (True -> True) -> True`, and `domain` is either the well-typed `True`
/// or the ill-typed `(fun (x : Sort 1) => True) trivial`, which beta-reduces to
/// it (`trivial : True`, but the binder wants `Sort 1`).
fn admit_with_domain(domain_is_ill_typed: bool) -> Result<(), axeyum_lean_kernel::KernelError> {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let anonymous = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let true_ = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);

    let domain = if domain_is_ill_typed {
        let sort_one = kernel.sort(one);
        let identity = kernel.lam(anonymous, sort_one, true_, BinderInfo::Default);
        kernel.app(identity, trivial)
    } else {
        true_
    };

    let arrow = kernel.pi(anonymous, true_, true_, BinderInfo::Default);
    let h = kernel.lam(anonymous, arrow, trivial, BinderInfo::Default);
    let argument = kernel.lam(anonymous, domain, trivial, BinderInfo::Default);
    let value = kernel.app(h, argument);
    let name = kernel.name_str(anonymous, "regression_lambda_domain");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: Vec::new(),
        ty: true_,
        value,
    })
}

#[test]
fn an_ill_typed_binder_domain_is_refused_even_when_it_beta_reduces_away() {
    let result = admit_with_domain(true);
    assert!(
        result.is_err(),
        "the kernel admitted a lambda whose binder domain is ill typed. It \
         beta-reduces to the expected domain, so `def_eq` cannot see it; only a \
         sort check on the domain itself can. Lean 4.30.0's kernel refuses this."
    );
}

#[test]
fn the_well_typed_twin_is_still_admitted() {
    assert_eq!(
        admit_with_domain(false),
        Ok(()),
        "the guard above must discriminate; a checker that refused this too \
         would satisfy it for the wrong reason"
    );
}
