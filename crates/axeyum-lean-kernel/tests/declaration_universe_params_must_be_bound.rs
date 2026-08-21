//! Regression: a declaration may only mention universe parameters it BINDS.
//!
//! Found 2026-08-18 by the adversarial kernel-vs-kernel differential
//! (`axeyum-lean-import/tests/real_lean_wire_differential.rs`), which feeds the
//! same `lean4export` bytes to this kernel and to official Lean 4.30.0's
//! `addDeclCore`. Five of eight violations in that run were this one defect
//! reached three different ways — rename the entry in a declaration's
//! `levelParams` (`decl.universe-param`), rename a `Level.param` record
//! (`level.param`), or point a `Level.succ` at a parameter level
//! (`level.succ`). Each leaves a declaration whose type or value mentions a
//! universe parameter its `levelParams` does not bind. Lean's kernel refused
//! every one with
//!
//!     (kernel) invalid reference to undefined universe level parameter 'u'
//!
//! and this kernel admitted every one.
//!
//! Mechanism. `Kernel::check_declaration` ran exactly two checks: the declared
//! type infers to a `Sort`, and the value's inferred type is def-eq to it.
//! Both are *relative* checks — they hold just as well with a free `u` on both
//! sides, because inference treats an unbound `Param` exactly like a bound one.
//! Nothing anywhere compared the parameters occurring in the term against the
//! parameters the declaration declares, so the binding list was decorative.
//!
//! Why it matters beyond fidelity. `Const(c, us)` substitutes `us` positionally
//! for `c`'s DECLARED parameters. A parameter the declaration does not declare
//! is therefore never substituted at any instantiation site: it survives into
//! every use as a universe nobody chose and nobody can choose, and two
//! unrelated declarations that both leak the name `u` are then forced to talk
//! about the same universe. That is not a state a universe-polymorphic
//! calculus has any rules for, which is why Lean's kernel refuses to enter it
//! rather than reasoning about what it would mean.
//!
//! This file is the minimal case, with the control that keeps it honest: the
//! well-formed twin — the identical declaration that *binds* `u` — must still
//! be ACCEPTED, or the guard could be satisfied by a checker that rejects
//! every universe-polymorphic declaration.

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, KernelError};

/// `axiom stray : Sort u -> Sort u`, declared either with `u` bound (`.{u}`) or
/// with an empty parameter list, which leaves `u` free.
fn admit_axiom(bind_the_parameter: bool) -> Result<(), KernelError> {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let u = kernel.name_str(anonymous, "u");
    let level = kernel.level_param(u);
    let sort = kernel.sort(level);
    let ty = kernel.pi(anonymous, sort, sort, BinderInfo::Default);
    let name = kernel.name_str(anonymous, "stray_universe_axiom");
    kernel.add_declaration(Declaration::Axiom {
        name,
        uparams: if bind_the_parameter {
            vec![u]
        } else {
            Vec::new()
        },
        ty,
    })
}

/// The same escape through a *value* rather than a type: the declared type is
/// closed (`True`), so nothing about it is universe-polymorphic, and the free
/// parameter rides in on the proof term instead.
///
/// This is the shape the differential actually produced. A checker that only
/// looked at the type would pass it.
fn admit_definition_whose_value_leaks(bind_the_parameter: bool) -> Result<(), KernelError> {
    let mut kernel = Kernel::new();
    let logic =
        axeyum_lean_kernel::build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let anonymous = kernel.anon();
    let u = kernel.name_str(anonymous, "u");
    let level = kernel.level_param(u);
    let sort = kernel.sort(level);
    let true_ = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);
    // `let _ : Sort u -> True := fun (_ : Sort u) => True.intro; True.intro`
    //
    // The let's body is what gives the whole term its type, so the declared
    // type stays the closed `True` and `u` occurs ONLY in the value. That is
    // the half a type-directed check cannot see.
    let discard = kernel.lam(anonymous, sort, trivial, BinderInfo::Default);
    let discard_ty = kernel.pi(anonymous, sort, true_, BinderInfo::Default);
    let value = kernel.let_(anonymous, discard_ty, discard, trivial);
    let name = kernel.name_str(anonymous, "stray_universe_definition");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: if bind_the_parameter {
            vec![u]
        } else {
            Vec::new()
        },
        ty: true_,
        value,
    })
}

#[test]
fn an_unbound_universe_parameter_in_the_type_is_refused() {
    let error = admit_axiom(false).expect_err(
        "a declaration whose type mentions a universe parameter it does not \
         bind must be refused; Lean's kernel calls this an `invalid reference \
         to undefined universe level parameter`",
    );
    assert!(
        matches!(error, KernelError::UndeclaredUniverseParam { .. }),
        "refused for the wrong reason: {error:?}"
    );
}

#[test]
fn an_unbound_universe_parameter_in_the_value_is_refused() {
    let error = admit_definition_whose_value_leaks(false)
        .expect_err("a value may not mention a universe parameter the declaration does not bind");
    assert!(
        matches!(error, KernelError::UndeclaredUniverseParam { .. }),
        "refused for the wrong reason: {error:?}"
    );
}

// The controls. Without these the guard above is satisfied by a kernel that
// refuses every universe-polymorphic declaration, which would be a far worse
// regression than the one being fixed and would not fail a single test.
#[test]
fn binding_the_parameter_is_still_accepted() {
    admit_axiom(true).expect("`axiom stray.{u} : Sort u -> Sort u` is well formed");
}

#[test]
fn binding_the_parameter_in_a_value_is_still_accepted() {
    admit_definition_whose_value_leaks(true)
        .expect("a universe-polymorphic proof term that BINDS its parameter is well formed");
}

/// The inductive gate is a SEPARATE admission path: it type-checks the group
/// itself and never routes through `Kernel::check_declaration`. The first fix
/// therefore left it uncovered, and the differential said so — one violation
/// survived, inside `Nat`'s group.
///
/// `inductive Wrap : Prop | mk : Sort u -> Wrap`, with `u` bound or free.
fn admit_inductive(bind_the_parameter: bool) -> Result<(), KernelError> {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let u = kernel.name_str(anonymous, "u");
    let level = kernel.level_param(u);
    let sort = kernel.sort(level);
    let prop = kernel.sort_zero();
    let wrap = kernel.name_str(anonymous, "Wrap");
    let wrap_const = kernel.const_(
        wrap,
        if bind_the_parameter {
            vec![level]
        } else {
            Vec::new()
        },
    );
    let mk = kernel.name_str(wrap, "mk");
    let mk_ty = kernel.pi(anonymous, sort, wrap_const, BinderInfo::Default);
    let uparams: Vec<_> = if bind_the_parameter {
        vec![u]
    } else {
        Vec::new()
    };
    kernel.add_inductive(wrap, &uparams, 0, prop, &[(mk, mk_ty)])
}

#[test]
fn an_unbound_universe_parameter_in_a_constructor_is_refused() {
    let error = admit_inductive(false).expect_err(
        "the inductive gate must refuse a constructor type that mentions a \
         universe parameter the group does not bind",
    );
    assert!(
        matches!(error, KernelError::UndeclaredUniverseParam { .. }),
        "refused for the wrong reason: {error:?}"
    );
}

#[test]
fn binding_the_parameter_in_a_constructor_is_still_accepted() {
    admit_inductive(true)
        .expect("`inductive Wrap.{u} : Prop | mk : Sort u -> Wrap` is well formed");
}

/// The prelude is the real control: it is where every axiom-freedom claim in
/// this repository is measured, it is densely universe-polymorphic, and if the
/// new check were even slightly too strict it would stop building.
#[test]
fn the_logic_prelude_still_builds() {
    let mut kernel = Kernel::new();
    axeyum_lean_kernel::build_logic_prelude(&mut kernel)
        .expect("the logic prelude must still build under the universe-closure check");
}
