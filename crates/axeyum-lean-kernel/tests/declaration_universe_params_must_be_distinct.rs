//! Regression: a declaration may not bind the same universe parameter twice.
//!
//! Found 2026-09-05 by the **public** Lean kernel conformance corpus
//! (`leanprover/lean-kernel-arena`, <https://arena.lean-lang.org>), case
//! `bad/tutorial/019_tut06_bad01`: a `def` whose `levelParams` is `[u, u]`.
//! Lean's kernel refuses it; this kernel admitted it. It was one of exactly two
//! cases in the corpus's 73-case reject half that this kernel accepted, and it
//! is the only one of the two that is a defect rather than a deliberate design
//! difference (ADR-1663; `docs/plan/lean-divergences.md` D2 and D1).
//!
//! Mechanism, and it is the same one as the sibling file
//! `declaration_universe_params_must_be_bound.rs`. `Kernel::check_declaration`
//! compared the parameters a term MENTIONS against the parameters the
//! declaration BINDS, which closed the "free universe" hole. Nothing looked at
//! the binding list itself. Both checks in `check_declaration` are *relative*
//! — inference and def-eq treat `[u, u]` exactly as they treat `[u]`, since
//! each occurrence of `u` in the term is the same `Param` node either way — so
//! a repeated binder was invisible to every check the kernel ran.
//!
//! Why it matters. `Const(c, us)` substitutes `us` **positionally** for `c`'s
//! declared parameters. With `levelParams = [u, u]`, `@c.{a, b}` has two
//! candidate substitutions for the single name `u` and the calculus has no rule
//! picking one, so the declaration does not denote one thing. Whether an
//! implementation takes the first or the last is an implementation detail no
//! user can see, which is exactly the kind of difference that makes two kernels
//! disagree about the same bytes.
//!
//! Both directions are tested, because a guard that only ever rejects is
//! satisfied by a checker that rejects everything:
//!
//! - the duplicate binding is REFUSED, with the variant that names the reason
//!   and the parameter it names, and
//! - the well-formed twin -- the identical declaration binding `u` once, and a
//!   two-parameter declaration binding two DIFFERENT names -- is still ADMITTED.

use axeyum_lean_kernel::{Declaration, Kernel, KernelError};

/// `def dup.{params} : Sort 1 := Sort 0`, over whatever binding list is asked
/// for. The body never mentions a parameter, so the only thing that can differ
/// between the runs below is the binding list itself.
fn admit_with_binders(binders: &[&str]) -> Result<(), KernelError> {
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let uparams: Vec<_> = binders
        .iter()
        .map(|binder| kernel.name_str(anonymous, *binder))
        .collect();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let ty = kernel.sort(one);
    let value = kernel.sort(zero);
    let name = kernel.name_str(anonymous, "tut06_bad01");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams,
        ty,
        value,
        hint: axeyum_lean_kernel::ReducibilityHint::Opaque,
    })
}

#[test]
fn a_repeated_universe_binder_is_refused() {
    let error = admit_with_binders(&["u", "u"])
        .expect_err("`levelParams = [u, u]` must be refused: Lean's kernel refuses it");
    assert!(
        matches!(error, KernelError::DuplicateUniverseParam { .. }),
        "expected DuplicateUniverseParam, got {error:?} -- a different rejection \
         would mean the declaration is refused for an unrelated reason and this \
         guard is not testing what it claims"
    );
}

#[test]
fn a_repeated_binder_names_the_parameter_that_repeats() {
    // The error has to carry WHICH parameter repeats, or a declaration with
    // several binders reports an unactionable "something is duplicated".
    let mut kernel = Kernel::new();
    let anonymous = kernel.anon();
    let u = kernel.name_str(anonymous, "u");
    let v = kernel.name_str(anonymous, "v");
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let ty = kernel.sort(one);
    let value = kernel.sort(zero);
    let name = kernel.name_str(anonymous, "three_binders");
    let error = kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![u, v, v],
            ty,
            value,
            hint: axeyum_lean_kernel::ReducibilityHint::Opaque,
        })
        .expect_err("`[u, v, v]` repeats `v` and must be refused");
    match error {
        KernelError::DuplicateUniverseParam { declaration, param } => {
            assert_eq!(declaration, name, "the error must name the declaration");
            assert_eq!(
                param, v,
                "the error must name `v`, the parameter that repeats, not `u`"
            );
        }
        other => panic!("expected DuplicateUniverseParam, got {other:?}"),
    }
}

#[test]
fn distinct_universe_binders_are_still_admitted() {
    // The control. Without it, `check_declaration` returning
    // `Err(DuplicateUniverseParam)` unconditionally would pass the two tests
    // above and break every universe-polymorphic declaration in the tree.
    admit_with_binders(&["u"]).expect("a single binder must still be admitted");
    admit_with_binders(&["u", "v"]).expect("two distinct binders must still be admitted");
    admit_with_binders(&[]).expect("no binders at all must still be admitted");
}
