//! ζ-reduction of a **local** `let` binding, at the trusted gate.
//!
//! Lean's kernel unfolds a let-bound free variable to its recorded value inside
//! `whnf_core` itself (`whnf_fvar`, `src/kernel/type_checker.cpp:346`, reached
//! from the `expr_kind::FVar` arm at line 416 of the pinned `d024af0`). The
//! placement is the whole content of the rule: `whnf_core` is called from
//! `lazy_delta_reduction_step` after **every** δ unfolding, so a local `let`
//! that only becomes the head of a term *during* the delta loop is still
//! reduced.
//!
//! This port used to do ζ on locals in a separate pass consulted at exactly two
//! points — the top of `def_eq_core` and the `whnf` entry point — and only on
//! the head of a spine. A let-local exposed by a δ or ι step inside the delta
//! loop was therefore never unfolded, the two sides drifted apart, and def-eq
//! returned `false` on terms whose full weak-head normal forms are the *same
//! interned expression*.
//!
//! That is not a hypothetical. It is `Nat.bitwise._unary`, the top declined root
//! in both scale censuses (236 of 500 sampled `Init`+`Std` streams and 186 of
//! 400 Mathlib ones). Lean writes it with `let n' := n / 2`, the generated
//! well-founded-recursion helper states its decreasing obligation in terms of
//! `n'`, and the obligation is discharged against `n / 2`; both sides reduce to
//! `PSigma.casesOn … (PSigma.mk …) …` with the same head, the same arity and
//! five pairwise definitionally equal arguments, and the pair was still refused.
//! See `docs/formalized-math-2026-08/diary-import-wfrec.md`.
//!
//! # The shape every test here uses
//!
//! ```text
//! axiom N     : Type
//! axiom K     : ∀ (a : N), Eq.{1} N a a → N
//! def   id2   : N → N := fun x => x        -- δ-reducible, so the delta loop runs
//! def   probe : N → N := fun n => let n' : N := n; K n (@Eq.refl.{1} N (id2 n'))
//! ```
//!
//! Checking `probe` forces `id2 n' =?= n` under a context where `n'` is a
//! let-local with value `n`. Because `id2` is a definition and `n` is an
//! ordinary local, `lazy_delta_step` unfolds the left side and only then does a
//! let-local become a head — the exact position the old pass could not see.
//! Every test goes through [`Kernel::add_declaration`], never through `def_eq`
//! directly, because the gate is what has to be right.
//!
//! Each positive is paired with a control in the same test, so a positive cannot
//! pass because the rule was switched on globally and stopped discriminating.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, LevelId, LogicPrelude, NameId,
    ReducibilityHint, build_logic_prelude,
};

/// The fixture environment: `N`, `K`, `g`, and the δ-reducible identity `id2`.
struct Fixture {
    logic: LogicPrelude,
    /// The universe level `1`, i.e. `N`'s sort.
    one: LevelId,
    /// `Const N []`.
    n_type: ExprId,
    /// `Const K []`.
    k: ExprId,
    /// `Const g []` — an *opaque* `N → N`, for the negative controls.
    g: ExprId,
    /// `Const id2 []` — a `Definition`, so it δ-unfolds.
    id2: ExprId,
    anon: NameId,
}

fn fixture(kernel: &mut Kernel) -> Fixture {
    let logic = build_logic_prelude(kernel).expect("logic prelude should build");
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_sort = kernel.sort(one);

    // `axiom N : Type`
    let n_name = kernel.name_str(anon, "N");
    kernel
        .add_declaration(Declaration::Axiom {
            name: n_name,
            uparams: vec![],
            ty: type_sort,
        })
        .expect("carrier type should admit");
    let n_type = kernel.const_(n_name, vec![]);

    // `axiom g : N → N` — never unfolds, so a let value built with it can never
    // be identified with a bare local.
    let g_name = kernel.name_str(anon, "g");
    let g_ty = kernel.pi(anon, n_type, n_type, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Axiom {
            name: g_name,
            uparams: vec![],
            ty: g_ty,
        })
        .expect("opaque endomorphism should admit");
    let g = kernel.const_(g_name, vec![]);

    // `axiom K : ∀ (a : N), Eq.{1} N a a → N`
    //
    // The second argument's type is what carries the definitional-equality
    // obligation, and it mentions the first argument — which is why `infer_app`
    // has to instantiate it before checking, and why the obligation is exactly
    // `<the argument we wrote> =?= n`.
    let k_name = kernel.name_str(anon, "K");
    let k_ty = {
        let a = kernel.bvar(0);
        let eq = kernel.const_(logic.eq, vec![one]);
        let eq_n = kernel.app(eq, n_type);
        let lhs_applied = kernel.app(eq_n, a);
        let equation = kernel.app(lhs_applied, a);
        let inner = kernel.pi(anon, equation, n_type, BinderInfo::Default);
        kernel.pi(anon, n_type, inner, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Axiom {
            name: k_name,
            uparams: vec![],
            ty: k_ty,
        })
        .expect("K should admit");
    let k = kernel.const_(k_name, vec![]);

    // `def id2 : N → N := fun x => x`
    let id2_name = kernel.name_str(anon, "id2");
    let id2_ty = kernel.pi(anon, n_type, n_type, BinderInfo::Default);
    let id2_value = {
        let body = kernel.bvar(0);
        kernel.lam(anon, n_type, body, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Definition {
            name: id2_name,
            uparams: vec![],
            ty: id2_ty,
            value: id2_value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("identity definition should admit");
    let id2 = kernel.const_(id2_name, vec![]);

    Fixture {
        logic,
        one,
        n_type,
        k,
        g,
        id2,
        anon,
    }
}

/// `@Eq.refl.{1} N witness`, whose type is `Eq.{1} N witness witness`.
fn eq_refl_at(kernel: &mut Kernel, fixture: &Fixture, witness: ExprId) -> ExprId {
    let refl = kernel.const_(fixture.logic.eq_refl, vec![fixture.one]);
    let applied = kernel.app(refl, fixture.n_type);
    kernel.app(applied, witness)
}

/// Try to admit
/// `def <label> : N → N := fun n => let n' : N := <let_value(n)>; K n (Eq.refl N <witness(n')>)`.
///
/// `let_value` is built from the bound `n` (as a de Bruijn index) and `witness`
/// from the let-bound `n'`, so a caller decides both what the local `let` is
/// bound to and how the proof argument mentions it.
fn admits(
    kernel: &mut Kernel,
    fixture: &Fixture,
    label: &str,
    let_value: impl FnOnce(&mut Kernel, ExprId) -> ExprId,
    witness: impl FnOnce(&mut Kernel, ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let anon = fixture.anon;
    // Inside the lambda: `n` is bvar 0. Inside the let body: `n'` is bvar 0 and
    // `n` is bvar 1.
    let bound_n = kernel.bvar(0);
    let let_value = let_value(kernel, bound_n);
    let n_prime = kernel.bvar(0);
    let witness = witness(kernel, n_prime);
    let proof = eq_refl_at(kernel, fixture, witness);
    let body = {
        let outer_n = kernel.bvar(1);
        let applied = kernel.app(fixture.k, outer_n);
        kernel.app(applied, proof)
    };
    let let_expr = kernel.let_(anon, fixture.n_type, let_value, body);
    let value = kernel.lam(anon, fixture.n_type, let_expr, BinderInfo::Default);
    let ty = kernel.pi(anon, fixture.n_type, fixture.n_type, BinderInfo::Default);

    let name = kernel.name_str(anon, label);
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// A let-local exposed **inside the delta loop** is ζ-reduced.
///
/// The obligation is `id2 n' =?= n` with `n' : N := n`. `id2` is a definition
/// and `n` is an ordinary local, so `lazy_delta_step` sees `(Some, None)`,
/// unfolds the left side to `n'`, and only then is a let-local the head. This is
/// the case the old two-call-site ζ pass could not reach, and it is the shape
/// `Nat.bitwise._unary` is refused on.
///
/// The negative control in the same test binds `n'` to `g n` for an opaque `g`,
/// so ζ still fires and still produces the *right* answer: refused.
#[test]
fn a_let_local_exposed_by_delta_reduction_is_zeta_reduced() {
    let mut kernel = Kernel::new();
    let fixture = fixture(&mut kernel);

    let positive = admits(
        &mut kernel,
        &fixture,
        "probe_delta_exposed",
        |_kernel, n| n,
        |kernel, n_prime| kernel.app(fixture.id2, n_prime),
    );
    assert!(
        positive.is_ok(),
        "`let n' := n; K n (Eq.refl N (id2 n'))` must admit: ζ has to fire on the \
         let-local `id2 n'` unfolds to, inside the delta loop. Got {positive:?}"
    );

    let control = admits(
        &mut kernel,
        &fixture,
        "control_delta_exposed",
        |kernel, n| kernel.app(fixture.g, n),
        |kernel, n_prime| kernel.app(fixture.id2, n_prime),
    );
    assert!(
        control.is_err(),
        "`let n' := g n; K n (Eq.refl N (id2 n'))` must be refused: ζ unfolds `n'` \
         to `g n`, and `g` is an axiom, so `g n` is not `n`"
    );
}

/// A let-local that is already the head **before** the delta loop was reduced
/// even by the old pass. Pinned so the diagnosis stays honest about which case
/// was actually broken: this test passes before and after the fix, and the one
/// above does not.
#[test]
fn a_let_local_at_the_head_was_always_zeta_reduced() {
    let mut kernel = Kernel::new();
    let fixture = fixture(&mut kernel);

    let positive = admits(
        &mut kernel,
        &fixture,
        "probe_head",
        |_kernel, n| n,
        |_kernel, n_prime| n_prime,
    );
    assert!(
        positive.is_ok(),
        "`let n' := n; K n (Eq.refl N n')` must admit. Got {positive:?}"
    );

    let control = admits(
        &mut kernel,
        &fixture,
        "control_head",
        |kernel, n| kernel.app(fixture.g, n),
        |_kernel, n_prime| n_prime,
    );
    assert!(
        control.is_err(),
        "`let n' := g n; K n (Eq.refl N n')` must be refused"
    );
}

/// ζ is not an excuse to identify two *ordinary* locals.
///
/// The rule reads a value the local context recorded for one specific free
/// variable. A lambda binder has no such value, so the wrong local is still the
/// wrong local — and `whnf_no_unfolding`'s `FVar` arm must fall through rather
/// than reduce.
#[test]
fn an_ordinary_local_has_no_value_and_is_never_unfolded() {
    let mut kernel = Kernel::new();
    let fixture = fixture(&mut kernel);
    let anon = fixture.anon;

    // `def probe_two : N → N → N := fun n m => K n (Eq.refl N (id2 m))`
    let m = kernel.bvar(0);
    let witness = kernel.app(fixture.id2, m);
    let proof = eq_refl_at(&mut kernel, &fixture, witness);
    let inner_body = {
        let n = kernel.bvar(1);
        let applied = kernel.app(fixture.k, n);
        kernel.app(applied, proof)
    };
    let inner = kernel.lam(anon, fixture.n_type, inner_body, BinderInfo::Default);
    let value = kernel.lam(anon, fixture.n_type, inner, BinderInfo::Default);
    let ty = {
        let inner_ty = kernel.pi(anon, fixture.n_type, fixture.n_type, BinderInfo::Default);
        kernel.pi(anon, fixture.n_type, inner_ty, BinderInfo::Default)
    };
    let name = kernel.name_str(anon, "probe_two_locals");
    let admitted = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    });
    assert!(
        admitted.is_err(),
        "`fun n m => K n (Eq.refl N (id2 m))` must be refused: `m` is a lambda \
         binder with no recorded value, so nothing may identify it with `n`"
    );
}

/// A let-local whose value mentions *another* let-local unfolds transitively,
/// which is what makes the rule a fixed point rather than one step.
///
/// Lean gets this for free: `whnf_fvar` returns `whnf_core(*value)`, so the
/// value is itself reduced, and a chain collapses. The control binds the last
/// link through the opaque `g`, so the chain still ends in a refusal when it
/// should.
#[test]
fn chained_let_locals_unfold_transitively() {
    let mut kernel = Kernel::new();
    let fixture = fixture(&mut kernel);
    let anon = fixture.anon;

    // `def probe_chain : N → N := fun n => let a : N := n; let b : N := a;
    //                                      K n (Eq.refl N (id2 b))`
    let build = |kernel: &mut Kernel, label: &str, last: &dyn Fn(&mut Kernel, ExprId) -> ExprId| {
        let n_in_a = kernel.bvar(0);
        let a_in_b = kernel.bvar(0);
        let b = kernel.bvar(0);
        let b_value = last(kernel, b);
        let witness = kernel.app(fixture.id2, b_value);
        let proof = eq_refl_at(kernel, &fixture, witness);
        let body = {
            let outer_n = kernel.bvar(2);
            let applied = kernel.app(fixture.k, outer_n);
            kernel.app(applied, proof)
        };
        let let_b = kernel.let_(anon, fixture.n_type, a_in_b, body);
        let let_a = kernel.let_(anon, fixture.n_type, n_in_a, let_b);
        let value = kernel.lam(anon, fixture.n_type, let_a, BinderInfo::Default);
        let ty = kernel.pi(anon, fixture.n_type, fixture.n_type, BinderInfo::Default);
        let name = kernel.name_str(anon, label);
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    };

    let positive = build(&mut kernel, "probe_chain", &|_kernel, b| b);
    assert!(
        positive.is_ok(),
        "`let a := n; let b := a; K n (Eq.refl N (id2 b))` must admit: ζ has to \
         follow the chain `b ↦ a ↦ n`. Got {positive:?}"
    );

    let control = build(&mut kernel, "control_chain", &|kernel, b| {
        kernel.app(fixture.g, b)
    });
    assert!(
        control.is_err(),
        "`… K n (Eq.refl N (id2 (g b)))` must be refused: the chain ends at `g n`"
    );
}
