//! Tests for the type-theory core (WHNF, def_eq, infer) — validated against
//! KNOWN typing judgments, beta/zeta reduction, def_eq pos/neg cases, and the
//! error cases that the trusted kernel must reject (not panic).
//!
//! Mathematical single-character binder names (`a`, `x`, `u`) match the
//! type-theory literature, so the relevant naming lints are relaxed.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::doc_markdown
)]

use crate::expr::{ExprId, ExprNode};
use crate::level::LevelNode;
use crate::tc::{KernelError, LocalContext, LocalDecl};
use crate::{BinderInfo, Declaration, Kernel, Lit, build_logic_prelude};

/// `Sort 0 : Sort 1`.
#[test]
fn sort_zero_has_type_sort_one() {
    let mut k = Kernel::new();
    let s0 = k.sort_zero();
    let ty = k.infer(s0).unwrap();
    // ty should be Sort (succ 0) == Sort 1.
    let z = k.level_zero();
    let one = k.level_succ(z);
    let expected = k.sort(one);
    assert_eq!(ty, expected);
}

/// `Sort u : Sort (u+1)` for a universe parameter `u`.
#[test]
fn sort_param_has_successor_type() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let un = k.name_str(anon, "u");
    let u = k.level_param(un);
    let su = k.sort(u);
    let ty = k.infer(su).unwrap();
    let succ_u = k.level_succ(u);
    let expected = k.sort(succ_u);
    assert_eq!(ty, expected);
}

/// Polymorphic identity `λ (α : Sort 0), λ (x : α), x` infers
/// `Π (α : Sort 0), α → α` i.e. `Π (α : Sort 0), Π (_ : α), α`.
#[test]
fn polymorphic_identity_type() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();

    // inner: λ (x : #0), #0   (x : α where α is the outer bound var)
    let alpha_ref = k.bvar(0); // refers to α inside the inner lambda's domain
    let x_ref = k.bvar(0); // the inner x
    let inner = k.lam(anon, alpha_ref, x_ref, BinderInfo::Default);
    // outer: λ (α : Sort 0), inner
    let id_fn = k.lam(anon, s0, inner, BinderInfo::Default);

    let inferred = k.infer(id_fn).unwrap();

    // expected: Π (α : Sort 0), Π (_ : #0), #1
    //   outer Pi domain = Sort 0
    //   inner Pi domain = α = #0, body = α = #1 (the outer binder)
    let dom_inner = k.bvar(0);
    let body_inner = k.bvar(1);
    let pi_inner = k.pi(anon, dom_inner, body_inner, BinderInfo::Default);
    let expected = k.pi(anon, s0, pi_inner, BinderInfo::Default);

    assert_eq!(inferred, expected, "inferred id type should be Π α, α → α");
    assert!(k.def_eq(inferred, expected));
}

/// `(λ (α : Sort 1), α) (Sort 0)` whnfs to `Sort 0` and infers `Sort 1`.
///
/// The binder domain is `Sort 1` because the argument `Sort 0` has type
/// `Sort 1` (so it must inhabit `Sort 1`). The result type is the bound `α`
/// instantiated to the argument `Sort 0`, whose type is `Sort 1`.
#[test]
fn beta_application_whnf_and_infer() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    let body = k.bvar(0); // returns its argument α
    let lam = k.lam(anon, s1, body, BinderInfo::Default);
    let app = k.app(lam, s0); // apply to Sort 0 (: Sort 1)

    // whnf -> Sort 0
    let reduced = k.whnf(app);
    assert_eq!(reduced, s0);

    // infer -> Sort 1 (the type of the argument Sort 0)
    let ty = k.infer(app).unwrap();
    assert_eq!(ty, s1);
}

/// Applying the polymorphic identity to a concrete typed argument type-checks
/// and reduces. We use `id (Sort 0) (Sort 0 -> Sort 0)`... simpler: instantiate
/// `α := (Sort 0 → Sort 0)` is itself a Sort? No — keep it well-typed: apply
/// the identity at the type `Sort 0` to an inhabitant. We use a free variable
/// `a : Sort 0` for the inhabitant via a local context is awkward at top level,
/// so instead apply id at `Sort 1` to `Sort 0` (`Sort 0 : Sort 1`).
#[test]
fn apply_identity_to_concrete_arg() {
    let mut k = Kernel::new();
    let anon = k.anon();
    // id : Π (α : Sort 2), α → α   (use Sort 2 so Sort 1 is a valid α)
    let z = k.level_zero();
    let one = k.level_succ(z);
    let two = k.level_succ(one);
    let s2 = k.sort(two);
    let alpha_ref = k.bvar(0);
    let x_ref = k.bvar(0);
    let inner = k.lam(anon, alpha_ref, x_ref, BinderInfo::Default);
    let id_fn = k.lam(anon, s2, inner, BinderInfo::Default);

    // id (Sort 1) : Sort 1 → Sort 1
    let s1 = k.sort(one);
    let id_at = k.app(id_fn, s1);
    // (id (Sort 1)) (Sort 0)   since Sort 0 : Sort 1
    let s0 = k.sort_zero();
    let full = k.app(id_at, s0);

    // type-checks
    let ty = k.infer(full).unwrap();
    // result type is Sort 1 (= α = Sort 1)
    assert_eq!(ty, s1);
    // reduces to Sort 0
    let reduced = k.whnf(full);
    assert_eq!(reduced, s0);
}

/// `whnf((λ x:A, x) a) == a` (beta).
#[test]
fn beta_reduces_to_argument() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let a_ty = k.sort_zero();
    let body = k.bvar(0);
    let id_fn = k.lam(anon, a_ty, body, BinderInfo::Default);
    // a is a free variable standing for some inhabitant.
    let a = k.fvar(99);
    let app = k.app(id_fn, a);
    assert_eq!(k.whnf(app), a);
}

/// WHNF entries from prior declaration revisions are unreachable and are
/// discarded before the first lookup in the new revision.
///
/// Both expressions here are **closed**, which is now what makes them eligible
/// for the kernel-global cache at all; see
/// `open_expressions_never_enter_the_context_free_whnf_cache` for the other
/// half of the split.
#[test]
fn whnf_cache_retains_only_the_current_environment_revision() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let body = k.bvar(0);
    let first_lam = k.lam(anon, ty, body, BinderInfo::Default);
    let first_arg = k.lit(Lit::Nat(41_u8.into()));
    let first = k.app(first_lam, first_arg);
    assert_eq!(k.whnf(first), first_arg);
    assert!(k.whnf_cache.1.contains_key(&first));

    let axiom = k.name_str(anon, "cacheRevisionAxiom");
    k.add_declaration(Declaration::Axiom {
        name: axiom,
        uparams: vec![],
        ty,
    })
    .expect("axiom admits");

    let second_lam = k.lam(anon, ty, body, BinderInfo::Default);
    let second_arg = k.lit(Lit::Nat(42_u8.into()));
    let second = k.app(second_lam, second_arg);
    assert_eq!(k.whnf(second), second_arg);
    assert_eq!(k.whnf_cache.0, k.env.revision());
    assert!(k.whnf_cache.1.contains_key(&second));
    assert!(!k.whnf_cache.1.contains_key(&first));
}

/// The kernel-global WHNF cache is keyed on `(environment revision, ExprId)`
/// with **no** local-context component, so nothing whose reduction could depend
/// on a local context may ever be stored in it.
///
/// `has_fvars` is the structural boundary that decides this: a closed term
/// cannot reach a context lookup, because every reduction step builds only from
/// subterms of the input and from (closed) environment declarations, so no
/// `FVar` can appear part-way through. This test pins the boundary itself —
/// reduce an expression that mentions a free variable and assert the global
/// cache stayed empty.
#[test]
fn open_expressions_never_enter_the_context_free_whnf_cache() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let body = k.bvar(0);
    let identity = k.lam(anon, ty, body, BinderInfo::Default);
    let a = k.fvar(41);
    let open = k.app(identity, a);
    assert!(k.has_fvars(open), "the probe expression must be open");

    assert_eq!(k.whnf(open), a);
    assert!(
        k.whnf_cache.1.is_empty(),
        "an open expression reached the context-free cache"
    );

    // The closed counterpart of the same redex does get cached, so the empty
    // cache above is the `has_fvars` split and not an inert reduction path.
    let closed_arg = k.lit(Lit::Nat(41_u8.into()));
    let closed = k.app(identity, closed_arg);
    assert_eq!(k.whnf(closed), closed_arg);
    assert!(k.whnf_cache.1.contains_key(&closed));
}

/// The sole kernel rollback boundary removes the environment suffix and
/// invalidates both environment-sensitive caches together.
#[test]
fn rollback_clears_environment_sensitive_caches() {
    let mut k = Kernel::new();
    let checkpoint = k.env.checkpoint();
    let anon = k.anon();
    let name = k.name_str(anon, "temporaryCacheAxiom");
    let ty = k.sort_zero();
    k.add_declaration(Declaration::Axiom {
        name,
        uparams: vec![],
        ty,
    })
    .expect("axiom admits");

    let c = k.const_(name, vec![]);
    assert_eq!(k.infer(c).expect("constant infers"), ty);
    assert_eq!(k.whnf(c), c);
    assert!(!k.infer_closed_cache.is_empty());
    assert!(!k.whnf_cache.1.is_empty());

    k.rollback(checkpoint);
    assert!(!k.env.contains(name));
    assert!(k.infer_closed_cache.is_empty());
    assert!(k.whnf_cache.1.is_empty());
    assert_eq!(k.whnf_cache.0, k.env.revision());
}

/// A `Let` whnfs to its instantiated body (zeta).
#[test]
fn let_zeta_reduces_to_body() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let val = k.fvar(5);
    // let _ : Sort 0 := fv5; #0   ==> fv5
    let body = k.bvar(0);
    let let_e = k.let_(anon, ty, val, body);
    assert_eq!(k.whnf(let_e), val);
}

/// A β-redex is def_eq to its reduct.
#[test]
fn def_eq_beta_redex() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ty = k.sort_zero();
    let body = k.bvar(0);
    let id_fn = k.lam(anon, ty, body, BinderInfo::Default);
    let a = k.fvar(3);
    let redex = k.app(id_fn, a);
    assert!(k.def_eq(redex, a));
    assert!(k.def_eq(a, redex));
}

/// Pi/Lam congruence: alpha-equivalent terms are def_eq (de Bruijn makes them
/// structurally identical; this checks congruence under fresh fvars too).
#[test]
fn def_eq_binder_congruence() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let nx = k.name_str(anon, "x");
    let ny = k.name_str(anon, "y");
    let s0 = k.sort_zero();
    let b0 = k.bvar(0);
    // Two lambdas differing only in binder name are def_eq (names don't matter).
    let lam_x = k.lam(nx, s0, b0, BinderInfo::Default);
    let lam_y = k.lam(ny, s0, b0, BinderInfo::Default);
    assert!(k.def_eq(lam_x, lam_y));

    // Pi congruence with def-eq (but not syntactically identical) domains:
    // domain `(λα.α) (Sort 0)` is def_eq to `Sort 0`.
    let id_on_types = {
        let s1_body = k.bvar(0);
        let z = k.level_zero();
        let one = k.level_succ(z);
        let s1 = k.sort(one);
        let lam = k.lam(anon, s1, s1_body, BinderInfo::Default);
        k.app(lam, s0)
    };
    let pi_reduced = k.pi(anon, s0, b0, BinderInfo::Default);
    let pi_redex = k.pi(anon, id_on_types, b0, BinderInfo::Default);
    assert!(k.def_eq(pi_redex, pi_reduced));
}

/// Two non-equal types are NOT def_eq.
#[test]
fn def_eq_negative() {
    let mut k = Kernel::new();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s0 = k.sort_zero();
    let s1 = k.sort(one);
    // Sort 0 and Sort 1 are different sorts.
    assert!(!k.def_eq(s0, s1));

    // Two distinct free variables are not def_eq.
    let a = k.fvar(1);
    let b = k.fvar(2);
    assert!(!k.def_eq(a, b));
}

/// Eta: `f` and `λ x, f x` are def_eq when `f : Π x, B`.
#[test]
fn def_eq_eta_expansion() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    // f is a local of Pi type via the local context inside a lambda. Build:
    //   λ (f : Sort 0 → Sort 0), <compare f with (λ x, f x)>
    // We test via def_eq under a context where f's type is a Pi.
    // Construct f as a free var and register it through a Pi-typed lambda:
    // Easier: build `g = λ (x : Sort 0), f x` requires f's type known by infer.
    // Use the standard trick: f := λ (y : Sort 0), y  (identity), its eta-form
    // λ (x : Sort 0), f x must be def_eq to f.
    let y = k.bvar(0);
    let f = k.lam(anon, s0, y, BinderInfo::Default);
    // eta form: λ (x : Sort 0), f x  with f lifted under the binder
    let f_lifted = k.lift_loose_bvars(f, 0, 1);
    let x = k.bvar(0);
    let app = k.app(f_lifted, x);
    let eta = k.lam(anon, s0, app, BinderInfo::Default);
    assert!(k.def_eq(f, eta));
    assert!(k.def_eq(eta, f));
}

/// Error: applying a non-function (`App(Sort 0, x)`) is rejected with NotAPi.
#[test]
fn error_apply_non_function() {
    let mut k = Kernel::new();
    let s0 = k.sort_zero();
    let x = k.fvar(0); // any arg; but fvar 0 is unbound -> would error first.
    // Use Sort 0 as the (well-typed) argument so the function-side error is
    // what surfaces.
    let app = k.app(s0, s0);
    let err = k.infer(app).unwrap_err();
    assert!(matches!(err, KernelError::NotAPi { .. }), "got {err:?}");
    let _ = x;
}

/// Error: an `App` whose argument type mismatches the Pi domain.
#[test]
fn error_app_arg_type_mismatch() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    // f : Π (α : Sort 1), Sort 0   (a function expecting a Sort-1 inhabitant)
    let s0_body = k.sort_zero();
    let f = k.lam(anon, s1, s0_body, BinderInfo::Default);
    // Apply f to `Sort 1`. Sort 1 : Sort 2, not Sort 1, so the arg type
    // (Sort 2) mismatches the domain (Sort 1).
    let arg = s1; // Sort 1 : Sort 2
    let app = k.app(f, arg);
    let err = k.infer(app).unwrap_err();
    assert!(
        matches!(err, KernelError::TypeMismatch { .. }),
        "got {err:?}"
    );
}

/// A well-typed application across the domain (Sort 0 : Sort 1 fits domain
/// Sort 1) type-checks — the positive counterpart to the mismatch test.
#[test]
fn app_arg_type_match_ok() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0_body = k.sort_zero();
    let f = k.lam(anon, s1, s0_body, BinderInfo::Default);
    // Sort 0 : Sort 1 matches domain Sort 1.
    let s0 = k.sort_zero();
    let app = k.app(f, s0);
    assert!(k.infer(app).is_ok());
}

/// Error: a `Lam` whose domain isn't a type. We use a domain that infers to a
/// non-Sort: `Sort 0 → Sort 0` applied... no, that's a Sort. Instead use an
/// fvar bound to a non-type, but fvars need a context. Simplest in-scope case:
/// a domain that is a lambda (`λ x:Sort 0, x`), whose type is a Pi, not a Sort.
#[test]
fn error_lambda_domain_not_a_type() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    // bad_dom = λ (x : Sort 0), x  : Sort 0 → Sort 0 (a Pi, not a Sort)
    let xb = k.bvar(0);
    let bad_dom = k.lam(anon, s0, xb, BinderInfo::Default);
    let body = k.bvar(0);
    let lam = k.lam(anon, bad_dom, body, BinderInfo::Default);
    let err = k.infer(lam).unwrap_err();
    assert!(matches!(err, KernelError::NotASort { .. }), "got {err:?}");
}

/// Error: a `Const` naming a declaration absent from the environment is
/// rejected with `UnknownConst` (the environment layer, ADR-0036 slice 3, now
/// resolves known constants; an unknown name is still an error, not a panic).
#[test]
fn error_const_unknown() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let cn = k.name_str(anon, "Nat");
    let c = k.const_(cn, vec![]);
    let err = k.infer(c).unwrap_err();
    assert!(
        matches!(err, KernelError::UnknownConst { .. }),
        "got {err:?}"
    );
}

/// An empty environment has no `String` bootstrap, so a string literal has no
/// type — and the refusal names the reserved declaration rather than saying
/// "unsupported". The environment here has never heard the name `String`, which
/// is why the reported name is absent rather than interned: looking it up must
/// not mint it (a minted name renumbers every subsequent export).
#[test]
fn error_lit_without_a_string_bootstrap() {
    let mut k = Kernel::new();
    let string = k.lit(Lit::Str("deferred".into()));
    let err = k.infer(string).unwrap_err();
    assert!(
        matches!(
            err,
            KernelError::StringLiteralBootstrapMismatch { string: None }
        ),
        "got {err:?}"
    );
}

/// Refusing a string literal must not **mint** a name.
///
/// Name ids are dense and assigned in insertion order, and `lean_export` walks
/// declarations in that order, so a single minted name renumbers an entire
/// subsequent export. The `Nat` acceleration lane shipped exactly that bug. The
/// `String` gate therefore does its own lookups first (which never intern) and
/// only consults the inherited `Nat` gate (which does) once the string-specific
/// names are known to exist — so a kernel that has never heard of
/// `String.ofList` comes out of a failed inference byte-for-byte as it went in.
#[test]
fn a_refused_string_literal_interns_no_name() {
    let mut k = Kernel::new();
    let string = k.lit(Lit::Str("deferred".into()));
    // The anonymous root is id 0 in every kernel and is minted by the first
    // thing that asks for it; take the baseline after it exists so the
    // measurement is about the *reserved* names, which is what renumbers.
    let _ = k.anon();
    let before = k.names.len();
    assert!(k.infer(string).is_err());
    assert_eq!(
        k.names.len(),
        before,
        "inference minted a name while refusing"
    );
    // And again, to catch a cache that mints on the miss path only once.
    assert!(k.infer(string).is_err());
    assert_eq!(k.names.len(), before);
}

/// Error: an unbound `FVar` reaching inference.
#[test]
fn error_unbound_fvar() {
    let mut k = Kernel::new();
    let fv = k.fvar(123);
    let err = k.infer(fv).unwrap_err();
    assert!(
        matches!(err, KernelError::UnboundFVar { id: 123 }),
        "got {err:?}"
    );
}

/// Error: a loose `BVar` reaching inference (a malformed open term).
#[test]
fn error_loose_bvar() {
    let mut k = Kernel::new();
    let b = k.bvar(0);
    let err = k.infer(b).unwrap_err();
    assert!(
        matches!(err, KernelError::LooseBVar { index: 0 }),
        "got {err:?}"
    );
}

/// A `Pi` into `Prop` stays in `Prop` (the impredicativity of `Prop`, via
/// `IMax`): `Π (p : Sort 0), p` has type `Sort 0`.
///
/// Here the codomain `p` (`#0`) is itself a `Prop` (its sort is `0`), so
/// `IMax (sort-of dom = 1) (sort-of body = 0) = 0` and the whole Pi lands in
/// `Prop`. (`Π (α : Sort 1), Sort 0` would instead land in `Sort 1`, because
/// its codomain `Sort 0` is a *type* whose sort is `1`, not a `Prop`.)
#[test]
fn pi_into_prop_is_prop() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    // Π (p : Sort 0), p   — for all propositions p, p (a proposition).
    let body = k.bvar(0);
    let pi = k.pi(anon, s0, body, BinderInfo::Default);
    let ty = k.infer(pi).unwrap();
    // Expect Sort 0 (after IMax simplification, the result level is Zero).
    match k.expr_node(ty).clone() {
        ExprNode::Sort(level) => {
            assert!(k.level_is_zero(level), "Pi into Prop should land in Prop");
        }
        other => panic!("expected Sort, got {other:?}"),
    }
}

/// The function arrow `Sort 0 → Sort 0` (a non-dependent Pi) infers `Sort 1`.
#[test]
fn arrow_type_infers_sort_one() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    // Π (_ : Sort 0), Sort 0  with a closed body (Sort 0, no bvar).
    let arrow = k.pi(anon, s0, s0, BinderInfo::Default);
    let ty = k.infer(arrow).unwrap();
    // sort-of dom = Sort 1 -> level 1; sort-of body = Sort 1 -> level 1;
    // IMax 1 1 = 1, so result is Sort 1.
    match k.expr_node(ty).clone() {
        ExprNode::Sort(level) => {
            let simp = k.simplify(level);
            let (inner, n) = k.level_succs(simp);
            assert!(matches!(k.level_node(inner), LevelNode::Zero));
            assert_eq!(n, 1, "Sort 0 -> Sort 0 should have type Sort 1");
        }
        other => panic!("expected Sort, got {other:?}"),
    }
}

/// `Let` type inference: `let x : Sort 1 := Sort 0; x` infers `Sort 1`
/// (the body `#0` is the let value `Sort 0`, whose type is `Sort 1`).
#[test]
fn let_infers_body_type() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    let body = k.bvar(0);
    let let_e = k.let_(anon, s1, s0, body);
    let ty = k.infer(let_e).unwrap();
    assert_eq!(ty, s1);
}

/// Consecutive lets are opened as one telescope without changing dependent
/// de Bruijn substitution order.
#[test]
fn dependent_let_telescope_infers() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();

    // let α : Sort 1 := Sort 0
    // let β : Sort 1 := α
    // β
    let outer_alpha = k.bvar(0);
    let inner_beta = k.bvar(0);
    let beta = k.let_(anon, s1, outer_alpha, inner_beta);
    let telescope = k.let_(anon, s1, s0, beta);
    assert_eq!(k.infer(telescope).unwrap(), s1);
}

/// A let-bound local is definitionally equal to its value while checking the
/// telescope body, without substituting that value through the complete body.
#[test]
fn let_local_value_participates_in_definitional_equality() {
    let mut k = Kernel::new();
    let prelude = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let type_ = k.sort(one);
    let prop = k.sort_zero();
    let alias = k.bvar(0);
    let identity_body = k.bvar(0);
    let identity = k.lam(anon, alias, identity_body, BinderInfo::Default);
    let false_ = k.const_(prelude.false_, vec![]);
    let application = k.app(identity, false_);
    let term = k.let_(anon, type_, prop, application);
    assert_eq!(k.infer(term).unwrap(), prop);
}

/// Zeta equality exposes only the recorded let value; it does not make an
/// unrelated argument type equal to the let-bound type.
#[test]
fn let_local_value_does_not_mask_argument_mismatch() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let type_ = k.sort(one);
    let prop = k.sort_zero();
    let alias = k.bvar(0);
    let identity_body = k.bvar(0);
    let identity = k.lam(anon, alias, identity_body, BinderInfo::Default);
    let application = k.app(identity, prop);
    let term = k.let_(anon, type_, prop, application);
    assert!(matches!(
        k.infer(term),
        Err(KernelError::TypeMismatch { .. })
    ));
}

/// A long independent let telescope remains linear enough for proof-export
/// terms while preserving the ordinary zeta-reduced result type.
#[test]
fn long_let_telescope_infers() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    let mut term = k.bvar(0);
    for _ in 0..2_048 {
        term = k.let_(anon, s1, s0, term);
    }
    assert_eq!(k.infer(term).unwrap(), s1);
}

/// `Let` rejects a value whose type mismatches the annotation.
#[test]
fn let_value_type_mismatch() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let two = k.level_succ(one);
    let s1 = k.sort(one);
    let s2 = k.sort(two);
    // let x : Sort 1 := Sort 1; x   — but Sort 1 : Sort 2 ≠ Sort 1.
    let body = k.bvar(0);
    let let_e = k.let_(anon, s1, s1, body);
    let err = k.infer(let_e).unwrap_err();
    assert!(
        matches!(err, KernelError::TypeMismatch { .. }),
        "got {err:?}"
    );
    let _ = s2;
}

/// Determinism: inference is a pure function of the term (same kernel
/// construction sequence yields the same inferred-type id).
#[test]
fn determinism_infer() {
    fn build() -> usize {
        let mut k = Kernel::new();
        let anon = k.anon();
        let s0 = k.sort_zero();
        let alpha_ref = k.bvar(0);
        let x_ref = k.bvar(0);
        let inner = k.lam(anon, alpha_ref, x_ref, BinderInfo::Default);
        let id_fn = k.lam(anon, s0, inner, BinderInfo::Default);
        k.infer(id_fn).unwrap().index()
    }
    assert_eq!(build(), build());
}

/// LocalContext basics: fresh fvars are distinct and lookups respect LIFO.
#[test]
fn local_context_push_pop_lookup() {
    use crate::tc::{LocalContext, LocalDecl};
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    let mut ctx = LocalContext::new();
    let f0 = ctx.fresh_fvar();
    let f1 = ctx.fresh_fvar();
    assert_ne!(f0, f1);
    assert_eq!(ctx.type_of(f0), None);
    ctx.push(LocalDecl {
        fvar: f0,
        name: anon,
        ty: s0,
        info: BinderInfo::Default,
    });
    assert_eq!(ctx.type_of(f0), Some(s0));
    ctx.pop();
    assert_eq!(ctx.type_of(f0), None);
}

/// Projection inference never trusts field-count metadata enough to index an
/// ill-shaped constructor telescope. This test injects an impossible
/// environment state through the crate-private unchecked test seam and proves
/// the trusted inference path still returns a typed error rather than panicking
/// or manufacturing a field type.
#[test]
fn projection_rejects_inconsistent_constructor_telescope_metadata() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let structure_name = k.name_str(anon, "MalformedStructure");
    let ctor_name = k.name_str(structure_name, "mk");
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let sort_one = k.sort(one);
    let malformed_ctor_type = k.sort_zero();

    k.env.insert_unchecked(Declaration::Inductive {
        name: structure_name,
        uparams: vec![],
        ty: sort_one,
        num_params: 0,
        num_indices: 0,
        is_recursive: false,
        ctor_names: vec![ctor_name],
    });
    k.env.insert_unchecked(Declaration::Constructor {
        name: ctor_name,
        uparams: vec![],
        ty: malformed_ctor_type,
        inductive: structure_name,
        idx: 0,
        num_fields: 1,
    });

    let value_fvar = 700;
    let structure_type = k.const_(structure_name, vec![]);
    let value = k.fvar(value_fvar);
    let projection = k.proj(structure_name, 0, value);
    let mut context = LocalContext::new();
    context.push(LocalDecl {
        fvar: value_fvar,
        name: anon,
        ty: structure_type,
        info: BinderInfo::Default,
    });
    assert_eq!(
        k.infer_in(projection, &mut context),
        Err(KernelError::MalformedProjectionConstructor {
            name: structure_name,
            ctor: ctor_name,
            field_index: 0,
        })
    );
}

// ---------------------------------------------------------------------------
// The WHNF cache key, and the collision it used to admit
// ---------------------------------------------------------------------------

/// Build `True.rec.{1} (fun _ : True => Prop) True h` with `h` the free
/// variable `fvar_id`, over a kernel carrying the logic prelude.
///
/// `True` is K-like — a `Prop` family, one constructor, that constructor with
/// zero fields, not mutual — so this application reduces if and only if
/// reduction can establish that `h`'s type really is `True`, which it can only
/// learn from a local context.
fn k_like_true_rec_probe(k: &mut Kernel, fvar_id: u64) -> (ExprId, ExprId, ExprId) {
    let logic = build_logic_prelude(k).expect("logic prelude builds");
    let anon = k.anon();
    let true_const = k.const_(logic.true_, vec![]);
    let prop = k.sort_zero();
    // motive : True -> Sort 1, constantly `Prop`.
    let motive = k.lam(anon, true_const, prop, BinderInfo::Default);
    // minor : motive True.intro = Prop, i.e. any proposition; `True` will do.
    let minor = true_const;
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let recursor = k.const_(logic.true_rec, vec![one]);
    let applied = k.app(recursor, motive);
    let applied = k.app(applied, minor);
    let major = k.fvar(fvar_id);
    let probe = k.app(applied, major);
    (probe, minor, true_const)
}

/// K-like reduction reads the **local context**, so the same `ExprId` has two
/// different correct weak head normal forms in two different contexts — and the
/// two contexts collide on the fvar id that distinguishes them.
///
/// This is the construction the cache key had to be settled against. All three
/// preconditions are asserted rather than assumed:
///
/// 1. `LocalContext::new` restarts its fvar counter at 0, so two independent
///    contexts really do mint the *same* id for different variables;
/// 2. `Kernel::fvar` interns, so that one id is one `ExprId` in both — the
///    whole cache key, under the old scheme;
/// 3. no declaration is admitted in between, so the environment revision (the
///    only other component of the old key) does not move either.
///
/// The payoff is the last two assertions: the pre-fix algorithm, run verbatim,
/// answers the *first* context's normal form in the second, while the shipped
/// algorithm answers each context correctly.
#[test]
fn whnf_cache_key_collision_is_constructible() {
    let mut k = Kernel::new();
    let (probe, minor, true_ty) = k_like_true_rec_probe(&mut k, 0);
    let false_ty = {
        let anon = k.anon();
        let false_name = k.name_str(anon, "False");
        k.const_(false_name, vec![])
    };
    let anon = k.anon();
    let revision_before = k.env.revision();

    // Context A: the local `h` really is a proof of `True`.
    let mut ctx_a = LocalContext::new();
    let fvar_a = ctx_a.fresh_fvar();
    assert_eq!(fvar_a, 0, "a fresh context mints fvar 0");
    ctx_a.push(LocalDecl {
        fvar: fvar_a,
        name: anon,
        ty: true_ty,
        info: BinderInfo::Default,
    });
    let normal_a = k.whnf_core(probe, &mut ctx_a);
    assert_eq!(
        normal_a, minor,
        "K-like reduction must fire on a major of the K-like family"
    );

    // Context B: same fvar id, different type. Nothing was admitted in between.
    let mut ctx_b = LocalContext::new();
    let fvar_b = ctx_b.fresh_fvar();
    assert_eq!(fvar_b, fvar_a, "the two contexts collide on the fvar id");
    ctx_b.push(LocalDecl {
        fvar: fvar_b,
        name: anon,
        ty: false_ty,
        info: BinderInfo::Default,
    });
    assert_eq!(
        k.env.revision(),
        revision_before,
        "no declaration was admitted, so the old key's other component is fixed"
    );

    let normal_b = k.whnf_core(probe, &mut ctx_b);
    assert_eq!(
        normal_b, probe,
        "a major that is not of the K-like family must leave the recursor stuck"
    );
    assert_ne!(
        normal_a, normal_b,
        "the same ExprId at one environment revision has two normal forms"
    );

    // Now the point. Run the pre-fix algorithm over the same two contexts.
    let mut ctx_a = LocalContext::new();
    let fvar = ctx_a.fresh_fvar();
    ctx_a.push(LocalDecl {
        fvar,
        name: anon,
        ty: true_ty,
        info: BinderInfo::Default,
    });
    let stale_a = k.whnf_core_context_free_cached(probe, &mut ctx_a);
    assert_eq!(stale_a, minor);

    let mut ctx_b = LocalContext::new();
    let fvar = ctx_b.fresh_fvar();
    ctx_b.push(LocalDecl {
        fvar,
        name: anon,
        ty: false_ty,
        info: BinderInfo::Default,
    });
    let stale_b = k.whnf_core_context_free_cached(probe, &mut ctx_b);
    assert_eq!(
        stale_b, minor,
        "the pre-fix cache returns the FIRST context's normal form in the second"
    );
    assert_ne!(
        stale_b, normal_b,
        "...which is not the second context's normal form: this is the collision"
    );
}

/// The shipped split survives the same collision when the two contexts are
/// exercised in the *other* order, and when the second context is entered
/// before the first is dropped.
#[test]
fn context_scoped_whnf_entries_do_not_leak_between_contexts() {
    let mut k = Kernel::new();
    let (probe, minor, true_ty) = k_like_true_rec_probe(&mut k, 0);
    let false_ty = {
        let anon = k.anon();
        let false_name = k.name_str(anon, "False");
        k.const_(false_name, vec![])
    };
    let anon = k.anon();

    let mut refuting = LocalContext::new();
    let fvar = refuting.fresh_fvar();
    refuting.push(LocalDecl {
        fvar,
        name: anon,
        ty: false_ty,
        info: BinderInfo::Default,
    });
    let mut admitting = LocalContext::new();
    let fvar = admitting.fresh_fvar();
    admitting.push(LocalDecl {
        fvar,
        name: anon,
        ty: true_ty,
        info: BinderInfo::Default,
    });

    // Both contexts are live at once and interleaved.
    assert_eq!(k.whnf_core(probe, &mut refuting), probe);
    assert_eq!(k.whnf_core(probe, &mut admitting), minor);
    assert_eq!(k.whnf_core(probe, &mut refuting), probe);
    assert_eq!(k.whnf_core(probe, &mut admitting), minor);
    assert!(
        !k.whnf_cache.1.contains_key(&probe),
        "a context-dependent normal form must never reach the kernel-global cache"
    );
    let keys: Vec<ExprId> = k.whnf_cache.1.keys().copied().collect();
    assert!(
        keys.iter().all(|&key| !k.has_fvars(key)),
        "every key in the context-free cache must be closed"
    );
}

/// Popping the local declaration that justified a K-like reduction invalidates
/// the memoised answer: the same `ExprId` goes back to being stuck.
///
/// This is what `LocalContext::push`/`pop` clearing the context-scoped cache
/// buys, and it is why that cache does not need a discriminator of its own.
#[test]
fn popping_the_local_that_justified_k_reduction_invalidates_the_entry() {
    let mut k = Kernel::new();
    let (probe, minor, true_ty) = k_like_true_rec_probe(&mut k, 0);
    let anon = k.anon();

    let mut ctx = LocalContext::new();
    let fvar = ctx.fresh_fvar();
    ctx.push(LocalDecl {
        fvar,
        name: anon,
        ty: true_ty,
        info: BinderInfo::Default,
    });
    assert_eq!(k.whnf_core(probe, &mut ctx), minor);

    ctx.pop().expect("the declaration is on the stack");
    assert_eq!(
        k.whnf_core(probe, &mut ctx),
        probe,
        "with the local gone, reduction has no reason to believe the major is True"
    );
}

/// The reconstruction preludes are **not** accelerated, and this is the
/// mechanism rather than a hope.
///
/// `build_logic_prelude` declares `Bool` with its constructors in the order
/// `[true, false]`. Lean's order is `[false, true]`, and `Bool.false` being
/// constructor 0 is what `Nat.beq`'s accelerated result means. So the whole
/// table is refused for any environment built by our preludes, every operation
/// keeps computing by its own declared body, and nothing about the 119-theorem
/// `nat` inventory or its empty axiom footprint can move because of this rule.
#[test]
fn the_reconstruction_prelude_is_not_accelerated() {
    let mut kernel = Kernel::new();
    let prelude = crate::build_nat_prelude(&mut kernel).expect("nat prelude must build");

    let anon = kernel.anon();
    let bool_name = kernel
        .lookup_name_str(anon, "Bool")
        .expect("the logic prelude declares Bool");
    let true_ = kernel
        .lookup_name_str(bool_name, "true")
        .expect("Bool.true");
    let false_ = kernel
        .lookup_name_str(bool_name, "false")
        .expect("Bool.false");
    let Some(crate::Declaration::Inductive { ctor_names, .. }) = kernel.env.get(bool_name) else {
        panic!("Bool must be an inductive");
    };
    assert_eq!(
        ctor_names.as_slice(),
        [true_, false_],
        "this test is about our prelude's constructor order; if it changed, the \
         acceleration guard changed meaning with it"
    );

    assert!(
        kernel.nat_binop_table().is_none(),
        "no literal arithmetic rule may fire in an environment whose `Bool` is \
         not Lean's"
    );
    // And the prelude's own `Nat.add` still computes, by its own definition.
    let add = kernel.const_(prelude.add, vec![]);
    let two = kernel.lit(crate::Lit::Nat(crate::NatLit::from(2_u8)));
    let three = kernel.lit(crate::Lit::Nat(crate::NatLit::from(3_u8)));
    let five = kernel.lit(crate::Lit::Nat(crate::NatLit::from(5_u8)));
    let applied = kernel.app(add, two);
    let applied = kernel.app(applied, three);
    assert!(kernel.def_eq(applied, five));
}

/// ζ over a **local `let`** happens inside `whnf_no_unfolding`, and only a
/// *hit* counts as a context read.
///
/// Both halves are load-bearing and both were wrong at some point on
/// 2026-08-15:
///
/// * Doing ζ for locals only at the def-eq entry points left a let-local that
///   became a head *during* `lazy_delta_step` permanently unreduced, which is
///   why `Nat.bitwise._unary` was refused (ADR-0462).
/// * Counting a **miss** as a context read made the closed-expression tripwire
///   in [`Kernel::whnf_no_unfolding`] fire on two of the first 250 Mathlib
///   streams. Reduction of a *closed* expression can call inference (K-like
///   reduction infers its major); that inference opens its own binders, and
///   reducing under them meets ordinary valueless locals. Their lookups return
///   the term unchanged — exactly what an empty context would give — so they
///   are not a dependence on the context and must not be counted.
#[test]
fn local_let_zeta_fires_in_whnf_core_and_only_a_hit_is_a_context_read() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let type_sort = {
        let zero = k.level_zero();
        let one = k.level_succ(zero);
        k.sort(one)
    };
    let carrier = k.name_str(anon, "N");
    k.add_declaration(Declaration::Axiom {
        name: carrier,
        uparams: vec![],
        ty: type_sort,
    })
    .expect("carrier axiom must admit");
    let n_type = k.const_(carrier, vec![]);
    let inhabitant = k.name_str(anon, "c");
    k.add_declaration(Declaration::Axiom {
        name: inhabitant,
        uparams: vec![],
        ty: n_type,
    })
    .expect("inhabitant axiom must admit");
    let value = k.const_(inhabitant, vec![]);

    let mut ctx = LocalContext::new();
    let plain = ctx.fresh_fvar();
    ctx.push(LocalDecl {
        fvar: plain,
        name: anon,
        ty: n_type,
        info: BinderInfo::Default,
    });
    let bound = ctx.fresh_fvar();
    ctx.push_let(
        LocalDecl {
            fvar: bound,
            name: anon,
            ty: n_type,
            info: BinderInfo::Default,
        },
        value,
    );

    // A local with no recorded value is already weak-head-normal, and looking
    // it up is NOT a context read: the answer is the same with or without a
    // context.
    let plain_expr = k.fvar(plain);
    let before = k.reduction_ctx_reads;
    let reduced = k.whnf_no_unfolding(plain_expr, &mut ctx);
    assert_eq!(reduced, plain_expr, "a valueless local must not reduce");
    assert_eq!(
        k.reduction_ctx_reads, before,
        "a MISS must not count as a context read; counting it fired the \
         closed-expression tripwire on real Mathlib streams"
    );

    // A let-local reduces to its value, in `whnf_no_unfolding` itself — the
    // δ-free reduction the lazy-delta loop calls after every unfolding — and
    // that IS a context read.
    let bound_expr = k.fvar(bound);
    let before = k.reduction_ctx_reads;
    let reduced = k.whnf_no_unfolding(bound_expr, &mut ctx);
    assert_eq!(
        reduced, value,
        "a let-local must ζ-reduce to its recorded value without δ"
    );
    assert!(
        k.reduction_ctx_reads > before,
        "a ζ HIT is the context changing the reduct and must be counted, or the \
         closed-expression whnf cache loses its tripwire"
    );

    // And it happens under an application spine, not only on a bare head.
    let applied = k.app(bound_expr, plain_expr);
    let reduced = k.whnf_no_unfolding(applied, &mut ctx);
    let expected = k.app(value, plain_expr);
    assert_eq!(
        reduced, expected,
        "ζ must re-apply the spine, as Lean's `whnf_core` does through its \
         `App` head"
    );
}
