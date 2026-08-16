//! **Structure-eta reduction of a stuck recursor major premise**, at the
//! trusted gate and at `whnf`.
//!
//! Lean's kernel, before it looks for a ι rule, replaces a major premise that is
//! not a constructor application by `mk e.0 … e.n-1` whenever the major's family
//! is a **non-recursive structure** — one constructor, zero indices, no
//! recursive field — and is not a `Prop`
//! (`to_cnstr_when_structure`, `src/kernel/inductive.h:63` of the pinned
//! `d024af0`, called from `inductive_reduce_rec` at line 96). ι then fires on a
//! major that is a bare variable or an opaque constant.
//!
//! This port had `to_cnstr_when_K` and the Nat/String literal hooks in exactly
//! that position and **not** this one, so a recursor applied to a structure
//! *variable* was permanently stuck. That is
//! `Nat.Linear.Poly.denote_reverse` — the top declined root in both scale
//! censuses after ζ moved into `whnf_core` (153 of 500 sampled `Init`+`Std`
//! streams). `Nat.Linear.Poly.denote` is `List.rec` over `List (Nat × Var)`
//! whose minor is a `Prod.rec` on the head element, and checking the lemma
//! requires reducing that `Prod.rec` against a `p : Nat × Var` that is a free
//! variable. See `docs/formalized-math-2026-08/diary-import-projrec.md`.
//!
//! # How these tests discriminate
//!
//! Every family here is one clause away from the guard: `Sum2` has two
//! constructors, `RecBox` has a recursive field, `IdxBox` has an index, `PBox`
//! is a `Prop`. Each is built so that **dropping that one clause would make the
//! recursor reduce** — the minors are chosen so the would-be reduct is a named
//! constant — and each control asserts that it does not. So a rule that stopped
//! discriminating fails these, not just a rule that stopped firing.
//!
//! The majors are opaque `axiom` constants rather than free variables wherever
//! possible, which keeps the terms closed and therefore lets `Kernel::whnf`
//! (which reduces in the *empty* local context) observe the rule directly. The
//! open, under-a-binder shape — the one the corpus actually declines on — is
//! covered by `open_major_under_a_binder_reduces_at_the_gate`.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, LevelId, LogicPrelude, NameId,
    ReducibilityHint, build_logic_prelude,
};

/// The shared carrier: `A : Type`, two opaque inhabitants, and the logic
/// prelude (for `Eq`/`Eq.refl`, which is how a gate-level test states a
/// definitional-equality obligation).
struct Carrier {
    logic: LogicPrelude,
    anon: NameId,
    /// Universe level `1` — `A`'s sort, and every recursor's elimination level.
    one: LevelId,
    /// `Const A []`.
    a_type: ExprId,
    /// `Const a0 []`.
    a0: ExprId,
    /// `Const a1 []`.
    a1: ExprId,
}

fn carrier(kernel: &mut Kernel) -> Carrier {
    let logic = build_logic_prelude(kernel).expect("logic prelude should build");
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_sort = kernel.sort(one);

    let carrier_name = kernel.name_str(anon, "A");
    add_axiom(kernel, carrier_name, type_sort);
    let a_type = kernel.const_(carrier_name, vec![]);

    let first_name = kernel.name_str(anon, "a0");
    add_axiom(kernel, first_name, a_type);
    let a0 = kernel.const_(first_name, vec![]);

    let second_name = kernel.name_str(anon, "a1");
    add_axiom(kernel, second_name, a_type);
    let a1 = kernel.const_(second_name, vec![]);

    Carrier {
        logic,
        anon,
        one,
        a_type,
        a0,
        a1,
    }
}

fn add_axiom(kernel: &mut Kernel, name: NameId, ty: ExprId) {
    kernel
        .add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty,
        })
        .expect("test axiom should admit");
}

/// `Const <family>.rec <levels>` applied to `args`, left to right.
fn rec_app(kernel: &mut Kernel, family: NameId, levels: Vec<LevelId>, args: Vec<ExprId>) -> ExprId {
    let rec_name = kernel.name_str(family, "rec");
    let head = kernel.const_(rec_name, levels);
    args.into_iter().fold(head, |acc, arg| kernel.app(acc, arg))
}

/// Admit `def <label> : Eq.{1} A <lhs> <rhs> := Eq.refl.{1} A <rhs>`.
///
/// Admission succeeds exactly when the kernel identifies `lhs` with `rhs`: the
/// value's inferred type is `Eq A rhs rhs` and the declared type is
/// `Eq A lhs rhs`, so the gate's `TypeMismatch` check *is* the def-eq
/// obligation. Nothing here calls `def_eq` directly, because the gate is what
/// has to be right.
fn admits_equation(
    kernel: &mut Kernel,
    carrier: &Carrier,
    label: &str,
    lhs: ExprId,
    rhs: ExprId,
) -> Result<(), KernelError> {
    let eq = kernel.const_(carrier.logic.eq, vec![carrier.one]);
    let eq_a = kernel.app(eq, carrier.a_type);
    let applied = kernel.app(eq_a, lhs);
    let ty = kernel.app(applied, rhs);

    let refl = kernel.const_(carrier.logic.eq_refl, vec![carrier.one]);
    let refl_a = kernel.app(refl, carrier.a_type);
    let value = kernel.app(refl_a, rhs);

    let name = kernel.name_str(carrier.anon, label);
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// `Pair` — the positive: one constructor, no indices, not recursive, `Type`.
// ---------------------------------------------------------------------------

/// `structure Pair : Type := mk (fst snd : A)`, plus `axiom p : Pair`.
struct Pair {
    name: NameId,
    /// `Const p []` — a stuck, *closed* major.
    p: ExprId,
}

fn add_pair(kernel: &mut Kernel, carrier: &Carrier) -> Pair {
    let name = kernel.name_str(carrier.anon, "Pair");
    let ctor = kernel.name_str(name, "mk");
    let type_sort = kernel.sort(carrier.one);
    let pair_const = kernel.const_(name, vec![]);
    let ctor_ty = {
        let inner = kernel.pi(
            carrier.anon,
            carrier.a_type,
            pair_const,
            BinderInfo::Default,
        );
        kernel.pi(carrier.anon, carrier.a_type, inner, BinderInfo::Default)
    };
    kernel
        .add_inductive(name, &[], 0, type_sort, &[(ctor, ctor_ty)])
        .expect("non-recursive one-constructor structure should admit");

    let p_name = kernel.name_str(carrier.anon, "p");
    add_axiom(kernel, p_name, pair_const);
    let p = kernel.const_(p_name, vec![]);
    Pair { name, p }
}

/// `Pair.rec.{1} (fun _ => A) (fun fst snd => fst) major`, i.e. "the first
/// field, the long way round".
fn pair_first_via_rec(
    kernel: &mut Kernel,
    carrier: &Carrier,
    pair: &Pair,
    major: ExprId,
) -> ExprId {
    let pair_const = kernel.const_(pair.name, vec![]);
    let motive = kernel.lam(
        carrier.anon,
        pair_const,
        carrier.a_type,
        BinderInfo::Default,
    );
    let minor = {
        let fst = kernel.bvar(1);
        let inner = kernel.lam(carrier.anon, carrier.a_type, fst, BinderInfo::Default);
        kernel.lam(carrier.anon, carrier.a_type, inner, BinderInfo::Default)
    };
    rec_app(
        kernel,
        pair.name,
        vec![carrier.one],
        vec![motive, minor, major],
    )
}

/// The rule, at `whnf` and at the gate, with the control that says it still
/// discriminates.
///
/// `Pair.rec … p` for an opaque `p : Pair` is stuck without this rule: `p` is
/// not a constructor application and never will be. With it, `p` becomes
/// `Pair.mk p.0 p.1`, ι fires, and the whole reduces to `p.0`.
#[test]
fn a_stuck_structure_major_is_eta_expanded_and_iota_fires() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);
    let pair = add_pair(&mut kernel, &carrier);

    let via_rec = pair_first_via_rec(&mut kernel, &carrier, &pair, pair.p);
    let first = kernel.proj(pair.name, 0, pair.p);
    let second = kernel.proj(pair.name, 1, pair.p);

    let reduced = kernel.whnf(via_rec);
    assert_ne!(
        reduced, via_rec,
        "`Pair.rec (fun _ => A) (fun fst snd => fst) p` must reduce: `Pair` is a \
         non-recursive structure, so the stuck major `p` is `Pair.mk p.0 p.1`"
    );

    let positive = admits_equation(&mut kernel, &carrier, "pair_first", via_rec, first);
    assert!(
        positive.is_ok(),
        "the recursor application must be definitionally the FIRST projection. Got {positive:?}"
    );

    let control = admits_equation(&mut kernel, &carrier, "pair_second", via_rec, second);
    assert!(
        control.is_err(),
        "it must NOT be the second projection — a rule that identifies the \
         recursor application with any projection has stopped discriminating"
    );
}

/// The shape the corpus actually declines on: the major is a **free variable**
/// bound by an enclosing binder, so the rule has to fire inside the local
/// context rather than on a closed term.
///
/// `def pairFirstEq : (p : Pair) → Eq A (Pair.rec … p) p.0 := fun p => Eq.refl A p.0`
#[test]
fn open_major_under_a_binder_reduces_at_the_gate() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);
    let pair = add_pair(&mut kernel, &carrier);
    let pair_const = kernel.const_(pair.name, vec![]);

    let admit = |kernel: &mut Kernel, label: &str, field: u32| -> Result<(), KernelError> {
        let bound = kernel.bvar(0);
        let via_rec = pair_first_via_rec(kernel, &carrier, &pair, bound);
        let bound = kernel.bvar(0);
        let projection = kernel.proj(pair.name, field, bound);

        let eq = kernel.const_(carrier.logic.eq, vec![carrier.one]);
        let eq_a = kernel.app(eq, carrier.a_type);
        let applied = kernel.app(eq_a, via_rec);
        let equation = kernel.app(applied, projection);
        let ty = kernel.pi(carrier.anon, pair_const, equation, BinderInfo::Default);

        let bound = kernel.bvar(0);
        let projection = kernel.proj(pair.name, field, bound);
        let refl = kernel.const_(carrier.logic.eq_refl, vec![carrier.one]);
        let refl_a = kernel.app(refl, carrier.a_type);
        let body = kernel.app(refl_a, projection);
        let value = kernel.lam(carrier.anon, pair_const, body, BinderInfo::Default);

        let name = kernel.name_str(carrier.anon, label);
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    };

    let positive = admit(&mut kernel, "pair_first_open", 0);
    assert!(
        positive.is_ok(),
        "`fun p => Eq.refl A p.0 : (p : Pair) → Eq A (Pair.rec … p) p.0` must \
         admit — the major is a bound variable, which is the shape \
         `Nat.Linear.Poly.denote_reverse` declines on. Got {positive:?}"
    );
    let control = admit(&mut kernel, "pair_second_open", 1);
    assert!(
        control.is_err(),
        "the same statement about the SECOND projection must be refused"
    );
}

// ---------------------------------------------------------------------------
// The four exclusions. Each family fails exactly one clause of the guard, and
// each is built so that dropping that clause would let the recursor reduce to a
// named constant.
// ---------------------------------------------------------------------------

/// Two constructors: `Sum2 := inl (x : A) | inr (y : A)`, with minors `a0` and
/// `a1`. Eta-expanding a stuck `s : Sum2` would have to *choose* a constructor,
/// and choosing the first would make `Sum2.rec … s` reduce to `a0` — an
/// identification that is not merely non-definitional but **false**, since `s`
/// may be an `inr`.
#[test]
fn a_two_constructor_family_is_not_eta_expanded() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);

    let name = kernel.name_str(carrier.anon, "Sum2");
    let inl = kernel.name_str(name, "inl");
    let inr = kernel.name_str(name, "inr");
    let type_sort = kernel.sort(carrier.one);
    let sum_const = kernel.const_(name, vec![]);
    let ctor_ty = kernel.pi(carrier.anon, carrier.a_type, sum_const, BinderInfo::Default);
    kernel
        .add_inductive(name, &[], 0, type_sort, &[(inl, ctor_ty), (inr, ctor_ty)])
        .expect("two-constructor family should admit");

    let s_name = kernel.name_str(carrier.anon, "s");
    add_axiom(&mut kernel, s_name, sum_const);
    let s = kernel.const_(s_name, vec![]);

    let motive = kernel.lam(carrier.anon, sum_const, carrier.a_type, BinderInfo::Default);
    let minor_l = kernel.lam(
        carrier.anon,
        carrier.a_type,
        carrier.a0,
        BinderInfo::Default,
    );
    let minor_r = kernel.lam(
        carrier.anon,
        carrier.a_type,
        carrier.a1,
        BinderInfo::Default,
    );
    let application = rec_app(
        &mut kernel,
        name,
        vec![carrier.one],
        vec![motive, minor_l, minor_r, s],
    );

    assert_eq!(
        kernel.whnf(application),
        application,
        "`Sum2.rec … s` must stay stuck: with two constructors there is no \
         eta rule, and reducing it would pick a branch arbitrarily"
    );
    let control = admits_equation(&mut kernel, &carrier, "sum2_first", application, carrier.a0);
    assert!(
        control.is_err(),
        "`Sum2.rec (fun _ => A) (fun _ => a0) (fun _ => a1) s = a0` must be \
         REFUSED. It is admitted the moment the one-constructor clause is \
         dropped, and it is false."
    );
}

/// A recursive field: `RecBox := mk (head : A) (tail : RecBox)`. Structure eta
/// is unsound here for the same reason [`Kernel::try_eta_structure`] excludes
/// it, and `is_non_rec_structure` is where Lean says so. The minor ignores its
/// fields and returns `a0`, so dropping the clause would make the recursor
/// reduce to `a0`.
#[test]
fn a_recursive_structure_is_not_eta_expanded() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);

    let name = kernel.name_str(carrier.anon, "RecBox");
    let ctor = kernel.name_str(name, "mk");
    let type_sort = kernel.sort(carrier.one);
    let box_const = kernel.const_(name, vec![]);
    let ctor_ty = {
        let inner = kernel.pi(carrier.anon, box_const, box_const, BinderInfo::Default);
        kernel.pi(carrier.anon, carrier.a_type, inner, BinderInfo::Default)
    };
    kernel
        .add_inductive(name, &[], 0, type_sort, &[(ctor, ctor_ty)])
        .expect("recursive one-constructor family should admit");

    let b_name = kernel.name_str(carrier.anon, "b");
    add_axiom(&mut kernel, b_name, box_const);
    let b = kernel.const_(b_name, vec![]);

    let motive = kernel.lam(carrier.anon, box_const, carrier.a_type, BinderInfo::Default);
    // `fun head tail ih => a0`
    let minor = {
        let innermost = kernel.lam(
            carrier.anon,
            carrier.a_type,
            carrier.a0,
            BinderInfo::Default,
        );
        let middle = kernel.lam(carrier.anon, box_const, innermost, BinderInfo::Default);
        kernel.lam(carrier.anon, carrier.a_type, middle, BinderInfo::Default)
    };
    let application = rec_app(&mut kernel, name, vec![carrier.one], vec![motive, minor, b]);

    assert_eq!(
        kernel.whnf(application),
        application,
        "`RecBox.rec … b` must stay stuck: `RecBox` is recursive, so \
         `is_non_rec_structure` is false and there is no eta rule"
    );
    let control = admits_equation(
        &mut kernel,
        &carrier,
        "recbox_const",
        application,
        carrier.a0,
    );
    assert!(
        control.is_err(),
        "`RecBox.rec (fun _ => A) (fun _ _ _ => a0) b = a0` must be REFUSED; \
         dropping the non-recursive clause admits it"
    );
}

/// An index: `IdxBox : A → Type := mk (x : A) : IdxBox a0`. The eta expansion
/// reconstructs the constructor from the *parameters* read off the major's
/// type; an index would have to be matched instead, and Lean's
/// `is_non_rec_structure` requires `nindices == 0` for exactly that reason.
#[test]
fn an_indexed_family_is_not_eta_expanded() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);

    let name = kernel.name_str(carrier.anon, "IdxBox");
    let ctor = kernel.name_str(name, "mk");
    let type_sort = kernel.sort(carrier.one);
    // `IdxBox : A → Type`
    let family_ty = kernel.pi(carrier.anon, carrier.a_type, type_sort, BinderInfo::Default);
    let idx_at_a0 = {
        let head = kernel.const_(name, vec![]);
        kernel.app(head, carrier.a0)
    };
    // `mk : (x : A) → IdxBox a0`
    let ctor_ty = kernel.pi(carrier.anon, carrier.a_type, idx_at_a0, BinderInfo::Default);
    kernel
        .add_inductive(name, &[], 0, family_ty, &[(ctor, ctor_ty)])
        .expect("indexed one-constructor family should admit");

    let ib_name = kernel.name_str(carrier.anon, "ib");
    add_axiom(&mut kernel, ib_name, idx_at_a0);
    let ib = kernel.const_(ib_name, vec![]);

    // `motive : (i : A) → IdxBox i → Sort 1`, constantly `A`.
    let motive = {
        let head = kernel.const_(name, vec![]);
        let bound = kernel.bvar(0);
        let applied = kernel.app(head, bound);
        let inner = kernel.lam(carrier.anon, applied, carrier.a_type, BinderInfo::Default);
        kernel.lam(carrier.anon, carrier.a_type, inner, BinderInfo::Default)
    };
    let minor = kernel.lam(
        carrier.anon,
        carrier.a_type,
        carrier.a0,
        BinderInfo::Default,
    );
    let application = rec_app(
        &mut kernel,
        name,
        vec![carrier.one],
        vec![motive, minor, carrier.a0, ib],
    );

    assert_eq!(
        kernel.whnf(application),
        application,
        "`IdxBox.rec … ib` must stay stuck: the family has an index, so it is \
         not a structure for eta purposes"
    );
    let control = admits_equation(
        &mut kernel,
        &carrier,
        "idxbox_const",
        application,
        carrier.a0,
    );
    assert!(
        control.is_err(),
        "`IdxBox.rec (fun i t => A) (fun _ => a0) a0 ib = a0` must be REFUSED; \
         dropping the zero-indices clause admits it"
    );
}

/// A `Prop` structure: `PBox : Prop := mk (x : A)`. Lean excludes it explicitly
/// (`if (whnf(infer_type(e_type)) == mk_Prop()) return e;`), and this pins that
/// the exclusion is ours too. Its recursor eliminates only into `Prop`, so the
/// observation has to be made at `whnf` — proof irrelevance would make any
/// gate-level equation between two `PA`s vacuous.
#[test]
fn a_prop_structure_is_not_eta_expanded() {
    let mut kernel = Kernel::new();
    let carrier = carrier(&mut kernel);
    let zero = kernel.level_zero();
    let prop_sort = kernel.sort(zero);

    let pa_name = kernel.name_str(carrier.anon, "PA");
    add_axiom(&mut kernel, pa_name, prop_sort);
    let pa_type = kernel.const_(pa_name, vec![]);
    let pa_proof_name = kernel.name_str(carrier.anon, "pa");
    add_axiom(&mut kernel, pa_proof_name, pa_type);
    let pa_proof = kernel.const_(pa_proof_name, vec![]);

    let name = kernel.name_str(carrier.anon, "PBox");
    let ctor = kernel.name_str(name, "mk");
    let box_const = kernel.const_(name, vec![]);
    // `mk : (x : A) → PBox` — one field, and that field is *data*, so `PBox` is
    // neither K-like (its constructor has a field) nor large-eliminating.
    let ctor_ty = kernel.pi(carrier.anon, carrier.a_type, box_const, BinderInfo::Default);
    kernel
        .add_inductive(name, &[], 0, prop_sort, &[(ctor, ctor_ty)])
        .expect("Prop structure should admit");

    let q_name = kernel.name_str(carrier.anon, "q");
    add_axiom(&mut kernel, q_name, box_const);
    let q = kernel.const_(q_name, vec![]);

    let motive = kernel.lam(carrier.anon, box_const, pa_type, BinderInfo::Default);
    let minor = kernel.lam(carrier.anon, carrier.a_type, pa_proof, BinderInfo::Default);
    let application = rec_app(&mut kernel, name, vec![], vec![motive, minor, q]);

    let reduced = kernel.whnf(application);
    assert_eq!(
        reduced, application,
        "`PBox.rec … q` must stay stuck: `PBox` is a `Prop`, which Lean's \
         `to_cnstr_when_structure` excludes explicitly. Dropping that clause \
         reduces this to `pa`."
    );
    assert_ne!(
        reduced, pa_proof,
        "and in particular it must not reduce to the minor's body"
    );
}
