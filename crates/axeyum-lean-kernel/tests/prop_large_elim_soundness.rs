//! Soundness probe: unrestricted large elimination from `Prop` + proof
//! irrelevance.
//!
//! `inductive.rs:36-37` defers "the `Prop`-subsingleton large-elimination
//! subtleties" and states "The motive is always allowed to eliminate into an
//! arbitrary `Sort v` here." `tc.rs:729-743` implements proof irrelevance.
//!
//! In Lean's type theory those two are only jointly sound when a `Prop`-valued
//! inductive that eliminates into a larger universe is a *subsingleton* (Lean
//! permits large elimination only for at most-one-constructor inductives whose
//! fields are themselves proofs). A two-constructor `Prop` that eliminates into
//! `Type` is the textbook route to `False`:
//!
//! - proof irrelevance gives `a === b` for the two distinct constructors, and
//! - large elimination gives a function separating them (`a |-> yes`, `b |-> no`),
//! - so congruence + iota + transitivity yields `yes === no` for two distinct
//!   constructors of a `Type`-level enum, from which `False` follows.
//!
//! This test asserts the two ingredients directly. If both pass, the kernel is
//! unsound and this test SHOULD fail once the subsingleton restriction lands —
//! at which point `add_inductive` must reject the large-eliminating recursor for
//! `Two`, and this file should be inverted into a negative test.

use axeyum_lean_kernel::{BinderInfo, ExprNode, Kernel};

/// Declare a nullary-constructor inductive at the given sort level.
/// `level == 0` is `Prop`; `level == 1` is `Type`.
fn declare_enum_at(
    k: &mut Kernel,
    name: &str,
    ctor_strs: &[&str],
    level: usize,
) -> (axeyum_lean_kernel::NameId, Vec<axeyum_lean_kernel::NameId>) {
    let anon = k.anon();
    let ind_name = k.name_str(anon, name);
    let mut lvl = k.level_zero();
    for _ in 0..level {
        lvl = k.level_succ(lvl);
    }
    let ty = k.sort(lvl);
    let ind_const = k.const_(ind_name, vec![]);
    let ctor_names: Vec<_> = ctor_strs.iter().map(|s| k.name_str(anon, *s)).collect();
    let ctors: Vec<_> = ctor_names.iter().map(|&cn| (cn, ind_const)).collect();
    k.add_inductive(ind_name, &[], 0, ty, &ctors)
        .expect("enum should admit");
    (ind_name, ctor_names)
}

#[test]
fn prop_large_elimination_plus_proof_irrelevance_is_unsound() {
    let mut k = Kernel::new();

    // `Two : Prop` with two distinct constructors. NOT a subsingleton.
    let (two_name, two_ctors) = declare_enum_at(&mut k, "Two", &["a", "b"], 0);
    // `Answer : Type` with two distinct constructors.
    let (_answer_name, answer_ctors) = declare_enum_at(&mut k, "Answer", &["yes", "no"], 1);

    let a = k.const_(two_ctors[0], vec![]);
    let b = k.const_(two_ctors[1], vec![]);
    let yes = k.const_(answer_ctors[0], vec![]);
    let no = k.const_(answer_ctors[1], vec![]);

    // INGREDIENT 1 — proof irrelevance: `a` and `b` are both proofs of the same
    // `Prop`, so the kernel considers them definitionally equal.
    assert!(
        k.def_eq(a, b),
        "expected proof irrelevance to equate two proofs of `Two : Prop`"
    );

    // INGREDIENT 2 — large elimination: build
    //   `Two.rec.{1} (motive := fun _ => Answer) yes no <major>`
    // The motive eliminates a `Prop` into `Sort 1`, which Lean permits only for
    // subsingletons. `Two` is not one.
    let rec_name = k.name_str(two_name, "rec");
    assert!(
        k.environment().contains(rec_name),
        "recursor should have been generated"
    );

    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let rec_const = k.const_(rec_name, vec![one]); // elim universe v := 1

    let anon = k.anon();
    let two_const = k.const_(two_name, vec![]);
    let answer_const = k.const_(_answer_name, vec![]);
    // motive := fun (_ : Two) => Answer
    let motive = k.lam(anon, two_const, answer_const, BinderInfo::Default);

    let partial = k.app(rec_const, motive);
    let partial = k.app(partial, yes);
    let partial = k.app(partial, no);
    let t_a = k.app(partial, a);
    let t_b = k.app(partial, b);

    // The recursor's type must actually infer — i.e. the kernel really admitted
    // this large-eliminating recursor rather than rejecting it.
    let t_a_ty = k.infer(t_a).expect("Two.rec applied at Sort 1 should infer");
    let t_a_ty_w = k.whnf(t_a_ty);
    assert!(
        matches!(k.expr_node(t_a_ty_w), ExprNode::Const(n, _) if *n == _answer_name),
        "expected the large elimination to produce an `Answer`"
    );

    // iota-reduction separates the two constructors.
    let wa = k.whnf(t_a);
    let wb = k.whnf(t_b);
    assert!(
        matches!(k.expr_node(wa), ExprNode::Const(n, _) if *n == answer_ctors[0]),
        "Two.rec ... a should iota-reduce to `yes`"
    );
    assert!(
        matches!(k.expr_node(wb), ExprNode::Const(n, _) if *n == answer_ctors[1]),
        "Two.rec ... b should iota-reduce to `no`"
    );

    // THE CONTRADICTION. `a === b` (ingredient 1), so congruence forces
    // `Two.rec .. a === Two.rec .. b`; iota (ingredient 2) reduces those sides to
    // the distinct constructors `yes` and `no`. A consistent definitional
    // equality cannot have both. Whether `def_eq` *finds* this path depends on
    // whnf ordering, so report it rather than assert it — the inconsistency is
    // established by ingredients 1 and 2 regardless.
    let found = k.def_eq(t_a, t_b);
    println!("def_eq(Two.rec..a, Two.rec..b) = {found}  (whnf sides: yes vs no)");
    println!(
        "def_eq(yes, no) = {}  <- if true, the kernel is directly inconsistent",
        k.def_eq(yes, no)
    );
}
