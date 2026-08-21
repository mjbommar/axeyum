//! Literal `Nat` arithmetic at the trusted gate — Lean's `reduce_nat` for the
//! two-argument cases, and the guards that decide when it may fire.
//!
//! **Why this rule exists at all.** `Char`, `UInt8/16/32/64`, `USize` and `Fin`
//! are `Nat` under bounds like `2^32` and `1114112`, and every official Lean
//! export that touches them asks the kernel to compute with those numbers.
//! Reaching them by `Nat.succ` steps is not slow, it is unbounded: measured
//! 2026-08-15 on real exports, `Option.repr` and `Lean.Parser.Attr.extIff` each
//! exhausted an 8 GB address space in ~90 s without this rule and import in
//! 0.05 s with it, and `Nat.Linear.Expr.denote_toPoly_go` — one declaration in
//! `Init` — consumed 25 GB in under four minutes.
//!
//! **What it costs.** This widens definitional equality, so the guards are the
//! subject of this file, not the arithmetic. The rule is keyed on the *name*
//! `Nat.add`, exactly as Lean's kernel is; `build_nat_binop_table` narrows that
//! to a `Definition` of exactly the right type in an environment whose `Bool` is
//! Lean's. What it cannot do is verify the body, and
//! `acceleration_trusts_the_declared_type_not_the_body` says so with a test
//! rather than a comment, so nobody later mistakes the guard for more than it
//! is. That residual trust is inherent to kernel `Nat` acceleration and is
//! Lean's own; the differential tests below pin our *semantics* against a real
//! recursive definition wherever one can be written down.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, Lit, NameId, NatLit, ReducibilityHint,
};

/// A Lean-shaped `Nat`/`Bool` environment, built by hand.
///
/// Deliberately **not** `build_logic_prelude`: this fixture can construct both
/// official Lean order `[false, true]` and the negative `[true, false]` order,
/// while supplying deliberately adversarial operation bodies that the trusted
/// acceleration rule must either override or leave alone.
struct Env {
    nat: NameId,
    nat_zero: NameId,
    nat_succ: NameId,
    nat_rec: NameId,
    nat_type: ExprId,
    bool_type: ExprId,
    bool_true: NameId,
    bool_false: NameId,
    add: NameId,
    mul: NameId,
}

fn nat_lit(kernel: &mut Kernel, value: u64) -> ExprId {
    kernel.lit(Lit::Nat(NatLit::from(value)))
}

fn build(kernel: &mut Kernel, lean_bool_order: bool) -> Env {
    let anon = kernel.anon();
    let zero_level = kernel.level_zero();
    let one_level = kernel.level_succ(zero_level);
    let type0 = kernel.sort(one_level);

    // inductive Nat : Type | zero | succ (n : Nat)
    let nat = kernel.name_str(anon, "Nat");
    let nat_zero = kernel.name_str(nat, "zero");
    let nat_succ = kernel.name_str(nat, "succ");
    let nat_type = kernel.const_(nat, vec![]);
    let succ_type = kernel.pi(anon, nat_type, nat_type, BinderInfo::Default);
    kernel
        .add_inductive(
            nat,
            &[],
            0,
            type0,
            &[(nat_zero, nat_type), (nat_succ, succ_type)],
        )
        .expect("Nat must be admitted");
    let nat_rec = kernel.name_str(nat, "rec");

    // inductive Bool : Type | false | true   (Lean's order)
    let bool_name = kernel.name_str(anon, "Bool");
    let bool_false = kernel.name_str(bool_name, "false");
    let bool_true = kernel.name_str(bool_name, "true");
    let bool_type = kernel.const_(bool_name, vec![]);
    let ctors = if lean_bool_order {
        [(bool_false, bool_type), (bool_true, bool_type)]
    } else {
        [(bool_true, bool_type), (bool_false, bool_type)]
    };
    kernel
        .add_inductive(bool_name, &[], 0, type0, &ctors)
        .expect("Bool must be admitted");

    let add = kernel.name_str(nat, "add");
    let mul = kernel.name_str(nat, "mul");
    Env {
        nat,
        nat_zero,
        nat_succ,
        nat_rec,
        nat_type,
        bool_type,
        bool_true,
        bool_false,
        add,
        mul,
    }
}

/// `Nat → Nat → result`, with the binder names Lean's own export uses, so the
/// shape check is exercised on a type that is *not* the anonymous arrow the
/// kernel would build for itself.
fn binary_type(kernel: &mut Kernel, env: &Env, result: ExprId) -> ExprId {
    let anon = kernel.anon();
    let n = kernel.name_str(anon, "n");
    let m = kernel.name_str(anon, "m");
    let inner = kernel.pi(m, env.nat_type, result, BinderInfo::Default);
    kernel.pi(n, env.nat_type, inner, BinderInfo::Default)
}

/// `fun (n m : Nat) => Nat.rec (motive := fun _ => Nat) n (fun _ ih => succ ih) m`
/// — Lean's `Nat.add`, recursing on the second argument.
fn add_body(kernel: &mut Kernel, env: &Env) -> ExprId {
    let anon = kernel.anon();
    let one_level = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let motive = kernel.lam(anon, env.nat_type, env.nat_type, BinderInfo::Default);
    let succ = kernel.const_(env.nat_succ, vec![]);
    let ih = kernel.bvar(0);
    let step_body = kernel.app(succ, ih);
    let step_inner = kernel.lam(anon, env.nat_type, step_body, BinderInfo::Default);
    let step = kernel.lam(anon, env.nat_type, step_inner, BinderInfo::Default);

    let rec_const = kernel.const_(env.nat_rec, vec![one_level]);
    let applied = kernel.app(rec_const, motive);
    // `n` is under two lambdas at this point, `m` under one.
    let n = kernel.bvar(1);
    let m = kernel.bvar(0);
    let applied = kernel.app(applied, n);
    let applied = kernel.app(applied, step);
    let applied = kernel.app(applied, m);
    let inner = kernel.lam(anon, env.nat_type, applied, BinderInfo::Default);
    kernel.lam(anon, env.nat_type, inner, BinderInfo::Default)
}

/// `fun (n m : Nat) => Nat.rec (motive := fun _ => Nat) zero (fun _ ih => add ih n) m`
fn mul_body(kernel: &mut Kernel, env: &Env) -> ExprId {
    let anon = kernel.anon();
    let one_level = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let motive = kernel.lam(anon, env.nat_type, env.nat_type, BinderInfo::Default);
    let zero = kernel.const_(env.nat_zero, vec![]);
    let add = kernel.const_(env.add, vec![]);
    let ih = kernel.bvar(0);
    // Inside `fun _ ih =>` the outer `n` has crossed four binders total.
    let n = kernel.bvar(3);
    let step_body = kernel.app(add, ih);
    let step_body = kernel.app(step_body, n);
    let step_inner = kernel.lam(anon, env.nat_type, step_body, BinderInfo::Default);
    let step = kernel.lam(anon, env.nat_type, step_inner, BinderInfo::Default);

    let rec_const = kernel.const_(env.nat_rec, vec![one_level]);
    let applied = kernel.app(rec_const, motive);
    let m = kernel.bvar(0);
    let applied = kernel.app(applied, zero);
    let applied = kernel.app(applied, step);
    let applied = kernel.app(applied, m);
    let inner = kernel.lam(anon, env.nat_type, applied, BinderInfo::Default);
    kernel.lam(anon, env.nat_type, inner, BinderInfo::Default)
}

fn define(kernel: &mut Kernel, name: NameId, ty: ExprId, value: ExprId) {
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: Vec::new(),
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap_or_else(|error| panic!("definition must be admitted: {error:?}"));
}

/// Declare an operation whose body is a stub of the right *type* but the wrong
/// *meaning*. Used only where the point is what the guard does or does not see.
fn define_stub(kernel: &mut Kernel, env: &Env, segment: &str, result: ExprId, stub: ExprId) {
    let name = kernel.name_str(env.nat, segment);
    let ty = binary_type(kernel, env, result);
    let anon = kernel.anon();
    let inner = kernel.lam(anon, env.nat_type, stub, BinderInfo::Default);
    let value = kernel.lam(anon, env.nat_type, inner, BinderInfo::Default);
    define(kernel, name, ty, value);
}

/// `Nat.<segment> a b`, for an operation already declared.
fn apply(kernel: &mut Kernel, env: &Env, segment: &str, a: u64, b: u64) -> ExprId {
    let name = kernel.name_str(env.nat, segment);
    let head = kernel.const_(name, vec![]);
    let a = nat_lit(kernel, a);
    let b = nat_lit(kernel, b);
    let applied = kernel.app(head, a);
    kernel.app(applied, b)
}

fn lean_env(kernel: &mut Kernel) -> Env {
    let env = build(kernel, true);
    let nat_type = env.nat_type;
    let bool_type = env.bool_type;
    let arith = binary_type(kernel, &env, nat_type);
    let predicate = binary_type(kernel, &env, bool_type);
    let _ = predicate;

    let body = add_body(kernel, &env);
    define(kernel, env.add, arith, body);
    let body = mul_body(kernel, &env);
    define(kernel, env.mul, arith, body);

    // The remaining twelve are declared with the right type and a stub body:
    // Lean's `Nat.div`, `Nat.mod` and `Nat.gcd` are well-founded recursions
    // whose unaccelerated kernel reduction is stuck by construction, so no
    // faithful body can be written here and none would reduce if it were. The
    // conventions they are held to are the ones this file asserts directly.
    let zero = kernel.const_(env.nat_zero, vec![]);
    let false_ = kernel.const_(env.bool_false, vec![]);
    for segment in [
        "sub",
        "div",
        "mod",
        "gcd",
        "pow",
        "land",
        "lor",
        "xor",
        "shiftLeft",
        "shiftRight",
    ] {
        define_stub(kernel, &env, segment, nat_type, zero);
    }
    for segment in ["beq", "ble"] {
        define_stub(kernel, &env, segment, bool_type, false_);
    }
    env
}

// ---------------------------------------------------------------------------
// The rule fires, and agrees with a real recursive definition
// ---------------------------------------------------------------------------

/// The differential that matters: the accelerated answer equals the answer the
/// *environment's own definition* computes, for the two operations whose Lean
/// definitions are structural recursions that a kernel can actually run.
///
/// `Trusted.add` is declared with the **same value expression** as `Nat.add`, so
/// δ-unfolding it reaches the identical body — but the acceleration is keyed on
/// the name `Nat.add`, so `Trusted.add` reduces by ι alone. Agreement between
/// the two is therefore evidence about the arithmetic, not a tautology.
#[test]
fn accelerated_addition_agrees_with_unaccelerated_recursion() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let anon = kernel.anon();
    let trusted = kernel.name_str(anon, "Trusted");

    for (name, segment, cases) in [
        (
            "add",
            "add",
            vec![(0_u64, 0_u64, 0_u64), (7, 5, 12), (0, 9, 9), (9, 0, 9)],
        ),
        (
            "mul",
            "mul",
            vec![(0, 6, 0), (6, 0, 0), (1, 7, 7), (4, 5, 20), (3, 3, 9)],
        ),
    ] {
        let source = kernel.name_str(env.nat, segment);
        let Some(Declaration::Definition { ty, value, .. }) =
            kernel.environment().get(source).cloned()
        else {
            panic!("{segment} must be a definition");
        };
        let copy = kernel.name_str(trusted, name);
        define(&mut kernel, copy, ty, value);

        for (a, b, expected) in cases {
            let accelerated = apply(&mut kernel, &env, segment, a, b);
            let expected_lit = nat_lit(&mut kernel, expected);
            assert!(
                kernel.def_eq(accelerated, expected_lit),
                "accelerated Nat.{segment} {a} {b} should be {expected}"
            );

            let head = kernel.const_(copy, vec![]);
            let x = nat_lit(&mut kernel, a);
            let y = nat_lit(&mut kernel, b);
            let applied = kernel.app(head, x);
            let unaccelerated = kernel.app(applied, y);
            assert!(
                kernel.def_eq(unaccelerated, expected_lit),
                "the same body, unaccelerated, must give {expected} for {segment} {a} {b}"
            );
            assert!(
                kernel.def_eq(accelerated, unaccelerated),
                "accelerated and unaccelerated Nat.{segment} {a} {b} must agree"
            );
        }
    }
}

/// The totality conventions are Lean's, and they are the ones a partial-looking
/// operator gets wrong. `x / 0 = 0` and `x % 0 = x` are not the mathematician's
/// conventions; they are the kernel's, and a differential fuzz that never
/// generates a zero divisor cannot see them (CLAUDE.md's standing rule).
#[test]
fn totality_conventions_match_lean() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    for (segment, a, b, expected) in [
        ("div", 7_u64, 0_u64, 0_u64),
        ("div", 0, 0, 0),
        ("div", 17, 5, 3),
        ("mod", 7, 0, 7),
        ("mod", 0, 0, 0),
        ("mod", 17, 5, 2),
        ("sub", 3, 9, 0),
        ("sub", 9, 3, 6),
        ("sub", 0, 0, 0),
        ("gcd", 0, 12, 12),
        ("gcd", 12, 0, 12),
        ("gcd", 0, 0, 0),
        ("gcd", 12, 18, 6),
        ("pow", 2, 0, 1),
        ("pow", 0, 0, 1),
        ("pow", 0, 3, 0),
        ("pow", 2, 32, 4_294_967_296),
        ("land", 12, 10, 8),
        ("lor", 12, 10, 14),
        ("xor", 12, 10, 6),
        ("shiftLeft", 1, 32, 4_294_967_296),
        ("shiftRight", 4_294_967_296, 32, 1),
        ("shiftRight", 5, 9, 0),
    ] {
        let applied = apply(&mut kernel, &env, segment, a, b);
        let expected_lit = nat_lit(&mut kernel, expected);
        assert!(
            kernel.def_eq(applied, expected_lit),
            "Nat.{segment} {a} {b} should reduce to {expected}"
        );
    }
}

/// The two predicates return Lean's `Bool` constructors, and the *wrong* one is
/// refused. A test that only checked `beq 3 3 ≡ true` would pass just as well
/// if the rule returned `true` unconditionally.
#[test]
fn predicates_return_the_right_bool_constructor_and_refuse_the_other() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let true_ = kernel.const_(env.bool_true, vec![]);
    let false_ = kernel.const_(env.bool_false, vec![]);
    for (segment, a, b, holds) in [
        ("beq", 3_u64, 3_u64, true),
        ("beq", 3, 4, false),
        ("beq", 0, 0, true),
        ("beq", 4_294_967_296, 4_294_967_296, true),
        ("ble", 3, 4, true),
        ("ble", 4, 4, true),
        ("ble", 5, 4, false),
        ("ble", 0, 0, true),
    ] {
        let applied = apply(&mut kernel, &env, segment, a, b);
        let (wanted, refused) = if holds {
            (true_, false_)
        } else {
            (false_, true_)
        };
        assert!(
            kernel.def_eq(applied, wanted),
            "Nat.{segment} {a} {b} has the wrong truth value"
        );
        assert!(
            !kernel.def_eq(applied, refused),
            "Nat.{segment} {a} {b} must not also equal the other Bool constructor"
        );
    }
}

/// Arbitrary precision, not machine words: `2^64` and beyond are ordinary
/// values here, and the operations that could silently wrap must not.
#[test]
fn arithmetic_is_arbitrary_precision() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let anon = kernel.anon();
    let big = "18446744073709551616"; // 2^64
    let bigger = "340282366920938463463374607431768211456"; // 2^128

    let name = kernel.name_str(env.nat, "mul");
    let head = kernel.const_(name, vec![]);
    let x = kernel.lit(Lit::Nat(NatLit::from_decimal(big).expect("2^64")));
    let applied = kernel.app(head, x);
    let applied = kernel.app(applied, x);
    let expected = kernel.lit(Lit::Nat(NatLit::from_decimal(bigger).expect("2^128")));
    assert!(
        kernel.def_eq(applied, expected),
        "2^64 * 2^64 must be 2^128, not a wrapped machine word"
    );
    let _ = anon;
}

// ---------------------------------------------------------------------------
// Negative: what the rule must NOT do
// ---------------------------------------------------------------------------

/// A false equation stays false. The whole point of a reduction rule is that it
/// decides equalities, so the rule earns its keep only if the ones it decides
/// the other way are refused.
#[test]
fn false_equations_are_still_refused() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    for (segment, a, b, wrong) in [
        ("add", 2_u64, 2_u64, 5_u64),
        ("add", 0, 0, 1),
        ("mul", 6, 7, 41),
        ("div", 7, 0, 7), // the *other* division-by-zero convention
        ("mod", 7, 0, 0), // the *other* remainder-by-zero convention
        ("sub", 3, 9, 6), // wrapping subtraction
        ("gcd", 12, 18, 3),
        ("pow", 2, 10, 100),
        ("shiftRight", 5, 1, 3),
    ] {
        let applied = apply(&mut kernel, &env, segment, a, b);
        let wrong_lit = nat_lit(&mut kernel, wrong);
        assert!(
            !kernel.def_eq(applied, wrong_lit),
            "Nat.{segment} {a} {b} must not be definitionally {wrong}"
        );
    }
}

/// An operation applied to something that is not a literal is not evaluated by
/// this rule. The rule computes with *values*; it must not invent one for an
/// open term.
///
/// Written on `Nat.add`, whose declared body really does recurse on its second
/// argument, so what is being observed is the accelerated path declining rather
/// than a definition with nothing to unfold. The result is a stuck recursor
/// application: the assertion is that it is not a literal, not that `whnf` was a
/// no-op — δ and β fire regardless, and they should.
#[test]
fn a_non_literal_argument_is_not_evaluated_to_a_value() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let head = kernel.const_(env.add, vec![]);
    let free = kernel.fvar(9_001);
    let seven = nat_lit(&mut kernel, 7);
    let applied = kernel.app(head, seven);
    let applied = kernel.app(applied, free);
    let normal = kernel.whnf(applied);
    assert!(
        !matches!(
            kernel.expr_node(normal),
            axeyum_lean_kernel::ExprNode::Lit(_)
        ),
        "an open argument must not produce a literal"
    );
    for value in [0_u64, 7, 8] {
        let literal = nat_lit(&mut kernel, value);
        assert!(
            !kernel.def_eq(applied, literal),
            "`Nat.add 7 x` for an open `x` must not be definitionally {value}"
        );
    }
}

/// Under-application and over-application are not this rule's shape. Lean checks
/// `nargs == 2` exactly, and so must we: a partially applied `Nat.add 3` is a
/// function, and `Nat.add 3 4 x` is ill-typed nonsense that the rule must not
/// silently rewrite.
#[test]
fn only_an_exactly_binary_application_is_evaluated() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let name = kernel.name_str(env.nat, "add");
    let head = kernel.const_(name, vec![]);
    let three = nat_lit(&mut kernel, 3);
    let four = nat_lit(&mut kernel, 4);

    let partial = kernel.app(head, three);
    let seven = nat_lit(&mut kernel, 7);
    assert!(
        !kernel.def_eq(partial, seven),
        "a partially applied operation is not a number"
    );

    let full = kernel.app(partial, four);
    let over = kernel.app(full, three);
    let normal = kernel.whnf(over);
    // The head reduces (it is `Nat.add 3 4`), but the extra argument must
    // survive: the result is an application, never the bare literal 7.
    assert_ne!(
        normal, seven,
        "an over-applied operation must not be evaluated as if it were binary"
    );
}

/// The bound Lean puts on `Nat.pow` (`ReducePowMaxExp`, `1 << 24`). Beyond it
/// the rule does not fire, and the term stays stuck rather than the kernel
/// trying to build a number with millions of digits.
#[test]
fn a_huge_exponent_leaves_pow_stuck_instead_of_exploding() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let name = kernel.name_str(env.nat, "pow");
    let head = kernel.const_(name, vec![]);
    let two = nat_lit(&mut kernel, 2);
    let huge = nat_lit(&mut kernel, 1 << 25);
    let applied = kernel.app(head, two);
    let applied = kernel.app(applied, huge);
    let normal = kernel.whnf(applied);
    assert!(
        !matches!(
            kernel.expr_node(normal),
            axeyum_lean_kernel::ExprNode::Lit(_)
        ),
        "an exponent above Lean's ReducePowMaxExp must leave `pow` stuck, not evaluated"
    );
    let one = nat_lit(&mut kernel, 1);
    assert!(
        !kernel.def_eq(applied, one),
        "an out-of-bound power must stay stuck, not collapse to a value"
    );
}

/// A universe-instantiated head is not this rule's shape. `Nat.add` carries no
/// universe parameters, so `@Nat.add.{0}` is not it; Lean's kernel matches the
/// constant itself, and a level argument means the head is something else.
#[test]
fn a_universe_instantiated_head_is_not_accelerated() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let level = kernel.level_zero();
    let head = kernel.const_(env.add, vec![level]);
    let three = nat_lit(&mut kernel, 3);
    let four = nat_lit(&mut kernel, 4);
    let applied = kernel.app(head, three);
    let applied = kernel.app(applied, four);
    let normal = kernel.whnf(applied);
    assert!(
        !matches!(
            kernel.expr_node(normal),
            axeyum_lean_kernel::ExprNode::Lit(_)
        ),
        "a head carrying universe arguments must not be evaluated as `Nat.add`"
    );
}

/// The type guard. `Nat.add` declared with a type that is not
/// `Nat → Nat → Nat` gets no rule, whatever it is named.
#[test]
fn a_wrongly_typed_declaration_is_not_accelerated() {
    let mut kernel = Kernel::new();
    let env = build(&mut kernel, true);
    let anon = kernel.anon();
    // `Nat.add : Nat → Nat` — one argument short.
    let unary = kernel.pi(anon, env.nat_type, env.nat_type, BinderInfo::Default);
    let x = kernel.bvar(0);
    let body = kernel.lam(anon, env.nat_type, x, BinderInfo::Default);
    define(&mut kernel, env.add, unary, body);

    let head = kernel.const_(env.add, vec![]);
    let three = nat_lit(&mut kernel, 3);
    let four = nat_lit(&mut kernel, 4);
    let applied = kernel.app(head, three);
    let applied = kernel.app(applied, four);
    let seven = nat_lit(&mut kernel, 7);
    assert!(
        !kernel.def_eq(applied, seven),
        "an operation of the wrong type must not be evaluated as addition"
    );
}

/// The kind guard. An `axiom` or an `opaque` named `Nat.add` has no value the
/// kernel may unfold, and it does not get a reduction rule either.
#[test]
fn an_axiom_or_opaque_named_like_an_operation_is_not_accelerated() {
    for as_axiom in [true, false] {
        let mut kernel = Kernel::new();
        let env = build(&mut kernel, true);
        let nat_type = env.nat_type;
        let ty = binary_type(&mut kernel, &env, nat_type);
        let declaration = if as_axiom {
            Declaration::Axiom {
                name: env.add,
                uparams: Vec::new(),
                ty,
            }
        } else {
            let anon = kernel.anon();
            let zero = kernel.const_(env.nat_zero, vec![]);
            let inner = kernel.lam(anon, nat_type, zero, BinderInfo::Default);
            let value = kernel.lam(anon, nat_type, inner, BinderInfo::Default);
            Declaration::Opaque {
                name: env.add,
                uparams: Vec::new(),
                ty,
                value,
            }
        };
        kernel
            .add_declaration(declaration)
            .expect("the declaration itself is well-formed");

        let head = kernel.const_(env.add, vec![]);
        let three = nat_lit(&mut kernel, 3);
        let four = nat_lit(&mut kernel, 4);
        let applied = kernel.app(head, three);
        let applied = kernel.app(applied, four);
        let seven = nat_lit(&mut kernel, 7);
        assert!(
            !kernel.def_eq(applied, seven),
            "a non-definition must not be evaluated as addition (axiom={as_axiom})"
        );
    }
}

/// The `Bool` guard is load-bearing rather than decorative. A non-Lean fixture
/// with constructors `[true, false]` would make accelerated `Nat.beq` return
/// the opposite truth value. In that fixture no operation is accelerated at
/// all, including arithmetic, because the table is refused as a whole.
#[test]
fn a_bool_whose_constructors_are_in_the_wrong_order_disables_the_table() {
    let mut kernel = Kernel::new();
    let env = build(&mut kernel, false);
    let nat_type = env.nat_type;
    let arith = binary_type(&mut kernel, &env, nat_type);
    let body = add_body(&mut kernel, &env);
    define(&mut kernel, env.add, arith, body);

    let head = kernel.const_(env.add, vec![]);
    let seven = nat_lit(&mut kernel, 7);
    let five = nat_lit(&mut kernel, 5);
    let applied = kernel.app(head, seven);
    let applied = kernel.app(applied, five);

    // The definition still computes by ι — this is a *disabled rule*, not a
    // broken kernel — but nothing here is the accelerated path.
    let twelve = nat_lit(&mut kernel, 12);
    assert!(
        kernel.def_eq(applied, twelve),
        "ordinary recursion must still compute the answer"
    );

    // What is gone is the acceleration, and `Nat.beq` shows it directly: with a
    // stub body of `fun _ _ => Bool.false` the *only* way `beq 3 3` could be
    // `Bool.true` is the rule firing. In the Lean-ordered environment it does
    // (`acceleration_trusts_the_declared_type_not_the_body`); here it must not.
    let bool_type = env.bool_type;
    let false_ = kernel.const_(env.bool_false, vec![]);
    define_stub(&mut kernel, &env, "beq", bool_type, false_);
    let applied = apply(&mut kernel, &env, "beq", 3, 3);
    let true_ = kernel.const_(env.bool_true, vec![]);
    assert!(
        !kernel.def_eq(applied, true_),
        "with a non-Lean `Bool` the predicate rule must not fire; it would have \
         returned the opposite constructor"
    );
    assert!(
        kernel.def_eq(applied, false_),
        "the declared body is what decides it when the rule is refused"
    );
}

/// **The trust boundary, stated as a test.** The rule checks the name, the
/// declaration kind and the type; it does not and cannot check the body. An
/// environment that declares `Nat.beq` as the constant `false` is still
/// evaluated as equality. This is Lean's own trust model for kernel `Nat`
/// acceleration, and the reason `axeyum-lean-import` consumes official exports
/// only. Recorded here so that a future reader does not mistake the guard for a
/// verification.
#[test]
fn acceleration_trusts_the_declared_type_not_the_body() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    // `Nat.beq` was declared above with the body `fun _ _ => Bool.false`.
    let applied = apply(&mut kernel, &env, "beq", 3, 3);
    let true_ = kernel.const_(env.bool_true, vec![]);
    assert!(
        kernel.def_eq(applied, true_),
        "the rule evaluates by name and type, not by the declared body"
    );
}

// ---------------------------------------------------------------------------
// Where the rule is called from, and what the `has_fvars` guard gives up
// (ADR-0536)
// ---------------------------------------------------------------------------

/// `Nat.rec.{1} (motive := fun _ => Nat) 111 (fun _ _ => 222) major`.
///
/// A probe for *where* the acceleration runs. `Kernel::reduce_rec` normalizes
/// its major with `whnf_core` — the δ-performing loop — so which minor this
/// selects reports whether the acceleration was reached from that loop or the
/// major was δ-unfolded to its declared body instead. `111` and `222` are
/// arbitrary and distinct; nothing else in the fixture produces either.
fn rec_on_major(kernel: &mut Kernel, env: &Env, major: ExprId) -> ExprId {
    let anon = kernel.anon();
    let one_level = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let motive = kernel.lam(anon, env.nat_type, env.nat_type, BinderInfo::Default);
    let on_zero = nat_lit(kernel, 111);
    let on_succ = nat_lit(kernel, 222);
    let step_inner = kernel.lam(anon, env.nat_type, on_succ, BinderInfo::Default);
    let step = kernel.lam(anon, env.nat_type, step_inner, BinderInfo::Default);

    let rec_const = kernel.const_(env.nat_rec, vec![one_level]);
    let applied = kernel.app(rec_const, motive);
    let applied = kernel.app(applied, on_zero);
    let applied = kernel.app(applied, step);
    kernel.app(applied, major)
}

/// `Nat.mod arg 0` — an operation whose *declared body* is the stub `fun _ _ =>
/// Nat.zero` and whose *accelerated* value is Lean's `x % 0 = x`. The two
/// answers differ for every nonzero `x`, so this application is a discriminator
/// between "the acceleration fired" and "the declaration decided".
fn mod_by_zero(kernel: &mut Kernel, env: &Env, arg: ExprId) -> ExprId {
    let name = kernel.name_str(env.nat, "mod");
    let head = kernel.const_(name, vec![]);
    let zero = nat_lit(kernel, 0);
    let applied = kernel.app(head, arg);
    kernel.app(applied, zero)
}

/// `(fun _ : Nat => 7) x` — a term that *mentions* the free variable `x` and
/// whose weak head normal form is nonetheless the literal `7`.
///
/// This is the exact class the `has_fvars` guard gives up, and it is the reason
/// the guard is a decision rather than an optimization: `has_fvars` is
/// structural, so it cannot see that this argument reduces to a literal.
fn seven_mentioning(kernel: &mut Kernel, env: &Env, variable: ExprId) -> ExprId {
    let anon = kernel.anon();
    let seven = nat_lit(kernel, 7);
    let constant = kernel.lam(anon, env.nat_type, seven, BinderInfo::Default);
    kernel.app(constant, variable)
}

/// **The δ-loop call site.** The acceleration is called from `Kernel::whnf_core`
/// — after the δ-free step and before δ — which is Lean's `whnf`
/// (`type_checker.cpp:670`), not Lean's `whnf_core`. `reduce_rec` normalizes its
/// major there, so a recursor whose major is `Nat.mod 7 0` selects the successor
/// minor (the accelerated `7`) rather than the zero minor (the stub body).
///
/// Deleting the `reduce_nat_binop` call in `Kernel::whnf_core` flips this to
/// `111` and kills this test and nothing else in the file.
#[test]
fn a_recursor_major_is_accelerated_by_the_delta_loop() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let seven = nat_lit(&mut kernel, 7);
    let major = mod_by_zero(&mut kernel, &env, seven);
    let probe = rec_on_major(&mut kernel, &env, major);

    let on_succ = nat_lit(&mut kernel, 222);
    let on_zero = nat_lit(&mut kernel, 111);
    assert!(
        kernel.def_eq(probe, on_succ),
        "`Nat.mod 7 0` must accelerate to 7 while the recursor normalizes its major"
    );
    assert!(
        !kernel.def_eq(probe, on_zero),
        "the stub body must not be what decides a closed major"
    );
}

/// **What the guard costs, at the δ-loop call site.** The same probe with a
/// major that *mentions* a free variable, and whose argument still reduces to
/// the literal `7`. Lean's `whnf` would accelerate it; we do not, because the
/// `has_fvars` guard Lean applies only in `lazy_delta_reduction`
/// (`type_checker.cpp:978`) is applied here too (ADR-0536).
///
/// So the *declaration* decides instead, and the answer is the stub's `111`.
/// That is the whole observable identification cost of the guard, written down
/// as an assertion rather than as prose: **deleting the `!self.has_fvars(whnfd)`
/// guard in `Kernel::whnf_core` flips this to `222` and kills this test.**
///
/// Note what is *not* lost: the term is still identified with something — the
/// kernel does not get stuck, it computes the environment's own answer. The
/// hazard the acceleration exists to remove (an unbounded successor chain) is
/// only reachable for a declaration whose body really does recurse, and there
/// the answers agree.
#[test]
fn an_open_recursor_major_is_decided_by_the_declaration_not_the_acceleration() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let anon = kernel.anon();

    let variable = kernel.bvar(0);
    let argument = seven_mentioning(&mut kernel, &env, variable);
    let major = mod_by_zero(&mut kernel, &env, argument);
    let probe = rec_on_major(&mut kernel, &env, major);
    let probe = kernel.lam(anon, env.nat_type, probe, BinderInfo::Default);

    let on_zero = nat_lit(&mut kernel, 111);
    let stub_answer = kernel.lam(anon, env.nat_type, on_zero, BinderInfo::Default);
    let on_succ = nat_lit(&mut kernel, 222);
    let accelerated_answer = kernel.lam(anon, env.nat_type, on_succ, BinderInfo::Default);

    assert!(
        kernel.def_eq(probe, stub_answer),
        "an open major must be decided by the declaration's own body"
    );
    assert!(
        !kernel.def_eq(probe, accelerated_answer),
        "the acceleration must not fire on a major that mentions a free variable"
    );
}

/// **What the guard costs, at the lazy-delta call site.** The other of the two
/// call sites, reached from `def_eq` directly: `def_eq_core` normalizes both
/// sides with the δ-*free* step (Lean's `whnf_core`, which carries no `Nat`
/// rule) and then enters `lazy_delta_step`, where Lean tries `reduce_nat` under
/// `!has_fvar(t_n) && !has_fvar(s_n)`.
///
/// **Deleting the `has_fvars` conjunction in `Kernel::lazy_delta_step` flips
/// both assertions and kills this test.** Deleting the whole `reduce_nat_binop`
/// block there instead kills `totality_conventions_match_lean`, which is the
/// closed control for the same site.
#[test]
fn an_open_operand_is_decided_by_the_declaration_in_lazy_delta() {
    let mut kernel = Kernel::new();
    let env = lean_env(&mut kernel);
    let anon = kernel.anon();

    let variable = kernel.bvar(0);
    let argument = seven_mentioning(&mut kernel, &env, variable);
    let open_mod = mod_by_zero(&mut kernel, &env, argument);
    let probe = kernel.lam(anon, env.nat_type, open_mod, BinderInfo::Default);

    let zero = kernel.const_(env.nat_zero, vec![]);
    let stub_answer = kernel.lam(anon, env.nat_type, zero, BinderInfo::Default);
    let seven = nat_lit(&mut kernel, 7);
    let accelerated_answer = kernel.lam(anon, env.nat_type, seven, BinderInfo::Default);

    assert!(
        kernel.def_eq(probe, stub_answer),
        "an open `Nat.mod` must δ-unfold to its declared body"
    );
    assert!(
        !kernel.def_eq(probe, accelerated_answer),
        "the acceleration must not fire when either side mentions a free variable"
    );
}
