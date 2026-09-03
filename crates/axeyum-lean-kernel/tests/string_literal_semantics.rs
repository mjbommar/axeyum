//! Primitive `String` literal semantics (ADR-0366): typing, the Unicode-scalar
//! `String.ofList` expansion, and the three reduction hooks -- with one negative
//! control per bootstrap clause.
//!
//! The environment these run in, and why it is built rather than imported, is
//! documented in [`support/lean_shaped_string.rs`](support/lean_shaped_string.rs).

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, KernelError, Lit};

#[path = "support/lean_shaped_string.rs"]
mod lean_shaped_string;

use lean_shaped_string::{Mutation, lean_shaped_kernel, list_of_scalars, of_list_of_scalars};

// ---------------------------------------------------------------------------
// Typing
// ---------------------------------------------------------------------------

#[test]
fn a_string_literal_infers_as_the_checked_string_constant() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    for payload in [
        "",
        "ab",
        "\u{0}\u{1}\u{1f}",
        "\u{e9}",
        "e\u{301}",
        "\u{1f642}",
        "λ→\u{1f642}",
    ] {
        let literal = kernel.lit(Lit::Str(payload.to_owned()));
        assert_eq!(
            kernel.infer(literal).expect("literal types"),
            env.string_type,
            "payload {payload:?}"
        );
    }
}

/// Every clause of the bootstrap, removed or corrupted one at a time. The
/// positive case is asserted in the same loop so a control cannot pass by the
/// rule having been disabled globally.
#[test]
fn every_bootstrap_clause_is_load_bearing() {
    let controls = [
        Mutation::NoOfList,
        Mutation::OfListIsAxiom,
        Mutation::OfListWrongCodomain,
        Mutation::OfListIsPolymorphic,
        Mutation::NoCharOfNat,
        Mutation::CharOfNatWrongDomain,
        Mutation::CharOfNatIsAxiom,
        Mutation::ListConstructorsReordered,
        Mutation::StringConstructorRenamed,
        Mutation::CharConstructorRenamed,
        Mutation::CharAtUniverseOne,
    ];

    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    assert_eq!(
        kernel.infer(literal).expect("the unmutated shape types"),
        env.string_type
    );
    assert!(
        kernel.level_is_zero(env.list_level),
        "the unmutated shape's `String.ofList` domain is `List.{{0}} Char`"
    );

    for mutation in controls {
        let (mut kernel, env) = lean_shaped_kernel(mutation);
        // `CharAtUniverseOne` is the only control that moves a universe, and it
        // has to keep moving exactly ONE: the level `String.ofList`'s `List`
        // argument is instantiated at. `String` itself follows `Char` up (a
        // `Type 1` field cannot sit in a `Type 0` structure — ADR-1495), which
        // the bootstrap never inspects, so this assertion is what stops the
        // control from degenerating into "some other clause broke".
        if mutation == Mutation::CharAtUniverseOne {
            assert!(
                !kernel.level_is_zero(env.list_level),
                "CharAtUniverseOne must leave a NONZERO list level to reject on"
            );
        }
        let literal = kernel.lit(Lit::Str("ab".to_owned()));
        let error = kernel
            .infer(literal)
            .expect_err("a mutated bootstrap must not type a string literal");
        assert!(
            matches!(error, KernelError::StringLiteralBootstrapMismatch { .. }),
            "{mutation:?}: {error:?}"
        );
    }
}

/// The `String` bootstrap stands on the `Nat` one, so an environment with no
/// canonical `Nat` types no string literal either — even though the reported
/// name is the `String` one.
#[test]
fn no_nat_bootstrap_means_no_string_bootstrap() {
    let mut kernel = Kernel::new();
    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    assert!(matches!(
        kernel.infer(literal),
        Err(KernelError::StringLiteralBootstrapMismatch { string: None })
    ));
}

// ---------------------------------------------------------------------------
// The expansion: Unicode scalars, in order
// ---------------------------------------------------------------------------

/// The conversion is over **Unicode scalar values**, exactly as Lean's
/// `utf8_decode` is, and the ordered controls next to each positive case are the
/// point: a byte-oriented conversion, a reordered list, or a dropped scalar all
/// have to be rejected by the same rule that accepts the right one.
#[test]
fn the_expansion_is_scalar_ordered_and_exact() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);

    // Empty, ASCII, control, BMP, supplementary plane.
    for (payload, scalars) in [
        ("", &[][..]),
        ("ab", &[0x61, 0x62][..]),
        ("\u{0}\u{1f}", &[0x00, 0x1f][..]),
        ("\u{e9}", &[0xe9][..]),
        ("\u{1f642}", &[0x1_f642][..]),
        ("a\u{e9}\u{1f642}", &[0x61, 0xe9, 0x1_f642][..]),
    ] {
        let literal = kernel.lit(Lit::Str(payload.to_owned()));
        let expected = of_list_of_scalars(&mut kernel, &env, scalars);
        assert!(
            kernel.def_eq(literal, expected),
            "payload {payload:?} did not expand to its scalars"
        );
        assert!(
            kernel.def_eq(expected, literal),
            "payload {payload:?} is not symmetric"
        );
    }

    // Multi-byte UTF-8 must not become multiple characters: `é` is one scalar
    // `0xE9`, never the two bytes `0xC3 0xA9` its UTF-8 encoding uses.
    let literal = kernel.lit(Lit::Str("\u{e9}".to_owned()));
    let as_bytes = of_list_of_scalars(&mut kernel, &env, &[0xc3, 0xa9]);
    assert!(!kernel.def_eq(literal, as_bytes));

    // Composed and decomposed sequences stay distinct: no normalization happens.
    let composed = kernel.lit(Lit::Str("\u{e9}".to_owned()));
    let decomposed = kernel.lit(Lit::Str("e\u{301}".to_owned()));
    assert!(!kernel.def_eq(composed, decomposed));
    let decomposed_scalars = of_list_of_scalars(&mut kernel, &env, &[0x65, 0x301]);
    assert!(kernel.def_eq(decomposed, decomposed_scalars));
    assert!(!kernel.def_eq(composed, decomposed_scalars));

    // Order is preserved, not merely the multiset.
    let ab = kernel.lit(Lit::Str("ab".to_owned()));
    let reversed = of_list_of_scalars(&mut kernel, &env, &[0x62, 0x61]);
    assert!(!kernel.def_eq(ab, reversed));

    // Two different literals are never definitionally equal.
    let ba = kernel.lit(Lit::Str("ba".to_owned()));
    assert!(!kernel.def_eq(ab, ba));
    let truncated = kernel.lit(Lit::Str("a".to_owned()));
    assert!(!kernel.def_eq(ab, truncated));
}

/// A bare literal is already in weak head normal form: nothing expands it until
/// a rule asks for constructor form. Lean keeps literals compact for the same
/// reason, and eager expansion would multiply memory on every `Repr` instance in
/// the corpus.
#[test]
fn ordinary_whnf_does_not_expand_a_literal() {
    let (mut kernel, _) = lean_shaped_kernel(Mutation::None);
    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    assert_eq!(kernel.whnf(literal), literal);
}

// ---------------------------------------------------------------------------
// Projection and recursor reduction
// ---------------------------------------------------------------------------

/// Lean's `reduce_proj_core` converts a projected literal before selecting a
/// field. This is the hook that carries the weight: `try_string_lit_expansion`
/// almost never fires, because lazy delta has already unfolded the
/// `String.ofList` head by the time definitional equality reaches it, and it is
/// *structure eta* plus this projection rule that actually identifies a literal
/// with a constructor application.
#[test]
fn projecting_a_literal_computes_through_the_expansion() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    let projection = kernel.proj(env.string, 0, literal);
    let expected = list_of_scalars(&mut kernel, &env, &[0x61, 0x62]);
    assert!(kernel.def_eq(projection, expected));

    let wrong = list_of_scalars(&mut kernel, &env, &[0x62, 0x61]);
    assert!(!kernel.def_eq(projection, wrong));
}

/// Structure eta over a literal: the literal and the constructor application it
/// denotes are identified field by field, through the projection rule above.
#[test]
fn a_literal_is_definitionally_its_constructor_application() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    let fields = list_of_scalars(&mut kernel, &env, &[0x61, 0x62]);
    let ctor = kernel.const_(env.string_ctor, vec![]);
    let application = kernel.app(ctor, fields);
    assert!(kernel.def_eq(literal, application));
    assert!(kernel.def_eq(application, literal));
}

/// The recursor hook: a `String.rec` whose major premise is a literal selects
/// the `String.ofByteArray` rule after the expansion is normalized. The identity
/// motive makes the reduct observable without any further machinery.
#[test]
fn a_recursor_reduces_through_a_literal_major() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let anon = kernel.anon();
    let rec_name = kernel.name_str(env.string, "rec");
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let rec_const = kernel.const_(rec_name, vec![one]);

    // motive := fun (_ : String) => List Char
    let list_char = env.list_char;
    let motive = kernel.lam(anon, env.string_type, list_char, BinderInfo::Default);
    // minor := fun (bytes : List Char) => bytes
    let minor = {
        let body = kernel.bvar(0);
        kernel.lam(anon, list_char, body, BinderInfo::Default)
    };

    let literal = kernel.lit(Lit::Str("ab".to_owned()));
    let application = {
        let step = kernel.app(rec_const, motive);
        let step = kernel.app(step, minor);
        kernel.app(step, literal)
    };
    let expected = list_of_scalars(&mut kernel, &env, &[0x61, 0x62]);
    assert_eq!(kernel.whnf(application), kernel.whnf(expected));
}

// ---------------------------------------------------------------------------
// The rule does not fire where Lean's does not
// ---------------------------------------------------------------------------

/// Lean compares `app_fn(s)` against the bare constant `String.ofList`, so the
/// expansion fires only on a one-argument application of exactly that constant.
/// A bare constant, a different head, and an alias are all inert.
#[test]
fn the_expansion_fires_only_on_an_immediate_of_list_application() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let literal = kernel.lit(Lit::Str("ab".to_owned()));

    // The bare constant is not an application.
    let bare = kernel.const_(env.of_list, vec![]);
    assert!(!kernel.def_eq(literal, bare));

    // A different head over the very same list is not `String.ofList`.
    let list = list_of_scalars(&mut kernel, &env, &[0x61, 0x62]);
    let alias = {
        let anon = kernel.anon();
        let name = kernel.name_str(anon, "notOfList");
        let ty = kernel.pi(anon, env.list_char, env.string_type, BinderInfo::Default);
        let value = {
            let list_char = env.list_char;
            let of_list = kernel.const_(env.of_list, vec![]);
            let body = {
                let arg = kernel.bvar(0);
                kernel.app(of_list, arg)
            };
            kernel.lam(anon, list_char, body, BinderInfo::Default)
        };
        kernel
            .add_declaration(Declaration::Opaque {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .expect("the alias admits");
        let head = kernel.const_(name, vec![]);
        kernel.app(head, list)
    };
    // `Opaque` never unfolds, so nothing but the string rule could identify
    // these two — and the string rule refuses, because the head is not
    // `String.ofList`.
    assert!(!kernel.def_eq(literal, alias));
}

// ---------------------------------------------------------------------------
// Our own preludes, and the hook that Lean 4.30 itself left dead
// ---------------------------------------------------------------------------

/// The solver-proof reconstruction prelude cannot impersonate Lean's `String`,
/// and it cannot do so **by mechanism** rather than by shape check: its alphabet
/// and sequence types are declared under `axeyum.string.<n>`, so the reserved
/// names `Char`, `List`, `String` and `String.ofList` are not even present in a
/// kernel that has built it. Nothing about the reconstruction preludes or their
/// axiom footprints can move because string literals became typable.
#[test]
fn the_reconstruction_prelude_is_not_a_string_bootstrap() {
    let mut kernel = Kernel::new();
    let logic = axeyum_lean_kernel::build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prelude = axeyum_lean_kernel::build_string_prelude(&mut kernel, logic, 4)
        .expect("string prelude builds");

    // The mechanism: a namespaced alphabet, not the reserved `Char`.
    let rendered = kernel.display_name(prelude.char_ind).to_string();
    assert!(
        rendered.starts_with("axeyum.string."),
        "the reconstruction alphabet must stay namespaced, got {rendered}"
    );

    let literal = kernel.lit(Lit::Str("abc".to_owned()));
    assert!(matches!(
        kernel.infer(literal),
        Err(KernelError::StringLiteralBootstrapMismatch { string: None })
    ));
}

/// Why `try_string_lit_expansion` is carried but never observed firing.
///
/// Lean's `is_def_eq_core` tries it **after** `lazy_delta_reduction`, and in
/// Lean 4.30 `String.ofList` is an ordinary definition — so lazy delta unfolds
/// the `String.ofList` head to the `String.ofByteArray` constructor application
/// before the hook can recognize it, and the hook's shape test never matches.
/// The rule was written when `String` was `structure String where mk :: (data :
/// List Char)` and the constant it keys on **was a constructor**, which delta
/// cannot unfold. What identifies a literal with a constructor application today
/// is structure eta plus the projection rule
/// (`projecting_a_literal_computes_through_the_expansion`).
///
/// This test pins the mechanism rather than the conclusion: removing the def-eq
/// hook from this kernel fails no test in this suite (measured 2026-08-15), and
/// this is why. The hook stays because the pinned source has it and its only
/// possible effect is to accept more, never less.
#[test]
fn delta_reaches_the_constructor_before_the_def_eq_hook_can_see_of_list() {
    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let list = list_of_scalars(&mut kernel, &env, &[0x61, 0x62]);
    let of_list = kernel.const_(env.of_list, vec![]);
    let application = kernel.app(of_list, list);

    let normal = kernel.whnf(application);
    let mut head = normal;
    while let axeyum_lean_kernel::ExprNode::App(function, _) = kernel.expr_node(head) {
        head = *function;
    }
    let axeyum_lean_kernel::ExprNode::Const(name, _) = kernel.expr_node(head) else {
        panic!("`String.ofList xs` should normalize to a constructor application");
    };
    assert_eq!(
        *name, env.string_ctor,
        "`String.ofList` is a definition, so delta reaches `String.ofByteArray` \
         and the literal-expansion hook never sees an `of_list` head"
    );
}
