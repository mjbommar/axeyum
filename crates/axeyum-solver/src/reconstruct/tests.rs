//! Tests for Alethe → Lean equality-rule reconstruction (P3.7 first slice).
//!
//! Each test **builds** a Lean proof term from an Alethe equality step and
//! confirms the trusted kernel `infer`s it to the right `Eq` proposition (or, for
//! the negative tests, that it is rejected). A green test is the kernel genuinely
//! accepting the reconstruction.
#![allow(clippy::similar_names)]

use axeyum_cnf::{AletheLit, AletheTerm};
use axeyum_lean_kernel::ExprNode;

use super::{
    ProofFragment, ReconstructCtx, ReconstructError, fresh_axiom, prove_unsat_to_lean_module,
    reconstruct_eq_step, render_ctx_module, require_infers_false, scan_proof_fragment,
};
use super::direct::reconstruct_checked_structural_certificate_to_lean_module;

fn legacy_checked_structural_certificate_module(
    prop_stem: &str,
    refuter_role: &str,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();
    let prop_name = ctx.prop_atom_const(prop_stem);
    let prop = ctx.kernel.const_(prop_name, vec![]);
    let asserted = fresh_axiom(&mut ctx, prop, "assume")?;
    let refuter_prop = ctx.mk_not(prop);
    let refuter = fresh_axiom(&mut ctx, refuter_prop, refuter_role)?;
    let proof = ctx.kernel.app(refuter, asserted);
    require_infers_false(&mut ctx, proof)?;
    Ok(render_ctx_module(&mut ctx, proof))
}

#[test]
fn checked_structural_emitter_is_byte_identical_for_every_registered_role() {
    let roles = [
        ("bool_simplification_42", "bool_simplification"),
        ("bool_uf_exhaustive_assertions", "bool_uf_exhaustive"),
        ("bool_euf_exhaustive_assertions", "bool_euf_exhaustive"),
        ("bool_euf_online_assertions", "bool_euf_online"),
        ("uf_arith_congruence_assertions", "uf_arith_congruence"),
        ("datatype_structural_assertions", "datatype_structural"),
        ("finite_domain_enum_assertions", "finite_domain_enum"),
        ("term_level_enum_assertions", "term_level_enum"),
        ("bv_defined_enum_assertions", "bv_defined_enum"),
        ("set_cardinality_assertions", "set_cardinality"),
        ("bv_forall_nonconstant_assertions", "bv_forall_nonconstant"),
        ("bv_uf_local_assertions", "bv_uf_local"),
        ("lra_dpll_assertions", "lra_dpll"),
        ("arith_dpll_assertions", "arith_dpll"),
        ("bounded_int_blast_assertions", "bounded_int_blast"),
        ("nra_even_power_assertions", "nra_even_power"),
        (
            "const_array_default_mismatch_assertions",
            "const_array_default_mismatch",
        ),
        ("store_chain_readback_assertions", "store_chain_readback"),
        (
            "cross_store_array_disequality_assertions",
            "cross_store_array_disequality",
        ),
        ("bv_abstraction_assertions", "bv_abstraction"),
        ("two_byte_memcpy_assertion", "two_byte_memcpy"),
        (
            "two_element_bubble_sort_assertion",
            "two_element_bubble_sort",
        ),
        (
            "two_element_selection_sort_assertion",
            "two_element_selection_sort",
        ),
        ("aligned_write_chain_assertion", "aligned_write_chain"),
        ("two_cell_xor_swap_assertion", "two_cell_xor_swap"),
        (
            "two_byte_xor_swap_roundtrip_assertion",
            "two_byte_xor_swap_roundtrip",
        ),
        ("binary_search16_assertion", "binary_search16"),
        ("fifo_bc04_assertion", "fifo_bc04"),
        (
            "bool_array_read_collapse_1_2_3",
            "bool_array_read_collapse",
        ),
    ];

    for (prop_stem, refuter_role) in roles {
        let legacy = legacy_checked_structural_certificate_module(prop_stem, refuter_role)
            .expect("legacy structural wrapper must reconstruct");
        let shared =
            reconstruct_checked_structural_certificate_to_lean_module(prop_stem, refuter_role)
                .expect("shared structural wrapper must reconstruct");
        assert_eq!(shared.as_bytes(), legacy.as_bytes(), "{refuter_role}");
    }
}

/// A bare atom literal `a` (positive). Helper for building clauses.
fn atom(s: &str) -> AletheTerm {
    AletheTerm::Const(s.to_owned())
}

/// `(= a b)` as a term.
fn eq_term(a: &str, b: &str) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![atom(a), atom(b)])
}

/// A positive literal `(= a b)`.
fn pos_eq(a: &str, b: &str) -> AletheLit {
    AletheLit {
        atom: eq_term(a, b),
        negated: false,
    }
}

/// A negated literal `(not (= a b))`.
fn neg_eq(a: &str, b: &str) -> AletheLit {
    AletheLit {
        atom: eq_term(a, b),
        negated: true,
    }
}

/// `alethe_term_to_expr` translates an atom `(= a b)` into a Lean `Eq` that
/// infers to `Prop`, and a bare atom into a term that infers to `α`.
#[test]
fn term_translation_atoms_and_equality() {
    let mut ctx = ReconstructCtx::new();

    // A bare atom `a` infers to the carrier `α`.
    let a_expr = ctx.alethe_term_to_expr(&atom("a")).unwrap();
    let a_ty = ctx.kernel_mut().infer(a_expr).unwrap();
    let alpha = ctx.alpha();
    assert!(
        ctx.kernel_mut().def_eq(a_ty, alpha),
        "atom `a` should have type α"
    );

    // `(= a b)` infers to a `Sort 0` (Prop): it is a proposition.
    let eq_ab = ctx.alethe_term_to_expr(&eq_term("a", "b")).unwrap();
    let eq_ty = ctx.kernel_mut().infer(eq_ab).unwrap();
    let eq_ty = ctx.kernel_mut().whnf(eq_ty);
    match ctx.kernel().expr_node(eq_ty) {
        ExprNode::Sort(level) => {
            let l = *level;
            assert!(
                ctx.kernel_mut().level_is_zero(l),
                "`(= a b)` should be a Prop (Sort 0)"
            );
        }
        other => panic!("`(= a b)` should infer to a Sort, got {other:?}"),
    }
}

/// `alethe_term_to_expr` translates a nested equality of function applications
/// `(= (f a) (f b))` and the result infers to `Prop`. The same atom maps to the
/// same constant on repeated use (determinism / sharing).
#[test]
fn term_translation_nested_and_sharing() {
    let mut ctx = ReconstructCtx::new();
    let fa = AletheTerm::App("f".to_owned(), vec![atom("a")]);
    let fb = AletheTerm::App("f".to_owned(), vec![atom("b")]);
    let eq = AletheTerm::App("=".to_owned(), vec![fa, fb]);
    let e = ctx.alethe_term_to_expr(&eq).unwrap();
    let ty = ctx.kernel_mut().infer(e).unwrap();
    let ty = ctx.kernel_mut().whnf(ty);
    assert!(matches!(ctx.kernel().expr_node(ty), ExprNode::Sort(_)));

    // The atom `a` re-translates to the SAME constant (interned id stability).
    let a1 = ctx.alethe_term_to_expr(&atom("a")).unwrap();
    let a2 = ctx.alethe_term_to_expr(&atom("a")).unwrap();
    assert_eq!(
        a1, a2,
        "the same atom must reconstruct to the same constant"
    );
}

/// An out-of-scope term — an indexed operator `((_ @bit_of 0) x)` (n-ary plain
/// applications are now in scope, but indexed operators are not) — yields a clear
/// `UnsupportedTerm` error, not a panic.
#[test]
fn term_translation_out_of_scope_errors() {
    let mut ctx = ReconstructCtx::new();
    let bit = AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![0],
        args: vec![atom("x")],
    };
    let err = ctx.alethe_term_to_expr(&bit).unwrap_err();
    assert!(matches!(err, ReconstructError::UnsupportedTerm { .. }));
}

/// `eq_reflexive` over an atom: `(cl (= a a))` reconstructs to `Eq.refl α a`,
/// which the kernel infers to `Eq α a a`.
#[test]
fn eq_reflexive_reconstructs() {
    let mut ctx = ReconstructCtx::new();
    let conclusion = vec![pos_eq("a", "a")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_reflexive", &[], &conclusion).unwrap();

    // Independently confirm: the proof infers to `Eq α a a`.
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.alethe_term_to_expr(&eq_term("a", "a")).unwrap();
    assert!(
        ctx.kernel_mut().def_eq(inferred, expected),
        "eq_reflexive proof infers to Eq α a a"
    );
}

/// `eq_symmetric`: from a (self-contained) step `(cl (not (= a b)) (= b a))`,
/// the reconstructed `Eq.rec` transport term infers to `Eq α b a`.
#[test]
fn eq_symmetric_reconstructs() {
    let mut ctx = ReconstructCtx::new();
    let conclusion = vec![neg_eq("a", "b"), pos_eq("b", "a")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_symmetric", &[], &conclusion).unwrap();

    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.alethe_term_to_expr(&eq_term("b", "a")).unwrap();
    assert!(
        ctx.kernel_mut().def_eq(inferred, expected),
        "eq_symmetric proof infers to Eq α b a"
    );
}

/// `eq_symmetric` threaded with an EXPLICIT premise proof `h : Eq α a b`: the
/// reconstructed transport over that premise infers to `Eq α b a`.
#[test]
fn eq_symmetric_with_explicit_premise() {
    let mut ctx = ReconstructCtx::new();
    // Build an explicit premise proof: an axiom h : Eq α a b.
    let eq_ab = ctx.alethe_term_to_expr(&eq_term("a", "b")).unwrap();
    let h = {
        use axeyum_lean_kernel::Declaration;
        let anon = ctx.kernel_mut().anon();
        let name = ctx.kernel_mut().name_str(anon, "h_premise");
        ctx.kernel_mut()
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: eq_ab,
            })
            .unwrap();
        ctx.kernel_mut().const_(name, vec![])
    };
    let conclusion = vec![neg_eq("a", "b"), pos_eq("b", "a")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_symmetric", &[h], &conclusion).unwrap();
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.alethe_term_to_expr(&eq_term("b", "a")).unwrap();
    assert!(ctx.kernel_mut().def_eq(inferred, expected));
}

/// `eq_transitive`: from `(cl (not (= a b)) (not (= b c)) (= a c))`, the
/// reconstructed transport infers to `Eq α a c`.
#[test]
fn eq_transitive_reconstructs() {
    let mut ctx = ReconstructCtx::new();
    let conclusion = vec![neg_eq("a", "b"), neg_eq("b", "c"), pos_eq("a", "c")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_transitive", &[], &conclusion).unwrap();

    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.alethe_term_to_expr(&eq_term("a", "c")).unwrap();
    assert!(
        ctx.kernel_mut().def_eq(inferred, expected),
        "eq_transitive proof infers to Eq α a c"
    );
}

/// **End-to-end driver**: a 2-step transitivity chain. Model `assume a=b` and
/// `assume b=c` as hypothesis-axiom proofs `h1 : Eq α a b`, `h2 : Eq α b c`,
/// thread them into an `eq_transitive` step, and confirm the final proof term
/// kernel-checks to `Eq α a c`.
#[test]
fn driver_transitivity_chain_end_to_end() {
    use axeyum_lean_kernel::Declaration;
    let mut ctx = ReconstructCtx::new();

    // assume a=b : Eq α a b.
    let eq_ab = ctx.alethe_term_to_expr(&eq_term("a", "b")).unwrap();
    let h1 = {
        let anon = ctx.kernel_mut().anon();
        let name = ctx.kernel_mut().name_str(anon, "assume_ab");
        ctx.kernel_mut()
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: eq_ab,
            })
            .unwrap();
        ctx.kernel_mut().const_(name, vec![])
    };
    // assume b=c : Eq α b c.
    let eq_bc = ctx.alethe_term_to_expr(&eq_term("b", "c")).unwrap();
    let h2 = {
        let anon = ctx.kernel_mut().anon();
        let name = ctx.kernel_mut().name_str(anon, "assume_bc");
        ctx.kernel_mut()
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: eq_bc,
            })
            .unwrap();
        ctx.kernel_mut().const_(name, vec![])
    };

    // eq_transitive ⊢ (cl (not (= a b)) (not (= b c)) (= a c)) with h1, h2.
    let conclusion = vec![neg_eq("a", "b"), neg_eq("b", "c"), pos_eq("a", "c")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_transitive", &[h1, h2], &conclusion).unwrap();

    // The final term kernel-checks to Eq α a c.
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.alethe_term_to_expr(&eq_term("a", "c")).unwrap();
    assert!(
        ctx.kernel_mut().def_eq(inferred, expected),
        "the transitivity chain reconstructs end-to-end to Eq α a c"
    );
}

/// **Negative soundness check**: a deliberately WRONG `eq_transitive` conclusion
/// — claiming the chain `a=b, b=c` proves `a=d` (it proves `a=c`) — is REJECTED.
/// Here the mismatch is caught structurally (the conclusion endpoints do not
/// match the chain), which is the boundary firing before the kernel even runs.
#[test]
fn negative_wrong_transitive_conclusion_rejected() {
    let mut ctx = ReconstructCtx::new();
    // Chain a=b, b=c but conclusion claims a=d.
    let conclusion = vec![neg_eq("a", "b"), neg_eq("b", "c"), pos_eq("a", "d")];
    let err = reconstruct_eq_step(&mut ctx, "eq_transitive", &[], &conclusion).unwrap_err();
    assert!(
        matches!(err, ReconstructError::MalformedStep { .. }),
        "a wrong transitivity conclusion must be rejected, got {err:?}"
    );
}

/// **Negative soundness check at the KERNEL gate**: build an `eq_transitive`
/// transport term directly but compare it against a wrong expected proposition
/// (`Eq α a d` instead of `Eq α a c`). The kernel infers `Eq α a c`, which is not
/// `def_eq` to `Eq α a d`, so the soundness gate rejects it. This exercises the
/// kernel as the checker (not just the structural pre-check).
#[test]
fn negative_kernel_gate_rejects_wrong_proposition() {
    let mut ctx = ReconstructCtx::new();

    // Correctly reconstruct a=b, b=c ⊢ a=c.
    let conclusion = vec![neg_eq("a", "b"), neg_eq("b", "c"), pos_eq("a", "c")];
    let proof = reconstruct_eq_step(&mut ctx, "eq_transitive", &[], &conclusion).unwrap();

    // The kernel infers Eq α a c.
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    // A deliberately wrong expected proposition: Eq α a d.
    let wrong = ctx.alethe_term_to_expr(&eq_term("a", "d")).unwrap();
    assert!(
        !ctx.kernel_mut().def_eq(inferred, wrong),
        "the kernel must NOT accept Eq α a c as Eq α a d"
    );
    // And the correct one IS accepted, confirming the term is genuine.
    let right = ctx.alethe_term_to_expr(&eq_term("a", "c")).unwrap();
    assert!(ctx.kernel_mut().def_eq(inferred, right));
}

/// An out-of-scope rule (here `resolution`) is rejected with a clear
/// `UnsupportedRule`, never a panic.
#[test]
fn unsupported_rule_rejected() {
    let mut ctx = ReconstructCtx::new();
    let conclusion = vec![pos_eq("a", "a")];
    let err = reconstruct_eq_step(&mut ctx, "resolution", &[], &conclusion).unwrap_err();
    assert!(matches!(err, ReconstructError::UnsupportedRule { .. }));
}

// ---------------------------------------------------------------------------
// Full EUF refutation: a REAL `prove_qf_uf_unsat_alethe` proof reconstructed to
// a kernel-checked `False`. This is the slice-2 deliverable.
// ---------------------------------------------------------------------------

use super::reconstruct_qf_uf_proof;
use axeyum_ir::{Sort, TermArena};

/// Confirm a reconstructed term `infer`s to a `Sort` (its type is a proposition),
/// and specifically that it is the prelude's `False`.
fn assert_infers_false(ctx: &mut ReconstructCtx, proof: axeyum_lean_kernel::ExprId) {
    let inferred = ctx
        .kernel_mut()
        .infer(proof)
        .expect("False term must infer");
    let false_ = {
        let name = ctx.prelude().false_;
        ctx.kernel_mut().const_(name, vec![])
    };
    assert!(
        ctx.kernel_mut().def_eq(inferred, false_),
        "the reconstructed refutation must kernel-check to `False`"
    );
    // And `False` itself is a Prop, so the term is a genuine proof, not data.
    let false_ty = {
        let name = ctx.prelude().false_;
        let f = ctx.kernel_mut().const_(name, vec![]);
        ctx.kernel_mut().infer(f).unwrap()
    };
    assert!(matches!(
        ctx.kernel().expr_node(false_ty),
        ExprNode::Sort(_)
    ));
}

fn bv_var(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let sym = arena.declare(name, Sort::BitVec(8)).expect("declare");
    arena.var(sym)
}

/// **THE END-TO-END DELIVERABLE**: take a REAL axeyum-emitted EUF `unsat` Alethe
/// proof for `a = b ∧ b = c ∧ a ≠ c`, reconstruct it through
/// `reconstruct_qf_uf_proof`, and assert the result kernel-checks to `False`.
///
/// This is a complete solver proof → Lean-kernel-verified term: the solver emits
/// the Alethe commands, reconstruction translates them into a Lean proof term, and
/// the trusted kernel `infer`s that term to `False`.
#[test]
fn end_to_end_transitivity_refutation_to_false() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    // REAL emitted proof (self-validated by check_alethe inside the emitter).
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions)
        .expect("emitter produces the transitivity refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof)
        .expect("the EUF refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// A longer chain `a=b ∧ b=c ∧ c=d ∧ a≠d` reconstructs end-to-end to `False`.
#[test]
fn end_to_end_longer_chain_refutation_to_false() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let d = bv_var(&mut arena, "d");
    let assertions = vec![
        arena.eq(a, b).unwrap(),
        arena.eq(b, c).unwrap(),
        arena.eq(c, d).unwrap(),
        {
            let e = arena.eq(a, d).unwrap();
            arena.not(e).unwrap()
        },
    ];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// A reversed-edge instance `a=b stored as b=a ∧ b=c ∧ a≠c`: the emitter inserts
/// an `eq_symmetric` flip resolution, which the walker reconstructs end-to-end.
#[test]
fn end_to_end_reversed_edge_refutation_to_false() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(b, a).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **Congruence end-to-end**: `a = b ∧ f(a) ≠ f(b)` is refuted by a depth-1
/// `eq_congruent` step; reconstruction transports `Eq.refl` through `Eq.rec`
/// (`congrArg`-style) and closes to `False`.
#[test]
fn end_to_end_congruence_refutation_to_false() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let assertions = vec![arena.eq(a, b).unwrap(), {
        let e = arena.eq(fa, fb).unwrap();
        arena.not(e).unwrap()
    }];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions)
        .expect("emitter produces the congruence refutation");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof)
        .expect("the congruence refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

fn stable_source_hash(source: &str) -> u64 {
    source.as_bytes().iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// R3 extraction gate: representative transitivity and congruence proofs must
/// keep emitting byte-identical Lean modules when their builders move into the
/// equality-owned submodule.
#[test]
fn equality_family_generated_source_is_byte_stable() {
    let mut fixtures = Vec::new();

    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let transitivity = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &transitivity).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    fixtures.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let congruence = vec![arena.eq(a, b).unwrap(), {
        let e = arena.eq(fa, fb).unwrap();
        arena.not(e).unwrap()
    }];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &congruence).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_uf_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    fixtures.push((source.len(), stable_source_hash(&source)));

    assert_eq!(
        fixtures,
        [
            (1_480, 16_524_372_807_544_528_002),
            (1_558, 9_142_307_883_420_495_535),
        ]
    );
}

/// R3 datatype extraction gate: each specialized axiom-free route must keep
/// emitting byte-identical Lean when its proof family moves behind one module.
#[test]
fn datatype_family_generated_source_is_byte_stable() {
    let mut fixtures = Vec::new();

    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = {
        let symbol = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let green_a = arena.construct(green, &[a]).unwrap();
    let tester = arena.dt_test(red, green_a).unwrap();
    let source = super::reconstruct_qf_dt_tester_to_lean_module(&arena, &[tester])
        .expect("tester route recognizes fixture")
        .expect("tester route reconstructs");
    fixtures.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = {
        let symbol = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let b = {
        let symbol = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let red_a = arena.construct(red, &[a]).unwrap();
    let green_b = arena.construct(green, &[b]).unwrap();
    let distinct = arena.eq(red_a, green_b).unwrap();
    let source = super::reconstruct_qf_dt_distinct_to_lean_module(&arena, &[distinct])
        .expect("distinctness route recognizes fixture")
        .expect("distinctness route reconstructs");
    fixtures.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let pair_mk = arena.add_constructor(
        pair,
        "mk",
        &[
            ("fst".into(), Sort::BitVec(2)),
            ("snd".into(), Sort::BitVec(2)),
        ],
    );
    let mut bv = |name: &str| {
        let symbol = arena.declare(name, Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let a = bv("a");
    let b = bv("b");
    let c = bv("c");
    let d = bv("d");
    let lhs = arena.construct(pair_mk, &[a, b]).unwrap();
    let rhs = arena.construct(pair_mk, &[c, d]).unwrap();
    let pair_eq = arena.eq(lhs, rhs).unwrap();
    let field_eq = arena.eq(a, c).unwrap();
    let field_ne = arena.not(field_eq).unwrap();
    let source =
        super::reconstruct_qf_dt_injective_to_lean_module(&arena, &[pair_eq, field_ne])
            .expect("injectivity route recognizes fixture")
            .expect("injectivity route reconstructs");
    fixtures.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let h = {
        let symbol = arena.declare("h", Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let x = {
        let symbol = arena.declare("x", Sort::Datatype(list)).unwrap();
        arena.var(symbol)
    };
    let cons_h_x = arena.construct(cons, &[h, x]).unwrap();
    let cycle = arena.eq(x, cons_h_x).unwrap();
    let source = super::reconstruct_qf_dt_acyclic_to_lean_module(&arena, &[cycle])
        .expect("acyclicity route recognizes fixture")
        .expect("acyclicity route reconstructs");
    fixtures.push((source.len(), stable_source_hash(&source)));

    assert_eq!(
        fixtures,
        [
            (2_057, 12_042_421_301_549_597_275),
            (3_069, 15_726_968_749_404_357_215),
            (2_640, 1_434_913_494_449_130_936),
            // The first-class RoundingMode IR extension requires a new
            // byte-stable snapshot; length and independent kernel checking are
            // unchanged, and repeated generation produced this exact hash.
            (3_940, 972_985_670_248_459_210),
        ]
    );
}

/// R3 quantifier extraction gate: universal instantiation and existential
/// elimination must keep emitting byte-identical Lean modules.
#[test]
fn quantifier_family_generated_source_is_byte_stable() {
    let mut fixtures = Vec::new();

    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let forall = arena.forall(x, fx_eq_c).unwrap();
    let av = arena.var(a);
    let fa = arena.apply(f, &[av]).unwrap();
    let fa_eq_c = arena.eq(fa, cv).unwrap();
    let not_fa_eq_c = arena.not(fa_eq_c).unwrap();
    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_c]).unwrap();
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof).unwrap();
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    fixtures.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let x = arena.declare("x", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let d = arena.declare("d", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let exists = arena.exists(x, fx_eq_c).unwrap();
    let yv = arena.var(y);
    let dv = arena.var(d);
    let fy = arena.apply(f, &[yv]).unwrap();
    let fy_eq_d = arena.eq(fy, dv).unwrap();
    let forall = arena.forall(y, fy_eq_d).unwrap();
    let c_eq_d = arena.eq(cv, dv).unwrap();
    let c_ne_d = arena.not(c_eq_d).unwrap();
    let cert = crate::prove_skolem_unsat_alethe(&mut arena, &[exists, forall, c_ne_d]).unwrap();
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_skolem_unsat_proof(&mut ctx, &cert).unwrap();
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    fixtures.push((source.len(), stable_source_hash(&source)));

    assert_eq!(
        fixtures,
        [
            (921, 17_229_612_914_579_886_985),
            (2_685, 12_920_678_261_632_022_537),
        ]
    );
}

/// **`QF_UFBV` Ackermann certificate end-to-end (ADR-0013 task #19)**: take a REAL
/// `prove_qf_ufbv_unsat_alethe` certificate for
/// `f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00)` — decided via the Ackermann reduction —
/// and reconstruct it through `reconstruct_qf_ufbv_proof` to a kernel-checked
/// `False`. The certificate's functional-consistency constraint is **derived** by
/// `eq_congruent` (the EUF head, kernel-checked) and consumed by the bit-blast
/// refutation (the tail, kernel-checked), so the result has **no trusted
/// reduction step** — the previously-trusted Ackermann congruence is now validated
/// by the Lean kernel.
#[test]
fn end_to_end_qf_ufbv_ackermann_certificate_to_false() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3])
        .expect("emitter produces the Ackermann certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the QF_UFBV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **n-ary EUF congruence end-to-end (task #22)**: a BINARY uninterpreted function
/// `g`. Its Ackermann consistency constraint `(a=b ∧ c=d) → g(a,c)=g(b,d)` is a
/// TWO-argument `eq_congruent`, which the unary-only reconstruction rejected
/// (`UnsupportedRule`). The n-ary `reconstruct_eq_congruent` derives it by folding
/// one `Eq.rec` transport per argument, so
/// `g(a,c) = #b00 ∧ a = b ∧ c = d ∧ ¬(g(b,d) = #b00)` reconstructs to a
/// kernel-checked `False` — completing the `QF_UFBV` certificate for multi-arg
/// functions.
#[test]
fn end_to_end_qf_ufbv_binary_congruence_to_false() {
    let mut arena = TermArena::new();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2), Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let d = {
        let s = arena.declare("d", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let gac = arena.apply(g, &[a, c]).unwrap();
    let gbd = arena.apply(g, &[b, d]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(gac, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = arena.eq(c, d).unwrap();
    let e4 = {
        let e = arena.eq(gbd, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3, e4])
        .expect("emitter produces the binary Ackermann certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the binary QF_UFBV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Transitive-argument Ackermann certificate end-to-end**: the consistency
/// constraint's argument equality `a = c` holds only by transitive closure
/// `a = b = c` (not a direct assertion), so the certificate derives it with an
/// `eq_transitive` chain. Reconstructing `f(a) = #b00 ∧ a = b ∧ b = c ∧
/// ¬(f(c) = #b00)` exercises that chain through `reconstruct_qf_ufbv_proof` to a
/// kernel-checked Lean `False`, confirming the widened fragment closes the Lean
/// loop (not just `check_alethe` / Carcara).
#[test]
fn end_to_end_qf_ufbv_transitive_congruence_to_false() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let fa = arena.apply(f, &[a]).unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = arena.eq(b, c).unwrap();
    let e4 = {
        let e = arena.eq(fc, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3, e4])
        .expect("emitter produces the transitive Ackermann certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the transitive QF_UFBV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Congruence-derived argument equality end-to-end (`symm`)**: nested
/// applications `f(g(a))` / `f(g(b))` whose outer congruence needs the *inner*
/// argument equality `g(a) = g(b)`. That inner equality is itself derived by
/// congruence over `a = b`, and the emitter's congruence-closure fallback may flip
/// the derived unit via the Alethe `symm` rule (premise the unit `(= e_a e_b)`,
/// conclusion the swapped `(= e_b e_a)`) to orient it for the outer step.
/// Reconstructing `f(g(a)) = #b00 ∧ a = b ∧ ¬(f(g(b)) = #b00)` exercises that
/// `symm` reconstruction through `reconstruct_qf_ufbv_proof` to a kernel-checked
/// Lean `False`, closing the Lean loop for the congruence-fallback fragment.
#[test]
fn end_to_end_qf_ufbv_congruence_derived_to_false() {
    let mut arena = TermArena::new();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let ga = arena.apply(g, &[a]).unwrap();
    let gb = arena.apply(g, &[b]).unwrap();
    let fga = arena.apply(f, &[ga]).unwrap();
    let fgb = arena.apply(f, &[gb]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fga, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fgb, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3])
        .expect("emitter produces the nested-congruence Ackermann certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the congruence-derived QF_UFBV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// A `QF_UFBV` proof with no Ackermann congruence blocks (not a certificate from
/// `prove_qf_ufbv_unsat_alethe`) is cleanly rejected, never mis-reconstructed.
#[test]
fn qf_ufbv_reconstruct_rejects_non_certificate() {
    // A plain EUF proof carries no `!cong_*` congruence blocks.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    let proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    assert!(matches!(
        super::reconstruct_qf_ufbv_proof(&mut ctx, &proof),
        Err(ReconstructError::UnsupportedRule { .. })
    ));
}

/// **`QF_ABV` array-elimination certificate end-to-end (ADR-0010 task #20)**: take
/// a REAL `prove_qf_abv_unsat_alethe_via_elimination` certificate for
/// `select(a, i) = #b0…0 ∧ i = j ∧ ¬(select(a, j) = #b0…0)` — decided via the
/// array-elimination reduction — and reconstruct it through the **shared**
/// `reconstruct_qf_ufbv_proof` to a kernel-checked `False`. An array variable `a`
/// is the unary uninterpreted function `sel_a := λ idx. select(a, idx)`, so the
/// **read-consistency** (Ackermann-over-select) constraint is **derived** by
/// `eq_congruent` over `sel_a` (the EUF head, kernel-checked) and consumed by the
/// bit-blast refutation (the tail, kernel-checked). The previously-trusted
/// Ackermann-over-select step is now validated by the Lean kernel — no trusted
/// reduction step remains.
#[test]
fn end_to_end_qf_abv_array_elimination_certificate_to_false() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = {
        let s = arena.declare("i", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let j = {
        let s = arena.declare("j", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e1, e2, e3])
        .expect("emitter produces the array-elimination certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the QF_ABV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Transitive array-elimination certificate end-to-end**: the read-consistency
/// constraint's index equality `i = j` holds only by transitive closure
/// `i = k = j`, so the cert derives it with an `eq_transitive` index chain.
/// `select(a,i)=#b00 ∧ i=k ∧ k=j ∧ ¬(select(a,j)=#b00)` reconstructs through the
/// shared `reconstruct_qf_ufbv_proof` to a kernel-checked Lean `False`, closing the
/// Lean loop for the widened array-elim fragment too.
#[test]
fn end_to_end_qf_abv_transitive_index_certificate_to_false() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = {
        let s = arena.declare("i", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let k = {
        let s = arena.declare("k", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let j = {
        let s = arena.declare("j", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, k).unwrap();
    let e3 = arena.eq(k, j).unwrap();
    let e4 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };

    let proof = crate::prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e1, e2, e3, e4])
        .expect("emitter produces the transitive array-elimination certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the transitive QF_ABV certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Datatype read-over-construct certificate end-to-end (ROUTE A, zero-trust)**:
/// take a REAL `prove_qf_dt_unsat_alethe_via_simplification` certificate for
/// `select_0(mk(a, b)) = #b00 ∧ ¬(a = #b00)` — decided via read-over-construct
/// simplification (`select_0(mk(a, b)) → a`) — and reconstruct it through the
/// **shared** `reconstruct_qf_ufbv_proof` to a kernel-checked `False`. The
/// `select`-over-`construct` fold is made explicit as a `!cong_*` block:
/// abstraction definition `(= w (!dtsel_2_0_mk (!dtcon_2_mk a b)))` + projection
/// equation `(= (!dtsel_2_0_mk (!dtcon_2_mk a b)) a)`, chained by `eq_transitive`
/// (the EUF head, kernel-checked), and consumed by the bit-blast refutation (the
/// tail, kernel-checked).
///
/// **ROUTE A:** the projection equation is **DERIVED by ι-reduction** (`Eq.refl`)
/// over a kernel inductive — NOT an assumed datatype axiom — so the certificate
/// carries no datatype trust point. [`assert_no_assumed_dt_projection_axiom`]
/// confirms the EUF head's only axioms are the input-assumption hypotheses (the
/// abstraction definition + the disequality), with the projection discharged by
/// reflexivity.
#[test]
fn end_to_end_qf_dt_read_over_construct_certificate_to_false() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(2)), ("b".into(), Sort::BitVec(2))],
    );
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap(); // select_0(mk(a,b)) -> a
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(sel, c00).unwrap(); // select_0(mk(a,b)) = 0
    let e2 = {
        let e = arena.eq(a, c00).unwrap();
        arena.not(e).unwrap() // a != 0
    };

    let proof = crate::prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[e1, e2])
        .expect("emitter produces the datatype simplification certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the datatype certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
    // Route-A audit: the projection is ι-reduction, not an assumed axiom.
    assert_no_assumed_dt_projection_axiom(&proof);
}

/// **ROUTE-A audit helper.** Reconstruct each `!cong_*` congruence block's EUF
/// head refutation in an inspectable [`ReconstructCtx`] and confirm it carries
/// **no assumed datatype-projection axiom**: every declared hypothesis axiom is
/// role `"assume"` (the input-assumption hypotheses — the abstraction definition
/// and the disequality), and the projection equation `(= (sel (C a…)) a_i)` is
/// instead discharged by `Eq.refl` (ι-reduction over the kernel inductive), so it
/// declares **no** extra axiom. Concretely: the block has exactly two assumed
/// equalities (def + diseq) under route A, vs. three under route B (def + proj +
/// diseq); we assert the projection did not mint an axiom by checking that the
/// number of `"assume"` axioms equals the number of *non-projection* assumes in
/// the block.
fn assert_no_assumed_dt_projection_axiom(proof: &[axeyum_cnf::AletheCommand]) {
    use axeyum_cnf::{AletheCommand, AletheTerm};
    let blocks = super::collect_congruence_blocks(proof);
    assert!(
        !blocks.is_empty(),
        "datatype certificate must have `!cong_*` congruence blocks"
    );
    for block in &blocks {
        let euf = super::euf_refutation_for_test(block);
        // Count the block's `assume`d equalities, splitting the projection
        // (whose asserted equality's LHS is a `!dtsel_*` selector application) from
        // the rest.
        let mut projection_assumes = 0usize;
        let mut other_assumes = 0usize;
        for cmd in &euf {
            if let AletheCommand::Assume { clause, .. } = cmd
                && let [lit] = clause.as_slice()
            {
                let is_proj = matches!(
                    &lit.atom,
                    AletheTerm::App(h, args)
                        if h == "="
                            && matches!(
                                args.first(),
                                Some(AletheTerm::App(head, _)) if head.starts_with("!dtsel_")
                            )
                );
                if is_proj {
                    projection_assumes += 1;
                } else {
                    other_assumes += 1;
                }
            }
        }
        assert!(
            projection_assumes >= 1,
            "the EUF head must contain a projection assume to discharge"
        );

        let mut head_ctx = ReconstructCtx::new();
        super::reconstruct_qf_uf_proof(&mut head_ctx, &euf)
            .expect("EUF head reconstructs to False");
        let roles = head_ctx.declared_axiom_roles();
        // Every declared axiom is an input `"assume"` hypothesis; NONE is a
        // datatype-projection axiom. Under route A the projection assumes are
        // discharged by `Eq.refl`, so the axiom count equals the NON-projection
        // assume count (the abstraction def + the disequality), not the total.
        assert!(
            roles.iter().all(|r| r == "assume"),
            "route A: only `assume` hypothesis axioms expected, got {roles:?}"
        );
        assert_eq!(
            roles.len(),
            other_assumes,
            "route A: the {projection_assumes} projection assume(s) must be \
             discharged by ι-reduction (Eq.refl), minting NO axiom — only the \
             {other_assumes} non-projection assume(s) become axioms (got {} axioms)",
            roles.len()
        );
    }
}

/// **Datatype certificate with a second field selected (ROUTE A)**:
/// `select_1(mk(a, b)) = #b01 ∧ ¬(b = #b01)` — exercises a non-zero index and a
/// distinct constant. Reconstructs to a kernel-checked `False` with the
/// projection discharged by ι-reduction (no assumed datatype axiom).
#[test]
fn end_to_end_qf_dt_second_field_certificate_to_false() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(2)), ("b".into(), Sort::BitVec(2))],
    );
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 1, p).unwrap(); // select_1(mk(a,b)) -> b
    let c01 = arena.bv_const(2, 1).unwrap();
    let e1 = arena.eq(sel, c01).unwrap(); // select_1(mk(a,b)) = 1
    let e2 = {
        let e = arena.eq(b, c01).unwrap();
        arena.not(e).unwrap() // b != 1
    };

    let proof = crate::prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[e1, e2])
        .expect("emitter produces the datatype simplification certificate");
    let mut ctx = ReconstructCtx::new();
    let term = super::reconstruct_qf_ufbv_proof(&mut ctx, &proof)
        .expect("the datatype certificate reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
    // Route-A audit: the field-1 projection is ι-reduction, not an assumed axiom.
    assert_no_assumed_dt_projection_axiom(&proof);
}

/// The emitter declines (returns `None`) when there is no
/// `select`-over-`construct` redex — a pure-residual problem belongs to the plain
/// `QF_BV` emitter, not this datatype path.
#[test]
fn qf_dt_emitter_declines_without_redex() {
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    assert!(
        crate::prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &assertions).is_none(),
        "no select-over-construct redex: the datatype emitter must decline"
    );
}

/// **NEGATIVE soundness check**: corrupt a REAL emitted proof — swap the closing
/// resolution's disequality to a non-complementary one — and confirm
/// reconstruction REJECTS it (no complementary unit pair → error), never a wrong
/// `False`.
#[test]
fn end_to_end_corrupted_proof_rejected() {
    use axeyum_cnf::{AletheCommand, AletheTerm};

    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    let mut proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emitter");

    // Corrupt the assumed disequality `(not (= a c))` into `(not (= a d))`, so the
    // closing resolution no longer has a complementary equality unit.
    for cmd in &mut proof {
        if let AletheCommand::Assume { clause, .. } = cmd
            && let [lit] = clause.as_mut_slice()
            && lit.negated
        {
            lit.atom = AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("a".to_owned()),
                    AletheTerm::Const("d".to_owned()),
                ],
            );
        }
    }

    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_qf_uf_proof(&mut ctx, &proof)
        .expect_err("a corrupted proof must be rejected, never a wrong False");
    // Either the closing resolution finds no complementary pair, or the kernel
    // rejects the malformed final term — both are sound rejections.
    assert!(
        matches!(
            err,
            ReconstructError::UnsupportedResolution { .. }
                | ReconstructError::KernelRejected { .. }
        ),
        "corruption must surface as a sound rejection, got {err:?}"
    );
}

/// **NEGATIVE soundness check at the kernel gate**: hand-build a proof whose
/// closing resolution pairs `h_eq : Eq α a c` with a disequality of a DIFFERENT
/// equality `Not (Eq α a c')` won't even match; instead corrupt the *theory*
/// clause so the reconstructed equality is wrong, and confirm the kernel rejects
/// the final term. Here we corrupt `eq_transitive`'s conclusion endpoint, which
/// the slice-1 structural check catches before the kernel — a sound rejection.
#[test]
fn end_to_end_corrupted_theory_clause_rejected() {
    use axeyum_cnf::{AletheCommand, AletheTerm};

    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a");
    let b = bv_var(&mut arena, "b");
    let c = bv_var(&mut arena, "c");
    let assertions = vec![arena.eq(a, b).unwrap(), arena.eq(b, c).unwrap(), {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    }];
    let mut proof = crate::prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emitter");

    // Corrupt the eq_transitive step's positive conclusion `(= a c)` into `(= a b)`
    // so the chain endpoints no longer match.
    for cmd in &mut proof {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "eq_transitive"
            && let Some(last) = clause.last_mut()
        {
            last.atom = AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("a".to_owned()),
                    AletheTerm::Const("b".to_owned()),
                ],
            );
        }
    }

    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_qf_uf_proof(&mut ctx, &proof)
        .expect_err("a corrupted theory clause must be rejected");
    assert!(
        matches!(
            err,
            ReconstructError::MalformedStep { .. }
                | ReconstructError::KernelRejected { .. }
                | ReconstructError::UnsupportedResolution { .. }
        ),
        "corruption must surface as a sound rejection, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Propositional resolution (P3.7 slice 3) — the clausal-layer foundation.
// ---------------------------------------------------------------------------

use super::reconstruct_resolution_proof;
use axeyum_cnf::AletheCommand;

/// A positive propositional literal `p`.
fn p_lit(name: &str) -> AletheLit {
    AletheLit {
        atom: atom(name),
        negated: false,
    }
}

/// A negated propositional literal `(not p)`.
fn n_lit(name: &str) -> AletheLit {
    AletheLit {
        atom: atom(name),
        negated: true,
    }
}

/// An `assume` command of a clause.
fn assume(id: &str, clause: Vec<AletheLit>) -> AletheCommand {
    AletheCommand::Assume {
        id: id.to_owned(),
        clause,
    }
}

/// A `resolution` step.
fn res_step(id: &str, clause: Vec<AletheLit>, premises: &[&str]) -> AletheCommand {
    AletheCommand::Step {
        id: id.to_owned(),
        clause,
        rule: "resolution".to_owned(),
        premises: premises.iter().map(|s| (*s).to_owned()).collect(),
        args: Vec::new(),
    }
}

/// The clause→Or encoding: a unit clause `(cl a)` ⇒ the atom Prop; `(cl a b)` ⇒
/// `Or a b`; the empty clause ⇒ `False`.
#[test]
fn clause_encoding_shapes() {
    let mut ctx = ReconstructCtx::new();

    // Unit clause `(cl a)` ⇒ the propositional atom `a` (infers to Prop).
    let unit = ctx.clause_to_prop(&[p_lit("a")]);
    let ty = ctx.kernel_mut().infer(unit).unwrap();
    assert!(matches!(ctx.kernel().expr_node(ty), ExprNode::Sort(_)));

    // Empty clause ⇒ `False`.
    let empty = ctx.clause_to_prop(&[]);
    let false_ = {
        let name = ctx.prelude().false_;
        ctx.kernel_mut().const_(name, vec![])
    };
    assert!(ctx.kernel_mut().def_eq(empty, false_));

    // `(cl a b)` ⇒ `Or a b`, a Prop.
    let two = ctx.clause_to_prop(&[p_lit("a"), p_lit("b")]);
    let two_ty = ctx.kernel_mut().infer(two).unwrap();
    assert!(matches!(ctx.kernel().expr_node(two_ty), ExprNode::Sort(_)));
}

/// **Smallest refutation**: `(cl a)`, `(cl (not a))` ⇒ resolution to `(cl)` ⇒
/// reconstruct to a kernel-checked `False`.
#[test]
fn smallest_refutation_reconstructs() {
    let commands = vec![
        assume("h1", vec![p_lit("a")]),
        assume("h2", vec![n_lit("a")]),
        res_step("empty", vec![], &["h1", "h2"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("a and not-a refutes to a kernel-checked False");
    assert_infers_false(&mut ctx, term);
}

/// The closing resolution works regardless of premise order: `(cl (not a))`,
/// `(cl a)` ⇒ `(cl)`.
#[test]
fn smallest_refutation_swapped_order() {
    let commands = vec![
        assume("h1", vec![n_lit("a")]),
        assume("h2", vec![p_lit("a")]),
        res_step("empty", vec![], &["h1", "h2"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands).unwrap();
    assert_infers_false(&mut ctx, term);
}

/// **Multi-step refutation**: `(a ∨ b)`, `(¬a)`, `(¬b)` ⇒ resolve `(a∨b)` with
/// `(¬a)` to get `(b)`, then with `(¬b)` to the empty clause. End-to-end to a
/// kernel-checked `False`.
#[test]
fn three_clause_refutation_reconstructs() {
    let commands = vec![
        assume("c1", vec![p_lit("a"), p_lit("b")]),
        assume("c2", vec![n_lit("a")]),
        assume("c3", vec![n_lit("b")]),
        // (a ∨ b) resolved with ¬a yields (b).
        res_step("s1", vec![p_lit("b")], &["c1", "c2"]),
        // (b) resolved with ¬b yields the empty clause.
        res_step("s2", vec![], &["s1", "c3"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the 3-clause refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// R3 resolution extraction gate: a representative multi-step refutation must
/// keep emitting a byte-identical Lean module when its proof family moves.
#[test]
fn resolution_family_generated_source_is_byte_stable() {
    let commands = vec![
        assume("c1", vec![p_lit("a"), p_lit("b")]),
        assume("c2", vec![n_lit("a")]),
        assume("c3", vec![n_lit("b")]),
        res_step("s1", vec![p_lit("b")], &["c1", "c2"]),
        res_step("s2", vec![], &["s1", "c3"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the representative resolution refutation reconstructs");
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);

    assert_eq!(
        (source.len(), stable_source_hash(&source)),
        (1_651, 3_433_224_910_840_366_031)
    );
}

/// The native LRAT emitter orders RUP hints by forward unit propagation. A
/// substantial implication chain must reconstruct by replaying those pivots and
/// resolving backwards, without a Davis–Putnam search over the whole premise set.
#[test]
fn ordered_rup_implication_chain_reconstructs() {
    const LINKS: usize = 128;

    let mut commands = Vec::with_capacity(LINKS + 2);
    commands.push(assume("h0", vec![p_lit("x0")]));
    for index in 1..LINKS {
        commands.push(assume(
            &format!("h{index}"),
            vec![
                n_lit(&format!("x{}", index - 1)),
                p_lit(&format!("x{index}")),
            ],
        ));
    }
    commands.push(assume(
        &format!("h{LINKS}"),
        vec![n_lit(&format!("x{}", LINKS - 1))],
    ));
    let premise_ids = (0..=LINKS)
        .map(|index| format!("h{index}"))
        .collect::<Vec<_>>();
    commands.push(AletheCommand::Step {
        id: "empty".to_owned(),
        clause: vec![],
        rule: "resolution".to_owned(),
        premises: premise_ids,
        args: Vec::new(),
    });

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the ordered RUP implication chain reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// A wide learned RUP clause is produced by resolving one growing conflict
/// clause against many binary reasons. This is the shape emitted by the public
/// ADR-0127/0129 BV residuals and must stay linear in the growing clause rather
/// than rebuilding every survivor injection quadratically.
#[test]
fn ordered_rup_wide_growing_clause_reconstructs() {
    const WIDTH: usize = 32;
    const LINKS: usize = 64;

    let conclusion = (0..WIDTH)
        .map(|index| p_lit(&format!("a{index}")))
        .collect::<Vec<_>>();
    let mut commands = Vec::new();
    commands.push(assume("seed", vec![p_lit("x0")]));
    for index in 1..=LINKS {
        commands.push(assume(
            &format!("link{index}"),
            vec![
                n_lit(&format!("x{}", index - 1)),
                p_lit(&format!("x{index}")),
            ],
        ));
    }
    let mut conflict = vec![n_lit(&format!("x{LINKS}"))];
    conflict.extend(conclusion.iter().cloned());
    commands.push(assume("conflict", conflict));
    let mut wide_premises = vec!["seed".to_owned()];
    wide_premises.extend((1..=LINKS).map(|index| format!("link{index}")));
    wide_premises.push("conflict".to_owned());
    commands.push(AletheCommand::Step {
        id: "wide".to_owned(),
        clause: conclusion.clone(),
        rule: "resolution".to_owned(),
        premises: wide_premises,
        args: Vec::new(),
    });
    for index in 0..WIDTH {
        commands.push(assume(&format!("not_a{index}"), vec![n_lit(&format!("a{index}"))]));
    }
    let mut close = (0..WIDTH)
        .map(|index| format!("not_a{index}"))
        .collect::<Vec<_>>();
    close.push("wide".to_owned());
    commands.push(AletheCommand::Step {
        id: "empty".to_owned(),
        clause: vec![],
        rule: "resolution".to_owned(),
        premises: close,
        args: Vec::new(),
    });

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the growing wide RUP clause reconstructs compactly");
    assert_infers_false(&mut ctx, term);
}

fn reconstruct_cps_test_commands(
    ctx: &mut ReconstructCtx,
    commands: &[AletheCommand],
) -> Result<super::ExprId, ReconstructError> {
    let mut assumptions = Vec::new();
    for command in commands {
        if let AletheCommand::Assume { clause, .. } = command {
            let proposition = ctx.clause_to_prop(clause);
            assumptions.push(super::fresh_axiom(ctx, proposition, "cps_test_assume")?);
        }
    }
    super::reconstruct_bitwise_cps_tail(ctx, commands, &assumptions)
}

#[test]
fn cps_rup_wide_growing_clause_reconstructs_and_checks() {
    const WIDTH: usize = 32;
    const LINKS: usize = 64;

    let conclusion = (0..WIDTH)
        .map(|index| p_lit(&format!("a{index}")))
        .collect::<Vec<_>>();
    let mut commands = vec![assume("seed", vec![p_lit("x0")])];
    for index in 1..=LINKS {
        commands.push(assume(
            &format!("link{index}"),
            vec![
                n_lit(&format!("x{}", index - 1)),
                p_lit(&format!("x{index}")),
            ],
        ));
    }
    let mut conflict = vec![n_lit(&format!("x{LINKS}"))];
    conflict.extend(conclusion.iter().cloned());
    commands.push(assume("conflict", conflict));
    let mut wide_premises = vec!["seed".to_owned()];
    wide_premises.extend((1..=LINKS).map(|index| format!("link{index}")));
    wide_premises.push("conflict".to_owned());
    commands.push(AletheCommand::Step {
        id: "wide".to_owned(),
        clause: conclusion.clone(),
        rule: "resolution".to_owned(),
        premises: wide_premises,
        args: Vec::new(),
    });
    for index in 0..WIDTH {
        commands.push(assume(
            &format!("not_a{index}"),
            vec![n_lit(&format!("a{index}"))],
        ));
    }
    let mut close = (0..WIDTH)
        .map(|index| format!("not_a{index}"))
        .collect::<Vec<_>>();
    close.push("wide".to_owned());
    commands.push(res_step(
        "empty",
        vec![],
        &close.iter().map(String::as_str).collect::<Vec<_>>(),
    ));

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_cps_test_commands(&mut ctx, &commands)
        .expect("the CPS growing-clause route reconstructs");
    assert_infers_false(&mut ctx, term);

    let mut deferred_ctx = ReconstructCtx::new();
    deferred_ctx.defer_open_step_checks = true;
    let deferred = reconstruct_cps_test_commands(&mut deferred_ctx, &commands)
        .expect("the deferred CPS growing-clause route reconstructs");
    deferred_ctx.defer_open_step_checks = false;
    assert_infers_false(&mut deferred_ctx, deferred);
}

#[test]
fn cps_rup_rejects_a_corrupted_conflict() {
    let commands = vec![
        assume("link", vec![n_lit("x0"), p_lit("x1")]),
        assume("seed", vec![p_lit("x0")]),
        assume("conflict", vec![p_lit("x1")]),
        res_step("empty", vec![], &["link", "seed", "conflict"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let error = reconstruct_cps_test_commands(&mut ctx, &commands)
        .expect_err("the compact route must reject a non-conflicting RUP chain");
    assert!(
        matches!(error, ReconstructError::UnsupportedResolution { .. }),
        "unexpected error: {error}"
    );
}

/// Alethe gate clauses can preserve LRAT entailment while changing the recorded
/// unit order. Deterministic unit closure must recover the implication graph from
/// the premise set when the first premise is initially unresolved.
#[test]
fn reordered_rup_premises_reconstruct_by_unit_closure() {
    let commands = vec![
        assume("link", vec![n_lit("x0"), p_lit("x1")]),
        assume("seed", vec![p_lit("x0")]),
        assume("conflict", vec![n_lit("x1")]),
        res_step("empty", vec![], &["link", "seed", "conflict"]),
    ];

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("unit closure recovers a reordered RUP chain");
    assert_infers_false(&mut ctx, term);
}

/// RUP can derive a strict subclause of the stated conclusion. The direct path
/// must constructively weaken that proof to the exact conclusion shape before it
/// enters a later resolution step.
#[test]
fn ordered_rup_subclause_weakens_to_stated_conclusion() {
    let commands = vec![
        assume("reason", vec![p_lit("a"), p_lit("x")]),
        assume("conflict", vec![n_lit("x")]),
        res_step(
            "weakened",
            vec![p_lit("a"), p_lit("b")],
            &["reason", "conflict"],
        ),
        assume("not_a", vec![n_lit("a")]),
        assume("not_b", vec![n_lit("b")]),
        res_step("empty", vec![], &["not_a", "not_b", "weakened"]),
    ];

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the derived subclause is weakened and then refuted");
    assert_infers_false(&mut ctx, term);
}

/// A larger refutation exercising an intermediate **two-literal resolvent**:
/// `(a ∨ b)`, `(¬a ∨ c)`, `(¬b)`, `(¬c)`. Resolve clause 1 and 2 on `a` to get
/// `(b ∨ c)`, then peel `b` (¬b) → `(c)`, then `c` (¬c) → `(cl)`.
#[test]
fn two_literal_resolvent_refutation() {
    let commands = vec![
        assume("c1", vec![p_lit("a"), p_lit("b")]),
        assume("c2", vec![n_lit("a"), p_lit("c")]),
        assume("c3", vec![n_lit("b")]),
        assume("c4", vec![n_lit("c")]),
        // (a ∨ b) ⊗ (¬a ∨ c) on a ⇒ (b ∨ c).
        res_step("s1", vec![p_lit("b"), p_lit("c")], &["c1", "c2"]),
        // (b ∨ c) ⊗ (¬b) ⇒ (c).
        res_step("s2", vec![p_lit("c")], &["s1", "c3"]),
        // (c) ⊗ (¬c) ⇒ (cl).
        res_step("s3", vec![], &["s2", "c4"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the two-literal-resolvent refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **The `em` axiom is declared** in the resolution context (the classical
/// commitment), even though the constructive binary reconstruction never consumes
/// it. Confirm the reconstruction succeeds (so `em` admitted) and that the final
/// term still kernel-checks to `False`.
#[test]
fn em_axiom_is_declared_and_classical_commitment_noted() {
    let commands = vec![
        assume("h1", vec![p_lit("a")]),
        assume("h2", vec![n_lit("a")]),
        res_step("empty", vec![], &["h1", "h2"]),
    ];
    let mut ctx = ReconstructCtx::new();
    // `em_axiom` admits Π (p : Prop), Or p (Not p) — exercised inside the driver.
    let term = reconstruct_resolution_proof(&mut ctx, &commands).unwrap();
    assert_infers_false(&mut ctx, term);
}

/// **End-to-end from the REAL emitter**: take a small UNSAT CNF, run the clausal
/// proof pipeline (`solve_with_drat_proof` → `elaborate_drat_to_lrat` →
/// `lrat_to_alethe`), and reconstruct the emitted resolution proof to a
/// kernel-checked `False`.
#[test]
fn real_emitter_unsat_cnf_reconstructs() {
    use axeyum_cnf::{
        CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, elaborate_drat_to_lrat,
        lrat_to_alethe, solve_with_drat_proof,
    };

    // A tiny UNSAT formula: (a ∨ b) ∧ (¬a) ∧ (¬b)  with a = v0, b = v1.
    let mut formula = CnfFormula::new(2);
    let a = CnfVar::new(0).unwrap();
    let b = CnfVar::new(1).unwrap();
    formula
        .add_clause(CnfClause::new(vec![
            CnfLit::positive(a),
            CnfLit::positive(b),
        ]))
        .unwrap();
    formula
        .add_clause(CnfClause::new(vec![CnfLit::positive(a).negated()]))
        .unwrap();
    formula
        .add_clause(CnfClause::new(vec![CnfLit::positive(b).negated()]))
        .unwrap();

    let drat = match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Unsat(proof) => proof,
        other => panic!("expected UNSAT with proof, got {other:?}"),
    };
    let lrat = elaborate_drat_to_lrat(&formula, &drat).expect("DRAT elaborates to LRAT");
    let alethe = lrat_to_alethe(&formula, &lrat);

    let mut ctx = ReconstructCtx::new();
    match reconstruct_resolution_proof(&mut ctx, &alethe) {
        Ok(term) => assert_infers_false(&mut ctx, term),
        Err(e) => {
            panic!("real emitter resolution proof did not reconstruct: {e:?}\nemitted: {alethe:#?}")
        }
    }
}

/// **NEGATIVE soundness check**: a bogus resolution — resolving two clauses with
/// **no** complementary literal (`(cl a)` and `(cl b)`) cannot yield the empty
/// clause; reconstruction must REJECT, never produce a wrong `False`.
#[test]
fn bogus_resolution_no_pivot_rejected() {
    let commands = vec![
        assume("h1", vec![p_lit("a")]),
        assume("h2", vec![p_lit("b")]),
        // Claim the empty clause from two non-complementary units: unsound.
        res_step("empty", vec![], &["h1", "h2"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect_err("a pivot-free resolution to `(cl)` must be rejected");
    assert!(
        matches!(err, ReconstructError::UnsupportedResolution { .. }),
        "got {err:?}"
    );
}

/// `normalize_lit_polarity` peels `(not …)` atoms into the `negated` flag, so a
/// `+(not X)` literal and a `-X` literal canonicalize identically, so resolution's
/// pivot matching (same atom key, opposite polarity) recognizes them as
/// complementary. The upstream CNF spells some negations as the flag and some as a
/// `(not …)` atom, which previously made the matching miss them.
#[test]
fn normalize_polarity_lets_not_atoms_resolve() {
    use super::normalize_lit_polarity;
    let x = AletheTerm::Const("x".to_owned());
    let not_x = AletheTerm::App("not".to_owned(), vec![x.clone()]);

    // `+(not x)` normalizes to `-x`; `-(not x)` normalizes to `+x`.
    let plus_not_x = AletheLit {
        atom: not_x.clone(),
        negated: false,
    };
    let n = normalize_lit_polarity(&plus_not_x);
    assert_eq!(n.atom.key(), x.key());
    assert!(n.negated, "`+(not x)` must normalize to `-x`");
    let minus_not_x = AletheLit {
        atom: not_x,
        negated: true,
    };
    let n2 = normalize_lit_polarity(&minus_not_x);
    assert_eq!(n2.atom.key(), x.key());
    assert!(!n2.negated, "`-(not x)` must normalize to `+x`");

    // Raw `+x` and `+(not x)` are NOT syntactically complementary (different atom
    // keys); after normalization (`+x` and `-x`) they share an atom key with
    // opposite polarity — the pivot condition resolution partitions on.
    let plus_x = AletheLit {
        atom: x,
        negated: false,
    };
    assert_ne!(
        plus_x.atom.key(),
        plus_not_x.atom.key(),
        "raw `+x` vs `+(not x)` are not syntactically complementary"
    );
    assert!(
        n.atom.key() == plus_x.atom.key() && n.negated != plus_x.negated,
        "after normalization, `+x` vs `-x` are complementary"
    );
}

/// **NEGATIVE soundness at the kernel gate**: a resolution that DOES have a pivot
/// but claims a WRONG resolvent (`(cl c)` from `(a ∨ b) ⊗ (¬a)`, whose true
/// resolvent is `(b)`) must be rejected — the reconstructed term infers to `(b)`,
/// not `(c)`, so the `check_against` kernel gate fires.
#[test]
fn wrong_resolvent_rejected_by_kernel() {
    let commands = vec![
        assume("c1", vec![p_lit("a"), p_lit("b")]),
        assume("c2", vec![n_lit("a")]),
        // True resolvent is (b); we lie and claim (c).
        res_step("s1", vec![p_lit("c")], &["c1", "c2"]),
        assume("c3", vec![n_lit("c")]),
        res_step("s2", vec![], &["s1", "c3"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect_err("a wrong resolvent must be rejected by the kernel");
    assert!(
        matches!(
            err,
            ReconstructError::KernelRejected { .. }
                | ReconstructError::UnsupportedResolution { .. }
        ),
        "got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Tseitin CNF-introduction rules (P3.7 slice 4) — the Boolean-gate layer.
//
// Each test BUILDS a CNF-intro rule's conclusion clause over fresh atom Props,
// reconstructs it via `reconstruct_cnf_intro_rule`, and confirms the trusted
// kernel `infer`s the proof term to the clause's gate `Or`-encoding. Green =
// the kernel genuinely accepting the tautology proof.
// ---------------------------------------------------------------------------

use super::reconstruct_cnf_intro_rule;

/// `(and t…)` term over named atoms.
fn and_t(names: &[&str]) -> AletheTerm {
    AletheTerm::App("and".to_owned(), names.iter().map(|n| atom(n)).collect())
}

/// `(or t…)` term over named atoms.
fn or_t(names: &[&str]) -> AletheTerm {
    AletheTerm::App("or".to_owned(), names.iter().map(|n| atom(n)).collect())
}

/// `(xor a b)` term.
fn xor_t(a: &str, b: &str) -> AletheTerm {
    AletheTerm::App("xor".to_owned(), vec![atom(a), atom(b)])
}

/// A positive literal of a term.
fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

/// A negated literal of a term.
fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

/// Reconstruct a CNF-intro rule and confirm the kernel infers its proof to the
/// gate `Or`-encoding of the conclusion clause.
fn assert_cnf_intro_ok(rule: &str, conclusion: &[AletheLit]) {
    let mut ctx = ReconstructCtx::new();
    let proof = reconstruct_cnf_intro_rule(&mut ctx, rule, conclusion)
        .unwrap_or_else(|e| panic!("{rule} should reconstruct, got {e:?}"));
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let expected = ctx.gate_clause_to_prop(conclusion);
    assert!(
        ctx.kernel_mut().def_eq(inferred, expected),
        "{rule} proof must infer to the gate Or-encoding of its clause"
    );
}

/// `and_pos`: `(cl (not (and a b)) a)` — `¬(a∧b) ∨ a`, and the other conjunct.
#[test]
fn and_pos_reconstructs() {
    // Conjunct `a` selected.
    assert_cnf_intro_ok("and_pos", &[neg(and_t(&["a", "b"])), pos(atom("a"))]);
    // Conjunct `b` selected.
    assert_cnf_intro_ok("and_pos", &[neg(and_t(&["a", "b"])), pos(atom("b"))]);
    // A 3-ary conjunction, middle conjunct.
    assert_cnf_intro_ok("and_pos", &[neg(and_t(&["a", "b", "c"])), pos(atom("b"))]);
}

/// `and_neg`: `(cl (and a b) (not a) (not b))` — `(a∧b) ∨ ¬a ∨ ¬b`.
#[test]
fn and_neg_reconstructs() {
    assert_cnf_intro_ok(
        "and_neg",
        &[pos(and_t(&["a", "b"])), neg(atom("a")), neg(atom("b"))],
    );
    // 3-ary.
    assert_cnf_intro_ok(
        "and_neg",
        &[
            pos(and_t(&["a", "b", "c"])),
            neg(atom("a")),
            neg(atom("b")),
            neg(atom("c")),
        ],
    );
}

/// `or_pos`: `(cl (not (or a b)) a b)` — `¬(a∨b) ∨ a ∨ b`.
#[test]
fn or_pos_reconstructs() {
    assert_cnf_intro_ok(
        "or_pos",
        &[neg(or_t(&["a", "b"])), pos(atom("a")), pos(atom("b"))],
    );
    // 3-ary.
    assert_cnf_intro_ok(
        "or_pos",
        &[
            neg(or_t(&["a", "b", "c"])),
            pos(atom("a")),
            pos(atom("b")),
            pos(atom("c")),
        ],
    );
}

/// `or_neg`: `(cl (or a b) (not a))` — `(a∨b) ∨ ¬a`, and the other disjunct.
#[test]
fn or_neg_reconstructs() {
    assert_cnf_intro_ok("or_neg", &[pos(or_t(&["a", "b"])), neg(atom("a"))]);
    assert_cnf_intro_ok("or_neg", &[pos(or_t(&["a", "b"])), neg(atom("b"))]);
    assert_cnf_intro_ok("or_neg", &[pos(or_t(&["a", "b", "c"])), neg(atom("c"))]);
}

/// `equiv_pos1`: `(cl (not (= a b)) a (not b))` — `¬(a↔b) ∨ a ∨ ¬b`.
#[test]
fn equiv_pos1_reconstructs() {
    assert_cnf_intro_ok(
        "equiv_pos1",
        &[neg(eq_term("a", "b")), pos(atom("a")), neg(atom("b"))],
    );
}

/// `equiv_pos2`: `(cl (not (= a b)) (not a) b)` — `¬(a↔b) ∨ ¬a ∨ b`.
#[test]
fn equiv_pos2_reconstructs() {
    assert_cnf_intro_ok(
        "equiv_pos2",
        &[neg(eq_term("a", "b")), neg(atom("a")), pos(atom("b"))],
    );
}

/// `equiv_neg1`: `(cl (= a b) (not a) (not b))` — `(a↔b) ∨ ¬a ∨ ¬b`.
#[test]
fn equiv_neg1_reconstructs() {
    assert_cnf_intro_ok(
        "equiv_neg1",
        &[pos(eq_term("a", "b")), neg(atom("a")), neg(atom("b"))],
    );
}

/// `equiv_neg2`: `(cl (= a b) a b)` — `(a↔b) ∨ a ∨ b`.
#[test]
fn equiv_neg2_reconstructs() {
    assert_cnf_intro_ok(
        "equiv_neg2",
        &[pos(eq_term("a", "b")), pos(atom("a")), pos(atom("b"))],
    );
}

/// `xor_pos1`: `(cl (not (xor a b)) a b)` — `¬(a⊕b) ∨ a ∨ b`. xor modeled as
/// `Not (Iff a b)`.
#[test]
fn xor_pos1_reconstructs() {
    assert_cnf_intro_ok(
        "xor_pos1",
        &[neg(xor_t("a", "b")), pos(atom("a")), pos(atom("b"))],
    );
}

/// `xor_pos2`: `(cl (not (xor a b)) (not a) (not b))` — `¬(a⊕b) ∨ ¬a ∨ ¬b`.
#[test]
fn xor_pos2_reconstructs() {
    assert_cnf_intro_ok(
        "xor_pos2",
        &[neg(xor_t("a", "b")), neg(atom("a")), neg(atom("b"))],
    );
}

/// `xor_neg1`: `(cl (xor a b) a (not b))` — `(a⊕b) ∨ a ∨ ¬b`.
#[test]
fn xor_neg1_reconstructs() {
    assert_cnf_intro_ok(
        "xor_neg1",
        &[pos(xor_t("a", "b")), pos(atom("a")), neg(atom("b"))],
    );
}

/// `xor_neg2`: `(cl (xor a b) (not a) b)` — `(a⊕b) ∨ ¬a ∨ b`.
#[test]
fn xor_neg2_reconstructs() {
    assert_cnf_intro_ok(
        "xor_neg2",
        &[pos(xor_t("a", "b")), neg(atom("a")), pos(atom("b"))],
    );
}

/// **NEGATIVE soundness**: a deliberately WRONG `and_pos` conclusion — claiming
/// `¬(a∧b) ∨ b` is true while selecting the wrong-shaped clause `¬(a∧b) ∨ c`
/// (where `c` is NOT a conjunct) — is NOT a tautology and must be REJECTED. In the
/// assignment `a=T, b=T, c=F` neither `¬(a∧b)` nor `c` holds.
#[test]
fn negative_wrong_and_pos_rejected() {
    let mut ctx = ReconstructCtx::new();
    // `¬(a∧b) ∨ c` — `c` is not a conjunct of `a∧b`, so this is not a tautology.
    let conclusion = vec![neg(and_t(&["a", "b"])), pos(atom("c"))];
    let err = reconstruct_cnf_intro_rule(&mut ctx, "and_pos", &conclusion).unwrap_err();
    assert!(
        matches!(
            err,
            ReconstructError::MalformedStep { .. } | ReconstructError::KernelRejected { .. }
        ),
        "a non-tautological and_pos clause must be rejected, got {err:?}"
    );
}

/// **NEGATIVE soundness at the kernel gate**: a correctly-reconstructed `and_pos`
/// for conjunct `a` does NOT infer to a clause claiming conjunct `b` was selected.
#[test]
fn negative_and_pos_wrong_conjunct_kernel_gate() {
    let mut ctx = ReconstructCtx::new();
    // Reconstruct the correct `¬(a∧b) ∨ a`.
    let conclusion_a = vec![neg(and_t(&["a", "b"])), pos(atom("a"))];
    let proof = reconstruct_cnf_intro_rule(&mut ctx, "and_pos", &conclusion_a).unwrap();
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    // The encoding of the WRONG clause `¬(a∧b) ∨ b`.
    let conclusion_b = vec![neg(and_t(&["a", "b"])), pos(atom("b"))];
    let wrong = ctx.gate_clause_to_prop(&conclusion_b);
    assert!(
        !ctx.kernel_mut().def_eq(inferred, wrong),
        "the and_pos proof for conjunct a must NOT match the clause for conjunct b"
    );
    // And the correct encoding IS accepted.
    let right = ctx.gate_clause_to_prop(&conclusion_a);
    assert!(ctx.kernel_mut().def_eq(inferred, right));
}

/// An out-of-scope rule (here `resolution`) is rejected with a clear
/// `UnsupportedRule`, never a panic.
#[test]
fn cnf_intro_unsupported_rule_rejected() {
    let mut ctx = ReconstructCtx::new();
    let conclusion = vec![neg(and_t(&["a", "b"])), pos(atom("a"))];
    let err = reconstruct_cnf_intro_rule(&mut ctx, "resolution", &conclusion).unwrap_err();
    assert!(matches!(err, ReconstructError::UnsupportedRule { .. }));
}

/// **Determinism**: reconstructing the same CNF-intro clause twice (in two fresh
/// contexts) yields structurally-identical proof terms.
#[test]
fn cnf_intro_is_deterministic() {
    let conclusion = vec![pos(and_t(&["a", "b"])), neg(atom("a")), neg(atom("b"))];
    let mut ctx1 = ReconstructCtx::new();
    let p1 = reconstruct_cnf_intro_rule(&mut ctx1, "and_neg", &conclusion).unwrap();
    let mut ctx2 = ReconstructCtx::new();
    let p2 = reconstruct_cnf_intro_rule(&mut ctx2, "and_neg", &conclusion).unwrap();
    assert_eq!(p1, p2, "CNF-intro reconstruction must be deterministic");
}

/// R3 CNF extraction gate: both a specialized n-ary rule and the general
/// truth-table route must keep emitting byte-identical Lean modules.
#[test]
fn cnf_family_generated_source_is_byte_stable() {
    let fixtures = [
        (
            "and_pos",
            vec![neg(and_t(&["a", "b", "c"])), pos(atom("b"))],
        ),
        (
            "xor_neg1",
            vec![pos(xor_t("a", "b")), pos(atom("a")), neg(atom("b"))],
        ),
    ];
    let mut snapshots = Vec::new();
    for (rule, conclusion) in fixtures {
        let mut ctx = ReconstructCtx::new();
        let proof = reconstruct_cnf_intro_rule(&mut ctx, rule, &conclusion)
            .unwrap_or_else(|error| panic!("{rule} should reconstruct: {error:?}"));
        let proposition = ctx.gate_clause_to_prop(&conclusion);
        let inferred = ctx.kernel_mut().infer(proof).unwrap();
        assert!(ctx.kernel_mut().def_eq(inferred, proposition));
        let source = ctx
            .kernel()
            .render_lean_module("cnf_intro_fixture", proposition, proof);
        snapshots.push((source.len(), stable_source_hash(&source)));
    }

    assert_eq!(
        snapshots,
        [
            (3_358, 14_531_428_178_443_531_371),
            (4_504, 11_358_181_693_276_788_078),
        ]
    );
}

/// **COMPOSITE**: combine two reconstructed CNF-intro clauses with the slice-3
/// resolution layer to refute. Take `and_neg` ⊢ `(a∧b) ∨ ¬a ∨ ¬b` and the units
/// `a`, `b`, `¬(a∧b)`: resolving them all yields the empty clause. We reconstruct
/// the `and_neg` tautology, assume the units, and drive
/// `reconstruct_resolution_proof` to a kernel-checked `False`.
///
/// Note the resolution layer treats `(and a b)` as an OPAQUE atom (keyed by its
/// s-expression) — consistent with `and_neg`'s clause, where `(and a b)` is one
/// literal. The gate-structured `and_neg` proof's *type* is the same right-nested
/// `Or`, so feeding the clause through the opaque clausal layer is sound: both
/// layers agree on the clause's `Or` shape; only the leaf atom `(and a b)` is
/// interpreted opaquely there (its internal structure is not needed for the
/// resolution refutation).
#[test]
fn composite_and_neg_feeds_resolution_refutation() {
    // The `and_neg` clause `(cl (and a b) (not a) (not b))`.
    let and_ab = and_t(&["a", "b"]);
    let and_neg_clause = vec![pos(and_ab.clone()), neg(atom("a")), neg(atom("b"))];

    // First confirm the gate reconstruction itself kernel-checks.
    assert_cnf_intro_ok("and_neg", &and_neg_clause);

    // Now drive a clausal refutation using the SAME clause shape as an assumption:
    //   c0: (cl (and a b) (not a) (not b))   [the and_neg tautology, as a clause]
    //   c1: (cl a)                            [unit]
    //   c2: (cl b)                            [unit]
    //   c3: (cl (not (and a b)))              [unit]
    // Resolve c0 ⊗ c1 on a ⇒ ((and a b) ∨ ¬b); ⊗ c2 on b ⇒ (and a b);
    // ⊗ c3 on (and a b) ⇒ (cl). The clausal layer (opaque atoms) refutes.
    let lit_and = pos(and_ab.clone());
    let lit_nand = neg(and_ab);
    let commands = vec![
        assume("c0", and_neg_clause.clone()),
        assume("c1", vec![pos(atom("a"))]),
        assume("c2", vec![pos(atom("b"))]),
        assume("c3", vec![lit_nand.clone()]),
        res_step("s1", vec![lit_and.clone(), neg(atom("b"))], &["c0", "c1"]),
        res_step("s2", vec![lit_and], &["s1", "c2"]),
        res_step("empty", vec![], &["s2", "c3"]),
    ];
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_resolution_proof(&mut ctx, &commands)
        .expect("the and_neg-fed clausal refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

// ---------------------------------------------------------------------------
// Bit-blast reconstruction (P3.7 slice 5) — the BITWISE QF_BV fragment.
//
// Each test BUILDS a `bitblast_*` step's conclusion `(= lhs rhs)` and confirms
// the trusted kernel `infer`s the reconstructed proof term to the bit-iff
// conjunction. Green = the kernel genuinely accepting the reflexive bitblast
// equalities under the pointwise bit model.
// ---------------------------------------------------------------------------

use super::reconstruct_bitblast_step;

/// `((_ @bit_of i) name)` as a term — the emitter's bit-projection spelling.
fn bit_of(name: &str, i: i128) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i],
        args: vec![atom(name)],
    }
}

/// `(@bbterm b…)`.
fn bbterm(bits: Vec<AletheTerm>) -> AletheTerm {
    AletheTerm::App("@bbterm".to_owned(), bits)
}

/// A positive unit conclusion `(cl (= lhs rhs))`.
fn bb_concl(lhs: AletheTerm, rhs: AletheTerm) -> Vec<AletheLit> {
    vec![AletheLit {
        atom: AletheTerm::App("=".to_owned(), vec![lhs, rhs]),
        negated: false,
    }]
}

/// Reconstruct a bitblast step and confirm its proof infers to a `Prop`.
fn assert_bitblast_ok(rule: &str, conclusion: &[AletheLit]) {
    let mut ctx = ReconstructCtx::new();
    let proof = reconstruct_bitblast_step(&mut ctx, rule, conclusion)
        .unwrap_or_else(|e| panic!("{rule} should reconstruct, got {e:?}"));
    // The proof's inferred type is the bit-iff conjunction; that type is itself a
    // Prop, so inferring it again lands in a `Sort` — a genuine proof, not data.
    let ty = ctx.kernel_mut().infer(proof).unwrap();
    let ty_ty = ctx.kernel_mut().infer(ty).unwrap();
    assert!(
        matches!(ctx.kernel().expr_node(ty_ty), ExprNode::Sort(_)),
        "{rule} proof must infer to a proposition"
    );
}

/// `bitblast_var` (width 2): `(= a (@bbterm a0 a1))` ⇒ `(a0 ↔ a0) ∧ (a1 ↔ a1)`.
#[test]
fn bitblast_var_reconstructs() {
    let concl = bb_concl(atom("a"), bbterm(vec![bit_of("a", 0), bit_of("a", 1)]));
    assert_bitblast_ok("bitblast_var", &concl);
}

/// `bitblast_const` (width 2, value 0b10 = `#b10`): bit0 false, bit1 true.
#[test]
fn bitblast_const_reconstructs() {
    let concl = bb_concl(atom("#b10"), bbterm(vec![atom("false"), atom("true")]));
    assert_bitblast_ok("bitblast_const", &concl);
}

/// `bitblast_not` (width 1): `(= (bvnot a) (@bbterm (not a0)))`.
#[test]
fn bitblast_not_reconstructs() {
    let bvnot = AletheTerm::App("bvnot".to_owned(), vec![atom("a")]);
    let gadget = AletheTerm::App("not".to_owned(), vec![bit_of("a", 0)]);
    let concl = bb_concl(bvnot, bbterm(vec![gadget]));
    assert_bitblast_ok("bitblast_not", &concl);
}

/// `bitblast_and` (width 2): `(= (bvand a b) (@bbterm (and a0 b0) (and a1 b1)))`.
#[test]
fn bitblast_and_reconstructs() {
    let bvand = AletheTerm::App("bvand".to_owned(), vec![atom("a"), atom("b")]);
    let g0 = AletheTerm::App("and".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let g1 = AletheTerm::App("and".to_owned(), vec![bit_of("a", 1), bit_of("b", 1)]);
    let concl = bb_concl(bvand, bbterm(vec![g0, g1]));
    assert_bitblast_ok("bitblast_and", &concl);
}

/// `bitblast_or` (width 1): `(= (bvor a b) (@bbterm (or a0 b0)))`.
#[test]
fn bitblast_or_reconstructs() {
    let bvor = AletheTerm::App("bvor".to_owned(), vec![atom("a"), atom("b")]);
    let g0 = AletheTerm::App("or".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let concl = bb_concl(bvor, bbterm(vec![g0]));
    assert_bitblast_ok("bitblast_or", &concl);
}

/// `bitblast_xor` (width 1): `(= (bvxor a b) (@bbterm (xor a0 b0)))`.
#[test]
fn bitblast_xor_reconstructs() {
    let bvxor = AletheTerm::App("bvxor".to_owned(), vec![atom("a"), atom("b")]);
    let g0 = AletheTerm::App("xor".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let concl = bb_concl(bvxor, bbterm(vec![g0]));
    assert_bitblast_ok("bitblast_xor", &concl);
}

/// `bitblast_xnor` (width 2): `(= (bvxnor a b) (@bbterm (= a0 b0) (= a1 b1)))` —
/// pointwise `a_i ↔ b_i`.
#[test]
fn bitblast_xnor_reconstructs() {
    let bvxnor = AletheTerm::App("bvxnor".to_owned(), vec![atom("a"), atom("b")]);
    let g0 = AletheTerm::App("=".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let g1 = AletheTerm::App("=".to_owned(), vec![bit_of("a", 1), bit_of("b", 1)]);
    let concl = bb_concl(bvxnor, bbterm(vec![g0, g1]));
    assert_bitblast_ok("bitblast_xnor", &concl);
}

/// **NEGATIVE soundness** for `xnor`: a `(xor a0 b0)` gadget where the rule
/// demands `(= a0 b0)` is REJECTED at the kernel gate.
#[test]
fn bitblast_xnor_wrong_gadget_rejected() {
    let mut ctx = ReconstructCtx::new();
    let bvxnor = AletheTerm::App("bvxnor".to_owned(), vec![atom("a"), atom("b")]);
    let wrong = AletheTerm::App("xor".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let concl = bb_concl(bvxnor, bbterm(vec![wrong]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_xnor", &concl)
        .expect_err("a wrong xnor gadget must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_equal` (width 2): `(= (= a b) (and (= a0 b0) (= a1 b1)))` — a
/// predicate-shaped conclusion (no `@bbterm`); reconstructs the reflexive iff.
#[test]
fn bitblast_equal_reconstructs() {
    let bv_eq = AletheTerm::App("=".to_owned(), vec![atom("a"), atom("b")]);
    let e0 = AletheTerm::App("=".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let e1 = AletheTerm::App("=".to_owned(), vec![bit_of("a", 1), bit_of("b", 1)]);
    let b = AletheTerm::App("and".to_owned(), vec![e0, e1]);
    let concl = bb_concl(bv_eq, b);
    assert_bitblast_ok("bitblast_equal", &concl);
}

/// `bitblast_ult` (predicate): `(= (bvult a b) B)` with `B` the unsigned
/// less-than form — reconstructs the reflexive `B ↔ B` (the lhs predicate binds
/// to `B` via the bridge end-to-end). width-1: `B = (and (not a0) b0)`.
#[test]
fn bitblast_ult_reconstructs() {
    let bvult = AletheTerm::App("bvult".to_owned(), vec![atom("a"), atom("b")]);
    let b = AletheTerm::App(
        "and".to_owned(),
        vec![
            AletheTerm::App("not".to_owned(), vec![bit_of("a", 0)]),
            bit_of("b", 0),
        ],
    );
    let concl = bb_concl(bvult, b);
    assert_bitblast_ok("bitblast_ult", &concl);
}

/// `bitblast_slt` (predicate): `(= (bvslt a b) B)`. width-1 signed `<` is
/// `B = (and a0 (not b0))` (the sign bits compared).
#[test]
fn bitblast_slt_reconstructs() {
    let bvslt = AletheTerm::App("bvslt".to_owned(), vec![atom("a"), atom("b")]);
    let b = AletheTerm::App(
        "and".to_owned(),
        vec![
            bit_of("a", 0),
            AletheTerm::App("not".to_owned(), vec![bit_of("b", 0)]),
        ],
    );
    let concl = bb_concl(bvslt, b);
    assert_bitblast_ok("bitblast_slt", &concl);
}

/// **NEGATIVE soundness at the kernel gate**: a WRONG gadget bit — claiming
/// `bvand a b` bit0 is `(or a0 b0)` instead of `(and a0 b0)` — makes the reflexive
/// iff ill-typed (the two sides are distinct Props), so reconstruction is REJECTED.
#[test]
fn bitblast_wrong_gadget_rejected() {
    let mut ctx = ReconstructCtx::new();
    let bvand = AletheTerm::App("bvand".to_owned(), vec![atom("a"), atom("b")]);
    // Wrong: an `or` gadget where the model demands `and`.
    let wrong = AletheTerm::App("or".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]);
    let concl = bb_concl(bvand, bbterm(vec![wrong]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_and", &concl)
        .expect_err("a wrong gadget bit must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_extract` (`((_ extract 2 1) x)` → `x`'s bits 1..=2): result bit `i`
/// is bit `lo + i` of `x`, so `(= ((_ extract 2 1) x) (@bbterm x1 x2))`
/// reconstructs to `(x1 ↔ x1) ∧ (x2 ↔ x2)`.
#[test]
fn bitblast_extract_reconstructs() {
    let extract = AletheTerm::Indexed {
        op: "extract".to_owned(),
        indices: vec![2, 1],
        args: vec![atom("x")],
    };
    let concl = bb_concl(extract, bbterm(vec![bit_of("x", 1), bit_of("x", 2)]));
    assert_bitblast_ok("bitblast_extract", &concl);
}

/// **NEGATIVE soundness at the kernel gate** for `extract`: claiming bit 0 of
/// `((_ extract 2 1) x)` is `@bit_of 0` (it must be `@bit_of 1 = lo`) makes the
/// reflexive iff ill-typed, so reconstruction is REJECTED.
#[test]
fn bitblast_extract_wrong_offset_rejected() {
    let mut ctx = ReconstructCtx::new();
    let extract = AletheTerm::Indexed {
        op: "extract".to_owned(),
        indices: vec![2, 1],
        args: vec![atom("x")],
    };
    // Wrong: bit 0 spelled `@bit_of 0` instead of `@bit_of 1` (= lo).
    let concl = bb_concl(extract, bbterm(vec![bit_of("x", 0), bit_of("x", 2)]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_extract", &concl)
        .expect_err("a wrong extract offset must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_sign_extend` (`((_ sign_extend 2) x)` over width(x)=3): result bits
/// are `x0 x1 x2` then two copies of the sign bit `x2`. width(x) is recovered as
/// `result_width - by = 5 - 2 = 3`.
#[test]
fn bitblast_sign_extend_reconstructs() {
    let se = AletheTerm::Indexed {
        op: "sign_extend".to_owned(),
        indices: vec![2],
        args: vec![atom("x")],
    };
    let concl = bb_concl(
        se,
        bbterm(vec![
            bit_of("x", 0),
            bit_of("x", 1),
            bit_of("x", 2),
            bit_of("x", 2),
            bit_of("x", 2),
        ]),
    );
    assert_bitblast_ok("bitblast_sign_extend", &concl);
}

/// **NEGATIVE soundness** for `sign_extend`: an extended bit spelled `x1` instead
/// of the sign bit `x2` is REJECTED at the kernel gate.
#[test]
fn bitblast_sign_extend_wrong_sign_rejected() {
    let mut ctx = ReconstructCtx::new();
    let se = AletheTerm::Indexed {
        op: "sign_extend".to_owned(),
        indices: vec![2],
        args: vec![atom("x")],
    };
    // Wrong: bit 3 is `x1` (must be the sign bit `x2`).
    let concl = bb_concl(
        se,
        bbterm(vec![
            bit_of("x", 0),
            bit_of("x", 1),
            bit_of("x", 2),
            bit_of("x", 1),
            bit_of("x", 2),
        ]),
    );
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_sign_extend", &concl)
        .expect_err("a wrong sign bit must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_add` (binary, width 2): the ripple-carry result bits are
///   bit0 = `(xor (xor a0 b0) false)`
///   bit1 = `(xor (xor a1 b1) (or (and a0 b0) (and (xor a0 b0) false)))`
/// reconstructed reflexively and kernel-checked.
fn and2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("and".to_owned(), vec![a, b])
}
fn or2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("or".to_owned(), vec![a, b])
}
fn xor2(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("xor".to_owned(), vec![a, b])
}

#[test]
fn bitblast_add_binary_width2_reconstructs() {
    let bvadd = AletheTerm::App("bvadd".to_owned(), vec![atom("a"), atom("b")]);
    let false_ = atom("false");
    let bit0 = xor2(xor2(bit_of("a", 0), bit_of("b", 0)), false_.clone());
    let carry1 = or2(
        and2(bit_of("a", 0), bit_of("b", 0)),
        and2(xor2(bit_of("a", 0), bit_of("b", 0)), false_),
    );
    let bit1 = xor2(xor2(bit_of("a", 1), bit_of("b", 1)), carry1);
    let concl = bb_concl(bvadd, bbterm(vec![bit0, bit1]));
    assert_bitblast_ok("bitblast_add", &concl);
}

/// **NEGATIVE soundness at the kernel gate** for `add`: a wrong bit0 (dropping
/// the `b0` term) makes the reflexive iff ill-typed, so it is REJECTED.
#[test]
fn bitblast_add_wrong_bit_rejected() {
    let mut ctx = ReconstructCtx::new();
    let bvadd = AletheTerm::App("bvadd".to_owned(), vec![atom("a"), atom("b")]);
    // Wrong: bit0 = (xor a0 false), missing the b0 operand.
    let wrong0 = xor2(bit_of("a", 0), atom("false"));
    let concl = bb_concl(bvadd, bbterm(vec![wrong0]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_add", &concl)
        .expect_err("a wrong add bit must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// An n-ary `bitblast_add` (3 operands) is outside the binary slice and surfaces
/// as `UnsupportedTerm` from `bv_bit` — never a panic or a wrong proof.
#[test]
fn bitblast_add_nary_unsupported() {
    let mut ctx = ReconstructCtx::new();
    let bvadd = AletheTerm::App("bvadd".to_owned(), vec![atom("a"), atom("b"), atom("c")]);
    let concl = bb_concl(bvadd, bbterm(vec![atom("false")]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_add", &concl).unwrap_err();
    assert!(
        matches!(err, ReconstructError::UnsupportedTerm { .. }),
        "got {err:?}"
    );
}

/// `bitblast_neg` (width 2): two's-complement `-x = (not x) + 1` as a ripple
/// carry with carry-in `true`:
///   bit0 = `(xor (xor (not x0) false) true)`
///   bit1 = `(xor (xor (not x1) false)
///               (or (and (not x0) false) (and (xor (not x0) false) true)))`
#[test]
fn bitblast_neg_width2_reconstructs() {
    let bvneg = AletheTerm::App("bvneg".to_owned(), vec![atom("x")]);
    let nx = |i: i128| AletheTerm::App("not".to_owned(), vec![bit_of("x", i)]);
    let f = || atom("false");
    let t = || atom("true");
    let bit0 = xor2(xor2(nx(0), f()), t());
    let carry1 = or2(and2(nx(0), f()), and2(xor2(nx(0), f()), t()));
    let bit1 = xor2(xor2(nx(1), f()), carry1);
    let concl = bb_concl(bvneg, bbterm(vec![bit0, bit1]));
    assert_bitblast_ok("bitblast_neg", &concl);
}

/// **NEGATIVE soundness** for `neg`: a wrong carry-in (`false` instead of `true`)
/// makes the reflexive iff ill-typed and is REJECTED at the kernel gate.
#[test]
fn bitblast_neg_wrong_carry_in_rejected() {
    let mut ctx = ReconstructCtx::new();
    let bvneg = AletheTerm::App("bvneg".to_owned(), vec![atom("x")]);
    let nx0 = AletheTerm::App("not".to_owned(), vec![bit_of("x", 0)]);
    // Wrong: carry-in `false` (must be `true` for two's complement +1).
    let wrong0 = xor2(xor2(nx0, atom("false")), atom("false"));
    let concl = bb_concl(bvneg, bbterm(vec![wrong0]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_neg", &concl)
        .expect_err("a wrong neg carry-in must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// The inlined multiplier term is exponential in width; an 8-bit `bvmul` (top
/// bit ~41 k un-shared nodes) must be GUARDED — a clean `UnsupportedTerm`, never
/// an OOM. (Reconstruction starts at the top bit, which trips the node budget.)
#[test]
fn bitblast_mult_wide_is_guarded_not_oom() {
    let mut ctx = ReconstructCtx::new();
    let bvmul = AletheTerm::App("bvmul".to_owned(), vec![atom("a"), atom("b")]);
    // 8-bit result: the gadget bits are placeholders — the guard fires on the
    // lhs bvmul bit before any large term is built or compared.
    let bits: Vec<AletheTerm> = (0..8).map(|i| bit_of("z", i128::from(i))).collect();
    let concl = bb_concl(bvmul, bbterm(bits));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_mult", &concl)
        .expect_err("a wide multiplier must be guarded, not OOM");
    assert!(
        matches!(err, ReconstructError::UnsupportedTerm { .. }),
        "got {err:?}"
    );
}

/// `bitblast_mult` (binary, width 2): shift-add multiplier result bits are
///   bit0 = `(and b0 a0)`
///   bit1 = `(xor (xor (and b0 a1) (and b1 a0)) false)`
/// reconstructed (result bit `i` = `res[i][i]`) and kernel-checked.
#[test]
fn bitblast_mult_binary_width2_reconstructs() {
    let bvmul = AletheTerm::App("bvmul".to_owned(), vec![atom("a"), atom("b")]);
    let bit0 = and2(bit_of("b", 0), bit_of("a", 0));
    let bit1 = xor2(
        xor2(
            and2(bit_of("b", 0), bit_of("a", 1)),
            and2(bit_of("b", 1), bit_of("a", 0)),
        ),
        atom("false"),
    );
    let concl = bb_concl(bvmul, bbterm(vec![bit0, bit1]));
    assert_bitblast_ok("bitblast_mult", &concl);
}

/// **NEGATIVE soundness** for `mult`: a wrong bit0 (`(and a0 b0)` operands
/// swapped relative to the emitter's `(and b0 a0)`) is REJECTED at the kernel
/// gate — the AND's operand order is part of the Prop identity.
#[test]
fn bitblast_mult_wrong_bit_rejected() {
    let mut ctx = ReconstructCtx::new();
    let bvmul = AletheTerm::App("bvmul".to_owned(), vec![atom("a"), atom("b")]);
    // Wrong: `(and a0 b0)` — the emitter spells bit0 as `(and b0 a0)`.
    let wrong0 = and2(bit_of("a", 0), bit_of("b", 0));
    let concl = bb_concl(bvmul, bbterm(vec![wrong0]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_mult", &concl)
        .expect_err("a wrong mult bit must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_concat` (width 2 high `a`, width 3 low `b`): result bits are the low
/// operand's first, then the high operand's — `b0 b1 b2 a0 a1`. Operand widths
/// come from the `@bbterm` operands here (the recorded-width path is exercised
/// end-to-end).
#[test]
fn bitblast_concat_reconstructs() {
    let hi = bbterm(vec![bit_of("a", 0), bit_of("a", 1)]);
    let lo = bbterm(vec![bit_of("b", 0), bit_of("b", 1), bit_of("b", 2)]);
    let concat = AletheTerm::App("concat".to_owned(), vec![hi, lo]);
    let concl = bb_concl(
        concat,
        bbterm(vec![
            bit_of("b", 0),
            bit_of("b", 1),
            bit_of("b", 2),
            bit_of("a", 0),
            bit_of("a", 1),
        ]),
    );
    assert_bitblast_ok("bitblast_concat", &concl);
}

/// **NEGATIVE soundness** for `concat`: putting the high operand's bits first
/// (`a0 …` instead of the low operand `b0 …`) is REJECTED at the kernel gate.
#[test]
fn bitblast_concat_wrong_order_rejected() {
    let mut ctx = ReconstructCtx::new();
    let hi = bbterm(vec![bit_of("a", 0), bit_of("a", 1)]);
    let lo = bbterm(vec![bit_of("b", 0), bit_of("b", 1), bit_of("b", 2)]);
    let concat = AletheTerm::App("concat".to_owned(), vec![hi, lo]);
    // Wrong: bit 0 is `a0` (must be the low operand's `b0`).
    let concl = bb_concl(
        concat,
        bbterm(vec![
            bit_of("a", 0),
            bit_of("b", 1),
            bit_of("b", 2),
            bit_of("a", 0),
            bit_of("a", 1),
        ]),
    );
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_concat", &concl)
        .expect_err("a wrong concat order must be rejected by the kernel");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "got {err:?}"
    );
}

/// `bitblast_comp` (width 2): `(bvcomp a b)` is a 1-bit result whose only bit is
/// the per-bit-equality AND `(and (= a0 b0) (= a1 b1))`. Operand width comes from
/// the `@bbterm` operands here.
#[test]
fn bitblast_comp_reconstructs() {
    let a = bbterm(vec![bit_of("a", 0), bit_of("a", 1)]);
    let b = bbterm(vec![bit_of("b", 0), bit_of("b", 1)]);
    let bvcomp = AletheTerm::App("bvcomp".to_owned(), vec![a, b]);
    let g = AletheTerm::App(
        "and".to_owned(),
        vec![
            AletheTerm::App("=".to_owned(), vec![bit_of("a", 0), bit_of("b", 0)]),
            AletheTerm::App("=".to_owned(), vec![bit_of("a", 1), bit_of("b", 1)]),
        ],
    );
    let concl = bb_concl(bvcomp, bbterm(vec![g]));
    assert_bitblast_ok("bitblast_comp", &concl);
}

/// A bitblast rule still outside the reconstructed fragment (`bitblast_shl`, a
/// shift — a Carcara hole the emitter never produces) is rejected with a clear
/// `UnsupportedRule`, never a panic.
#[test]
fn bitblast_shl_is_unsupported() {
    let mut ctx = ReconstructCtx::new();
    let shl = AletheTerm::App("bvshl".to_owned(), vec![atom("a"), atom("b")]);
    let concl = bb_concl(shl, bbterm(vec![bit_of("a", 0)]));
    let err = reconstruct_bitblast_step(&mut ctx, "bitblast_shl", &concl).unwrap_err();
    assert!(
        matches!(err, ReconstructError::UnsupportedRule { .. }),
        "got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// THE STRETCH: a full bitwise QF_BV `unsat` proof from the REAL emitter,
// reconstructed end-to-end to a kernel-checked `False`.
// ---------------------------------------------------------------------------

use super::reconstruct_qf_bv_proof;

/// A top-level self-disequality `not (= t t)` is unsat by reflexivity, even when
/// `t` is a BV term the bit-blast emitter does not otherwise refute directly.
/// The direct structural route closes it with only the input assumption and
/// `Eq.refl`.
#[test]
fn end_to_end_reflexive_disequality_reconstructs_directly() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let x = {
        let s = arena.declare("x", Sort::BitVec(6)).unwrap();
        arena.var(s)
    };
    let all_ones = arena.bv_const(6, 0b11_1111).unwrap();
    let comp = arena.bv_comp(x, all_ones).unwrap();
    let eq = arena.eq(comp, comp).unwrap();
    let diseq = arena.not(eq).unwrap();

    assert_eq!(
        scan_proof_fragment(&arena, &[diseq]),
        ProofFragment::ReflexiveDisequality
    );
    let (fragment, source) =
        prove_unsat_to_lean_module(&mut arena, &[diseq]).expect("self-disequality reconstructs");
    assert_eq!(fragment, ProofFragment::ReflexiveDisequality);
    assert!(
        !source.contains("sorryAx"),
        "self-disequality module must not use sorryAx:\n{source}"
    );
}

/// **END-TO-END (the milestone)**: a 1-bit `(= (bvand a b) a) ∧ (not (= (bvand a
/// b) a))` is unsat; the REAL `prove_qf_bv_unsat_alethe` emits the full bitwise
/// proof (`bitblast_var`/`and`/`equal` + cong/trans + equiv + CNF-intro + resolution),
/// and `reconstruct_qf_bv_proof` reconstructs it to a kernel-checked `False`.
///
/// Every BITWISE `bitblast_*` step's bit-iff content is separately kernel-checked
/// during the walk; the closing `(cl)` is `infer`-checked against `False`.
#[test]
fn end_to_end_bitwise_bvand_refutation_to_false() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let and = arena.bv_and(a, b).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq])
        .expect("emitter produces the bitwise refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("the bitwise QF_BV refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// R3 bit-blast extraction gate: both a pointwise Boolean operator and an
/// arithmetic ripple-carry operator must keep emitting byte-identical modules.
#[test]
fn bitblast_family_generated_source_is_byte_stable() {
    let mut snapshots = Vec::new();

    let mut arena = TermArena::new();
    let a = {
        let symbol = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(symbol)
    };
    let b = {
        let symbol = arena.declare("b", Sort::BitVec(1)).unwrap();
        arena.var(symbol)
    };
    let and = arena.bv_and(a, b).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    snapshots.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let mk = |arena: &mut TermArena, name: &str| {
        let symbol = arena.declare(name, Sort::BitVec(2)).unwrap();
        arena.var(symbol)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let c = mk(&mut arena, "c");
    let sum = arena.bv_add(a, b).unwrap();
    let eq = arena.eq(sum, c).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    let source = render_ctx_module(&mut ctx, term);
    snapshots.push((source.len(), stable_source_hash(&source)));

    assert_eq!(
        snapshots,
        [
            (6_171, 6_475_695_101_939_760_022),
            (19_619, 1_281_267_001_421_498_970),
        ]
    );
}

/// The same, width 2, with a direct `(= a b) ∧ (not (= a b))` (all-leaf predicate
/// → the v1 direct `bitblast_equal` path, no cong/trans).
#[test]
fn end_to_end_bitwise_eq_refutation_to_false() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(a, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Assert the reconstruction declared **only** the input-assumption hypotheses and
/// `em` — no bridge axiom (`cong`/`trans`/`equiv`/`bitblast`). `expected_assumes` is
/// how many input `assume` clauses the proof has. This is the slice-6 closedness bar.
fn assert_closed_over_assumptions(ctx: &ReconstructCtx, expected_assumes: usize) {
    let roles = ctx.declared_axiom_roles();
    let assumes = roles.iter().filter(|r| r.as_str() == "assume").count();
    let ems = roles.iter().filter(|r| r.as_str() == "em").count();
    assert_eq!(
        assumes, expected_assumes,
        "expected {expected_assumes} input-assumption hypotheses, got roles {roles:?}"
    );
    assert!(ems <= 1, "at most one `em` axiom, got roles {roles:?}");
    // The crux: nothing else. No `cong`/`trans`/`equiv*`/`bitblast_*` bridge axiom.
    let bridge: Vec<&String> = roles
        .iter()
        .filter(|r| r.as_str() != "assume" && r.as_str() != "em")
        .collect();
    assert!(
        bridge.is_empty(),
        "the fused `False` must be closed over only input assumptions + `em`; \
         found extra axiom roles {bridge:?}"
    );
}

/// **THE SLICE-6 BAR — closed bitwise proof**: the `(= (bvand a b) a) ∧ ¬…`
/// refutation reconstructs to a `False` term **closed over only the two input
/// `assume` hypotheses and `em`** — there is NO bridge axiom for
/// `cong`/`trans`/`equiv1`/`equiv2`/`bitblast_*`. The bridge is fused by modeling
/// each predicate directly in its bit-level `Prop` form.
#[test]
fn end_to_end_bitwise_bvand_is_closed_over_assumptions() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let and = arena.bv_and(a, b).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    // The new soundness bar: closed over only the input assumptions + em.
    assert_closed_over_assumptions(&ctx, 2);
}

/// The same closedness bar for the width-2 direct-`bitblast_equal` path
/// (`(= a b) ∧ ¬(= a b)`): a fused `False`, no bridge axioms.
#[test]
fn end_to_end_bitwise_eq_is_closed_over_assumptions() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(a, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
    assert_closed_over_assumptions(&ctx, 2);
}

/// **Scalability regression guard (P3.7).** A nested 3-bit arithmetic refutation
/// `(bvadd (bvmul a b) (bvneg c)) = a ∧ ¬(…)` exercises every gate kind (multiplier
/// and-trees, ripple-carry adder, the equiv1/equiv2 bridge over the full bit
/// equality). Before the polynomial CNF-introduction + bridge proofs this took
/// **> 60 s** (a `2^leaves` truth-table per Tseitin tautology); it now reconstructs
/// in tens of ms. If the exponential case-split ever returns, THIS test hangs the
/// suite — that is the intended canary. It must still close to a kernel-checked
/// `False`.
#[test]
fn end_to_end_nested_arith_reconstructs_polynomially() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(3)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let c = mk(&mut arena, "c");
    let mul = arena.bv_mul(a, b).unwrap();
    let neg = arena.bv_neg(c).unwrap();
    let add = arena.bv_add(mul, neg).unwrap();
    let eq = arena.eq(add, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("nested arithmetic refutation must reconstruct to kernel-checked False");
    assert_infers_false(&mut ctx, term);
}

/// **Derived-operator coverage via lowering (P3.7).** `bvsub` has no core bitblast
/// rule, but `axeyum_rewrite::lower_derived_bv` rewrites it to `bvadd a (bvneg b)`
/// (denotation-preserving, exhaustively tested in `axeyum-rewrite`). After lowering,
/// `(bvsub a b) = a ∧ ¬(…)` emits a core-only proof that reconstructs to a
/// kernel-checked `False` — the proof track now covers `bvsub` end to end.
#[test]
fn end_to_end_bvsub_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(2)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let sub = arena.bv_sub(a, b).unwrap();
    let eq = arena.eq(sub, a).unwrap();
    let neq = arena.not(eq).unwrap();
    // `prove_…_lowered` lowers bvsub→add+neg internally; the emitter (no bitblast_sub)
    // then sees core ops only.
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// The comparison family lowers too: `bvule a b → ¬(bvult b a)`. The unsat pair
/// `bvule a b ∧ bvult b a` (`a ≤ b` and `b < a`) lowers to `¬(bvult b a) ∧ bvult b a`
/// — core ops only — and reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_bvule_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(2)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let le = arena.bv_ule(a, b).unwrap();
    let gt = arena.bv_ult(b, a).unwrap();
    // `bvule a b` lowers to `¬(bvult b a)`; paired with `bvult b a` this is `¬Q ∧ Q`.
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[le, gt])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Structural lowering: `zero_extend k a → concat (0:k) a` (core ops). Exercises
/// `bitblast_concat` reconstruction with a **constant** high operand (the case that
/// the `operand_bit_term`/`gate_term_to_prop` Boolean-literal fix unblocked).
#[test]
fn end_to_end_zero_extend_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let ze = arena.zero_ext(2, a).unwrap(); // width 4
    let eq = arena.eq(ze, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Structural lowering: `rotate_left k a → concat (extract …) (extract …)` (core
/// **Composition guard.** Several derived operators in one formula must lower and
/// reconstruct together. `bvule (bvsub a b) c ∧ bvult c (bvsub a b)` is `¬Q ∧ Q`
/// (where `Q = bvult c (a-b)`): it nests `bvsub` inside both a `bvule` and a `bvult`.
/// Lowering rewrites all three to core; the conjunction reconstructs to a
/// kernel-checked `False`.
#[test]
fn end_to_end_mixed_derived_ops_compose() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(3)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let c = mk(&mut arena, "c");
    let diff = arena.bv_sub(a, b).unwrap();
    let le = arena.bv_ule(diff, c).unwrap(); // a-b ≤ c
    let gt = arena.bv_ult(c, diff).unwrap(); // c < a-b  (= ¬(a-b ≤ c))
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[le, gt])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Composition: a constant **shift** feeding a **comparison** pair.
/// `bvult (bvshl a 1) c ∧ bvule c (bvshl a 1)` is `Q ∧ ¬Q` (`bvule c x = ¬bvult x c`);
/// both the shift and the two comparisons lower to core and reconstruct to `False`.
#[test]
fn end_to_end_shift_into_comparison_composes() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(3)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let c = mk(&mut arena, "c");
    let one = arena.bv_const(3, 1).unwrap();
    let sh = arena.bv_shl(a, one).unwrap();
    let q = arena.bv_ult(sh, c).unwrap(); // bvult (a<<1) c
    let nq = arena.bv_ule(c, sh).unwrap(); // bvule c (a<<1) = ¬q
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[q, nq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Composition: **nested** derived ops — a `bvnand` inside a `rotate`, equated.
/// `(rotate_left (bvnand a b) 1) = d ∧ ¬(…)` exercises a derived op feeding another
/// derived op (the rotate lowers to `concat`/`extract` over the lowered `bvnand`).
#[test]
fn end_to_end_nested_derived_ops_compose() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(4)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let d = mk(&mut arena, "d");
    let nand = arena.bv_nand(a, b).unwrap();
    let rot = arena.rotate_left(1, nand).unwrap();
    let eq = arena.eq(rot, d).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// ops). A `(rotate_left a 1) = b ∧ ¬(…)` query reconstructs to a kernel-checked
/// `False`.
#[test]
fn end_to_end_rotate_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let r = arena.rotate_left(1, a).unwrap();
    let eq = arena.eq(r, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Constant-amount shift lowering: `bvshl a #b0001 → concat (extract 2 0 a) (0:1)`
/// (core ops). A `(bvshl a 1) = b ∧ ¬(…)` query reconstructs to a kernel-checked
/// `False` — covers a constant shift end to end (exercises `concat` with a constant
/// low operand).
#[test]
fn end_to_end_const_shift_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let one = arena.bv_const(4, 1).unwrap();
    let shl = arena.bv_shl(a, one).unwrap();
    let eq = arena.eq(shl, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Variable-amount shift lowering: `bvshl a s` (non-constant `s`) → a barrel-shifter
/// network of constant shifts + `and`/`or`/`not` muxes (all core). A `(bvshl a s) =
/// b ∧ ¬(…)` query reconstructs to a kernel-checked `False` — the "hard" shift case
/// now closes end to end.
#[test]
fn end_to_end_variable_shift_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(4)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let s = mk(&mut arena, "s");
    let b = mk(&mut arena, "b");
    let shl = arena.bv_shl(a, s).unwrap();
    let eq = arena.eq(shl, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// `bvmul` lowered to a **shift-add** core network (no inlined `mult_bit_term` tree)
/// reconstructs end-to-end to a kernel-checked `False` via the projection encoding.
/// The lowering is polynomial-size (vs the exponential multiplier gadget), so it
/// scales to widths the gadget cannot — kept at width 3 here only for suite speed.
#[test]
fn end_to_end_bvmul_shift_add_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(3)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let c = mk(&mut arena, "c");
    let m = arena.bv_mul(a, b).unwrap();
    let eq = arena.eq(m, c).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// Unsigned division lowering: `bvudiv` → an unrolled long-division network of core
/// ops. At width 2 this reconstructs end-to-end to a kernel-checked `False`. It
/// exercises the `cnf_intro`-over-Boolean-constant fix (the divider's adders over
/// zero-const bits produce `xor` clauses whose operands are `false`/`(not false)`).
/// NOTE: larger widths are blocked by the multiplier-style term blowup (coverage
/// note), so this is kept at width 2.
#[test]
fn end_to_end_udiv_width2_via_lowering_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(2)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let y = mk(&mut arena, "y");
    let b = mk(&mut arena, "b");
    let d = arena.bv_udiv(a, y).unwrap();
    let eq = arena.eq(d, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_lowered(&mut arena, &[eq, neq])
        .expect("emitter accepts lowered core");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof).expect("reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **NEGATIVE soundness (slice 6)**: corrupt the closing resolution of a REAL
/// bitwise proof — drop a premise so it can no longer fold to `(cl)` — and confirm
/// the fused walk REJECTS it rather than producing a `False` from a non-refutation.
#[test]
fn end_to_end_bitwise_corrupted_close_rejected() {
    use axeyum_cnf::AletheCommand;
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let and = arena.bv_and(a, b).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let mut proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");

    // Corrupt the final `(cl)` step: keep only its first premise, so it can no
    // longer resolve to the empty clause.
    if let Some(AletheCommand::Step {
        clause, premises, ..
    }) = proof.last_mut()
        && clause.is_empty()
        && premises.len() >= 2
    {
        premises.truncate(1);
    }

    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect_err("a corrupted closing resolution must be rejected, never a wrong False");
    assert!(
        matches!(
            err,
            ReconstructError::UnsupportedResolution { .. }
                | ReconstructError::KernelRejected { .. }
        ),
        "corruption must surface as a sound rejection, got {err:?}"
    );
}

/// **End-to-end**: a real `(= (bvadd a b) a) ∧ ¬…` `QF_BV` unsat proof — whose
/// bit-blast goes through the ripple-carry `bitblast_add` — now reconstructs all
/// the way to a kernel-checked `False`.
#[test]
fn end_to_end_add_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let add = arena.bv_add(a, b).unwrap();
    let eq = arena.eq(add, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a binary-add QF_BV proof must reconstruct to kernel-checked False");
}

/// **THE CLOSEDNESS BAR for the ripple-carry adder**: the `(= (bvadd a b) a) ∧ ¬…`
/// refutation — whose bit-blast runs the carry-chain `bitblast_add` — reconstructs
/// to a `False` term **closed over only the two input `assume` hypotheses and
/// `em`**. There is NO load-bearing bridge/bitblast/carry axiom: the per-bit carry
/// recurrence is proved as an `em`-tautology iff and fused through the equiv1/equiv2
/// bridge, leaving no `cong`/`trans`/`bitblast_add` axiom in `declared_axiom_roles`.
#[test]
fn end_to_end_add_is_closed_over_assumptions() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let add = arena.bv_add(a, b).unwrap();
    let eq = arena.eq(add, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a binary-add QF_BV proof must reconstruct to kernel-checked False");
    assert_infers_false(&mut ctx, term);
    // The crux: a bvadd-containing fused `False` is still closed over only the input
    // assumptions + `em` — no carry/bridge axiom is left load-bearing.
    assert_closed_over_assumptions(&ctx, 2);
}

/// **End-to-end**: a `(= (bvneg a) a) ∧ ¬…` `QF_BV` unsat proof — bit-blasted via
/// the two's-complement ripple-carry `bitblast_neg` — reconstructs to a
/// kernel-checked `False`.
#[test]
fn end_to_end_neg_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let neg = arena.bv_neg(a).unwrap();
    let eq = arena.eq(neg, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvneg QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end**: a `(= (bvxnor a b) a) ∧ ¬…` `QF_BV` unsat proof — bit-blasted
/// via the pointwise `bitblast_xnor` — reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_xnor_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let xnor = arena.bv_xnor(a, b).unwrap();
    let eq = arena.eq(xnor, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvxnor QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end**: a `(= ((_ sign_extend 2) a) d) ∧ ¬…` `QF_BV` unsat proof —
/// bit-blasted via `bitblast_sign_extend` — reconstructs to a kernel-checked
/// `False`.
#[test]
fn end_to_end_sign_extend_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let se = arena.sign_ext(2, a).unwrap(); // width 4
    let d = {
        let s = arena.declare("d", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(se, d).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a sign_extend QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end**: a `(= (bvmul a b) a) ∧ ¬…` `QF_BV` unsat proof — bit-blasted
/// via the shift-add `bitblast_mult` — reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_mul_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let mul = arena.bv_mul(a, b).unwrap();
    let eq = arena.eq(mul, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvmul QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end (projection-encoding win, P3.7).** A **nested** multiply
/// `(= (bvmul (bvmul a b) c) (bvmul (bvmul a b) c))` (negated → unsat) over **width
/// 4**. Under the old *inlined* `@bbterm`-form reduction the outer `bvmul`'s gadget
/// embedded the inner `(bvmul a b)`'s full bit-tree, squaring the node count per
/// nesting level — so a nested multiply blew up emission/reconstruction at ~width 3.
/// With the **projection** encoding (Carcara's own `build_term_vec` scheme), the
/// outer step references `((_ @bit_of i) (bvmul a b))` projections and the inner
/// multiply is a *separate*, bounded `bitblast_equal` bit-definition — so the proof
/// stays `O(size²)` per term and this nested width-4 case reconstructs to a
/// kernel-checked `False`. If the inlining regresses, this hangs the suite.
#[test]
fn end_to_end_nested_mul_projection_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(4)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let c = mk(&mut arena, "c");
    let ab = arena.bv_mul(a, b).unwrap();
    let abc = arena.bv_mul(ab, c).unwrap();
    let eq = arena.eq(abc, abc).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a nested-bvmul QF_BV proof must reconstruct to kernel-checked False");
    assert_infers_false(&mut ctx, term);
}

/// **End-to-end**: a `(= (concat a b) d) ∧ ¬…` `QF_BV` unsat proof — bit-blasted
/// via `bitblast_concat`, with operand widths recovered from the `bitblast_var`
/// leaves — reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_concat_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let cat = arena.concat(a, b).unwrap(); // width 4
    let d = {
        let s = arena.declare("d", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(cat, d).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a concat QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end**: `(bvult a b) ∧ ¬(bvult a b)` — bit-blasted via the unsigned
/// less-than `bitblast_ult`, the predicate bridged to its ladder `B` — reconstructs
/// to a kernel-checked `False`.
#[test]
fn end_to_end_ult_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let ult = arena.bv_ult(a, b).unwrap();
    let nult = arena.not(ult).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[ult, nult]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvult QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end**: `(bvslt a b) ∧ ¬(bvslt a b)` — bit-blasted via the signed
/// less-than `bitblast_slt` — reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_slt_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let slt = arena.bv_slt(a, b).unwrap();
    let nslt = arena.not(slt).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[slt, nslt]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvslt QF_BV proof must reconstruct to kernel-checked False");
}

/// **End-to-end, GENUINELY unsat (not `x ∧ ¬x`)**: `(bvult a b) ∧ (bvult b a)` is
/// unsatisfiable by antisymmetry. Its refutation is a real resolution DAG — the
/// case the Davis–Putnam resolution reconstruction was built for (greedy/pool/
/// chain folds all dead-end here). It reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_ult_antisymmetry_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let ab = arena.bv_ult(a, b).unwrap();
    let ba = arena.bv_ult(b, a).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[ab, ba]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("bvult antisymmetry must reconstruct to kernel-checked False");
}

/// **End-to-end**: a `(= (bvcomp a b) c) ∧ ¬…` `QF_BV` unsat proof — bit-blasted
/// via `bitblast_comp` (the per-bit-equality AND, operand width from the
/// `bitblast_var` leaves) — reconstructs to a kernel-checked `False`.
#[test]
fn end_to_end_comp_reconstructs() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let comp = arena.bv_comp(a, b).unwrap(); // 1-bit result
    let c = {
        let s = arena.declare("c", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(comp, c).unwrap();
    let neq = arena.not(eq).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("emitter");
    let mut ctx = ReconstructCtx::new();
    reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("a bvcomp QF_BV proof must reconstruct to kernel-checked False");
}

// ===========================================================================
// LRA `la_generic` (Farkas) reconstruction tests (P3.7 arithmetic, slice 1).
// ===========================================================================

/// R3 arithmetic extraction gate: one linear Farkas proof and one nonlinear
/// SOS proof must keep emitting byte-identical Lean modules when the shared
/// arithmetic context, exact-linear forms, and ring normalizer move behind one
/// cohesive submodule.
#[test]
fn arithmetic_family_generated_source_is_byte_stable() {
    use axeyum_ir::{Rational, TermArena};

    let mut snapshots = Vec::new();

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let upper = arena.real_le(x, zero).unwrap();
    let lower = arena.real_le(one, x).unwrap();
    let mut ctx = super::LraReconstructCtx::new();
    let proof = super::reconstruct_lra_proof(&mut ctx, &arena, &[upper, lower])
        .expect("linear fixture reconstructs");
    let source = super::gate_and_render_lra_module(&mut ctx, proof, "LRA")
        .expect("linear fixture renders");
    snapshots.push((source.len(), stable_source_hash(&source)));

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let square = arena.real_mul(x, x).unwrap();
    let negative_square = arena.real_lt(square, zero).unwrap();
    let source = super::reconstruct_sos_to_lean_module(&arena, &[negative_square])
        .expect("SOS fixture reconstructs and renders");
    snapshots.push((source.len(), stable_source_hash(&source)));

    assert_eq!(
        snapshots,
        [
            (7_747, 232_852_107_906_522_853),
            (1_088, 9_042_568_084_332_375_518),
        ]
    );
}

/// **The bar**: a real `x ≤ 0 ∧ 1 ≤ x` LRA `unsat` instance reconstructs, via its
/// REAL self-checked Farkas certificate, to a kernel-checked Lean term of type
/// `False` over the arithmetic prelude (the baby-Farkas order chain).
#[test]
fn lra_transitivity_reconstructs_to_false() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_le(x, zero).unwrap(); // x ≤ 0
    let a2 = arena.real_le(one, x).unwrap(); // 1 ≤ x

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("transitivity LRA unsat reconstructs to False");

    // The returned term's inferred type is def_eq to `False` (already gated inside
    // reconstruct_lra_proof, re-confirmed here for the bar).
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(
        ctx.kernel_mut().def_eq(inferred, false_),
        "reconstructed LRA term must infer to False"
    );
}

/// The `≥`-phrased variant `x ≤ 0 ∧ x ≥ 1` reaches the same kernel-checked `False`
/// (the `≥` is normalized into the `1 ≤ x` lower bound).
#[test]
fn lra_transitivity_ge_phrasing_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_le(x, zero).unwrap(); // x ≤ 0
    let a2 = arena.real_ge(x, one).unwrap(); // x ≥ 1

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("≥-phrased transitivity LRA unsat reconstructs to False");
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(ctx.kernel_mut().def_eq(inferred, false_));
}

/// **Strict-`<` antisymmetry** `x < y ∧ y < x` reconstructs to a kernel-checked
/// `False` via `lt_trans` → `lt x x` → `lt_irrefl` (the strict sibling of the `≤`
/// baby shape, and the base case of an N-cycle).
#[test]
fn lra_strict_antisymmetry_reconstructs() {
    use axeyum_ir::TermArena;

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let a1 = arena.real_lt(x, y).unwrap(); // x < y
    let a2 = arena.real_lt(y, x).unwrap(); // y < x

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("strict antisymmetry LRA unsat reconstructs to False");
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(
        ctx.kernel_mut().def_eq(inferred, false_),
        "strict-antisymmetry LRA term must infer to False"
    );
}

/// **Strict-`<` 3-cycle** `x < y ∧ y < z ∧ z < x` reconstructs to a kernel-checked
/// `False` via `lt_trans` folded around the cycle → `lt x x` → `lt_irrefl`. Exercises
/// the N-constraint generalization (`try_strict_cycle`) beyond the 2-constraint case.
#[test]
fn lra_strict_3cycle_reconstructs() {
    use axeyum_ir::TermArena;

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let a1 = arena.real_lt(x, y).unwrap(); // x < y
    let a2 = arena.real_lt(y, z).unwrap(); // y < z
    let a3 = arena.real_lt(z, x).unwrap(); // z < x

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2, a3])
        .expect("strict 3-cycle LRA unsat reconstructs to False");
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(
        ctx.kernel_mut().def_eq(inferred, false_),
        "strict-3-cycle LRA term must infer to False"
    );
}

/// A **satisfiable** instance has no Farkas refutation, so reconstruction is
/// rejected (a `MalformedStep`, never a wrong `False`).
#[test]
fn lra_satisfiable_is_rejected() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, ReconstructError, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let five = arena.real_const(Rational::integer(5));
    let a = arena.real_le(x, five).unwrap(); // x ≤ 5, satisfiable

    let mut ctx = LraReconstructCtx::new();
    let err = reconstruct_lra_proof(&mut ctx, &arena, &[a])
        .expect_err("a satisfiable instance has no Farkas refutation");
    assert!(
        matches!(err, ReconstructError::MalformedStep { .. }),
        "got {err:?}"
    );
}

/// What used to be "out of slice 1" — `2x ≤ -1 ∧ x ≥ 0`, whose Farkas refutation
/// needs a `2`-coefficient term (`1·(2x+1) + 2·(−x) = 1 > 0`) — is now reconstructed
/// by the general ring engine to a kernel-checked `False`. (This was previously a
/// rejection test; the general Farkas path subsumes it.)
#[test]
fn lra_general_two_coeff_with_constant_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let neg_one = arena.real_const(Rational::integer(-1));
    let zero = arena.real_const(Rational::integer(0));
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_le(two_x, neg_one).unwrap(); // 2x ≤ -1
    let a2 = arena.real_ge(x, zero).unwrap(); // x ≥ 0

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("integer-coefficient Farkas shape reconstructs via the general engine");
    assert_lra_infers_false(&mut ctx, proof);
}

/// A genuinely out-of-scope `unsat` instance — `(1/2)·x ≤ -1 ∧ x ≥ 0`, whose Farkas
/// atom `(1/2)x + 1 ≤ 0` carries a **non-integer** coefficient — is rejected (the
/// additive ring engine only models integer-coefficient atoms), honestly reporting
/// the boundary rather than guessing a `False`.
#[test]
fn lra_noninteger_coefficient_is_rejected() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, ReconstructError, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let half = arena.real_const(Rational::new(1, 2));
    let neg_one = arena.real_const(Rational::integer(-1));
    let zero = arena.real_const(Rational::integer(0));
    let half_x = arena.real_mul(half, x).unwrap();
    let a1 = arena.real_le(half_x, neg_one).unwrap(); // (1/2)x ≤ -1
    let a2 = arena.real_ge(x, zero).unwrap(); // x ≥ 0

    let mut ctx = LraReconstructCtx::new();
    let err = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect_err("a non-integer-coefficient atom is outside the additive ring engine");
    assert!(
        matches!(
            err,
            ReconstructError::MalformedStep { .. } | ReconstructError::UnsupportedTerm { .. }
        ),
        "got {err:?}"
    );
}

/// **NEGATIVE soundness**: a non-`False` proposition (`zero_lt_one : lt zero one`)
/// is NOT `def_eq` to `False`, so the kernel gate would reject any claim that it is.
/// This proves the trusted gate — not the untrusted glue — guarantees soundness: a
/// wrong combination can never be accepted as `False`.
#[test]
fn lra_bogus_combination_is_kernel_rejected() {
    use super::LraReconstructCtx;

    let mut ctx = LraReconstructCtx::new();
    let zlo = {
        let n = ctx.arith().zero_lt_one;
        ctx.kernel_mut().const_(n, vec![])
    };
    let inferred = ctx.kernel_mut().infer(zlo).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(
        !ctx.kernel_mut().def_eq(inferred, false_),
        "a non-False proposition must NOT be def_eq to False (the soundness gate)"
    );
}

/// Determinism: reconstructing the same instance twice yields a structurally
/// identical proof term (same `ExprId`), since interning is insertion-ordered.
#[test]
fn lra_reconstruction_is_deterministic() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let build = || {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let one = arena.real_const(Rational::integer(1));
        let a1 = arena.real_le(x, zero).unwrap();
        let a2 = arena.real_le(one, x).unwrap();
        let mut ctx = LraReconstructCtx::new();
        reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2]).unwrap()
    };
    assert_eq!(build(), build(), "LRA reconstruction must be deterministic");
}

/// Assert that a reconstructed LRA term's inferred type is `def_eq` to `False`.
fn assert_lra_infers_false(ctx: &mut super::LraReconstructCtx, proof: super::ExprId) {
    let inferred = ctx.kernel_mut().infer(proof).unwrap();
    let false_ = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    assert!(
        ctx.kernel_mut().def_eq(inferred, false_),
        "reconstructed LRA term must infer to False"
    );
}

/// **Non-unit multipliers, 2 constraints**: `2x ≤ 0 ∧ 1 ≤ x`. The Farkas
/// refutation needs `λ = (1, 2)`: `1·(2x) + 2·(1 - x) = 2 > 0`. This is the first
/// case beyond the unit-multiplier / `{-1,0,+1}` slice, exercising the general
/// ring engine (scale `1 ≤ x` by 2, sum, cancel `2x` against `-2x`, leave `2`).
#[test]
fn lra_general_two_constraint_nonunit_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_le(two_x, zero).unwrap(); // 2x ≤ 0
    let a2 = arena.real_le(one, x).unwrap(); // 1 ≤ x

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("non-unit-multiplier 2-constraint Farkas reconstructs to False");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **N-constraint general Farkas** (3 constraints, multiple variables):
/// `x + y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y`. The refutation is `1·(x+y) + 1·(1-x) + 1·(1-y) = 2 > 0`;
/// the variables cancel across three constraints. Exercises the multi-constraint,
/// multi-variable cancellation path of the ring engine.
#[test]
fn lra_general_three_constraint_multivar_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let x_plus_y = arena.real_add(x, y).unwrap();
    let a1 = arena.real_le(x_plus_y, zero).unwrap(); // x + y ≤ 0
    let a2 = arena.real_le(one, x).unwrap(); // 1 ≤ x
    let a3 = arena.real_le(one, y).unwrap(); // 1 ≤ y

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2, a3])
        .expect("3-constraint multivar Farkas reconstructs to False");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **N-constraint with larger non-unit multipliers**: `3x ≤ 0 ∧ 2 ≤ 2x`. The
/// refutation is `2·(3x) + 3·(2 - 2x) = 6 > 0` (multipliers `(2, 3)`, coefficients
/// `> 1` on both the variable and the scaling), stressing repeated scaling and a
/// larger constant `K = 6` (a six-`one` sum in the `lt zero K` builder).
#[test]
fn lra_general_larger_multipliers_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let three = arena.real_const(Rational::integer(3));
    let zero = arena.real_const(Rational::integer(0));
    let three_x = arena.real_mul(three, x).unwrap();
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_le(three_x, zero).unwrap(); // 3x ≤ 0
    let a2 = arena.real_le(two, two_x).unwrap(); // 2 ≤ 2x

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("larger-multiplier Farkas reconstructs to False");
    assert_lra_infers_false(&mut ctx, proof);
}

/// The general path keeps the slice-1 baby shape `x ≤ 0 ∧ 1 ≤ x` reconstructing
/// (it is just the `λ = (1, 1)`, `K = 1` instance of the general engine — though in
/// practice the dedicated transitivity path handles it first; this confirms the
/// general engine ALSO closes it when reached).
#[test]
fn lra_general_engine_handles_unit_baby_shape() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, try_general_farkas};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a1 = arena.real_le(x, zero).unwrap();
    let a2 = arena.real_le(one, x).unwrap();

    let cert = crate::lra_farkas_certificate(&arena, &[a1, a2])
        .unwrap()
        .expect("unsat");
    let mut ctx = LraReconstructCtx::new();
    let proof = try_general_farkas(&mut ctx, &cert)
        .expect("no error")
        .expect("general engine reconstructs the unit baby shape");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **Genuinely rational multipliers** (denominator-clearing path): a directly-built
/// `FarkasCertificate` over atoms `3x − 1 ≤ 0` and `−2x + 1 ≤ 0` with multipliers
/// `λ = (2/3, 1)`. The combination `(2/3)·(3x − 1) + 1·(−2x + 1)` cancels `x`
/// (`2 − 2 = 0`) and leaves the **positive** constant `1/3 > 0`, a real refutation.
///
/// The natural `lra.rs` Fourier–Motzkin output already normalizes multipliers to
/// integers, so this is the only test that exercises [`try_general_farkas`]'s
/// `lcm`-denominator-clearing (`λ = (2/3, 1)` scaled by `lcm(3,1) = 3` to integer
/// `μ = (2, 3)`, then `K = 2·(−1) + 3·(1) = 1`). We first `verify()` the cert is a
/// genuine Farkas refutation (so we are not feeding the engine a bogus combination),
/// then reconstruct it to a kernel-checked `False`.
#[test]
fn lra_general_rational_multipliers_reconstructs() {
    use axeyum_ir::Rational;

    use super::{LraReconstructCtx, try_general_farkas};

    // atom0: 3x − 1 ≤ 0 ; atom1: −2x + 1 ≤ 0.
    let cert = crate::FarkasCertificate {
        atoms: vec![
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(3))],
                constant: Rational::integer(-1),
                strict: false,
            },
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(-2))],
                constant: Rational::integer(1),
                strict: false,
            },
        ],
        multipliers: vec![Rational::new(2, 3), Rational::integer(1)],
        origins: vec![0, 1],
        vars: Vec::new(),
    };
    assert!(
        cert.verify(),
        "the directly-built rational-multiplier cert must be a genuine Farkas refutation"
    );
    // Multipliers genuinely carry a denominator > 1 (exercise the clearing path).
    assert_eq!(cert.multipliers[0].denominator(), 3);

    let mut ctx = LraReconstructCtx::new();
    let proof = try_general_farkas(&mut ctx, &cert)
        .expect("no error")
        .expect("rational-multiplier general Farkas reconstructs");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **Strict, rational multipliers, mixed engine** (denominator-clearing on a strict
/// atom): a directly-built cert over the **strict** atom `3x − 1 < 0` and the
/// non-strict `−2x + 1 ≤ 0`, multipliers `λ = (2/3, 1)`. The combination cancels
/// `x` and yields the strict `Σ < 0` with `Σ = K = 1/3 > 0` (after clearing,
/// integer `μ = (2, 3)`, `K = 1`), refuted via `0 < K` and `lt_trans` → `0 < 0` →
/// `lt_irrefl`. Exercises [`try_mixed_farkas`]'s `lcm`-clearing on a strict atom and
/// the strict-scaling `add_lt_add` fold.
#[test]
fn lra_mixed_rational_multipliers_reconstructs() {
    use axeyum_ir::Rational;

    use super::{LraReconstructCtx, try_mixed_farkas};

    let cert = crate::FarkasCertificate {
        atoms: vec![
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(3))],
                constant: Rational::integer(-1),
                strict: true, // 3x − 1 < 0
            },
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(-2))],
                constant: Rational::integer(1),
                strict: false, // −2x + 1 ≤ 0
            },
        ],
        multipliers: vec![Rational::new(2, 3), Rational::integer(1)],
        origins: vec![0, 1],
        vars: Vec::new(),
    };
    assert!(
        cert.verify(),
        "the strict rational-multiplier cert must be a genuine Farkas refutation"
    );
    assert_eq!(cert.multipliers[0].denominator(), 3);

    let mut ctx = LraReconstructCtx::new();
    let proof = try_mixed_farkas(&mut ctx, &cert)
        .expect("no error")
        .expect("strict rational-multiplier mixed Farkas reconstructs");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **NEGATIVE — the kernel is the soundness backstop.** A *wrong* Farkas combination
/// must never yield a `False`. Two layers are checked:
///
/// 1. **Untrusted pre-checks** reject a non-refutation early: a cert over `x ≤ 0`
///    and `−x ≤ 0` (i.e. `x ≥ 0`) with multipliers `(1, 1)` cancels `x` but leaves
///    `K = 0` — the combination is `0 ≤ 0`, *true*, not a refutation. The
///    non-strict engine requires `K > 0`, so it returns `Ok(None)` (falls through)
///    rather than fabricating a `False`. `cert.verify()` agrees it is not a
///    refutation.
/// 2. **Trusted kernel gate** is the final backstop: even a hand-assembled *wrong*
///    arithmetic term (here `lt_irrefl zero` applied to `zero_lt_one`, a deliberate
///    type error — `lt_irrefl zero : ¬ lt zero zero` cannot consume `lt zero one`)
///    is rejected by `infer`; the kernel never admits it as a proof of `False`.
///
/// Together: a bogus combination is rejected — by the pre-check when possible, by the
/// kernel `infer`/`def_eq` gate unconditionally — and never produces a wrong `False`.
#[test]
fn lra_bogus_farkas_combination_is_rejected() {
    use axeyum_ir::Rational;

    use super::{LraReconstructCtx, try_general_farkas};

    // Layer 1: a non-refutation cert (K = 0) falls through to `Ok(None)`.
    let non_refutation = crate::FarkasCertificate {
        atoms: vec![
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(1))],
                constant: Rational::zero(),
                strict: false, // x ≤ 0
            },
            crate::FarkasAtom {
                coeffs: vec![(0, Rational::integer(-1))],
                constant: Rational::zero(),
                strict: false, // −x ≤ 0
            },
        ],
        multipliers: vec![Rational::integer(1), Rational::integer(1)],
        origins: vec![0, 1],
        vars: Vec::new(),
    };
    assert!(
        !non_refutation.verify(),
        "x ≤ 0 ∧ −x ≤ 0 is satisfiable (x = 0); not a Farkas refutation"
    );
    let mut ctx = LraReconstructCtx::new();
    let outcome = try_general_farkas(&mut ctx, &non_refutation)
        .expect("a non-refutation must not error-out the engine, only fall through");
    assert!(
        outcome.is_none(),
        "a non-refutation (K = 0) must NOT reconstruct to a `False`; got {outcome:?}"
    );

    // Layer 2: the trusted kernel gate rejects a hand-built WRONG combination. We
    // mis-apply `lt_irrefl zero : ¬ lt zero zero` to `zero_lt_one : lt zero one` —
    // an ill-typed term. `infer` must FAIL (never silently yield a `False`).
    let irrefl_zero_at_zlo = {
        let arith = *ctx.arith();
        let zero = {
            let z = arith.zero;
            ctx.kernel_mut().const_(z, vec![])
        };
        let irrefl = {
            let i = arith.lt_irrefl;
            ctx.kernel_mut().const_(i, vec![])
        };
        // lt_irrefl zero : Not (lt zero zero) = (lt zero zero → False).
        let not_lt_zz = ctx.kernel_mut().app(irrefl, zero);
        // zero_lt_one : lt zero one — the WRONG argument (expected lt zero zero).
        let zlo = {
            let z = arith.zero_lt_one;
            ctx.kernel_mut().const_(z, vec![])
        };
        ctx.kernel_mut().app(not_lt_zz, zlo)
    };
    assert!(
        ctx.kernel_mut().infer(irrefl_zero_at_zlo).is_err(),
        "the kernel must REJECT (fail to infer) an ill-typed Farkas combination — \
         a wrong term can never be admitted as a proof of `False`"
    );
}

// ---------------------------------------------------------------------------
// Quantifier instantiation: a REAL `prove_quant_unsat_alethe` proof for a
// universally-quantified `unsat` reconstructed to a kernel-checked `False` via
// `forall_elim` (application of a `Pi (x:α), ⟦P x⟧` axiom to the witness).
// ---------------------------------------------------------------------------

use super::reconstruct_quant_unsat_proof;

/// **THE QUANTIFIER DELIVERABLE (minimal, one instance)**: take a REAL emitted
/// proof for `∀x. (f x = c) ∧ ¬(f a = c)`, reconstruct it, and assert the result
/// kernel-checks to `False`. The universal is modeled as a dependent product
/// `Pi (x:α), Eq α (f x) c`; the single `x := a` instantiation is `forall_elim`
/// (apply the axiom to `⟦a⟧`), feeding the ground EUF close.
#[test]
fn end_to_end_forall_one_instance_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let forall = arena.forall(x, fx_eq_c).unwrap();
    let av = arena.var(a);
    let fa = arena.apply(f, &[av]).unwrap();
    let fa_eq_c = arena.eq(fa, cv).unwrap();
    let not_fa_eq_c = arena.not(fa_eq_c).unwrap();

    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_c])
        .expect("emitter produces the quantifier-instantiation refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof)
        .expect("the quantifier refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Two genuine instances**: `∀x. (f x = c) ∧ f a ≠ f b`. Both `x := a` and
/// `x := b` are `forall_elim`'d, giving `f a = c` and `f b = c`; the ground EUF
/// tail derives `f a = f b` and closes against `f a ≠ f b` to `False`.
#[test]
fn end_to_end_forall_two_instances_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let b = arena.declare("b", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let forall = arena.forall(x, fx_eq_c).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let fa = arena.apply(f, &[av]).unwrap();
    let fb = arena.apply(f, &[bv]).unwrap();
    let fa_eq_fb = arena.eq(fa, fb).unwrap();
    let not_fa_eq_fb = arena.not(fa_eq_fb).unwrap();

    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_fb])
        .expect("emitter produces the two-instance refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof)
        .expect("the two-instance refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **Two top-level universals**: `∀x.(f x = a) ∧ ∀y.(f y = b) ∧ a ≠ b`. Each
/// universal is its own dependent-product axiom `Pi (x:α), Eq α (f x) a` /
/// `Pi (y:α), Eq α (f y) b`; instantiating both at the shared witness `a` gives
/// `f a = a` and `f a = b`, whence the ground EUF tail derives `a = b` and closes
/// against `a ≠ b` to a kernel-checked `False`. Each `forall_inst` is a
/// `forall_elim` on the *matching* axiom.
#[test]
fn end_to_end_two_universals_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let b = arena.declare("b", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    let av = arena.var(a);
    let bv = arena.var(b);
    // ∀x. f(x) = a
    let xv = arena.var(x);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_a = arena.eq(fx, av).unwrap();
    let f1 = arena.forall(x, fx_eq_a).unwrap();
    // ∀y. f(y) = b
    let yv = arena.var(y);
    let fy = arena.apply(f, &[yv]).unwrap();
    let fy_eq_b = arena.eq(fy, bv).unwrap();
    let f2 = arena.forall(y, fy_eq_b).unwrap();
    // a ≠ b
    let a_eq_b = arena.eq(av, bv).unwrap();
    let not_a_eq_b = arena.not(a_eq_b).unwrap();

    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[f1, f2, not_a_eq_b])
        .expect("emitter produces the two-universal refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof)
        .expect("the two-universal refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **Nested universal**: `∀x.∀y.(h x y = c) ∧ ¬(h s t = c)`. The chain is modeled
/// as the iterated dependent product `Pi (x:α), Pi (y:α), Eq α (h x y) c`;
/// instantiating it at `x := s, y := t` is **two** `forall_elim` applications
/// `(axiom ⟦s⟧) ⟦t⟧`, whose `infer`'d type Pi-reduces to `h s t = c`, contradicting
/// `¬(h s t = c)` and closing to a kernel-checked `False`.
#[test]
fn end_to_end_nested_universal_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let s = arena.declare("s", alpha).unwrap();
    let t = arena.declare("t", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let h = arena.declare_fun("h", &[alpha, alpha], alpha).unwrap();

    let xv = arena.var(x);
    let yv = arena.var(y);
    let cv = arena.var(c);
    let hxy = arena.apply(h, &[xv, yv]).unwrap();
    let hxy_eq_c = arena.eq(hxy, cv).unwrap();
    // ∀x.∀y. h(x, y) = c
    let inner = arena.forall(y, hxy_eq_c).unwrap();
    let forall = arena.forall(x, inner).unwrap();
    // ¬(h(s, t) = c)
    let sv = arena.var(s);
    let tv = arena.var(t);
    let hst = arena.apply(h, &[sv, tv]).unwrap();
    let hst_eq_c = arena.eq(hst, cv).unwrap();
    let not_hst = arena.not(hst_eq_c).unwrap();

    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[forall, not_hst])
        .expect("emitter produces the nested-universal refutation");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof)
        .expect("the nested-universal refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// **Scaling deliverable — e-matching-sourced witness reconstructs to `False`**:
/// `∀x.(f x = c) ∧ f a ≠ c`, but with **24 decoy ground leaves of the binder's
/// sort** — far past the emitter's brute-force candidate cap. The cartesian
/// witness search bails, so the witness `x := a` is sourced from the solver's
/// trigger-driven e-matching (only `f(a)` matches `f(x)`). The emitted proof's
/// lone `forall_elim` still reconstructs to a kernel-checked `False`, so a
/// quantified `unsat` the *solver* decides scalably also gets a trusted proof.
#[test]
fn end_to_end_ematch_sourced_witness_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let forall = arena.forall(x, fx_eq_c).unwrap();

    let av = arena.var(a);
    let fa = arena.apply(f, &[av]).unwrap();
    let fa_eq_c = arena.eq(fa, cv).unwrap();
    let not_fa_eq_c = arena.not(fa_eq_c).unwrap();

    // 24 decoy leaves of `alpha`, summed into one harmless ground equality; ≫ the
    // brute-force cap of 16, so the cartesian search returns None and e-matching
    // must supply the witness.
    let mut acc: Option<axeyum_ir::TermId> = None;
    for i in 0..24u32 {
        let s = arena.declare(&format!("d{i}"), alpha).unwrap();
        let dv = arena.var(s);
        acc = Some(match acc {
            None => dv,
            Some(prev) => arena.bv_add(prev, dv).unwrap(),
        });
    }
    let sum = acc.unwrap();
    let sum_eq_self = arena.eq(sum, sum).unwrap();

    let proof = crate::prove_quant_unsat_alethe(&mut arena, &[forall, not_fa_eq_c, sum_eq_self])
        .expect("e-matching sources the witness past the brute-force cap");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_quant_unsat_proof(&mut ctx, &proof)
        .expect("the e-matching-sourced refutation reconstructs");
    assert_infers_false(&mut ctx, term);
}

/// The reconstructed nested universal axiom is an iterated dependent product
/// `Pi (x:α), Pi (y:α), Eq α (h x y) c` — confirm its declared type is a `Pi`
/// whose body is itself a `Pi`, so the two `forall_elim` applications type-check.
#[test]
fn nested_forall_axiom_is_iterated_product() {
    use axeyum_cnf::AletheTerm;
    use axeyum_lean_kernel::ExprNode;

    let mut ctx = ReconstructCtx::new();
    // body: (= (h x y) c).
    let body = AletheTerm::App(
        "=".to_owned(),
        vec![
            AletheTerm::App(
                "h".to_owned(),
                vec![
                    AletheTerm::Const("x".to_owned()),
                    AletheTerm::Const("y".to_owned()),
                ],
            ),
            AletheTerm::Const("c".to_owned()),
        ],
    );
    let proof = super::declare_forall_axiom(&mut ctx, &["x", "y"], &body).expect("axiom declares");
    let ty = ctx.kernel_mut().infer(proof).expect("infer axiom type");
    let ExprNode::Pi(_, _, inner, _) = ctx.kernel().expr_node(ty) else {
        panic!("the nested universal axiom must be a dependent product `Pi (x:α), …`");
    };
    let inner = *inner;
    assert!(
        matches!(ctx.kernel().expr_node(inner), ExprNode::Pi(..)),
        "the nested axiom body must itself be a `Pi (y:α), …`"
    );
}

/// The reconstructed universal axiom is a genuine dependent product
/// `Pi (x:α), Eq α (f x) c` — confirm its declared type is a `Pi`, so
/// `forall_elim` (application) is type-correct.
#[test]
fn forall_axiom_is_dependent_product() {
    use axeyum_cnf::AletheTerm;
    use axeyum_lean_kernel::ExprNode;

    let mut ctx = ReconstructCtx::new();
    // body: (= (f x) c).
    let body = AletheTerm::App(
        "=".to_owned(),
        vec![
            AletheTerm::App("f".to_owned(), vec![AletheTerm::Const("x".to_owned())]),
            AletheTerm::Const("c".to_owned()),
        ],
    );
    let proof = super::declare_forall_axiom(&mut ctx, &["x"], &body).expect("axiom declares");
    let ty = ctx.kernel_mut().infer(proof).expect("infer axiom type");
    assert!(
        matches!(ctx.kernel().expr_node(ty), ExprNode::Pi { .. }),
        "the universal axiom must be a dependent product `Pi (x:α), …`"
    );
}

/// A malformed `forall_inst` whose instance is **not** a consistent substitution
/// of the body is rejected (no wrong `False`): the body `(= (g x) x)` has `x`
/// twice, but the instance `(= (g a) b)` maps it to two different witnesses.
#[test]
fn forall_inst_inconsistent_witness_rejected() {
    use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};

    let forall_atom = AletheTerm::App(
        "forall".to_owned(),
        vec![
            AletheTerm::Const("x".to_owned()),
            AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::App("g".to_owned(), vec![AletheTerm::Const("x".to_owned())]),
                    AletheTerm::Const("x".to_owned()),
                ],
            ),
        ],
    );
    let bad_inst = AletheTerm::App(
        "=".to_owned(),
        vec![
            AletheTerm::App("g".to_owned(), vec![AletheTerm::Const("a".to_owned())]),
            AletheTerm::Const("b".to_owned()),
        ],
    );
    let commands = vec![
        AletheCommand::Assume {
            id: "q_forall".to_owned(),
            clause: vec![AletheLit {
                atom: forall_atom.clone(),
                negated: false,
            }],
        },
        AletheCommand::Step {
            id: "q_inst0".to_owned(),
            clause: vec![
                AletheLit {
                    atom: forall_atom,
                    negated: true,
                },
                AletheLit {
                    atom: bad_inst,
                    negated: false,
                },
            ],
            rule: "forall_inst".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        },
        AletheCommand::Step {
            id: "q_res0".to_owned(),
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: vec!["q_forall".to_owned(), "q_inst0".to_owned()],
            args: Vec::new(),
        },
    ];
    let mut ctx = ReconstructCtx::new();
    let err = reconstruct_quant_unsat_proof(&mut ctx, &commands)
        .expect_err("inconsistent witness must be rejected");
    assert!(matches!(err, ReconstructError::MalformedStep { .. }));
}

// ---------------------------------------------------------------------------
// Existential skolemization (P3.7): a top-level `∃` certificate reconstructs to
// a kernel-checked `False` over the ORIGINAL `∃` assertions, via `Exists.elim`
// wrapping the (parametric-in-`sk`) skolemized refutation.
// ---------------------------------------------------------------------------

use super::reconstruct_skolem_unsat_proof;

/// **THE EXISTENTIAL DELIVERABLE (∃ + ∀ end-to-end)**: take a REAL emitted
/// certificate for `∃x.(f x = c) ∧ ∀y.(f y = d) ∧ (c ≠ d)`, reconstruct it, and
/// assert the result kernel-checks to `False`. The existential is modeled as
/// `Exists.{1} α (fun x => Eq α (f x) c)`; skolemizing gives `f(!skq_0) = c`, the
/// universal instantiates at `!skq_0` to `f(!skq_0) = d`, so by congruence
/// `c = d`, contradicting `c ≠ d`. That whole EUF refutation is **parametric in
/// the skolem** `!skq_0`, so it is wrapped in `Exists.elim` over the honest `∃`
/// hypothesis — kernel-checked `False` over the ORIGINAL `∃` assertion.
#[test]
fn end_to_end_exists_forall_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let d = arena.declare("d", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    // ∃x. f(x) = c.
    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let exists = arena.exists(x, fx_eq_c).unwrap();
    // ∀y. f(y) = d.
    let yv = arena.var(y);
    let dv = arena.var(d);
    let fy = arena.apply(f, &[yv]).unwrap();
    let fy_eq_d = arena.eq(fy, dv).unwrap();
    let forall = arena.forall(y, fy_eq_d).unwrap();
    // c ≠ d.
    let c_eq_d = arena.eq(cv, dv).unwrap();
    let not_c_eq_d = arena.not(c_eq_d).unwrap();

    let cert = crate::prove_skolem_unsat_alethe(&mut arena, &[exists, forall, not_c_eq_d])
        .expect("emitter produces the skolemization refutation certificate");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_skolem_unsat_proof(&mut ctx, &cert)
        .expect("the existential skolemization reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Pure-`∃` (no universal) wrapped in `Exists.elim`**:
/// `∃x.(g x = a) ∧ (g b = a) ∧ ¬(g b = a)`. A single-equality existential body
/// over a *fresh* skolem can never itself force a clash (the model is free to set
/// `g(sk) = a` and leave the rest arbitrary), so a genuinely-unsat pure-`∃`
/// derives its contradiction from the **ground** facts — here directly from
/// `g(b) = a` vs `¬(g(b) = a)`. The skolemized refutation thus does not use the
/// witness, and the `Exists.elim` minor `fun w hw => R` ignores both binders.
/// This still kernel-checks to a sound `False` over the original `∃` assertion,
/// exercising the no-universal `Exists.elim` wrapping path end-to-end.
#[test]
fn end_to_end_pure_exists_ground_clash_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let b = arena.declare("b", alpha).unwrap();
    let g = arena.declare_fun("g", &[alpha], alpha).unwrap();

    // ∃x. g(x) = a.
    let xv = arena.var(x);
    let av = arena.var(a);
    let gx = arena.apply(g, &[xv]).unwrap();
    let gx_eq_a = arena.eq(gx, av).unwrap();
    let exists = arena.exists(x, gx_eq_a).unwrap();
    // g(b) = a  and  ¬(g(b) = a) — a ground contradiction independent of x.
    let bv = arena.var(b);
    let gb = arena.apply(g, &[bv]).unwrap();
    let gb_eq_a = arena.eq(gb, av).unwrap();
    let not_gb_eq_a = arena.not(gb_eq_a).unwrap();

    let cert = crate::prove_skolem_unsat_alethe(&mut arena, &[exists, gb_eq_a, not_gb_eq_a])
        .expect("emitter produces a skolemization certificate for the pure-∃ clash");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_skolem_unsat_proof(&mut ctx, &cert)
        .expect("the pure-existential refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Two existentials, both essential — nested `Exists.elim`**:
/// `∃x.(f x = c) ∧ ∃z.(f z = e) ∧ ∀y.(f y = d) ∧ ¬(c = e)`. Instantiating `∀y`
/// at both skolems gives `f(!skq_0) = d` and `f(!skq_1) = d`; with the two
/// existential facts `f(!skq_0) = c` and `f(!skq_1) = e` this forces `c = d` and
/// `e = d`, hence `c = e` — contradicting `¬(c = e)`. BOTH witnesses are used, so
/// the reconstruction nests two `Exists.elim`s (innermost-out), threading each
/// skolem to its bound witness. Kernel-checked `False` over the two original `∃`s.
#[test]
fn end_to_end_two_existentials_nested_to_false() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let z = arena.declare("z", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let d = arena.declare("d", alpha).unwrap();
    let e = arena.declare("e", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();

    let cv = arena.var(c);
    let dv = arena.var(d);
    let ev = arena.var(e);

    // ∃x. f(x) = c.
    let xv = arena.var(x);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let exists_x = arena.exists(x, fx_eq_c).unwrap();
    // ∃z. f(z) = e.
    let zv = arena.var(z);
    let fz = arena.apply(f, &[zv]).unwrap();
    let fz_eq_e = arena.eq(fz, ev).unwrap();
    let exists_z = arena.exists(z, fz_eq_e).unwrap();
    // ∀y. f(y) = d.
    let yv = arena.var(y);
    let fy = arena.apply(f, &[yv]).unwrap();
    let fy_eq_d = arena.eq(fy, dv).unwrap();
    let forall = arena.forall(y, fy_eq_d).unwrap();
    // ¬(c = e).
    let c_eq_e = arena.eq(cv, ev).unwrap();
    let not_c_eq_e = arena.not(c_eq_e).unwrap();

    let cert =
        crate::prove_skolem_unsat_alethe(&mut arena, &[exists_x, exists_z, forall, not_c_eq_e])
            .expect("emitter produces the two-existential skolemization certificate");
    assert_eq!(cert.skolems.len(), 2, "two existentials skolemized");

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_skolem_unsat_proof(&mut ctx, &cert)
        .expect("the two-existential refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **Mixed strict/non-strict, not a cycle** (Task #16): `x < 0 ∧ 0 ≤ x`. The Farkas
/// refutation is `1·(x < 0) + 1·(0 ≤ x)`: summing the strict `x < 0` with the
/// non-strict `−x ≤ 0` gives `0 < 0` (`K = 0`), refuted directly by `lt_irrefl`. This
/// is neither a pure strict cycle (`try_strict_cycle`) nor pure non-strict
/// (`try_general_farkas` rejects strict atoms), so only the mixed engine closes it.
#[test]
fn lra_mixed_strict_nonstrict_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap(); // x < 0  (strict)
    let a2 = arena.real_le(zero, x).unwrap(); // 0 ≤ x  (non-strict)

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect("mixed strict/non-strict Farkas reconstructs to False");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **Mixed, 3 constraints, non-unit multiplier on the strict atom** (Task #16):
/// `2x < 0 ∧ 1 ≤ x ∧ 1 ≤ y` with the strict atom carrying weight. The Farkas
/// refutation is `1·(2x < 0) + 2·(1 − x ≤ 0) + 0·…` → `2x + 2 − 2x = 2`, a strict
/// `2 < 0` (`K = 2 > 0`), closed via `0 < 2` and `lt_trans` → `0 < 0` → `lt_irrefl`.
/// Here the strict atom `2x < 0` is summed (its scaling exercises repeated
/// `add_lt_add`) with the non-strict `2·(1 − x) ≤ 0`. The `1 ≤ y` is a decoy the
/// certificate gives a zero multiplier, confirming the engine only sums used atoms.
#[test]
fn lra_mixed_three_constraint_nonunit_strict_reconstructs() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let one = arena.real_const(Rational::integer(1));
    let zero = arena.real_const(Rational::integer(0));
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_lt(two_x, zero).unwrap(); // 2x < 0  (strict)
    let a2 = arena.real_le(one, x).unwrap(); // 1 ≤ x   (non-strict)
    let a3 = arena.real_le(one, y).unwrap(); // 1 ≤ y   (decoy, unused)

    let mut ctx = LraReconstructCtx::new();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2, a3])
        .expect("mixed 3-constraint non-unit-strict Farkas reconstructs to False");
    assert_lra_infers_false(&mut ctx, proof);
}

/// **Route 2** (Task #15): the `bvsub`-rewrite refutation reconstructs to a
/// kernel-checked `False` over the ORIGINAL `bvsub` assertions.
///
/// `(= (bvsub a b) a) ∧ (bvult a b)` is unsat (`a - b = a` forces `b = 0`, then
/// `a < b = a < 0` is impossible). `prove_qf_bv_unsat_alethe_route2` keeps `bvsub` at
/// the term level — it emits a Carcara-valid `bv_poly_simp` step
/// `(= (bvsub a b) (bvadd a (bvneg b)))` and bit-blasts the `bvadd`/`bvneg`. The
/// reconstruction's faithful `bv_bit` model of `bvsub a b` IS the `bvadd a (bvneg b)`
/// ripple-carry, so the `bvsub` bit-definition is reflexive and the closing `(cl)`
/// `infer`-checks against `False` — certifying the un-lowered formula.
#[test]
fn end_to_end_route2_bvsub_refutation_to_false() {
    use axeyum_ir::TermArena;
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let sub = arena.bv_sub(a, b).unwrap();
    let eq = arena.eq(sub, a).unwrap();
    let lt = arena.bv_ult(a, b).unwrap();
    let proof = crate::prove_qf_bv_unsat_alethe_route2(&mut arena, &[eq, lt])
        .expect("Route-2 emitter produces the bvsub refutation");
    // The emitted proof keeps `bvsub` at the term level via a `bv_poly_simp` step.
    assert!(
        proof.iter().any(|c| matches!(
            c,
            axeyum_cnf::AletheCommand::Step { rule, .. } if rule == "bv_poly_simp"
        )),
        "Route-2 proof must contain the bvsub→bvadd∘bvneg bv_poly_simp step"
    );

    let mut ctx = ReconstructCtx::new();
    let term = reconstruct_qf_bv_proof(&mut ctx, &proof)
        .expect("the Route-2 bvsub refutation reconstructs to a kernel-checked term");
    assert_infers_false(&mut ctx, term);
}

/// **The unified dispatcher (#29)**: `prove_unsat_to_lean` is the single entry that
/// classifies a goal's fragment, routes to the matching emitter+reconstructor, and
/// kernel-checks the result — returning the `ProofFragment` it used. Each theory
/// reaches a kernel-verified `False` through one call.
#[test]
fn unified_dispatcher_routes_each_fragment_to_kernel_false() {
    use axeyum_ir::{Rational, Sort, TermArena};

    use super::{ProofFragment, prove_unsat_to_lean};

    // QF_UFBV: f(a)=#b00 ∧ a=b ∧ ¬(f(b)=#b00) — has both Apply and BitVec.
    // The direct local finite-BV/UF refuter has priority over the general
    // Ackermann Alethe route when it can close the row.
    {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
            .unwrap();
        let a = {
            let s = arena.declare("a", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let b = {
            let s = arena.declare("b", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let c00 = arena.bv_const(2, 0).unwrap();
        let e1 = arena.eq(fa, c00).unwrap();
        let e2 = arena.eq(a, b).unwrap();
        let e3 = {
            let e = arena.eq(fb, c00).unwrap();
            arena.not(e).unwrap()
        };
        let frag = prove_unsat_to_lean(&mut arena, &[e1, e2, e3])
            .expect("QF_UFBV unsat dispatches + kernel-checks to False");
        assert_eq!(frag, ProofFragment::BvUfLocal);
    }

    // LRA: x < 0 ∧ 0 ≤ x — Int/Real sorts, no functions. The general
    // Boolean-structured LRA DPLL proof route has priority over the older
    // conjunctive fallback when it certifies the row.
    {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let zero = arena.real_const(Rational::integer(0));
        let a1 = arena.real_lt(x, zero).unwrap();
        let a2 = arena.real_le(zero, x).unwrap();
        let frag = prove_unsat_to_lean(&mut arena, &[a1, a2])
            .expect("LRA unsat dispatches + kernel-checks to False");
        assert_eq!(frag, ProofFragment::LraDpll);
    }

    // Quantifier ∀: ∀x.(f x = c) ∧ ¬(f a = c) — top-level universal.
    {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let a = arena.declare("a", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
        let xv = arena.var(x);
        let cv = arena.var(c);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let forall = arena.forall(x, fx_eq_c).unwrap();
        let av = arena.var(a);
        let fa = arena.apply(f, &[av]).unwrap();
        let not_fa_eq_c = {
            let e = arena.eq(fa, cv).unwrap();
            arena.not(e).unwrap()
        };
        let frag = prove_unsat_to_lean(&mut arena, &[forall, not_fa_eq_c])
            .expect("∀ unsat dispatches + kernel-checks to False");
        assert_eq!(frag, ProofFragment::Forall);
    }

    // Existential ∃: ∃x.(f x = c) ∧ ∀y.(f y = d) ∧ c ≠ d — top-level existential
    // (skolemized), routed ahead of the ∀.
    {
        let mut arena = TermArena::new();
        let alpha = Sort::BitVec(8);
        let x = arena.declare("x", alpha).unwrap();
        let y = arena.declare("y", alpha).unwrap();
        let c = arena.declare("c", alpha).unwrap();
        let d = arena.declare("d", alpha).unwrap();
        let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
        let xv = arena.var(x);
        let cv = arena.var(c);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_c = arena.eq(fx, cv).unwrap();
        let exists = arena.exists(x, fx_eq_c).unwrap();
        let yv = arena.var(y);
        let dv = arena.var(d);
        let fy = arena.apply(f, &[yv]).unwrap();
        let fy_eq_d = arena.eq(fy, dv).unwrap();
        let forall = arena.forall(y, fy_eq_d).unwrap();
        let not_c_eq_d = {
            let e = arena.eq(cv, dv).unwrap();
            arena.not(e).unwrap()
        };
        let frag = prove_unsat_to_lean(&mut arena, &[exists, forall, not_c_eq_d])
            .expect("∃ unsat dispatches + kernel-checks to False");
        assert_eq!(frag, ProofFragment::Exists);
    }
}

/// Debug: build `nat_ne_succ` and infer its type; expect
/// `Π (n : Nat), Eq Nat n (Nat.succ n) → False`.
/// The `n ≠ Nat.succ n` lemma built by [`super::build_nat_ne_succ`] `infer`s to
/// `Π (n : Nat), Eq Nat n (Nat.succ n) → False` — the trusted kernel genuinely
/// accepts the by-induction proof (base-case discriminator + step `succ`
/// injectivity), so acyclicity's `n = succ n` contradiction is kernel-checked, not
/// assumed.
#[test]
fn nat_ne_succ_infers_to_pi_eq_false() {
    let mut ctx = ReconstructCtx::new();
    // The sub-pieces all type-check on their own.
    let discr = super::build_nat_discriminator(&mut ctx);
    assert!(
        ctx.kernel_mut().infer(discr).is_ok(),
        "discriminator infers"
    );
    let pred = super::build_nat_pred(&mut ctx);
    assert!(ctx.kernel_mut().infer(pred).is_ok(), "pred selector infers");
    let mz = super::build_nat_ne_succ_m_zero(&mut ctx);
    assert!(ctx.kernel_mut().infer(mz).is_ok(), "base minor infers");
    let ms = super::build_nat_ne_succ_m_succ(&mut ctx);
    assert!(ctx.kernel_mut().infer(ms).is_ok(), "step minor infers");

    // The assembled lemma infers to `Π (n : Nat), Eq Nat n (Nat.succ n) → False`.
    let lemma = super::build_nat_ne_succ(&mut ctx);
    let ty = ctx
        .kernel_mut()
        .infer(lemma)
        .expect("nat_ne_succ infers to a Pi type");
    let rendered = ctx.kernel().render_lean(ty);
    assert!(
        rendered.contains("Nat") && rendered.contains("Eq") && rendered.contains("False"),
        "nat_ne_succ : Π (n : Nat), Eq Nat n (Nat.succ n) → False, got: {rendered}"
    );
}

/// The generalized `n ≠ Nat.succ^k n` lemma built by
/// [`super::build_nat_ne_succ_pow`] `infer`s to
/// `Π (n : Nat), Eq Nat n (Nat.succ^k n) → False` for several `k ≥ 1` — the
/// trusted kernel accepts the chained-induction proof, so the MULTI-step
/// acyclicity `size x = Nat.succ^k (size x)` contradiction is kernel-checked, not
/// assumed. (`k = 1` reproduces `nat_ne_succ`'s type.)
#[test]
fn nat_ne_succ_pow_infers_to_pi_eq_succ_pow_false() {
    for k in 1usize..=4 {
        let mut ctx = ReconstructCtx::new();
        let mz = super::build_nat_ne_succ_pow_m_zero(&mut ctx, k);
        assert!(
            ctx.kernel_mut().infer(mz).is_ok(),
            "pow base minor infers (k={k})"
        );
        let ms = super::build_nat_ne_succ_pow_m_succ(&mut ctx, k);
        assert!(
            ctx.kernel_mut().infer(ms).is_ok(),
            "pow step minor infers (k={k})"
        );
        let lemma = super::build_nat_ne_succ_pow(&mut ctx, k);
        let ty = ctx
            .kernel_mut()
            .infer(lemma)
            .unwrap_or_else(|e| panic!("nat_ne_succ_pow (k={k}) infers: {e:?}"));
        let rendered = ctx.kernel().render_lean(ty);
        assert!(
            rendered.contains("Nat") && rendered.contains("Eq") && rendered.contains("False"),
            "nat_ne_succ_pow (k={k}) : Π (n : Nat), Eq Nat n (Nat.succ^k n) → False, got: {rendered}"
        );
        // The RHS must carry exactly `k` `Nat.succ` applications (the chained
        // contradiction's depth).
        let succ_count = rendered.matches("Nat.succ").count();
        assert_eq!(
            succ_count, k,
            "nat_ne_succ_pow (k={k}) RHS must have k `Nat.succ`s, got {succ_count}: {rendered}"
        );
    }
}
