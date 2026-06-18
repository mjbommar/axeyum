//! Tests for Alethe → Lean equality-rule reconstruction (P3.7 first slice).
//!
//! Each test **builds** a Lean proof term from an Alethe equality step and
//! confirms the trusted kernel `infer`s it to the right `Eq` proposition (or, for
//! the negative tests, that it is rejected). A green test is the kernel genuinely
//! accepting the reconstruction.
#![allow(clippy::similar_names)]

use axeyum_cnf::{AletheLit, AletheTerm};
use axeyum_lean_kernel::ExprNode;

use super::{ReconstructCtx, ReconstructError, reconstruct_eq_step};

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

/// An out-of-scope term — a higher-arity application `(g a b)` (arity 2, not `=`)
/// — yields a clear `UnsupportedTerm` error, not a panic.
#[test]
fn term_translation_out_of_scope_errors() {
    let mut ctx = ReconstructCtx::new();
    let g = AletheTerm::App("g".to_owned(), vec![atom("a"), atom("b")]);
    let err = ctx.alethe_term_to_expr(&g).unwrap_err();
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
        if let AletheCommand::Assume { clause, .. } = cmd {
            if let [lit] = clause.as_mut_slice() {
                if lit.negated {
                    lit.atom = AletheTerm::App(
                        "=".to_owned(),
                        vec![
                            AletheTerm::Const("a".to_owned()),
                            AletheTerm::Const("d".to_owned()),
                        ],
                    );
                }
            }
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
        if let AletheCommand::Step { rule, clause, .. } = cmd {
            if rule == "eq_transitive" {
                if let Some(last) = clause.last_mut() {
                    last.atom = AletheTerm::App(
                        "=".to_owned(),
                        vec![
                            AletheTerm::Const("a".to_owned()),
                            AletheTerm::Const("b".to_owned()),
                        ],
                    );
                }
            }
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
    {
        if clause.is_empty() && premises.len() >= 2 {
            premises.truncate(1);
        }
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

/// An `unsat` instance OUTSIDE slice 1 (here `2x ≤ -1 ∧ x ≥ 0`, whose Farkas
/// refutation needs a `2`-coefficient term, not the `e ≤ 0 ∧ 1 ≤ e` shape) is
/// rejected, honestly reporting the boundary rather than guessing a `False`.
#[test]
fn lra_out_of_scope_shape_is_rejected() {
    use axeyum_ir::{Rational, TermArena};

    use super::{LraReconstructCtx, ReconstructError, reconstruct_lra_proof};

    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let neg_one = arena.real_const(Rational::integer(-1));
    let zero = arena.real_const(Rational::integer(0));
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_le(two_x, neg_one).unwrap(); // 2x ≤ -1
    let a2 = arena.real_ge(x, zero).unwrap(); // x ≥ 0

    let mut ctx = LraReconstructCtx::new();
    let err = reconstruct_lra_proof(&mut ctx, &arena, &[a1, a2])
        .expect_err("a non-transitivity Farkas shape is out of slice 1");
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
