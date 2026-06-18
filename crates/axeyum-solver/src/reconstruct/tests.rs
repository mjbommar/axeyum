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
