//! **Real-Lean cross-check** of reconstructed refutations (destination-3).
//!
//! `prove_unsat_to_lean_module` renders a self-contained `prelude`-mode Lean 4
//! module (`theorem axeyum_refutation : False := <proof>` over the reachable
//! declarations) for each supported fragment. These tests feed that module to a
//! real `lean` binary: an external, Lean-grade kernel must accept it, and
//! `#print axioms` must report no `sorryAx` (no cheating). This independently
//! corroborates the in-tree [`axeyum_lean_kernel::Kernel`] check.
//!
//! The `lean` binary is optional: each test **skips** (prints a note, passes)
//! when it is absent. Install it with `elan` (a `leanprover/lean4` toolchain on
//! `PATH`), or point `AXEYUM_LEAN_BIN` at a `lean` executable.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]

use std::path::PathBuf;
use std::process::Command;

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_solver::prove_unsat_to_lean_module;

/// Resolve the `lean` binary: `AXEYUM_LEAN_BIN` if set, otherwise the first
/// `lean` on `PATH`. Returns `None` (→ skip) if unavailable.
fn lean_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_LEAN_BIN") {
        let pb = PathBuf::from(p);
        if pb.is_file() {
            return Some(pb);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("lean"))
        .find(|c| c.is_file())
}

/// Write `source` to a temp `.lean` file and run `lean` on it. Asserts the
/// module type-checks (exit 0) and that `#print axioms` reports no `sorryAx`.
/// Skips silently when no `lean` binary is available.
fn lean_accepts(tag: &str, source: &str) {
    let Some(bin) = lean_bin() else {
        eprintln!("[skip] {tag}: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    };
    let dir = std::env::temp_dir().join(format!("axeyum_lean_{tag}"));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{tag}.lean"));
    std::fs::write(&file, source).expect("write lean module");

    let out = Command::new(&bin)
        .arg(&file)
        .output()
        .expect("run lean binary");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the {tag} module ({})\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ({}) ===\n{source}",
        bin.display(),
        file.display()
    );
    // `#print axioms axeyum_refutation` prints to stdout; a real proof must not
    // lean on the `sorryAx` escape hatch.
    assert!(
        !stdout.contains("sorryAx"),
        "{tag}: reconstructed proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "{tag}: missing `#print axioms` output:\n{stdout}"
    );
    eprintln!("[lean ok] {tag}: {}", stdout.trim().replace('\n', " | "));
}

/// `QF_UFBV`: `f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00)` — `Apply` + `BitVec`, refuted
/// by congruence; the exported module must check in real Lean.
#[test]
fn qf_ufbv_refutation_checks_in_real_lean() {
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
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3]).expect("QF_UFBV unsat reconstructs");
    lean_accepts("qf_ufbv", &source);
}

/// `LRA`: `x < 0 ∧ 0 ≤ x` — a Farkas refutation over the axiomatized ordered field.
#[test]
fn lra_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &[a1, a2]).expect("LRA unsat reconstructs");
    lean_accepts("lra", &source);
}

/// Universal: `∀x.(f x = c) ∧ ¬(f a = c)` — instantiation refutation.
#[test]
fn forall_refutation_checks_in_real_lean() {
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
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[forall, not_fa_eq_c])
        .expect("∀ unsat reconstructs");
    lean_accepts("forall", &source);
}

/// Existential: `∃x.(f x = c) ∧ ∀y.(f y = d) ∧ c ≠ d` — skolemization refutation.
#[test]
fn exists_refutation_checks_in_real_lean() {
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
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[exists, forall, not_c_eq_d])
        .expect("∃ unsat reconstructs");
    lean_accepts("exists", &source);
}

/// `QF_ABV`: `select(a, i) = 0 ∧ i = j ∧ ¬(select(a, j) = 0)` is unsat by read
/// consistency (`i = j ⇒ select(a, i) = select(a, j)`). The reconstructed array
/// refutation (via array elimination → `QF_UFBV`) must type-check in real Lean.
#[test]
fn qf_abv_read_consistency_refutation_checks_in_real_lean() {
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
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
        .expect("QF_ABV read-consistency unsat reconstructs");
    lean_accepts("qf_abv", &source);
}

/// Datatypes: `select_0(mk(a, b)) = #b00 ∧ ¬(a = #b00)` is unsat by
/// read-over-construct. Reconstructed via datatype simplification → `QF_UFBV`;
/// the refutation must type-check in real Lean.
#[test]
fn datatype_read_over_construct_checks_in_real_lean() {
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
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let c = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(sel, c).unwrap();
    let e2 = {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("datatype read-over-construct unsat reconstructs");
    lean_accepts("datatype", &source);
}

/// Datatype **is-tester** fold (route-A, the is-tester twin of read-over-construct).
/// Two pure is-tester contradictions, both discharged BY ι (no assumed fold axiom):
///
///   - TRUE fold:  `¬is_Green(Green a)` is UNSAT — `is_Green(Green a)` ι-reduces to
///     `Bool.true`, so `Eq.refl Bool true` closes the negated hypothesis.
///   - FALSE fold: `is_Red(Green a)` is UNSAT — `is_Red(Green a)` ι-reduces to
///     `Bool.false`, contradicting the asserted `… = true` via the
///     `Bool.true ≠ Bool.false` discriminator (`Bool.rec` ι, axiom-free).
///
/// The exported module must type-check in real Lean and `#print axioms` must
/// report no `sorryAx` — the fold is kernel-computed, not assumed.
#[test]
fn tester_fold_checks_in_real_lean() {
    // A two-constructor datatype `Color = Red(v) | Green(w)`.
    let build = |tested_is_green: bool, negate: bool| {
        let mut arena = TermArena::new();
        let color = arena.declare_datatype("Color");
        let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
        let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
        let a = {
            let s = arena.declare("a", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        // Argument is always `Green(a)`; vary which constructor we test for.
        let g = arena.construct(green, &[a]).unwrap();
        let tested = if tested_is_green { green } else { red };
        let is_c = arena.dt_test(tested, g).unwrap();
        let assertion = if negate {
            arena.not(is_c).unwrap()
        } else {
            is_c
        };
        let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
            .expect("is-tester fold unsat reconstructs");
        source
    };

    // TRUE fold: ¬is_Green(Green a) — tested == builder, negated.
    lean_accepts("tester_true", &build(true, true));
    // FALSE fold: is_Red(Green a) — tested != builder, positive.
    lean_accepts("tester_false", &build(false, false));
}

/// `QF_BV` (the foundational bit-blasting path): `bvule a b ∧ bvult b a`
/// (`a ≤ b ∧ b < a`, `BitVec(2)`) is unsat. It lowers to core ops and the
/// bit-level resolution refutation must type-check in real Lean.
#[test]
fn qf_bv_comparison_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(2)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let le = arena.bv_ule(a, b).unwrap();
    let gt = arena.bv_ult(b, a).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[le, gt])
        .expect("QF_BV comparison unsat reconstructs");
    lean_accepts("qf_bv", &source);
}

/// **Disjunctive `QF_LRA`** (the Boolean-structured case split): the conjunctive
/// system `x ≤ 0 ∧ y ≤ 0` plus the clause `(x ≥ 1 ∨ y ≥ 1)` is UNSAT — each leaf
/// is a two-atom Farkas contradiction (`x ≤ 0 ∧ 1 ≤ x` ⇒ `1 ≤ 0`, and likewise
/// for `y`). The conjunctive Farkas path declines a top-level positive `Or`, so
/// this carries a Lean proof only through the new `Or.rec` case-split
/// reconstruction. The exported module must check in real Lean with no `sorryAx`.
#[test]
fn disjunctive_lra_case_split_checks_in_real_lean() {
    use axeyum_solver::ProofFragment;
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let y_le_0 = arena.real_le(y, zero).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let y_ge_1 = arena.real_ge(y, one).unwrap();
    let clause = arena.or(x_ge_1, y_ge_1).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[x_le_0, y_le_0, clause])
        .expect("disjunctive-LRA unsat reconstructs to a kernel-checked False");
    assert_eq!(
        frag,
        ProofFragment::DisjunctiveLra,
        "routed to the disjunctive-LRA case-split reconstructor"
    );
    // The in-tree kernel already accepted (infer + def_eq False inside the call);
    // the rendered module must not lean on the sorryAx escape hatch.
    assert!(
        !source.contains("sorryAx"),
        "disjunctive-LRA module depends on sorryAx:\n{source}"
    );
    lean_accepts("disjunctive_lra", &source);
}

/// **Decline (feasible) disjunctive `QF_LRA`**: `x ≤ 0 ∧ (x ≥ 1 ∨ y ≥ 1) ∧ y ≤ 5`
/// is SATISFIABLE (take `y = 1`), so the disjunctive detector must NOT match and
/// no proof may be fabricated — `prove_unsat_to_lean_module` returns an error
/// (the conjunctive Farkas path also declines the positive `Or`).
#[test]
fn disjunctive_lra_feasible_set_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let five = arena.real_const(Rational::integer(5));
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let y_le_5 = arena.real_le(y, five).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let y_ge_1 = arena.real_ge(y, one).unwrap();
    let clause = arena.or(x_ge_1, y_ge_1).unwrap();
    let result = prove_unsat_to_lean_module(&mut arena, &[x_le_0, y_le_5, clause]);
    assert!(
        result.is_err(),
        "a satisfiable disjunctive set must not produce a fabricated refutation; got {result:?}"
    );
}

/// **Regression**: the existing CONJUNCTIVE LRA refutation `x < 0 ∧ 0 ≤ x` still
/// routes to [`ProofFragment::Lra`] and reconstructs byte-identically (the new
/// disjunctive path only fires on a top-level `Or`).
#[test]
fn conjunctive_lra_still_reconstructs_unchanged() {
    use axeyum_solver::ProofFragment;
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[a1, a2])
        .expect("conjunctive LRA unsat still reconstructs");
    assert_eq!(
        frag,
        ProofFragment::Lra,
        "conjunctive LRA stays on the Lra path"
    );
    assert!(!source.contains("sorryAx"));
}

// --- Constant-shift → concat lowering identity, kernel-certified (ROUTE B) ------
//
// The `lower_const_shift` rewrite (axeyum-rewrite) collapses a *constant* shift to
// `extract`/`concat`/`sign_extend`. That lowering step used to be TRUSTED. These
// tests certify the identity itself as a Lean-kernel-checked theorem: the per-bit
// equality `⋀_i ( bit_i(shift) ↔ bit_i(concat) )` is proved reflexively and gated by
// the kernel — a WRONG lowering is rejected, never accepted. Carcara has no rule for
// the `(= (bvshl a k) (concat …))` bridge (STEP-0 probe: `bv_poly_simp`/`bitblast_*`/
// `*_simplify` all reject it), so this standalone kernel lemma is the certificate.

use axeyum_cnf::AletheTerm;
use axeyum_solver::{
    ReconstructCtx, prove_const_shift_lowering_to_lean_module, reconstruct_const_shift_lowering,
};

/// `(bvshl a #b0001)` over width 4 — the LHS the test certifies.
fn shl1_w4() -> AletheTerm {
    AletheTerm::App(
        "bvshl".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    )
}

/// `(concat ((_ extract 2 0) a) #b0)` — the width-4 lowering of `bvshl a 1`
/// (drop the top bit, append one zero at the low end).
fn shl1_w4_concat() -> AletheTerm {
    AletheTerm::App(
        "concat".to_owned(),
        vec![
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![2, 0],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
            AletheTerm::Const("#b0".to_owned()),
        ],
    )
}

/// **ROUTE-B positive (`bvshl`)**: the constant-left-shift lowering identity
/// `(bvshl a #b0001) = (concat ((_ extract 2 0) a) #b0)` reconstructs to a real-Lean
/// kernel-checked theorem with **no `sorryAx`**.
#[test]
fn const_shl_lowering_checks_in_real_lean() {
    let source = prove_const_shift_lowering_to_lean_module(&shl1_w4(), &shl1_w4_concat(), 4)
        .expect("constant bvshl lowering reconstructs to a kernel-checked theorem");
    // In-tree kernel already accepted (infer + def_eq inside the call); the rendered
    // module must check in real Lean with no sorryAx.
    assert!(
        !source.contains("sorryAx"),
        "const-shl lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_shl_lowering", &source);
}

/// **ROUTE-B positive (`bvlshr`)**: the constant-logical-right-shift identity
/// `(bvlshr a #b0001) = (concat #b0 ((_ extract 3 1) a))` over width 4 — prepend a
/// zero at the high end, drop the low bit.
#[test]
fn const_lshr_lowering_checks_in_real_lean() {
    let shift = AletheTerm::App(
        "bvlshr".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    );
    let concat = AletheTerm::App(
        "concat".to_owned(),
        vec![
            AletheTerm::Const("#b0".to_owned()),
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![3, 1],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
        ],
    );
    let source = prove_const_shift_lowering_to_lean_module(&shift, &concat, 4)
        .expect("constant bvlshr lowering reconstructs to a kernel-checked theorem");
    assert!(
        !source.contains("sorryAx"),
        "const-lshr lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_lshr_lowering", &source);
}

/// **ROUTE-B positive (`bvashr`)**: the constant-arithmetic-right-shift identity
/// `(bvashr a #b0001) = ((_ sign_extend 1) ((_ extract 3 1) a))` over width 4 — drop
/// the low bit, fill the high end with the sign (`sign_extend` of the surviving high
/// slice, whose MSB is `a`'s sign bit).
#[test]
fn const_ashr_lowering_checks_in_real_lean() {
    let shift = AletheTerm::App(
        "bvashr".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    );
    let rhs = AletheTerm::Indexed {
        op: "sign_extend".to_owned(),
        indices: vec![1],
        args: vec![AletheTerm::Indexed {
            op: "extract".to_owned(),
            indices: vec![3, 1],
            args: vec![AletheTerm::Const("a".to_owned())],
        }],
    };
    let source = prove_const_shift_lowering_to_lean_module(&shift, &rhs, 4)
        .expect("constant bvashr lowering reconstructs to a kernel-checked theorem");
    assert!(
        !source.contains("sorryAx"),
        "const-ashr lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_ashr_lowering", &source);
}

/// **ROUTE-B negative (the check has teeth)**: a WRONG lowering of `bvshl a 1` —
/// claiming `(concat ((_ extract 3 1) a) #b0)` (the wrong `extract` slice, the
/// `lshr` pattern) — must be **REJECTED** by the kernel, never certified. This proves
/// the per-bit reflexive proof only type-checks for a genuinely-equal lowering.
#[test]
fn wrong_const_shift_lowering_is_rejected_by_kernel() {
    let mut ctx = ReconstructCtx::new();
    let wrong_concat = AletheTerm::App(
        "concat".to_owned(),
        vec![
            // WRONG: `bvshl a 1` keeps bits 2..0 of `a` in the high part, not 3..1.
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![3, 1],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
            AletheTerm::Const("#b0".to_owned()),
        ],
    );
    let result = reconstruct_const_shift_lowering(&mut ctx, &shl1_w4(), &wrong_concat, 4);
    assert!(
        matches!(
            result,
            Err(axeyum_solver::ReconstructError::KernelRejected { .. })
        ),
        "a wrong shift→concat lowering must be kernel-REJECTED, got {result:?}"
    );
}

/// **Regression / boundary**: the CORRECT lowering reconstructs through the in-tree
/// kernel (`reconstruct_const_shift_lowering` returns `Ok`) — the positive companion
/// to the rejection test, without needing a `lean` binary.
#[test]
fn const_shift_lowering_in_tree_kernel_accepts() {
    let mut ctx = ReconstructCtx::new();
    let ok = reconstruct_const_shift_lowering(&mut ctx, &shl1_w4(), &shl1_w4_concat(), 4);
    assert!(
        ok.is_ok(),
        "the correct bvshl lowering must be kernel-accepted, got {ok:?}"
    );
}

// --- Certified conjunctive QF_LRA Craig interpolant (lra_interpolant_certified) ---
//
// The interpolant `I` carries two Farkas certificates witnessing its two Craig
// soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction is itself
// a conjunctive LRA refutation, so `prove_unsat_to_lean_module` reconstructs it to
// a Lean-kernel-checked `theorem … : False`. Feeding both to the REAL `lean`
// binary — accepted, no `sorryAx` — is the external check that upgrades the
// interpolant from Validated to Checked via the Lean route.

/// Write `source` to a temp `.lean` file and run `lean`; return `true` iff the
/// module type-checks (exit 0). Skips (returns early `true`-equivalent via the
/// caller's guard) when no `lean` binary is available. Used by the TAMPER test to
/// confirm the kernel REJECTS a corrupted module.
fn lean_typechecks(tag: &str, source: &str) -> Option<bool> {
    let bin = lean_bin()?;
    let dir = std::env::temp_dir().join(format!("axeyum_lean_{tag}"));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{tag}.lean"));
    std::fs::write(&file, source).expect("write lean module");
    let out = Command::new(&bin)
        .arg(&file)
        .output()
        .expect("run lean binary");
    Some(out.status.success())
}

#[test]
fn certified_lra_interpolant_both_farkas_certs_checked_by_real_lean() {
    use axeyum_solver::lra_interpolant_certified;
    // A: x ≤ 0 ; B: x ≥ 1.  Unsat; shared variable x.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");

    // Craig condition 1: A ∧ ¬I reconstructs to a kernel-checked `: False`.
    let (_frag_a, source_a) = prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i)
        .expect("A ∧ ¬I reconstructs to a Lean module");
    assert!(
        !source_a.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{source_a}"
    );
    lean_accepts("interp_a_not_i", &source_a);

    // Craig condition 2: I ∧ B reconstructs to a kernel-checked `: False`.
    let (_frag_b, source_b) = prove_unsat_to_lean_module(&mut arena, &cert.i_and_b)
        .expect("I ∧ B reconstructs to a Lean module");
    assert!(
        !source_b.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{source_b}"
    );
    lean_accepts("interp_i_b", &source_b);
}

// (A rational-coefficient certified interpolant — `3x ≤ 1 ∧ 2x ≥ 3` — is exercised
// against the Lean *in-tree* kernel inside `lra_interpolant_certified` and against
// Carcara in `carcara_crosscheck`; it is intentionally NOT fed to the real `lean`
// binary here because the verbose nested-`add` reconstruction overruns Lean's
// default `maxRecDepth` during elaboration — a pretty-printing depth limit, not a
// soundness rejection. The unit-coefficient case above already proves real-Lean
// acceptance of both Farkas certs end to end.)

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified
/// refutation module and replace its proof term with `sorry`. The real Lean kernel
/// then EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated certificate cannot pass the gate the positive tests use.
#[test]
fn tampered_certified_lra_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::lra_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();
    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i).expect("A ∧ ¬I reconstructs");

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    // Keep the trailing `#print axioms` line so the axiom audit still runs.
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive tests rely on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_interp_tampered");
        let file = dir.join("interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

// --- Certified conjunctive QF_UF (EUF) Craig interpolant (qf_uf_interpolant_certified) ---
//
// The EUF interpolant `I` carries two congruence certificates witnessing its two
// Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction is a
// single-disequality congruence conflict, so `prove_unsat_to_lean_module`
// reconstructs it (through the `QfUf` fragment) to a Lean-kernel-checked
// `theorem … : False`. Feeding both to the REAL `lean` binary — accepted, no
// `sorryAx` — is the external check that upgrades the EUF interpolant from Validated
// to Checked via the Lean route.

#[test]
fn certified_euf_interpolant_both_congruence_certs_checked_by_real_lean() {
    use axeyum_solver::qf_uf_interpolant_certified;
    // A: a=b, b=c ; B: a≠c.  I = (a=c), a positive equality conjunction.
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let a = {
        let s = arena.declare("a", alpha).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", alpha).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", alpha).unwrap();
        arena.var(s)
    };
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();

    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");

    // Craig condition 1: A ∧ ¬I reconstructs to a kernel-checked `: False`.
    let (_frag_a, source_a) = prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i)
        .expect("A ∧ ¬I reconstructs to a Lean module");
    assert!(
        !source_a.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{source_a}"
    );
    lean_accepts("euf_interp_a_not_i", &source_a);

    // Craig condition 2: I ∧ B reconstructs to a kernel-checked `: False`.
    let (_frag_b, source_b) = prove_unsat_to_lean_module(&mut arena, &cert.i_and_b)
        .expect("I ∧ B reconstructs to a Lean module");
    assert!(
        !source_b.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{source_b}"
    );
    lean_accepts("euf_interp_i_b", &source_b);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified EUF
/// refutation module and replace its proof term with `sorry`. The real Lean kernel
/// then EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated EUF certificate cannot pass the gate the positive test
/// uses.
#[test]
fn tampered_certified_euf_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::qf_uf_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let a = {
        let s = arena.declare("a", alpha).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", alpha).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", alpha).unwrap();
        arena.var(s)
    };
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();
    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i).expect("A ∧ ¬I reconstructs");

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("euf_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_euf_interp_tampered");
        let file = dir.join("euf_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered EUF refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

// --- Certified conjunctive QF_LIA Craig interpolant (lia_interpolant_certified) ---
//
// The LIA interpolant `I` carries two KERNEL-CHECKED integer certificates witnessing
// its two Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction
// is an integer-infeasible system the integer-prelude reconstructor covers
// (Diophantine / interval cut), so each certificate is a Lean module
// `prove_unsat_to_lean_module` already kernel-checked in-tree. Feeding both to the
// REAL `lean` binary — accepted, no `sorryAx` — is the external check that upgrades
// the LIA interpolant from Validated to Checked. Carcara has NO `lia_generic` rule
// (warns + `holey`), so for integers the Lean kernel is the external checker.

#[test]
fn certified_lia_interpolant_both_integer_certs_checked_by_real_lean() {
    use axeyum_solver::{ProofFragment, lia_interpolant_certified};
    // A: 2x ≥ 1 ; B: 2x ≤ 0 over Int.  Unsat; shared variable x.  I = (2x ≥ 1), and
    // both A ∧ ¬I and I ∧ B are the empty integer interval 1 ≤ 2x ≤ 0 (IntInequality).
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_x, one).unwrap();
    let b0 = arena.int_le(two_x, zero).unwrap();

    let cert = lia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified LIA interpolant exists");

    // Both certificates reconstructed through a COVERED integer fragment.
    assert!(matches!(
        cert.a_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));
    assert!(matches!(
        cert.b_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));

    // Craig condition 1: A ∧ ¬I is the kernel-checked integer module on the cert.
    assert!(
        !cert.a_certificate.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{}",
        cert.a_certificate
    );
    lean_accepts("lia_interp_a_not_i", &cert.a_certificate);

    // Craig condition 2: I ∧ B likewise.
    assert!(
        !cert.b_certificate.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{}",
        cert.b_certificate
    );
    lean_accepts("lia_interp_i_b", &cert.b_certificate);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified LIA
/// integer module and replace its proof term with `sorry`. The real Lean kernel then
/// EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated LIA certificate cannot pass the gate the positive test
/// uses.
#[test]
fn tampered_certified_lia_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::lia_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_x, one).unwrap();
    let b0 = arena.int_le(two_x, zero).unwrap();
    let cert = lia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified LIA interpolant exists");
    let source = &cert.a_certificate;

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("lia_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_lia_interp_tampered");
        let file = dir.join("lia_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered LIA refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

/// BOUNDARY (`QF_UFLRA` interpolant cert): the certified conjunctive `QF_UFLRA` Craig
/// interpolant (`uflra_interpolant_certified`) carries its two soundness conditions
/// as `la_generic` refutations over OPAQUE uninterpreted-function applications, and
/// those are externally re-checked by **Carcara** (see `carcara_crosscheck.rs`). The
/// Lean-kernel reconstruction path (`prove_unsat_to_lean_module`) does NOT yet cover
/// the opaque-application `LRA` fragment, so it declines these conjunctions — the
/// external check for this cert is Carcara, not Lean. This test pins that boundary so
/// a future Lean-fragment extension is a deliberate, noticed change.
#[test]
fn uflra_opaque_application_refutation_is_declined_by_lean_path() {
    use axeyum_ir::Sort;
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let c = arena.real_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let five = arena.real_const(Rational::integer(5));
    // f(c) >= 5 ∧ f(c) < 5 — UNSAT with f(c) opaque; Carcara checks it via la_generic.
    let a = arena.real_ge(fc, five).unwrap();
    let b = arena.real_lt(fc, five).unwrap();
    assert!(
        prove_unsat_to_lean_module(&mut arena, &[a, b]).is_err(),
        "the Lean reconstruction path does not (yet) cover opaque-application LRA; \
         this cert's external check is Carcara"
    );
}

// --- Certified conjunctive QF_UFLIA Craig interpolant (uflia_interpolant_certified) ---
//
// The QF_UFLIA interpolant `I` carries two KERNEL-CHECKED integer certificates witnessing
// its two Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Because the
// conjunctive construction declines whenever congruence is needed (the function-free
// relaxation is then sat), the certifiable interpolant is always congruence-free — its UF
// applications `(f c)` are OPAQUE shared integers. Each conjunction is therefore an
// integer-infeasible system over opaque applications that the integer-prelude
// reconstructor covers (Diophantine / interval cut, with each `(f c)` treated as a fresh
// opaque integer), so each certificate is a Lean module `prove_unsat_to_lean_module`
// already kernel-checked in-tree. Feeding both to the REAL `lean` binary — accepted, no
// `sorryAx` — is the external check that upgrades the QF_UFLIA interpolant from Validated
// to Checked. Carcara has NO `lia_generic` rule (warns + `holey`), so for integers the
// Lean kernel is the external checker (unlike QF_UFLRA, whose opaque-application
// `la_generic` refutations Carcara checks).

#[test]
fn certified_uflia_interpolant_both_integer_certs_checked_by_real_lean() {
    use axeyum_solver::{ProofFragment, uflia_interpolant_certified};
    // A: 2·f(c) ≥ 1 ; B: 2·f(c) ≤ 0 over Int, with f(c) a SHARED opaque integer
    // application. Unsat (2·f(c) is even, cannot be ≥ 1 and ≤ 0). I = (2·f(c) ≥ 1), and
    // both A ∧ ¬I and I ∧ B are diff-multiplier integer intervals over the opaque f(c).
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let c = arena.int_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let two = arena.int_const(2);
    let two_fc = arena.int_mul(two, fc).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_fc, one).unwrap();
    let b0 = arena.int_le(two_fc, zero).unwrap();

    let cert = uflia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLIA interpolant exists");

    // Both certificates reconstructed through a COVERED integer fragment.
    assert!(matches!(
        cert.a_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));
    assert!(matches!(
        cert.b_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));

    // Craig condition 1: A ∧ ¬I is the kernel-checked integer module on the cert.
    assert!(
        !cert.a_certificate.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{}",
        cert.a_certificate
    );
    lean_accepts("uflia_interp_a_not_i", &cert.a_certificate);

    // Craig condition 2: I ∧ B likewise.
    assert!(
        !cert.b_certificate.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{}",
        cert.b_certificate
    );
    lean_accepts("uflia_interp_i_b", &cert.b_certificate);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified `QF_UFLIA`
/// integer module and replace its proof term with `sorry`. The real Lean kernel then
/// EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are rejections.
/// A fabricated `QF_UFLIA` certificate cannot pass the gate the positive test uses.
#[test]
fn tampered_certified_uflia_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::uflia_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let c = arena.int_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let two = arena.int_const(2);
    let two_fc = arena.int_mul(two, fc).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_fc, one).unwrap();
    let b0 = arena.int_le(two_fc, zero).unwrap();
    let cert = uflia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLIA interpolant exists");
    let source = &cert.a_certificate;

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("uflia_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST expose
        // `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_uflia_interp_tampered");
        let file = dir.join("uflia_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered QF_UFLIA refutation must expose sorryAx in the audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}
