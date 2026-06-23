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
