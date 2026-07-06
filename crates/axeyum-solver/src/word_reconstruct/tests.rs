//! Tests for the word-clash → kernel-checked Lean reconstruction.
//!
//! Positive: each covered class (direct clash, chained clash, contradicted
//! disequality) reconstructs to a module whose proof the kernel already checked to
//! `False` (a successful return *is* the kernel gate — [`WordCtx::gate_and_render`]
//! `infer`s + `def_eq False`-compares before rendering). Routing: the scanner
//! classifies these as [`ProofFragment::WordEquation`]. Declines: self-loop /
//! length shapes are safely declined. Negative: a deliberately wrong proof term is
//! rejected by the kernel gate (never a bogus `False`). Property: ≥300 generated
//! certified refutations all reconstruct + kernel-check.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use axeyum_ir::{Sort, TermArena, TermId};

use super::*;
use crate::reconstruct::ProofFragment;

const W: u32 = 8;

fn seq_var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena
        .declare(name, Sort::Seq(axeyum_ir::ArraySortKey::BitVec(W)))
        .expect("seq var");
    arena.var(s)
}

/// A single-character constant sequence for byte `c`.
fn ch(arena: &mut TermArena, c: u8) -> TermId {
    let e = arena.bv_const(W, u128::from(c)).expect("char const");
    arena.seq_unit(e).expect("seq.unit")
}

/// A concrete constant string from bytes, as a right-nested `str.++` of units.
fn word(arena: &mut TermArena, bytes: &[u8]) -> TermId {
    assert!(!bytes.is_empty());
    let mut acc = ch(arena, bytes[bytes.len() - 1]);
    for &b in bytes[..bytes.len() - 1].iter().rev() {
        let u = ch(arena, b);
        acc = arena.seq_concat(u, acc).expect("concat");
    }
    acc
}

fn eq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.eq(a, b).expect("eq")
}

fn neq(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    let e = arena.eq(a, b).expect("eq");
    arena.not(e).expect("not")
}

/// Reconstruct through the public entry, asserting the module was kernel-checked.
fn reconstruct(arena: &mut TermArena, assertions: &[TermId]) -> String {
    let src = reconstruct_word_clash_to_lean_module(arena, assertions)
        .expect("word refutation reconstructs + kernel-checks to False");
    assert!(src.contains("theorem"), "renders a Lean theorem module");
    assert!(
        src.contains(WORD_LEAN_THEOREM),
        "module carries the word theorem name"
    );
    src
}

// ----- routing ---------------------------------------------------------------

#[test]
fn scanner_routes_word_shape_to_word_equation_fragment() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let assertions = [eq(&mut arena, x, a), eq(&mut arena, x, b)];
    let frag = crate::reconstruct::scan_proof_fragment(&arena, &assertions);
    assert_eq!(frag, ProofFragment::WordEquation);
}

#[test]
fn scanner_rejects_non_word_shape() {
    // A Bool equality is not a Seq word literal.
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).expect("bool var");
    let pv = arena.var(p);
    let t = arena.bool_const(true);
    let assertions = [eq(&mut arena, pv, t)];
    assert!(!is_word_equation_shape(&arena, &assertions));
}

// ----- covered classes -------------------------------------------------------

#[test]
fn constant_clash_direct() {
    // x = "a" ∧ x = "b": one variable forced to two distinct one-char constants.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let assertions = [eq(&mut arena, x, a), eq(&mut arena, x, b)];
    reconstruct(&mut arena, &assertions);
}

#[test]
fn constant_clash_direct_multichar_interior_position() {
    // x = "abc" ∧ x = "abd": the clash is at interior position 2 (a,b common).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let abc = word(&mut arena, b"abc");
    let abd = word(&mut arena, b"abd");
    let assertions = [eq(&mut arena, x, abc), eq(&mut arena, x, abd)];
    reconstruct(&mut arena, &assertions);
}

#[test]
fn constant_clash_chained() {
    // x = "a" ∧ x = y ∧ y = "b": the clash closes through the derived x ≈ y.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let assertions = [
        eq(&mut arena, x, a),
        eq(&mut arena, x, y),
        eq(&mut arena, y, b),
    ];
    reconstruct(&mut arena, &assertions);
}

#[test]
fn disequality_direct() {
    // x = "hi" ∧ y = "hi" ∧ x ≠ y: the premises force x ≈ y, contradicting x ≠ y.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let hi1 = word(&mut arena, b"hi");
    let hi2 = word(&mut arena, b"hi");
    let assertions = [
        eq(&mut arena, x, hi1),
        eq(&mut arena, y, hi2),
        neq(&mut arena, x, y),
    ];
    reconstruct(&mut arena, &assertions);
}

#[test]
fn disequality_chained_through_variables() {
    // x = y ∧ y = z ∧ x ≠ z: a pure variable chain, no concrete constant at all.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z = seq_var(&mut arena, "z");
    let assertions = [
        eq(&mut arena, x, y),
        eq(&mut arena, y, z),
        neq(&mut arena, x, z),
    ];
    reconstruct(&mut arena, &assertions);
}

#[test]
fn end_to_end_prove_unsat_to_lean_module_reports_word_fragment() {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let assertions = [eq(&mut arena, x, a), eq(&mut arena, x, b)];
    let (frag, src) =
        crate::prove_unsat_to_lean_module(&mut arena, &assertions).expect("reconstructs");
    assert_eq!(frag, ProofFragment::WordEquation);
    assert!(src.contains("theorem"));
}

// ----- documented declines ---------------------------------------------------

#[test]
fn self_loop_length_shape_declines() {
    // x = "a" ++ x: a self-loop / length contradiction — deferred (not this slice).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let ax = arena.seq_concat(a, x).expect("concat");
    let assertions = [eq(&mut arena, x, ax)];
    assert!(
        reconstruct_word_clash_to_lean_module(&mut arena, &assertions).is_err(),
        "self-loop is a documented decline, not a wrong False"
    );
}

#[test]
fn variable_prefix_cancellation_declines() {
    // x ++ "a" = x ++ "b": a cancellation clash — deferred (needs append cancel).
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let xa = arena.seq_concat(x, a).expect("concat");
    let xb = arena.seq_concat(x, b).expect("concat");
    let assertions = [eq(&mut arena, xa, xb)];
    // Either the refuter declines it, or the clash-finder finds no concrete
    // members — both surface as an Err (a safe decline), never a wrong False.
    assert!(reconstruct_word_clash_to_lean_module(&mut arena, &assertions).is_err());
}

#[test]
fn satisfiable_system_declines() {
    // x = "a" ∧ y = "b": perfectly satisfiable — the refuter never certifies it.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let assertions = [eq(&mut arena, x, a), eq(&mut arena, y, b)];
    assert!(
        reconstruct_word_clash_to_lean_module(&mut arena, &assertions).is_err(),
        "a satisfiable system yields no refutation (safe decline, never a False)"
    );
}

// ----- negative: the kernel rejects a wrong proof ----------------------------

#[test]
fn kernel_rejects_discriminator_on_equal_strings() {
    // Assemble a DELIBERATELY WRONG proof: apply the clash discriminator to the
    // reflexive equality of a string with ITSELF (no genuine clash). Both `g A`
    // reduce to the SAME Bool value, so `bool_true_ne_false` cannot infer to
    // `False`; the kernel gate must reject it (never a bogus certificate).
    let codepoints: std::collections::BTreeSet<u128> = [b'a'.into()].into_iter().collect();
    let mut ctx = WordCtx::new(&codepoints);
    let a = ctx.concrete_str(&[u128::from(b'a')]).expect("concrete");
    let str_ty = ctx.sp.str_const(&mut ctx.kernel);
    // refl : Eq Str a a (no clash). Build g and mis-apply the discriminator.
    let refl = ctx.eq_refl(str_ty, a);
    let bool_ty = ctx.kernel.const_(ctx.sp.logic.bool_, vec![]);
    let g = build_projection_tester(&mut ctx, 0, 0); // is_a ∘ head
    let g_a = ctx.kernel.app(g, a); // ι→ true
    let congr = ctx.congr_arg(str_ty, bool_ty, g, a, a, refl); // Eq Bool (g a)(g a) = Eq Bool true true
    let bogus = ctx.bool_true_ne_false(g_a, congr); // g_a ι→ true, NOT false
    assert!(
        ctx.gate_and_render(bogus).is_err(),
        "the kernel must reject a discriminator over a non-clash"
    );
}

#[test]
fn kernel_rejects_unrelated_hypothesis_chain() {
    // A "corrupted certificate": claim a disequality contradiction between two
    // strings the (empty) premise set does NOT connect. The chain cannot be built,
    // so reconstruction declines — no False is fabricated.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    // x ≠ y with NO equalities: not refutable, and no chain exists.
    let assertions = [neq(&mut arena, x, y)];
    assert!(reconstruct_word_clash_to_lean_module(&mut arena, &assertions).is_err());
}

// ----- property: generated certified refutations all reconstruct -------------

/// A tiny deterministic LCG for reproducible generation (no external dep).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        self.0 >> 16
    }
    fn range(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random non-empty lowercase word of length 1..=4.
fn rand_word(rng: &mut Lcg) -> Vec<u8> {
    let len = 1 + usize::try_from(rng.range(4)).expect("small");
    (0..len)
        .map(|_| b'a' + u8::try_from(rng.range(6)).expect("small"))
        .collect()
}

#[test]
fn property_generated_refutations_reconstruct_and_kernel_check() {
    let mut rng = Lcg(0x_a1ce_5eed);
    let mut ok = 0usize;
    let target = 360usize;
    for _ in 0..target {
        let mut arena = TermArena::new();
        let x = seq_var(&mut arena, "x");
        let y = seq_var(&mut arena, "y");
        let z = seq_var(&mut arena, "z");
        let shape = rng.range(3);
        let assertions: Vec<TermId> = match shape {
            0 => {
                // Direct clash: x = C1 ∧ x = C2 with distinct concrete C1, C2.
                let mut c1 = rand_word(&mut rng);
                let mut c2 = rand_word(&mut rng);
                // Force a genuine differing position (not just a length prefix):
                // append a distinguishing tail char so a same-position clash exists.
                let n = c1.len().min(c2.len());
                if !(0..n).any(|i| c1[i] != c2[i]) {
                    c1.push(b'x');
                    c2.push(b'y');
                }
                let w1 = word(&mut arena, &c1);
                let w2 = word(&mut arena, &c2);
                vec![eq(&mut arena, x, w1), eq(&mut arena, x, w2)]
            }
            1 => {
                // Chained clash: x = y ∧ y = C1 ∧ x = C2 (distinct at a position).
                let mut c1 = rand_word(&mut rng);
                let mut c2 = rand_word(&mut rng);
                let n = c1.len().min(c2.len());
                if !(0..n).any(|i| c1[i] != c2[i]) {
                    c1.push(b'x');
                    c2.push(b'y');
                }
                let w1 = word(&mut arena, &c1);
                let w2 = word(&mut arena, &c2);
                vec![
                    eq(&mut arena, x, y),
                    eq(&mut arena, y, w1),
                    eq(&mut arena, x, w2),
                ]
            }
            _ => {
                // Disequality: x = C ∧ y = C ∧ x ≠ y (same concrete, disequal).
                let c = rand_word(&mut rng);
                let w1 = word(&mut arena, &c);
                let w2 = word(&mut arena, &c);
                let _ = z;
                vec![
                    eq(&mut arena, x, w1),
                    eq(&mut arena, y, w2),
                    neq(&mut arena, x, y),
                ]
            }
        };
        match reconstruct_word_clash_to_lean_module(&mut arena, &assertions) {
            Ok(src) => {
                assert!(src.contains("theorem"));
                ok += 1;
            }
            Err(e) => panic!("generated certified refutation must reconstruct: {e:?}"),
        }
    }
    assert_eq!(ok, target, "every generated refutation reconstructs");
    assert!(ok >= 300, "property covers at least 300 cases");
}
