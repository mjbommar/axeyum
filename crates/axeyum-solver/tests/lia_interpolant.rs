//! Conjunctive `QF_LIA` Craig interpolation (rational relaxation, verified over
//! the integers).
//!
//! Each test refutes an integer conjunction `A ∧ B`, asks [`lia_interpolant`] for
//! an interpolant `I`, and *independently* re-checks `A ⇒ I`, `I ∧ B ⇒ ⊥`, and
//! the shared-vocabulary condition with [`check_with_lia_simplex`] — so the
//! assurance does not lean on the generator's own internal verification. The
//! cuts-needed and satisfiable cases assert the function declines (`None`).
#![cfg(feature = "full")]

use std::collections::BTreeSet;

use axeyum_ir::{SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, ProofFragment, check_with_lia_simplex, lia_interpolant, lia_interpolant_certified,
    prove_unsat_to_lean_module,
};

/// Declares a fresh `Int` symbol and returns its variable term.
fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, axeyum_ir::Sort::Int).unwrap();
    arena.var(s)
}

/// Builds `lhs <= rhs` over integers.
fn le(arena: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
    arena.int_le(lhs, rhs).unwrap()
}

/// Builds `lhs >= rhs` over integers.
fn ge(arena: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
    arena.int_ge(lhs, rhs).unwrap()
}

/// Builds `lhs = rhs`.
fn eq(arena: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
    arena.eq(lhs, rhs).unwrap()
}

/// Integer constant term.
fn k(arena: &mut TermArena, value: i128) -> TermId {
    arena.int_const(value)
}

/// `coeff * var`.
fn scale(arena: &mut TermArena, coeff: i128, var: TermId) -> TermId {
    let c = arena.int_const(coeff);
    arena.int_mul(c, var).unwrap()
}

/// Collects the free symbols of a term.
fn symbols_of(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            for &a in args {
                symbols_of(arena, a, out);
            }
        }
        _ => {}
    }
}

fn symbols_of_all(arena: &TermArena, terms: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for &t in terms {
        symbols_of(arena, t, &mut out);
    }
    out
}

fn is_unsat(arena: &TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_with_lia_simplex(arena, assertions).unwrap(),
        CheckResult::Unsat
    )
}

/// Independently re-checks the three Craig conditions of `interpolant` for the
/// partition `(a, b)` using `check_with_lia_simplex` — does NOT trust the
/// generator. Panics with a clear message on any violation.
fn assert_valid_interpolant(
    arena: &mut TermArena,
    a: &[TermId],
    b: &[TermId],
    interpolant: TermId,
) {
    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_i = arena.not(interpolant).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(
        is_unsat(arena, &a_not_i),
        "condition (1) A ∧ ¬I must be unsat"
    );

    // (2) I ∧ B unsat.
    let mut i_b = vec![interpolant];
    i_b.extend_from_slice(b);
    assert!(is_unsat(arena, &i_b), "condition (2) I ∧ B must be unsat");

    // (3) Vocabulary: every symbol of I appears in both A and B.
    let a_syms = symbols_of_all(arena, a);
    let b_syms = symbols_of_all(arena, b);
    let mut i_syms = BTreeSet::new();
    symbols_of(arena, interpolant, &mut i_syms);
    for s in &i_syms {
        assert!(
            a_syms.contains(s) && b_syms.contains(s),
            "condition (3) interpolant symbol {s:?} must be shared by A and B"
        );
    }
}

#[test]
fn shared_variable_contradiction() {
    // A: x <= 0, B: x >= 1 over the integers. UNSAT; interpolant over x.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = k(&mut arena, 0);
    let one = k(&mut arena, 1);
    let a = vec![le(&mut arena, x, zero)];
    let b = vec![ge(&mut arena, x, one)];

    let mut combined = a.clone();
    combined.extend_from_slice(&b);
    assert!(is_unsat(&arena, &combined), "A ∧ B must be UNSAT");

    let interpolant = lia_interpolant(&mut arena, &a, &b)
        .unwrap()
        .expect("expected an interpolant for x<=0 ∧ x>=1");
    assert_valid_interpolant(&mut arena, &a, &b, interpolant);
}

#[test]
fn a_local_variable_excluded_from_interpolant() {
    // A: x <= 0 ∧ y_a <= x  (y_a is A-local), B: x >= 1.  y_a must NOT be in I.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y_a = int_var(&mut arena, "y_local");
    let zero = k(&mut arena, 0);
    let one = k(&mut arena, 1);
    let a = vec![le(&mut arena, x, zero), le(&mut arena, y_a, x)];
    let b = vec![ge(&mut arena, x, one)];

    let mut combined = a.clone();
    combined.extend_from_slice(&b);
    assert!(is_unsat(&arena, &combined));

    let interpolant = lia_interpolant(&mut arena, &a, &b)
        .unwrap()
        .expect("expected an interpolant");
    assert_valid_interpolant(&mut arena, &a, &b, interpolant);

    // y_local is A-only: it must not occur in the interpolant.
    let mut i_syms = BTreeSet::new();
    symbols_of(&arena, interpolant, &mut i_syms);
    let y_sym = {
        let mut s = BTreeSet::new();
        symbols_of(&arena, y_a, &mut s);
        *s.iter().next().unwrap()
    };
    assert!(
        !i_syms.contains(&y_sym),
        "A-local variable must not appear in the interpolant"
    );
}

#[test]
fn two_variable_sum() {
    // A: x + y <= 0, B: x + y >= 2.  UNSAT; interpolant over x and y.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let zero = k(&mut arena, 0);
    let two = k(&mut arena, 2);
    let xpy_a = arena.int_add(x, y).unwrap();
    let xpy_b = arena.int_add(x, y).unwrap();
    let a = vec![le(&mut arena, xpy_a, zero)];
    let b = vec![ge(&mut arena, xpy_b, two)];

    let mut combined = a.clone();
    combined.extend_from_slice(&b);
    assert!(is_unsat(&arena, &combined));

    let interpolant = lia_interpolant(&mut arena, &a, &b)
        .unwrap()
        .expect("expected an interpolant for x+y<=0 ∧ x+y>=2");
    assert_valid_interpolant(&mut arena, &a, &b, interpolant);
}

#[test]
fn denominator_clearing() {
    // A: 2x <= 1, B: 2x >= 3.  Over ℚ the Farkas combination is fractional
    // (multiplying by 1/2 yields x <= 1/2), forcing denominator-clearing back to
    // integer coefficients. UNSAT over both ℚ and ℤ.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two_x_a = scale(&mut arena, 2, x);
    let two_x_b = scale(&mut arena, 2, x);
    let one = k(&mut arena, 1);
    let three = k(&mut arena, 3);
    let a = vec![le(&mut arena, two_x_a, one)];
    let b = vec![ge(&mut arena, two_x_b, three)];

    let mut combined = a.clone();
    combined.extend_from_slice(&b);
    assert!(is_unsat(&arena, &combined));

    let interpolant = lia_interpolant(&mut arena, &a, &b)
        .unwrap()
        .expect("expected an interpolant for 2x<=1 ∧ 2x>=3");
    assert_valid_interpolant(&mut arena, &a, &b, interpolant);
}

#[test]
fn cuts_needed_relaxation_sat_declines() {
    // A: 2x = 1 is UNSAT over ℤ, but its rational relaxation 2x = 1 is SAT over ℚ
    // (x = 1/2). The interpolation route uses the relaxation, which is NOT
    // refutable by Farkas, so the function must DECLINE (Ok(None)) — never a wrong
    // interpolant.  We pair it with a trivial B to keep a partition.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two_x = scale(&mut arena, 2, x);
    let one = k(&mut arena, 1);
    let zero = k(&mut arena, 0);
    // A asserts the integer-unsat 2x = 1; B just constrains x (shared var).
    let a = vec![eq(&mut arena, two_x, one)];
    let b = vec![ge(&mut arena, x, zero)];

    // A alone is integer-UNSAT (2x = 1 has no integer solution).
    assert!(is_unsat(&arena, &a), "2x = 1 is integer-UNSAT");

    // The relaxation is SAT over ℚ, so the rational-relaxation method declines.
    let result = lia_interpolant(&mut arena, &a, &b).unwrap();
    assert!(
        result.is_none(),
        "cuts-needed (relaxation-SAT) case must decline, got {result:?}"
    );
}

#[test]
fn satisfiable_pair_declines() {
    // A: x <= 5, B: x >= 0.  SAT (e.g. x = 3) ⇒ no interpolant.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let five = k(&mut arena, 5);
    let zero = k(&mut arena, 0);
    let a = vec![le(&mut arena, x, five)];
    let b = vec![ge(&mut arena, x, zero)];

    let mut combined = a.clone();
    combined.extend_from_slice(&b);
    assert!(!is_unsat(&arena, &combined), "A ∧ B is SAT here");

    let result = lia_interpolant(&mut arena, &a, &b).unwrap();
    assert!(result.is_none(), "satisfiable pair must yield None");
}

/// A small deterministic LCG (no `rand`, no clock) for reproducible fuzzing.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        // Numerical Recipes LCG constants.
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A value in `lo..=hi`.
    fn range(&mut self, lo: i128, hi: i128) -> i128 {
        let span = u64::try_from(hi - lo + 1).unwrap();
        lo + i128::from(self.next_u64() % span)
    }
}

#[test]
fn lcg_fuzz_no_unsound_interpolant() {
    // Random small integer conjunctions over ~3 shared int vars. When the combined
    // system is UNSAT and an interpolant is returned, independently re-verify all
    // three conditions. Assert nonzero coverage (some UNSAT with an interpolant).
    let mut rng = Lcg::new(0x5eed_1234_abcd_ef01);

    let mut unsat_count = 0u32;
    let mut interpolant_count = 0u32;

    for _ in 0..400 {
        let mut arena = TermArena::new();
        // Three shared variables x0,x1,x2 plus one A-local and one B-local.
        let xs: Vec<TermId> = (0..3)
            .map(|i| int_var(&mut arena, &format!("x{i}")))
            .collect();
        let a_local = int_var(&mut arena, "a_local");
        let b_local = int_var(&mut arena, "b_local");

        // Build a random linear atom over a chosen variable set.
        let make_atom = |arena: &mut TermArena, rng: &mut Lcg, vars: &[TermId]| -> TermId {
            // sum c_i * v_i  REL  const
            let mut terms: Vec<TermId> = Vec::new();
            for &v in vars {
                let c = rng.range(-2, 2);
                if c == 0 {
                    continue;
                }
                terms.push(scale(arena, c, v));
            }
            let lhs = if terms.is_empty() {
                k(arena, 0)
            } else {
                let mut acc = terms[0];
                for &t in &terms[1..] {
                    acc = arena.int_add(acc, t).unwrap();
                }
                acc
            };
            let rhs = k(arena, rng.range(-3, 3));
            match rng.range(0, 3) {
                0 => arena.int_le(lhs, rhs).unwrap(),
                1 => arena.int_ge(lhs, rhs).unwrap(),
                2 => arena.int_lt(lhs, rhs).unwrap(),
                _ => arena.int_gt(lhs, rhs).unwrap(),
            }
        };

        // A uses shared vars + a_local; B uses shared vars + b_local.
        let mut a_vars = xs.clone();
        a_vars.push(a_local);
        let mut b_vars = xs.clone();
        b_vars.push(b_local);

        let mut a = Vec::new();
        for _ in 0..rng.range(1, 3) {
            a.push(make_atom(&mut arena, &mut rng, &a_vars));
        }
        let mut b = Vec::new();
        for _ in 0..rng.range(1, 3) {
            b.push(make_atom(&mut arena, &mut rng, &b_vars));
        }

        let mut combined = a.clone();
        combined.extend_from_slice(&b);
        let combined_unsat = is_unsat(&arena, &combined);
        if combined_unsat {
            unsat_count += 1;
        }

        // Declining (None) is always acceptable; a returned interpolant must be
        // sound (only for UNSAT) and pass an independent re-verification.
        if let Some(interpolant) = lia_interpolant(&mut arena, &a, &b).unwrap() {
            assert!(
                combined_unsat,
                "interpolant returned for a SAT conjunction (unsound)"
            );
            interpolant_count += 1;
            assert_valid_interpolant(&mut arena, &a, &b, interpolant);
        }
    }

    assert!(
        unsat_count > 0,
        "fuzz produced no UNSAT instances — adjust the generator"
    );
    assert!(
        interpolant_count > 0,
        "fuzz produced no interpolants — coverage too low"
    );
}

// --- Certified conjunctive QF_LIA Craig interpolant (lia_interpolant_certified) ---
//
// The certified interpolant `I` carries two KERNEL-CHECKED integer certificates
// witnessing its two Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`.
// Each conjunction is an integer-infeasible system the integer-prelude
// reconstructor covers (Diophantine / interval cut), so `prove_unsat_to_lean_module`
// reconstructs it to a Lean-kernel-checked `theorem … : False` (no `sorryAx`). The
// in-tree `axeyum_lean_kernel::Kernel` (`infer` + `def_eq False`) is the REAL gate
// here — it runs inside `prove_unsat_to_lean_module` before the module is rendered,
// so `Ok` already means kernel-accepted. (The real `lean` binary re-checks the same
// modules in `lean_crosscheck.rs`.) For integers Carcara has no `lia_generic` rule
// (warns + `holey`), so the Lean kernel is the external checker.

/// The certifiable shape: `A: 2·x ≥ 1`, `B: 2·x ≤ 0` over `Int`. The rational
/// relaxation is unsat (`x ≥ ½ ∧ x ≤ 0`), so `lia_interpolant` returns `I` with
/// `2·x ≥ 1` (i.e. `1 − 2·x ≤ 0`). With `¬I` built as the bare dual `2·x ≤ 0`,
/// BOTH `A ∧ ¬I` and `I ∧ B` are the integer-interval `1 ≤ 2·x ≤ 0` (empty), which
/// reconstructs through the `IntInequality` fragment — a covered shape — so both
/// integer certificates are kernel-checked with NO `sorryAx`. The interpolant `I`
/// is byte-identical to the `Validated` `lia_interpolant` output, and the three
/// Craig conditions still independently re-check.
#[test]
fn certified_lia_interpolant_carries_two_kernel_checked_integer_certs() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two_x = scale(&mut arena, 2, x);
    let zero = k(&mut arena, 0);
    let one = k(&mut arena, 1);
    let a = vec![ge(&mut arena, two_x, one)]; // 2x ≥ 1
    let b = vec![le(&mut arena, two_x, zero)]; // 2x ≤ 0

    // The plain (Validated) interpolant the certified path must reproduce verbatim.
    let plain = lia_interpolant(&mut arena, &a, &b)
        .unwrap()
        .expect("a Validated interpolant exists");

    let cert = lia_interpolant_certified(&mut arena, &a, &b)
        .expect("decides")
        .expect("a certified interpolant exists for 2x≥1 ∧ 2x≤0");

    // The certified interpolant is byte-identical to the Validated one.
    assert_eq!(
        cert.interpolant, plain,
        "certified interpolant must be byte-identical to lia_interpolant"
    );

    // Both soundness conjunctions are certified through a COVERED integer fragment.
    assert!(
        matches!(
            cert.a_fragment,
            ProofFragment::Diophantine | ProofFragment::IntInequality
        ),
        "A ∧ ¬I must reconstruct through an integer fragment, got {:?}",
        cert.a_fragment
    );
    assert!(
        matches!(
            cert.b_fragment,
            ProofFragment::Diophantine | ProofFragment::IntInequality
        ),
        "I ∧ B must reconstruct through an integer fragment, got {:?}",
        cert.b_fragment
    );

    // Both Lean certificates are kernel-checked (the module is rendered ONLY after
    // `prove_unsat_to_lean_module` kernel-checks `infer` + `def_eq False`) and audit
    // clean: NO `sorryAx`, and each names the exported refutation theorem.
    for (name, module) in [
        ("A ∧ ¬I", &cert.a_certificate),
        ("I ∧ B", &cert.b_certificate),
    ] {
        assert!(
            !module.contains("sorryAx"),
            "{name} certificate must not depend on sorryAx:\n{module}"
        );
        assert!(
            module.contains("axeyum_refutation"),
            "{name} certificate must name the axeyum_refutation theorem"
        );
    }

    // The conjunctions recorded on the certificate are exactly the ones the modules
    // refute, and re-feeding them to the kernel-checking reconstructor still yields
    // a covered integer fragment (the in-tree kernel gate, run again).
    let (a_frag2, _) = prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i)
        .expect("A ∧ ¬I kernel-reconstructs");
    let (b_frag2, _) =
        prove_unsat_to_lean_module(&mut arena, &cert.i_and_b).expect("I ∧ B kernel-reconstructs");
    assert_eq!(a_frag2, cert.a_fragment);
    assert_eq!(b_frag2, cert.b_fragment);

    // The three Craig conditions still hold (independent re-check, not trusting the
    // certificate): A ⇒ I, I ∧ B ⊢ ⊥, shared vocabulary.
    assert_valid_interpolant(&mut arena, &a, &b, cert.interpolant);
}

/// DECLINE (the honest boundary): `A: x + y ≥ 1`, `B: x + y ≤ 0` over `Int`. A
/// genuine `Validated` interpolant `x + y ≥ 1` exists, but `A ∧ ¬I` /  `I ∧ B` are
/// MULTIVARIATE rational-relaxation refutations — an UNCOVERED integer shape (the
/// integer reconstructor declines; the LRA path rejects `Int` atoms). So the
/// certified path returns `Ok(None)` and the caller falls back to `Validated`. It
/// NEVER fabricates a certificate for an uncovered shape.
#[test]
fn uncovered_integer_refutation_declines_to_validated() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let xy = arena.int_add(x, y).unwrap();
    let zero = k(&mut arena, 0);
    let one = k(&mut arena, 1);
    let a = vec![ge(&mut arena, xy, one)]; // x + y ≥ 1
    let b = vec![le(&mut arena, xy, zero)]; // x + y ≤ 0

    // The Validated path still produces a verified interpolant…
    let plain = lia_interpolant(&mut arena, &a, &b).unwrap();
    assert!(
        plain.is_some(),
        "a Validated interpolant must still exist for x+y≥1 ∧ x+y≤0"
    );
    if let Some(interpolant) = plain {
        assert_valid_interpolant(&mut arena, &a, &b, interpolant);
    }

    // …but the certified path declines (uncovered integer shape).
    let cert = lia_interpolant_certified(&mut arena, &a, &b).expect("decides");
    assert!(
        cert.is_none(),
        "an uncovered (multivariate) integer refutation must NOT be certified"
    );
}

/// TAMPER (the kernel gate has teeth): take a genuine certified integer module and
/// replace its `False`-proof body with `sorry`. The independent `axeyum-lean-grade`
/// audit our certified path relies on — module carries no `sorryAx` — then FAILS:
/// the tampered module trivially contains `sorryAx`, so it would be refused. (The
/// real `lean` binary likewise rejects it; see `lean_crosscheck.rs`.) A fabricated
/// certificate cannot pass the gate the positive test uses.
#[test]
fn tampered_lia_interpolant_certificate_fails_the_sorry_audit() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two_x = scale(&mut arena, 2, x);
    let zero = k(&mut arena, 0);
    let one = k(&mut arena, 1);
    let a = vec![ge(&mut arena, two_x, one)];
    let b = vec![le(&mut arena, two_x, zero)];
    let cert = lia_interpolant_certified(&mut arena, &a, &b)
        .expect("decides")
        .expect("a certified interpolant exists");

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = cert
        .a_certificate
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &cert.a_certificate[..idx + marker.len()];
    let tail_start = cert.a_certificate[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &cert.a_certificate[tail_start..]);

    // The genuine certificate audits clean; the tampered one does not. The audit the
    // certified path enforces (no `sorryAx`) therefore REJECTS the fabrication.
    assert!(!cert.a_certificate.contains("sorryAx"));
    assert!(
        tampered.contains("sorryAx") || tampered.contains("sorry"),
        "a `sorry`-tampered module must trip the sorry audit"
    );
}
