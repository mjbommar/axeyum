//! Tests for the lexicographic-order clash → kernel-checked Lean reconstruction.
//!
//! Positive: each covered first-clash shape (`str.<=` first-char clash, second-char
//! clash, proper superstring, strict `<` of equal strings) reconstructs to a module
//! whose proof the kernel already checked to `False` (a successful return *is* the
//! kernel gate — [`LexCtx::gate_and_render`] `infer`s + `def_eq False`-compares
//! before rendering). Declines: transitivity/substitution and Boolean-fold shapes
//! are safely declined; a satisfiable problem is declined. Negative: deliberately
//! wrong reconstructions (a *true* atom, a corrupted clash direction) are rejected
//! by the kernel gate — never a bogus `False`. Property: ≥200 generated certified
//! refutations all reconstruct + kernel-check.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use super::*;

fn lit(s: &str) -> Vec<Seg> {
    s.chars().map(|c| Seg::Lit(c as u32)).collect()
}

fn var(name: &str) -> Seg {
    Seg::Var(name.to_owned())
}

/// Reconstruct through the public entry, asserting the module was kernel-checked.
fn reconstruct_ok(problem: &LexProblem) -> String {
    let src = reconstruct_lex_clash_to_lean_module(problem)
        .expect("lex refutation reconstructs + kernel-checks to False");
    assert!(src.contains("theorem"), "renders a Lean theorem module");
    assert!(
        src.contains(LEX_LEAN_THEOREM),
        "renders the lex refutation theorem"
    );
    assert!(!src.contains("sorry"), "no sorry escape hatch");
    src
}

/// A single-assertion problem asserting `atom` (forced true).
fn assert_atom(atom: LexAtom) -> LexProblem {
    LexProblem {
        atoms: vec![atom],
        assertions: vec![LexFormula::Atom(0)],
    }
}

// -------------------------------------------------------------------------
// Positive: the covered first-clash shapes reconstruct + kernel-check.
// -------------------------------------------------------------------------

#[test]
fn first_char_clash_le_reconstructs() {
    // "B"++x <= "A"++y : false (66 > 65 at pos 0), asserted true ⇒ unsat.
    let problem = assert_atom(LexAtom::Lex {
        left: vec![Seg::Lit('B' as u32), var("x")],
        right: vec![Seg::Lit('A' as u32), var("y")],
        strict: false,
    });
    reconstruct_ok(&problem);
}

#[test]
fn second_char_clash_le_reconstructs() {
    // "AD"++x <= "AC"++y : pos0 equal, pos1 68 > 67 ⇒ false; tails variable.
    let problem = assert_atom(LexAtom::Lex {
        left: vec![Seg::Lit('A' as u32), Seg::Lit('D' as u32), var("x")],
        right: vec![Seg::Lit('A' as u32), Seg::Lit('C' as u32), var("y")],
        strict: false,
    });
    reconstruct_ok(&problem);
}

#[test]
fn strict_first_char_clash_reconstructs() {
    // "B"++x < "A"++y : false; strict variant folds on the same charlt branch.
    let problem = assert_atom(LexAtom::Lex {
        left: vec![Seg::Lit('B' as u32), var("x")],
        right: vec![Seg::Lit('A' as u32), var("y")],
        strict: true,
    });
    reconstruct_ok(&problem);
}

#[test]
fn proper_superstring_le_reconstructs() {
    // "abc" <= "ab" : left is a proper superstring ⇒ false (fully determined).
    let problem = assert_atom(LexAtom::Lex {
        left: lit("abc"),
        right: lit("ab"),
        strict: false,
    });
    reconstruct_ok(&problem);
}

#[test]
fn strict_equal_strings_reconstructs() {
    // "ab" < "ab" : equal strings, strict ⇒ false.
    let problem = assert_atom(LexAtom::Lex {
        left: lit("ab"),
        right: lit("ab"),
        strict: true,
    });
    reconstruct_ok(&problem);
}

#[test]
fn forced_true_through_conjunction_reconstructs() {
    // (and (str.<= "A"++x "B"++y) (str.<= "AD"++u "AC"++v)) : the 2nd conjunct is
    // a forced-true false atom ⇒ the whole conjunction is unsat.
    let problem = LexProblem {
        atoms: vec![
            LexAtom::Lex {
                left: vec![Seg::Lit('A' as u32), var("x")],
                right: vec![Seg::Lit('B' as u32), var("y")],
                strict: false,
            },
            LexAtom::Lex {
                left: vec![Seg::Lit('A' as u32), Seg::Lit('D' as u32), var("u")],
                right: vec![Seg::Lit('A' as u32), Seg::Lit('C' as u32), var("v")],
                strict: false,
            },
        ],
        assertions: vec![LexFormula::And(vec![
            LexFormula::Atom(0),
            LexFormula::Atom(1),
        ])],
    };
    reconstruct_ok(&problem);
}

#[test]
fn forced_true_through_double_negation_reconstructs() {
    // (not (not (str.<= "AD"++x "AC"++y))) forces the false atom true ⇒ unsat.
    // Exercises the polarity fold in `collect_forced_true`.
    let problem = LexProblem {
        atoms: vec![LexAtom::Lex {
            left: vec![Seg::Lit('A' as u32), Seg::Lit('D' as u32), var("x")],
            right: vec![Seg::Lit('A' as u32), Seg::Lit('C' as u32), var("y")],
            strict: false,
        }],
        // ¬¬atom0 forces atom0 true.
        assertions: vec![LexFormula::Not(Box::new(LexFormula::Not(Box::new(
            LexFormula::Atom(0),
        ))))],
    };
    reconstruct_ok(&problem);
}

// -------------------------------------------------------------------------
// Declines (safe unknown, never a wrong verdict).
// -------------------------------------------------------------------------

#[test]
fn satisfiable_atom_is_declined() {
    // "A"++x <= "B"++y : always TRUE ⇒ not unsat ⇒ refute_lex declines ⇒ Err.
    let problem = assert_atom(LexAtom::Lex {
        left: vec![Seg::Lit('A' as u32), var("x")],
        right: vec![Seg::Lit('B' as u32), var("y")],
        strict: false,
    });
    assert!(
        reconstruct_lex_clash_to_lean_module(&problem).is_err(),
        "a satisfiable lex atom must be declined, not refuted"
    );
}

#[test]
fn leading_variable_atom_is_declined() {
    // x ++ "A" <= "B" : leading variable blocks constant evaluation ⇒ unknown.
    let problem = assert_atom(LexAtom::Lex {
        left: vec![var("x"), Seg::Lit('A' as u32)],
        right: lit("B"),
        strict: false,
    });
    assert!(reconstruct_lex_clash_to_lean_module(&problem).is_err());
}

#[test]
fn transitivity_chain_is_declined() {
    // x<=y ∧ y<=w ∧ x = "G"++xp ∧ w = "E" : refute_lex certifies (Arm B), but this
    // slice defers the transitivity/substitution shape ⇒ Err (safe unknown).
    let problem = LexProblem {
        atoms: vec![
            LexAtom::Lex {
                left: vec![var("x")],
                right: vec![var("y")],
                strict: false,
            },
            LexAtom::Lex {
                left: vec![var("y")],
                right: vec![var("w")],
                strict: false,
            },
            LexAtom::Eq {
                left: vec![var("x")],
                right: vec![Seg::Lit('G' as u32), var("xp")],
            },
            LexAtom::Eq {
                left: vec![var("w")],
                right: lit("E"),
            },
        ],
        assertions: vec![
            LexFormula::Atom(0),
            LexFormula::Atom(1),
            LexFormula::Atom(2),
            LexFormula::Atom(3),
        ],
    };
    // Sanity: the checker DOES certify this unsat…
    assert_eq!(refute_lex(&problem), LexOutcome::Unsat);
    // …but our first-clash slice declines it (no forced-true first-clash atom).
    assert!(reconstruct_lex_clash_to_lean_module(&problem).is_err());
}

// -------------------------------------------------------------------------
// Negative: corrupted reconstructions are rejected by the kernel gate.
// -------------------------------------------------------------------------

#[test]
fn corrupted_true_atom_rejected_by_kernel() {
    // Directly drive the low-level builder on a TRUE atom ("A" <= "B"): lex ↝ true,
    // so `h : Eq Bool true true` cannot close to False — the kernel gate rejects it.
    let err = build_clash_module(&lit("A"), &lit("B"), false)
        .expect_err("a true atom must not reconstruct to False");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "expected a kernel rejection, got {err:?}"
    );
}

#[test]
fn corrupted_clash_direction_rejected_by_kernel() {
    // Mis-stated clash: claim "AC" <= "AD" is false (it is TRUE, 67 < 68 at pos 1).
    // lex ↝ true, so the discriminator proof does not infer to False ⇒ rejected.
    let err = build_clash_module(&lit("AC"), &lit("AD"), false)
        .expect_err("a wrong clash direction must be rejected");
    assert!(
        matches!(err, ReconstructError::KernelRejected { .. }),
        "expected a kernel rejection, got {err:?}"
    );
}

#[test]
fn corrupted_strict_prefix_rejected_by_kernel() {
    // "ab" < "abc" is TRUE (proper prefix). Driving the strict builder on it yields
    // lex ↝ true, rejected by the kernel gate.
    let err = build_clash_module(&lit("ab"), &lit("abc"), true)
        .expect_err("a true proper-prefix strict atom must be rejected");
    assert!(matches!(err, ReconstructError::KernelRejected { .. }));
}

// -------------------------------------------------------------------------
// Property: certified first-clash refutations all reconstruct + kernel-check.
// -------------------------------------------------------------------------

/// A deterministic LCG (MMIX constants) for reproducible property generation.
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next() % n).expect("fits")
    }
}

#[test]
fn property_certified_first_clashes_reconstruct() {
    // Generate first-character-clash atoms: an equal determined prefix, then a
    // strictly-decreasing determined pair (left > right), then optional variable or
    // literal tails. Every such atom is variable-independently false, so asserting
    // it true is a genuine unsat this slice must reconstruct + kernel-check.
    let alpha = [
        u32::from(b'a'),
        u32::from(b'b'),
        u32::from(b'c'),
        u32::from(b'd'),
    ];
    let mut checked = 0u64;
    for seed in 0..260u64 {
        let mut rng = Lcg::new(seed);

        // Shared equal prefix (0..=2 determined equal code points).
        let prefix_len = rng.below(3);
        let mut left: Vec<Seg> = Vec::new();
        let mut right: Vec<Seg> = Vec::new();
        for _ in 0..prefix_len {
            let c = alpha[rng.below(alpha.len() as u64)];
            left.push(Seg::Lit(c));
            right.push(Seg::Lit(c));
        }
        // The clash pair: left code strictly greater than right code.
        let hi = 1 + rng.below(alpha.len() as u64 - 1); // 1..=len-1
        let lo = rng.below(hi as u64); // 0..hi
        left.push(Seg::Lit(alpha[hi]));
        right.push(Seg::Lit(alpha[lo]));
        // Optional tails (literal and/or variable) past the clash.
        match rng.below(4) {
            0 => {}
            1 => left.push(var("x")),
            2 => {
                left.push(Seg::Lit(alpha[rng.below(alpha.len() as u64)]));
                right.push(var("y"));
            }
            _ => {
                left.push(var("x"));
                right.push(Seg::Lit(alpha[rng.below(alpha.len() as u64)]));
            }
        }
        let strict = rng.below(2) == 0;

        // Ground truth: this atom is variable-independently false.
        assert_eq!(
            eval_lex_const(&left, &right, strict),
            Some(false),
            "generated atom must be a certified clash (seed {seed})"
        );
        let problem = assert_atom(LexAtom::Lex {
            left,
            right,
            strict,
        });
        assert_eq!(
            refute_lex(&problem),
            LexOutcome::Unsat,
            "checker must certify the generated clash (seed {seed})"
        );
        // The kernel gate fires inside: a successful return is a checked `False`.
        reconstruct_ok(&problem);
        checked += 1;
    }
    assert!(
        checked >= 200,
        "property must exercise ≥200 clashes ({checked})"
    );
}
