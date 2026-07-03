//! Round-trip + tamper tests for the word-conflict Alethe emitter.
//!
//! Round-trip: a certificate for each certified conflict shape (constant clash,
//! chained/augmented clash, self-loop, contradicted disequality) self-checks and
//! derives the empty clause. Tamper: mutating the proof (clause, premise, constant,
//! rule, or the closing step) must make the self-check reject — never a bogus
//! `Ok(true)`.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId};

use super::{WordAletheError, WordClashCertificate, word_conflict_alethe};

const ELEM: ArraySortKey = ArraySortKey::BitVec(8);

fn seq_var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Seq(ELEM)).expect("seq var");
    arena.var(s)
}

/// A one-character constant sequence `"c"`.
fn ch(arena: &mut TermArena, c: u8) -> TermId {
    let e = arena.bv_const(8, u128::from(c)).expect("char");
    arena.seq_unit(e).expect("unit")
}

fn cat(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
    arena.seq_concat(a, b).expect("concat")
}

/// Assert a certificate self-checks and its last command derives `(cl)`.
fn assert_valid(cert: &WordClashCertificate) {
    assert!(cert.check(), "emitted certificate must self-check");
    match cert.commands.last().expect("non-empty proof") {
        AletheCommand::Step { clause, rule, .. } => {
            assert!(clause.is_empty(), "final step must derive the empty clause");
            assert_eq!(rule, "resolution");
        }
        AletheCommand::Assume { .. } => panic!("final command must be a step"),
    }
    // The clash rule appears exactly once, as the theory tautology step.
    let clashes = cert
        .commands
        .iter()
        .filter(|c| matches!(c, AletheCommand::Step { rule, .. } if rule == super::WORD_CLASH_RULE))
        .count();
    assert_eq!(clashes, 1, "exactly one clash step");
}

/// A certificate with `commands` replaced (same `elem`), for tamper checks.
fn with_commands(
    cert: &WordClashCertificate,
    commands: Vec<AletheCommand>,
) -> WordClashCertificate {
    WordClashCertificate {
        commands,
        premises: cert.premises.clone(),
        disequality_driven: cert.disequality_driven,
        elem: cert.elem,
    }
}

// ----- round-trip over the certified shapes ----------------------------------

#[test]
fn constant_clash_direct() {
    // x = "a" ∧ x = "b": one variable forced to two distinct constants.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let cert = word_conflict_alethe(&mut arena, &[(x, a), (x, b)], &[]).expect("emits");
    assert_valid(&cert);
    assert!(!cert.disequality_driven);
}

#[test]
fn constant_clash_chained() {
    // x = "a" ∧ x = y ∧ y = "b": the clash closes through the derived x ≈ y.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    let cert = word_conflict_alethe(&mut arena, &[(x, a), (x, y), (y, b)], &[]).expect("emits");
    assert_valid(&cert);
    assert!(!cert.disequality_driven);
}

#[test]
fn self_loop_prefix_constant() {
    // x = "a" ++ x: a cycle forcing a nonempty constant to ε.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let a = ch(&mut arena, b'a');
    let rhs = cat(&mut arena, a, x);
    let cert = word_conflict_alethe(&mut arena, &[(x, rhs)], &[]).expect("emits");
    assert_valid(&cert);
    assert!(!cert.disequality_driven);
}

#[test]
fn augmented_constant_clash() {
    // x = y ++ x ∧ y = "a": the cycle forces y ≈ ε, clashing with y ≈ "a".
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let yx = cat(&mut arena, y, x);
    let cert = word_conflict_alethe(&mut arena, &[(x, yx), (y, a)], &[]).expect("emits");
    assert_valid(&cert);
}

#[test]
fn contradicted_disequality_chain() {
    // x = y ∧ y = z ∧ x ≠ z: transitivity contradicts the disequality.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let z = seq_var(&mut arena, "z");
    let cert = word_conflict_alethe(&mut arena, &[(x, y), (y, z)], &[(x, z)]).expect("emits");
    assert_valid(&cert);
    assert!(cert.disequality_driven);
    // A disequality assume is present.
    assert!(cert.commands.iter().any(|c| matches!(
        c,
        AletheCommand::Assume { clause, .. } if clause.iter().any(|l| l.negated)
    )));
}

#[test]
fn satisfiable_is_not_refuted() {
    // x = "a" ∧ y = "b": no contradiction.
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    assert!(matches!(
        word_conflict_alethe(&mut arena, &[(x, a), (y, b)], &[]),
        Err(WordAletheError::NotRefuted)
    ));
}

// ----- tamper modes (each must make the self-check reject) --------------------

/// A fresh valid certificate to mutate (the chained clash, which has several
/// premises and a nonempty clash clause).
fn sample() -> WordClashCertificate {
    let mut arena = TermArena::new();
    let x = seq_var(&mut arena, "x");
    let y = seq_var(&mut arena, "y");
    let a = ch(&mut arena, b'a');
    let b = ch(&mut arena, b'b');
    word_conflict_alethe(&mut arena, &[(x, a), (x, y), (y, b)], &[]).expect("emits")
}

/// The index of the clash `Step` in the command list.
fn clash_index(cmds: &[AletheCommand]) -> usize {
    cmds.iter()
        .position(
            |c| matches!(c, AletheCommand::Step { rule, .. } if rule == super::WORD_CLASH_RULE),
        )
        .expect("clash step present")
}

#[test]
fn tamper_flip_clash_literal_negation() {
    // Flip a clash literal's polarity: it no longer negates its assume, so the
    // rebuilt system changes and the resolution can no longer close.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    let ci = clash_index(&cmds);
    if let AletheCommand::Step { clause, .. } = &mut cmds[ci] {
        clause[0].negated = !clause[0].negated;
    }
    assert!(
        !with_commands(&cert, cmds).check(),
        "flipped literal accepted"
    );
}

#[test]
fn tamper_rename_assume_variable() {
    // Rename a variable inside an assume atom: it no longer matches the clash
    // literal, so the empty clause is not derivable.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    for c in &mut cmds {
        if let AletheCommand::Assume { clause, .. } = c {
            rename_first_const(&mut clause[0].atom);
        }
    }
    assert!(
        !with_commands(&cert, cmds).check(),
        "renamed assume accepted"
    );
}

#[test]
fn tamper_drop_clash_literal() {
    // Drop a clash literal: the rebuilt system loses a premise and (with the
    // corresponding assume still present) resolution cannot close.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    let ci = clash_index(&cmds);
    if let AletheCommand::Step { clause, .. } = &mut cmds[ci] {
        clause.pop();
    }
    assert!(
        !with_commands(&cert, cmds).check(),
        "dropped literal accepted"
    );
}

#[test]
fn tamper_rename_rule() {
    // Rename the clash rule: the callback returns None → UnsupportedRule.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    let ci = clash_index(&cmds);
    if let AletheCommand::Step { rule, .. } = &mut cmds[ci] {
        *rule = "not_a_real_rule".to_owned();
    }
    assert!(!with_commands(&cert, cmds).check(), "renamed rule accepted");
}

#[test]
fn tamper_corrupt_constant() {
    // Corrupt a character literal in the clash clause so the constant clash
    // disappears (both constants become "a"): the rebuilt system is satisfiable,
    // so the clash callback returns Some(false).
    let cert = sample();
    let mut cmds = cert.commands.clone();
    let ci = clash_index(&cmds);
    if let AletheCommand::Step { clause, .. } = &mut cmds[ci] {
        for lit in clause.iter_mut() {
            set_all_chars_to_a(&mut lit.atom);
        }
    }
    // Also rewrite the assumes to match, so the failure is the clash callback (a
    // satisfiable rebuilt system) rather than a resolution mismatch.
    for c in &mut cmds {
        if let AletheCommand::Assume { clause, .. } = c {
            set_all_chars_to_a(&mut clause[0].atom);
        }
    }
    assert!(
        !with_commands(&cert, cmds).check(),
        "corrupted-constant (satisfiable) system accepted"
    );
}

#[test]
fn tamper_add_spurious_clash_literal() {
    // Add an extra clash literal with no matching assume: resolution cannot
    // cancel it, so the empty clause is not derivable.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    let ci = clash_index(&cmds);
    if let AletheCommand::Step { clause, .. } = &mut cmds[ci] {
        clause.push(AletheLit {
            atom: AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("ghost".to_owned()),
                    AletheTerm::Const("phantom".to_owned()),
                ],
            ),
            negated: true,
        });
    }
    assert!(
        !with_commands(&cert, cmds).check(),
        "spurious extra literal accepted"
    );
}

#[test]
fn tamper_drop_final_resolution() {
    // Remove the closing resolution step: the empty clause is never derived.
    let cert = sample();
    let mut cmds = cert.commands.clone();
    cmds.pop();
    assert!(
        !with_commands(&cert, cmds).check(),
        "proof without the empty clause accepted"
    );
}

// ----- small AletheTerm mutators (test-local) --------------------------------

/// Rename the first `Const` symbol encountered (depth-first) by appending `!`.
fn rename_first_const(term: &mut AletheTerm) -> bool {
    match term {
        AletheTerm::Const(name) => {
            name.push('!');
            true
        }
        AletheTerm::App(head, args) => {
            // Do not rename the `char` width/value numerals — only real names.
            if head == "char" {
                return false;
            }
            args.iter_mut().any(rename_first_const)
        }
        AletheTerm::Indexed { .. } => false,
    }
}

/// Force every `char` literal's value to `'a'` (97), collapsing constant clashes.
fn set_all_chars_to_a(term: &mut AletheTerm) {
    match term {
        AletheTerm::App(head, args) if head == "char" && args.len() == 2 => {
            args[1] = AletheTerm::Const(u128::from(b'a').to_string());
        }
        AletheTerm::App(_, args) | AletheTerm::Indexed { args, .. } => {
            for a in args.iter_mut() {
                set_all_chars_to_a(a);
            }
        }
        AletheTerm::Const(_) => {}
    }
}
