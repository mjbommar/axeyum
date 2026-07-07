//! **Constant-time / 2-safety by self-composition** (Track 5, P5.3 / T5.3.1).
//!
//! Constant-time is a *hyperproperty*: it relates two runs that agree on the
//! public inputs but differ on the secret. Reflecting one function twice over a
//! shared public symbol and two distinct secret symbols, and comparing the
//! branch decisions each run leaks, decides whether control flow is
//! secret-independent — with a certificate on the safe side and a concrete
//! distinguishing witness on the leaky side.
//!
//! Proved here:
//! - a **public-predicated** function (`if pub > 100 { secret } else { 0 }`) is
//!   control-flow constant-time even though its *output* depends on the secret —
//!   the distinction constant-time is actually about;
//! - a **secret-predicated** function (`if secret > 100 { 1 } else { 0 }`) is
//!   **refuted**, and the countermodel's two secret values are shown to steer
//!   control flow apart (the branch scrutinee really differs);
//! - a **branch-free** function is trivially constant-time.
//!
//! Fixtures are committed debug-MIR text; not invoked at test time.

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use axeyum_verify::reflect::hyper::control_flow_ct_goal;
use axeyum_verify::reflect::mir::{MirParam, reflect_mir_params_with_leaks};

// `_1` is the public input, `_2` the secret. Branch is on the PUBLIC input, so
// control flow is constant-time; the returned value is the secret when taken.
const PUBLIC_PREDICATED_MIR: &str = r"
fn ct(_1: u32, _2: u32) -> u32 {
    debug pub => _1;
    debug secret => _2;
    let mut _0: u32;
    let mut _3: bool;

    bb0: {
        _3 = Gt(copy _1, const 100_u32);
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = copy _2;
        goto -> bb3;
    }

    bb2: {
        _0 = const 0_u32;
        goto -> bb3;
    }

    bb3: {
        return;
    }
}
";

// Branch is on the SECRET input — a secret-dependent branch (leaky).
const SECRET_PREDICATED_MIR: &str = r"
fn leaky(_1: u32, _2: u32) -> u32 {
    debug pub => _1;
    debug secret => _2;
    let mut _0: u32;
    let mut _3: bool;

    bb0: {
        _3 = Gt(copy _2, const 100_u32);
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 1_u32;
        goto -> bb3;
    }

    bb2: {
        _0 = const 0_u32;
        goto -> bb3;
    }

    bb3: {
        return;
    }
}
";

// No branches at all: `(pub & 0xff) ^ secret` — trivially constant-time.
const BRANCH_FREE_MIR: &str = r"
fn mix(_1: u32, _2: u32) -> u32 {
    debug pub => _1;
    debug secret => _2;
    let mut _0: u32;
    let mut _3: u32;

    bb0: {
        _3 = BitAnd(copy _1, const 255_u32);
        _0 = BitXor(move _3, copy _2);
        return;
    }
}
";

/// Declare `(public, secret_a, secret_b)` — the shared public symbol and the two
/// distinct secret symbols the self-composition runs over.
fn syms(arena: &mut TermArena) -> (SymbolId, SymbolId, SymbolId) {
    let p = arena.declare("pub", Sort::BitVec(32)).unwrap();
    let sa = arena.declare("secret_a", Sort::BitVec(32)).unwrap();
    let sb = arena.declare("secret_b", Sort::BitVec(32)).unwrap();
    (p, sa, sb)
}

fn scalar(term: TermId) -> MirParam {
    MirParam::Scalar(term, 32, false)
}

/// The public-predicated function is control-flow constant-time: its branch
/// scrutinee depends only on the public input, so both runs leak the same
/// decision for every secret pair — proved.
#[test]
fn public_predicated_is_constant_time() {
    let mut arena = TermArena::new();
    let (p, sa, sb) = syms(&mut arena);
    let (pt, sat, sbt) = (arena.var(p), arena.var(sa), arena.var(sb));
    let run_a = [scalar(pt), scalar(sat)];
    let run_b = [scalar(pt), scalar(sbt)];
    let goal = control_flow_ct_goal(&mut arena, &run_a, &run_b, PUBLIC_PREDICATED_MIR);
    let outcome = prove(&mut arena, &[], goal, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "public-predicated branch must be constant-time, got {outcome:?}"
    );
}

/// Even though the public-predicated function is constant-time, its **output**
/// is not secret-independent: `ct(pub, s_a) != ct(pub, s_b)` is satisfiable
/// (when `pub > 100` the result is the secret). This pins the distinction
/// constant-time is really about — control flow, not the value.
#[test]
fn public_predicated_output_still_leaks_the_secret() {
    let mut arena = TermArena::new();
    let (p, sa, sb) = syms(&mut arena);
    let (pt, sat, sbt) = (arena.var(p), arena.var(sa), arena.var(sb));
    let (out_a, _, _) = reflect_mir_params_with_leaks(
        &mut arena,
        &[scalar(pt), scalar(sat)],
        PUBLIC_PREDICATED_MIR,
    );
    let (out_b, _, _) = reflect_mir_params_with_leaks(
        &mut arena,
        &[scalar(pt), scalar(sbt)],
        PUBLIC_PREDICATED_MIR,
    );
    let outputs_equal = arena.eq(out_a, out_b).unwrap();
    let outcome = prove(&mut arena, &[], outputs_equal, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Disproved(_)),
        "the output DOES depend on the secret; equality must be refuted, got {outcome:?}"
    );
}

/// The secret-predicated function is **not** constant-time: the branch scrutinee
/// depends on the secret, so the leaked decisions can differ. The countermodel's
/// two secret values are shown to actually steer control flow apart.
#[test]
fn secret_predicated_is_refuted_with_a_distinguishing_witness() {
    let mut arena = TermArena::new();
    let (p, sa, sb) = syms(&mut arena);
    let (pt, sat, sbt) = (arena.var(p), arena.var(sa), arena.var(sb));
    let run_a = [scalar(pt), scalar(sat)];
    let run_b = [scalar(pt), scalar(sbt)];
    let goal = control_flow_ct_goal(&mut arena, &run_a, &run_b, SECRET_PREDICATED_MIR);
    let outcome = prove(&mut arena, &[], goal, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("secret-predicated branch must be refuted as leaky, got {outcome:?}");
    };
    // Replay-check: the two witnessed secrets really land on opposite sides of
    // the `> 100` branch (one leaks, the other doesn't).
    let secret = |sym| match model.get(sym) {
        Some(Value::Bv { value, .. }) => u32::try_from(value).unwrap(),
        other => panic!("no secret value in countermodel: {other:?}"),
    };
    let (va, vb) = (secret(sa), secret(sb));
    assert_ne!(
        va > 100,
        vb > 100,
        "the witness secrets {va} and {vb} must take different branches"
    );
}

/// A branch-free function leaks nothing: constant-time holds trivially (the
/// goal is a vacuous conjunction, proved).
#[test]
fn branch_free_is_constant_time() {
    let mut arena = TermArena::new();
    let (p, sa, sb) = syms(&mut arena);
    let (pt, sat, sbt) = (arena.var(p), arena.var(sa), arena.var(sb));
    let (_, _, leaks) =
        reflect_mir_params_with_leaks(&mut arena, &[scalar(pt), scalar(sat)], BRANCH_FREE_MIR);
    assert!(leaks.is_empty(), "a branch-free function must leak nothing");
    let goal = control_flow_ct_goal(
        &mut arena,
        &[scalar(pt), scalar(sat)],
        &[scalar(pt), scalar(sbt)],
        BRANCH_FREE_MIR,
    );
    let outcome = prove(&mut arena, &[], goal, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "branch-free function is trivially constant-time, got {outcome:?}"
    );
}
