//! Deeply nested input must never abort the process.
//!
//! A stack overflow is strictly worse than a timeout: it is an abort, so the
//! solver cannot report a first-class `unknown` (a hard rule) and a harness
//! reads the exit as a crash. Nine scored `QF_BV/sage/app7` parity benchmarks
//! once died exactly this way, in a natively recursive `to_real` fold that ran
//! on every query (`fcc8760d`) — they were never hard, they were unreachable.
//!
//! Every shape below drives a **public** front door (`check_auto`, or the
//! SMT-LIB text entry `solve_smtlib`) with input whose *nesting depth* is far
//! past what a recursive frame survives on the harness's thread stack. The
//! assertions are deliberately weak — the point is that the call **returns**,
//! whatever it returns; a regression aborts the test binary instead of failing.
//!
//! Nesting this deep is not adversarial: an SMT-LIB source controls it directly,
//! since `(and (and (and …)))`, `(bvadd (bvadd …))` and `(store (store …))`
//! spines are what symbolic-execution and bounded-model-checking front ends
//! emit.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{ArraySortKey, Rational, Sort, TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{SolverConfig, check_auto, solve_smtlib};

/// Deep enough that any native recursion over the term spine overflows.
const TERM_DEPTH: usize = 100_000;
/// Same, for shapes fed as SMT-LIB *text* (the source string is materialized,
/// so this trades depth for a test that stays under a second).
const TEXT_DEPTH: usize = 20_000;
/// Conjunction spines are the one shape whose *downstream* cost grows steeply
/// with the conjunct count, so the shape that runs the full pipeline over them
/// uses a smaller — still far past any stack — depth to keep the suite fast.
const CONJUNCTION_DEPTH: usize = 8_000;

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_millis(200)),
        ..SolverConfig::default()
    }
}

/// Drives `assertion` through the term-level front door; the result is
/// irrelevant, returning at all is the point.
fn returns_from_check_auto(arena: &mut TermArena, assertion: TermId) {
    let _ = check_auto(arena, &[assertion], &config());
}

/// Drives `text` through the SMT-LIB text front door.
fn returns_from_solve_smtlib(text: &str) {
    let _ = solve_smtlib(text, &config());
}

// ---------------------------------------------------------------------------
// Term-level front door
// ---------------------------------------------------------------------------

/// A left-associated `bvadd` spine — the `sage/app7` shape of `fcc8760d`.
#[test]
fn deep_bv_add_spine_returns() {
    let mut arena = TermArena::new();
    let x = arena.declare("dx", Sort::BitVec(8)).unwrap();
    let mut acc = arena.var(x);
    let one = arena.bv_const(8, 1).unwrap();
    for _ in 0..TERM_DEPTH {
        acc = arena.bv_add(acc, one).unwrap();
    }
    let zero = arena.bv_const(8, 0).unwrap();
    let goal = arena.eq(acc, zero).unwrap();
    returns_from_check_auto(&mut arena, goal);
}

/// A left-associated integer `+` spine (the LIA/NIA routes).
#[test]
fn deep_int_add_spine_returns() {
    let mut arena = TermArena::new();
    let n = arena.declare("dn", Sort::Int).unwrap();
    let mut acc = arena.var(n);
    let one = arena.int_const(1);
    for _ in 0..TERM_DEPTH {
        acc = arena.int_add(acc, one).unwrap();
    }
    let zero = arena.int_const(0);
    let goal = arena.int_le(acc, zero).unwrap();
    returns_from_check_auto(&mut arena, goal);
}

/// A left-associated real `+` spine (the LRA route and the rewrite passes it
/// shares with every other logic).
#[test]
fn deep_real_add_spine_returns() {
    let mut arena = TermArena::new();
    let r = arena.declare("dr", Sort::Real).unwrap();
    let mut acc = arena.var(r);
    let one = arena.real_const(Rational::integer(1));
    for _ in 0..TERM_DEPTH {
        acc = arena.real_add(acc, one).unwrap();
    }
    let zero = arena.real_const(Rational::zero());
    let goal = arena.real_le(acc, zero).unwrap();
    returns_from_check_auto(&mut arena, goal);
}

/// A `store` chain, which the EUF bridge interns node by node.
#[test]
fn deep_store_chain_returns() {
    let mut arena = TermArena::new();
    let a = arena
        .declare(
            "darr",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mut acc = arena.var(a);
    let one = arena.bv_const(8, 1).unwrap();
    for i in 0..TERM_DEPTH {
        let idx = arena.bv_const(8, (i % 251) as u128).unwrap();
        acc = arena.store(acc, idx, one).unwrap();
    }
    let zero = arena.bv_const(8, 0).unwrap();
    let read = arena.select(acc, zero).unwrap();
    let goal = arena.eq(read, zero).unwrap();
    returns_from_check_auto(&mut arena, goal);
}

/// A `not` spine.
#[test]
fn deep_not_spine_returns() {
    let mut arena = TermArena::new();
    let p = arena.declare("dp", Sort::Bool).unwrap();
    let mut acc = arena.var(p);
    for _ in 0..TERM_DEPTH {
        acc = arena.not(acc).unwrap();
    }
    returns_from_check_auto(&mut arena, acc);
}

/// An `ite` spine.
#[test]
fn deep_ite_spine_returns() {
    let mut arena = TermArena::new();
    let c = arena.declare("dc", Sort::Bool).unwrap();
    let cv = arena.var(c);
    let mut acc = arena.bv_const(8, 1).unwrap();
    for i in 0..TERM_DEPTH {
        let k = arena.bv_const(8, (i % 251) as u128).unwrap();
        acc = arena.ite(cv, acc, k).unwrap();
    }
    let zero = arena.bv_const(8, 0).unwrap();
    let goal = arena.eq(acc, zero).unwrap();
    returns_from_check_auto(&mut arena, goal);
}

/// A left-associated `and` spine, the shape every conjunction flattener walks.
#[test]
fn deep_and_spine_returns() {
    let mut arena = TermArena::new();
    let x = arena.declare("dax", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let k = arena.bv_const(8, 7).unwrap();
    let leaf = arena.bv_ule(xv, k).unwrap();
    let mut acc = leaf;
    for _ in 0..CONJUNCTION_DEPTH {
        acc = arena.and(acc, leaf).unwrap();
    }
    returns_from_check_auto(&mut arena, acc);
}

// ---------------------------------------------------------------------------
// SMT-LIB text front door
// ---------------------------------------------------------------------------

/// `(bvadd (bvadd … ) …)` written out as source: the whole-script scans, the
/// parser, and the s-expression tree's own destructor all see the depth.
#[test]
fn deep_bvadd_source_returns() {
    let mut body = String::from("x");
    for i in 0..TEXT_DEPTH {
        body = format!("(bvadd {body} (_ bv{} 8))", i % 251);
    }
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= {body} (_ bv0 8)))\n(check-sat)\n"
    ));
}

/// `(not (not … ))` as source. Before `SExpr`'s iterative destructor this
/// aborted *after* the query had already been decided.
#[test]
fn deep_not_source_returns() {
    let body = format!("{}p{}", "(not ".repeat(TEXT_DEPTH), ")".repeat(TEXT_DEPTH));
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert {body})\n(check-sat)\n"
    ));
}

/// A `let` chain, which the parser threads scope by scope.
#[test]
fn deep_let_source_returns() {
    let mut opens = String::new();
    for i in 1..TEXT_DEPTH {
        opens.push_str(&format!("(let ((v{i} (bvadd v{} (_ bv1 8)))) ", i - 1));
    }
    let text = format!(
        "(set-logic QF_BV)\n(declare-const v0 (_ BitVec 8))\n(assert (= {opens}v{}{} (_ bv0 8)))\n(check-sat)\n",
        TEXT_DEPTH - 1,
        ")".repeat(TEXT_DEPTH - 1)
    );
    returns_from_solve_smtlib(&text);
}

/// A `store` chain as source (the QF_ABV route).
#[test]
fn deep_store_source_returns() {
    let mut body = String::from("a");
    for i in 0..TEXT_DEPTH {
        body = format!("(store {body} (_ bv{} 8) (_ bv1 8))", i % 251);
    }
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_ABV)\n(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\n(assert (= (select {body} (_ bv0 8)) (_ bv0 8)))\n(check-sat)\n"
    ));
}

/// A `str.++` chain as source (the string route).
#[test]
fn deep_str_concat_source_returns() {
    let mut body = String::from("s");
    for i in 0..TEXT_DEPTH {
        body = format!("(str.++ {body} \"{}\")", i % 10);
    }
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_S)\n(declare-const s String)\n(assert (= {body} \"\"))\n(check-sat)\n"
    ));
}

/// A `re.++` chain as source. The regex front end declines past its nesting cap
/// rather than recursing into an abort.
#[test]
fn deep_regex_source_returns() {
    let mut re = String::from("(str.to_re \"a\")");
    for _ in 0..TEXT_DEPTH {
        re = format!("(re.++ {re} (str.to_re \"b\"))");
    }
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_S)\n(declare-const s String)\n(assert (str.in_re s {re}))\n(check-sat)\n"
    ));
}

/// An `(and (and …))` spine as source.
///
/// This one stops at the parser rather than running the whole pipeline: the
/// front door's whole-script scans, and the s-expression tree's own destructor,
/// are what the depth exercises, and deciding tens of thousands of conjuncts
/// costs seconds that add nothing to the gate.
#[test]
fn deep_and_source_parses() {
    let mut body = String::from("true");
    for i in 0..TEXT_DEPTH {
        body = format!("(and {body} p{})", i % 8);
    }
    let decls: String = (0..8)
        .map(|i| format!("(declare-const p{i} Bool)\n"))
        .collect();
    let text = format!("(set-logic QF_UF)\n{decls}(assert {body})\n(check-sat)\n");
    let script = parse_script(&text).expect("a deep conjunction still parses");
    assert_eq!(script.assertions.len(), 1);
    // Dropping the parsed script is itself part of what this gates.
    drop(script);
}

/// An integer `+` spine as source (the LIA route's polynomial collectors).
#[test]
fn deep_int_add_source_returns() {
    let mut body = String::from("n");
    for i in 0..TEXT_DEPTH {
        body = format!("(+ {body} {})", i % 7);
    }
    returns_from_solve_smtlib(&format!(
        "(set-logic QF_LIA)\n(declare-const n Int)\n(assert (<= {body} 0))\n(check-sat)\n"
    ));
}
