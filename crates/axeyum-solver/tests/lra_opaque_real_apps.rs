//! Soundness-negative suite for the opaque-real-subterm abstraction (ADR-2065).
//!
//! The abstraction is a **relaxation**: a real-sorted uninterpreted application
//! or array read becomes a fresh, otherwise-unconstrained column. So
//!
//! > abstraction unsat  ⟹  original unsat
//!
//! and **nothing** in the other direction. Every test here is built around that
//! asymmetry, and the suite is organised so that each guard has a test that dies
//! when that guard alone is deleted — the mutation matrix is in
//! `bench-results/real-opaque-20260914/ref/guard-deletion.md`.
//!
//! # The shape of each pair
//!
//! Six witnesses, one per `AUFLIRA` row ADR-2050 measured, reduced to the shape
//! of that row's minimal unsat core (median ONE conjunct; four of six are
//! propositional, two add one arithmetic step). **Beside each is a non-vacuity
//! control**: the same query with the contradiction removed. A witness that
//! says `unsat` proves nothing on its own — a parser bug that dropped
//! assertions makes everything `unsat` and every witness "passes". The control
//! is what makes the witness's `unsat` mean something, and it must NOT be
//! `unsat`.
//!
//! # And the direction that would be a wrong verdict
//!
//! `abstraction_sat_must_never_become_sat` and its siblings are the real
//! subject: queries whose ABSTRACTION is satisfiable and whose ORIGINAL is
//! `unsat` (congruence, the array axioms). A `sat` on any of those is a wrong
//! verdict shipped. They assert `!= Sat`, not `== Unsat`, because deciding them
//! is not this rung's job — refusing to guess is.

#![cfg(feature = "full")]

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_arith_dpll};

/// Runs the query through the same front door a benchmark takes, with the
/// abstraction in its SHIPPED state (the kill switch is not touched, so this is
/// what a user gets).
fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    let config = SolverConfig::default();
    check_with_arith_dpll(arena, assertions, &config)
        .expect("the lazy linear-arithmetic route decides or declines, never errors")
}

/// A declared real function of one real argument — in `AUFLIRA` this is exactly
/// what `log` and `divide` are: **declared**, not theory symbols, so plain
/// opaque reals. The whole point of the change is that an application of one is
/// a perfectly good *leaf* of a linear constraint.
fn real_fn1(arena: &mut TermArena, name: &str, arg: TermId) -> TermId {
    let f = arena
        .declare_fun(name, &[Sort::Real], Sort::Real)
        .expect("declare a real unary function");
    arena.apply(f, &[arg]).expect("apply it")
}

fn real_fn2(arena: &mut TermArena, name: &str, a: TermId, b: TermId) -> TermId {
    let f = arena
        .declare_fun(name, &[Sort::Real, Sort::Real], Sort::Real)
        .expect("declare a real binary function");
    arena.apply(f, &[a, b]).expect("apply it")
}

/// `(select a i)` of real element sort, over an `Int`-indexed array — the third
/// refused shape ADR-2050 measured (`(declare-fun s_values7 () (Array Int Real))`).
fn real_select(arena: &mut TermArena, array_name: &str, index: i128) -> TermId {
    let a = arena
        .array_var_with_sorts(array_name, Sort::Int, Sort::Real)
        .expect("an Int-indexed array of reals");
    let i = arena.int_const(index);
    arena.select(a, i).expect("select")
}

fn r(arena: &mut TermArena, value: i128) -> TermId {
    arena.real_const(Rational::integer(value))
}

/// Requires that the decline came from the opaque-real `sat` gate specifically,
/// **by name**, not merely that the result was not `sat`.
///
/// This is the difference between a test of the VERDICT and a test of the
/// GUARD, and it is the whole reason this helper exists. Every closure on this
/// path produces a non-`sat`, so a bare `!matches!(.., Sat)` assertion passes
/// with any one of them deleted -- measured, the first guard-deletion run came
/// back FIVE SURVIVORS out of five. Naming the reason is what makes the
/// full-path gate observable: delete it and the decline still happens, but it
/// comes from sat-model reconstruction and says something else.
fn assert_declined_by_the_opaque_real_gate(result: &CheckResult) {
    let CheckResult::Unknown(reason) = result else {
        panic!("expected a decline, got {result:?}");
    };
    assert!(
        reason
            .detail
            .contains("opaque real UF applications or array reads"),
        "the decline must name the guard that fired, or a deleted guard is \
         indistinguishable from an intact one: {}",
        reason.detail
    );
}

// ---------------------------------------------------------------------------
// The six witnesses, each with its non-vacuity control beside it.
// ---------------------------------------------------------------------------

/// W1 (`quaternion_ds1_inuse_0013`, 27 atoms opaqued): the largest refusal, and
/// the plainest shape — a propositional contradiction whose two literals both
/// carry an opaque application. Before ADR-2065 the whole query was refused
/// because `linearize` met `(log x)`.
#[test]
fn w1_propositional_contradiction_through_an_opaque_application() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let logx = real_fn1(&mut arena, "log", x);
    let zero = r(&mut arena, 0);
    let p = arena.real_le(logx, zero).unwrap();
    let np = arena.not(p).unwrap();
    let both = arena.and(p, np).unwrap();
    assert_eq!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "p AND NOT p is unsat whatever p is; the opaque atom must not refuse the query"
    );
}

/// W1's control. Same query, the contradiction removed. If this says `unsat` the
/// witness above is proving nothing.
#[test]
fn w1_control_without_the_contradiction_is_not_unsat() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let logx = real_fn1(&mut arena, "log", x);
    let zero = r(&mut arena, 0);
    let p = arena.real_le(logx, zero).unwrap();
    assert_ne!(
        check(&mut arena, &[p]),
        CheckResult::Unsat,
        "a single satisfiable atom must not be refuted -- if it is, W1 measures a \
         dropped assertion, not the abstraction"
    );
}

/// W2 (`gauss_init_0292`, 4 atoms opaqued): the contradiction is between an
/// antecedent and its consequent, both over the SAME opaque term. This is the
/// one that needs the sharing: two occurrences of `(divide x y)` must take ONE
/// column, which is sound because the arena is hash-consed.
#[test]
fn w2_shared_opaque_term_carries_the_contradiction() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let d = real_fn2(&mut arena, "divide", x, y);
    let one = r(&mut arena, 1);
    let two = r(&mut arena, 2);
    let lo = arena.real_ge(d, two).unwrap(); // divide(x,y) >= 2
    let hi = arena.real_le(d, one).unwrap(); // divide(x,y) <= 1
    let both = arena.and(lo, hi).unwrap();
    assert_eq!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "2 <= d <= 1 is unsat; it is only visible if BOTH occurrences of divide(x,y) \
         take the same column"
    );
}

/// W2's control: widen the window so the same two atoms are consistent.
#[test]
fn w2_control_consistent_window_is_not_unsat() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let d = real_fn2(&mut arena, "divide", x, y);
    let one = r(&mut arena, 1);
    let two = r(&mut arena, 2);
    let lo = arena.real_ge(d, one).unwrap();
    let hi = arena.real_le(d, two).unwrap();
    let both = arena.and(lo, hi).unwrap();
    assert_ne!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "1 <= d <= 2 is satisfiable"
    );
}

/// W3 (`gauss_array_0490`, 2 atoms opaqued): the array read. `(select a 0)`
/// bounded both ways.
#[test]
fn w3_array_read_of_real_sort_carries_the_contradiction() {
    let mut arena = TermArena::new();
    let s = real_select(&mut arena, "s_values7", 0);
    let zero = r(&mut arena, 0);
    let one = r(&mut arena, 1);
    let lo = arena.real_ge(s, one).unwrap();
    let hi = arena.real_lt(s, zero).unwrap();
    let both = arena.and(lo, hi).unwrap();
    assert_eq!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "s >= 1 AND s < 0 is unsat; `select` of real sort must be a legal leaf"
    );
}

/// W3's control.
#[test]
fn w3_control_consistent_array_read_is_not_unsat() {
    let mut arena = TermArena::new();
    let s = real_select(&mut arena, "s_values7", 0);
    let zero = r(&mut arena, 0);
    let one = r(&mut arena, 1);
    let lo = arena.real_ge(s, zero).unwrap();
    let hi = arena.real_le(s, one).unwrap();
    let both = arena.and(lo, hi).unwrap();
    assert_ne!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "0 <= s <= 1 is satisfiable"
    );
}

/// W4 (`gauss_array_0289`): two DIFFERENT array reads plus one genuine
/// arithmetic step — ADR-2050's `x >= 1 ⊢ x > 0` shape, with the opaque terms as
/// leaves of a linear combination rather than as whole atoms.
#[test]
fn w4_opaque_reads_as_leaves_of_a_linear_combination() {
    let mut arena = TermArena::new();
    let s0 = real_select(&mut arena, "s_values7", 0);
    let s1 = real_select(&mut arena, "s_values7", 1);
    let one = r(&mut arena, 1);
    let zero = r(&mut arena, 0);
    let sum = arena.real_add(s0, s1).unwrap();
    let ge1 = arena.real_ge(sum, one).unwrap(); // s0 + s1 >= 1
    let le0 = arena.real_le(sum, zero).unwrap(); // s0 + s1 <= 0
    let both = arena.and(ge1, le0).unwrap();
    assert_eq!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "s0+s1 >= 1 AND s0+s1 <= 0 is unsat; the two reads must be independent \
         COLUMNS, not a refusal"
    );
}

/// W4's control.
#[test]
fn w4_control_consistent_sum_is_not_unsat() {
    let mut arena = TermArena::new();
    let s0 = real_select(&mut arena, "s_values7", 0);
    let s1 = real_select(&mut arena, "s_values7", 1);
    let one = r(&mut arena, 1);
    let zero = r(&mut arena, 0);
    let sum = arena.real_add(s0, s1).unwrap();
    let ge0 = arena.real_ge(sum, zero).unwrap();
    let le1 = arena.real_le(sum, one).unwrap();
    let both = arena.and(ge0, le1).unwrap();
    assert_ne!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "0 <= s0+s1 <= 1 is satisfiable"
    );
}

/// W5 (`gauss_array_0013`): an opaque term mixed with an ORDINARY real symbol,
/// which is the case that catches a column-space bug — the symbol columns and
/// the opaque columns share one index space, and `vars.len()` counts only the
/// former.
#[test]
fn w5_opaque_and_ordinary_columns_in_one_system() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let logx = real_fn1(&mut arena, "log", x);
    let two = r(&mut arena, 2);
    let zero = r(&mut arena, 0);
    // x >= 2  AND  log(x) >= x  AND  log(x) <= 0
    let a = arena.real_ge(x, two).unwrap();
    let b = arena.real_ge(logx, x).unwrap();
    let c = arena.real_le(logx, zero).unwrap();
    let ab = arena.and(a, b).unwrap();
    let all = arena.and(ab, c).unwrap();
    assert_eq!(
        check(&mut arena, &[all]),
        CheckResult::Unsat,
        "x >= 2, log(x) >= x, log(x) <= 0 refutes with the opaque term as ONE \
         column beside the symbol column for x"
    );
}

/// W5's control: drop the upper bound on the opaque term. If `vars.len()` were
/// still sizing the tableau this would be the row that mis-indexes.
#[test]
fn w5_control_without_the_upper_bound_is_not_unsat() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let logx = real_fn1(&mut arena, "log", x);
    let two = r(&mut arena, 2);
    let a = arena.real_ge(x, two).unwrap();
    let b = arena.real_ge(logx, x).unwrap();
    let ab = arena.and(a, b).unwrap();
    assert_ne!(
        check(&mut arena, &[ab]),
        CheckResult::Unsat,
        "x >= 2 with log(x) >= x is satisfiable"
    );
}

/// W6 (`gauss_array_0390`, 3 atoms opaqued): a nested opaque term — an
/// application whose ARGUMENT is itself an array read. The abstraction must
/// stop at the outermost real-sorted node it cannot linearize and not descend
/// into it looking for something to refuse.
#[test]
fn w6_nested_opaque_term_is_abstracted_at_the_outermost_node() {
    let mut arena = TermArena::new();
    let s = real_select(&mut arena, "s_values7", 3);
    let nested = real_fn1(&mut arena, "log", s);
    let five = r(&mut arena, 5);
    let four = r(&mut arena, 4);
    let lo = arena.real_ge(nested, five).unwrap();
    let hi = arena.real_le(nested, four).unwrap();
    let both = arena.and(lo, hi).unwrap();
    assert_eq!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "5 <= log(select(a,3)) <= 4 is unsat"
    );
}

/// W6's control.
#[test]
fn w6_control_consistent_nested_term_is_not_unsat() {
    let mut arena = TermArena::new();
    let s = real_select(&mut arena, "s_values7", 3);
    let nested = real_fn1(&mut arena, "log", s);
    let four = r(&mut arena, 4);
    let five = r(&mut arena, 5);
    let lo = arena.real_ge(nested, four).unwrap();
    let hi = arena.real_le(nested, five).unwrap();
    let both = arena.and(lo, hi).unwrap();
    assert_ne!(
        check(&mut arena, &[both]),
        CheckResult::Unsat,
        "4 <= log(select(a,3)) <= 5 is satisfiable"
    );
}

// ---------------------------------------------------------------------------
// The sat side. These are the wrong-verdict tests.
// ---------------------------------------------------------------------------

/// **Congruence.** `x = y` entails `f(x) = f(y)`, so `f(x) > f(y)` is UNSAT.
/// The abstraction gives `f(x)` and `f(y)` independent columns, so the
/// ABSTRACTION is satisfiable. Returning `sat` here would be a wrong verdict
/// shipped — a model of a relaxation presented as a model of the query.
///
/// The assertion is `!= Sat`, not `== Unsat`: deciding this needs `UFLRA`, and
/// declining is the correct behaviour for this rung.
#[test]
fn congruence_violating_abstraction_must_never_become_sat() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let xy = arena.eq(x, y).unwrap();
    let gt = arena.real_gt(fx, fy).unwrap();
    let both = arena.and(xy, gt).unwrap();
    let result = check(&mut arena, &[both]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x = y AND f(x) > f(y) is UNSAT by congruence; the abstraction is satisfiable \
         and a `sat` here is a wrong verdict: {result:?}"
    );
    assert_declined_by_the_opaque_real_gate(&result);
}

/// The same defect through the **array axioms**: `select(store(a,i,v), i) = v`,
/// so `select(store(a,i,v), i) > v` is unsat. Two opaque columns in the
/// abstraction, hence satisfiable there.
#[test]
fn array_axiom_violating_abstraction_must_never_become_sat() {
    let mut arena = TermArena::new();
    let a = arena
        .array_var_with_sorts("a", Sort::Int, Sort::Real)
        .unwrap();
    let i = arena.int_const(7);
    let v = arena.real_var("v").unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(stored, i).unwrap();
    let gt = arena.real_gt(read, v).unwrap();
    let result = check(&mut arena, &[gt]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "select(store(a,i,v),i) > v is UNSAT by read-over-write; a `sat` is a wrong \
         verdict: {result:?}"
    );
    assert_declined_by_the_opaque_real_gate(&result);
}

/// The plainest form: an abstraction that is satisfiable and carries an opaque
/// column must not yield a model. There is nothing to decide here — the query
/// IS satisfiable — but a `sat` would be accompanied by a model that binds no
/// value for `g`, which is not a model of this query at all.
///
/// This is the test that dies when the `has_opaque_real_apps` gate before
/// `finish_sat` is deleted.
#[test]
fn a_satisfiable_abstraction_with_an_opaque_column_yields_no_model() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let g = arena
        .declare_fun("g", &[Sort::Real], Sort::Real)
        .expect("declare g");
    let gx = arena.apply(g, &[x]).unwrap();
    let zero = r(&mut arena, 0);
    let ge = arena.real_ge(gx, zero).unwrap();
    let result = check(&mut arena, &[ge]);
    match result {
        CheckResult::Sat(model) => panic!(
            "the abstraction of `g(x) >= 0` is satisfiable, but its solution binds no \
             value for `g` and so is not a model of this query; got {model:?}"
        ),
        CheckResult::Unsat => panic!("`g(x) >= 0` is satisfiable; `unsat` is a wrong verdict"),
        CheckResult::Unknown(_) => {}
    }
    assert_declined_by_the_opaque_real_gate(&result);
}

// ---------------------------------------------------------------------------
// The abstraction must not become the ONLY answer: `unsat` still has to be
// right about the original query.
// ---------------------------------------------------------------------------

/// The direction that DOES transfer, stated as a test rather than as a comment:
/// a refutation found over the relaxation is a refutation of the original, and
/// an independent check of the same query without any opaque term agrees.
///
/// Read as a pair with `w1_control_…`: together they say the route's `unsat` is
/// about the query and not about the abstraction.
#[test]
fn an_unsat_over_the_relaxation_agrees_with_the_unabstracted_query() {
    // With the opaque term.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let hx = real_fn1(&mut arena, "h", x);
    let one = r(&mut arena, 1);
    let zero = r(&mut arena, 0);
    let a = arena.real_ge(hx, one).unwrap();
    let b = arena.real_le(hx, zero).unwrap();
    let both = arena.and(a, b).unwrap();
    assert_eq!(check(&mut arena, &[both]), CheckResult::Unsat);

    // The identical shape with a plain symbol in place of `h(x)`: same verdict,
    // reached without the abstraction at all.
    let mut plain = TermArena::new();
    let t = plain.real_var("t").unwrap();
    let one = plain.real_const(Rational::integer(1));
    let zero = plain.real_const(Rational::integer(0));
    let a = plain.real_ge(t, one).unwrap();
    let b = plain.real_le(t, zero).unwrap();
    let both = plain.and(a, b).unwrap();
    assert_eq!(
        check(&mut plain, &[both]),
        CheckResult::Unsat,
        "the unabstracted shape must be unsat too, or the witness above is about \
         the abstraction rather than about the query"
    );
}

// ---------------------------------------------------------------------------
// The enumeration itself, pinned.
// ---------------------------------------------------------------------------

/// The `Sat`-exit enumeration (ADR-2065 §1) is only worth having if a NEW `Sat`
/// exit cannot appear without someone re-running it. This pins the counts the
/// enumeration was taken over.
///
/// It derives the counts from the SOURCE, not from a remembered list, and the
/// numbers are the ones `bench-results/real-opaque-20260914/satexits.py`
/// printed. If this fails, the right response is to re-run that script and
/// re-check `ref/sat-exits.md` — **not** to bump the number here, which would
/// turn the guard into a record of whoever edited last.
///
/// Test regions are excluded by brace balance. The first version of the
/// enumerator cut each file at its first `#[cfg(test)]` line instead, and
/// because that attribute marks a test-only helper in the MIDDLE of both files
/// it discarded 2,397 and 3,133 lines of production code — including a whole
/// `CheckResult::Sat` construction — while printing a clean-looking result.
#[test]
fn the_sat_exit_enumeration_still_describes_the_source() {
    let lra = include_str!("../src/lra.rs");
    let dpll = include_str!("../src/dpll_lia.rs");

    assert_eq!(
        (
            production_sat_sites(lra, "Decision::Sat("),
            production_sat_sites(lra, "CheckResult::Sat("),
            production_sat_sites(dpll, "CheckResult::Sat("),
        ),
        (3, 3, 6),
        "the `Sat` construction sites moved. Re-run \
         `bash bench-results/real-opaque-20260914/sat-exits.sh`, decide for each new \
         site whether an ABSTRACTED system can reach it, and update \
         `ref/sat-exits.md`. Do not just change these numbers."
    );

    // The closures, by presence. A guard that is deleted rather than moved must
    // not pass this file silently — the guard-deletion matrix in
    // `ref/guard-deletion.md` is what says each one is load-bearing.
    assert_eq!(
        lra.matches("if ctx.has_opaque_vars() {").count(),
        2,
        "both `Decision::Sat` exits reachable from an abstracted system are closed \
         on `has_opaque_vars`. The `if` spelling is load-bearing in this pin: the \
         INTEGER collector's own (pre-existing, unrelated) downgrade binds the same \
         predicate with `let`, and counting the bare call name gives 4"
    );
    assert_eq!(
        dpll.matches("self.ctx.has_opaque_real_apps(arena)").count(),
        2,
        "both refinement-loop sat exits are gated on `has_opaque_real_apps`"
    );
    assert!(
        dpll.contains("theory_model(arena, &real_lits, real_model_oracle, deadline)"),
        "sat-model reconstruction must use the UNabstracted real oracle"
    );
}

/// Counts `needle` outside every `#[cfg(test)]` region, skipping each region by
/// brace balance from the attribute to the column-0 close brace.
fn production_sat_sites(src: &str, needle: &str) -> usize {
    let lines: Vec<&str> = src.lines().collect();
    let mut in_test = vec![false; lines.len()];
    let mut i = 0;
    while i < lines.len() {
        if lines[i].starts_with("#[cfg(test)]") {
            // Signed depth without a cast: `isize::try_from` on a brace count
            // cannot fail for any file this repository holds, and a `saturating`
            // fallback would silently mis-scope a region rather than fail.
            let mut depth: isize = 0;
            let mut opened = false;
            let mut j = i;
            while j < lines.len() {
                let opens = isize::try_from(lines[j].matches('{').count()).expect("brace count");
                let closes = isize::try_from(lines[j].matches('}').count()).expect("brace count");
                depth += opens - closes;
                if opens > 0 {
                    opened = true;
                }
                if opened && depth <= 0 {
                    break;
                }
                j += 1;
            }
            assert!(
                opened && j < lines.len() && lines[j].trim_end() == "}",
                "a cfg(test) region starting at line {} does not end at a column-0 \
                 close brace; this counter cannot be trusted on that shape and must \
                 fail rather than skip it",
                i + 1
            );
            for entry in in_test.iter_mut().take(j + 1).skip(i) {
                *entry = true;
            }
            i = j + 1;
        } else {
            i += 1;
        }
    }
    lines
        .iter()
        .enumerate()
        .filter(|(k, line)| !in_test[*k] && line.contains(needle) && !line.contains("::Sat(_)"))
        .count()
}
